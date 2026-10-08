#!/usr/bin/env python3
"""Original finite counterexample search, independent of inherited scripts.

Only synthetic rational inputs are used. No numerical approximation to a
matrix square root is used. This is finite evidence, not an unbounded proof.
"""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from pathlib import Path
import json
import platform
import argparse
import sys


def interval(a, b):
    w = [x*y for x, y in zip(a, b)]
    s = sum(w, F(0))
    k = max(F(0), 2*max(w)-s)
    t = sum((x*x+y*y for x, y in zip(a, b)), F(0))
    return k, s, t-2*s, t-2*k


def matrix(a, r):
    return [[a[0]**2, r*a[0]*a[1]], [r*a[0]*a[1], a[1]**2]]


def det2(a):
    return a[0][0]*a[1][1]-a[0][1]*a[1][0]


def trace_product(a, b):
    return sum((a[i][j]*b[j][i] for i in range(2) for j in range(2)), F(0))


def exact_fidelity_enclosure(a, b, lo, hi):
    # For two by two PSD matrices, F(A,B)^2 = tr(AB)+2 sqrt(det A det B).
    c = trace_product(a, b)
    d = det2(a)*det2(b)
    assert d >= 0
    # Every squaring below is conditioned on both sides being nonnegative.
    upper = c <= hi*hi and 4*d <= (hi*hi-c)**2
    lower = lo*lo <= c or 4*d >= (lo*lo-c)**2
    return lower and upper


def gram(rows):
    return [[sum((x*y for x, y in zip(u, v)), F(0)) for v in rows] for u in rows]


def quadratic(a, b):
    return sum((a[i]*b[i][j]*a[j] for i in range(len(a)) for j in range(len(a))), F(0))


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: exact checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    scalars = (F(0), F(1, 2), F(1), F(2))
    correlations = (F(-1), F(-2, 3), F(-1, 3), F(0), F(1, 3), F(2, 3), F(1))
    cases = witnesses = stars = 0
    profiles = list(product(scalars, repeat=2))
    for a, b in product(profiles, repeat=2):
        lo, hi, _, _ = interval(a, b)
        for ra, rb in product(correlations, repeat=2):
            assert exact_fidelity_enclosure(matrix(a, ra), matrix(b, rb), lo, hi), (a,b,ra,rb)
            cases += 1
        w0, w1 = a[0]*b[0], a[1]*b[1]
        for step in range(9):
            f = lo + F(step, 8)*(hi-lo)
            rb = (f*f-w0*w0-w1*w1)/(2*w0*w1) if w0*w1 else F(0)
            assert -1 <= rb <= 1
            B = matrix(b, rb)
            assert det2(B) >= 0
            assert quadratic(a, B) == f*f
            witnesses += 1
    a = (F(1), F(2))
    targets = ((F(2), F(1)), (F(1,2), F(3,2)), (F(0), F(2)))
    for steps in product(range(9), repeat=3):
        for b, step in zip(targets, steps):
            lo, hi, _, _ = interval(a, b)
            f = lo + F(step,8)*(hi-lo)
            w0, w1 = a[0]*b[0], a[1]*b[1]
            rb = (f*f-w0*w0-w1*w1)/(2*w0*w1) if w0*w1 else F(0)
            assert quadratic(a, matrix(b,rb)) == f*f
        stars += 1
    # Exact rank-two target: lengths 3,4,5 close a planar triangle.
    rows = ((F(3), F(0)), (F(0),F(4)), (F(-3),F(-4)))
    B = gram(rows)
    assert [B[i][i] for i in range(3)] == [F(9), F(16), F(25)]
    assert quadratic((F(1),)*3, B) == 0
    # Rank-one target restriction: odd three-coordinate sums cannot be zero.
    rank_one_min = min(abs(sum(signs)) for signs in product((-1,1),repeat=3))
    assert rank_one_min == 1
    report = {
        'scope': 'finite independent synthetic exact-rational checks; not a general proof',
        'python': platform.python_version(),
        'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'two_dimensional_psd_pairs_checked': cases,
        'two_dimensional_attaining_witnesses_checked': witnesses,
        'shared_reference_three_target_tuples_checked': stars,
        'failures': [],
        'd3_rank_two_zero_fidelity_witness': {'a': ['1','1','1'], 'b':['3','4','5'],
            'B': [[str(x) for x in row] for row in B], 'quadratic_form':'0'},
        'd3_both_real_rank_one_counterexample': {'a': ['1']*3, 'b':['1']*3,
            'minimum_fidelity': '1', 'maximum_squared_distance': '4',
            'unrestricted_psd_maximum_squared_distance': '6'},
        'limitations': [
            'The two-dimensional square-root identity is used mathematically, not machine-proved by this Python checker.',
            'Witness fidelity uses the independently formalized rank-one reference identity only after that Lean proof passes.',
            'No inherited checker or source-data file is imported, executed, copied, or modified.'
        ]}
    out = args.output
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS_FINITE_CHECKS','cases':cases,'witnesses':witnesses,'star_tuples':stars}))


if __name__ == '__main__':
    main()
