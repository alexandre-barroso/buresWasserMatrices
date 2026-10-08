"""Original finite-data audit of vowel marginal summaries (exploratory revision).

Input: pinned author-authorized Hillenbrand1995 ZIP, read without extraction.
No audio, inherited executable code or serialized objects are loaded.
"""
from pathlib import Path
from zipfile import ZipFile
from collections import Counter, defaultdict
from itertools import combinations
import argparse, csv, datetime, hashlib, json, platform, re
import numpy as np

VOWELS = ['iy', 'ih', 'ei', 'eh', 'ae', 'ah', 'aw', 'oa', 'oo', 'uw', 'uh', 'er']
GROUPS = ['men', 'women', 'children']
GROUP = {'m': 'men', 'w': 'women', 'b': 'children', 'g': 'children'}
ARCHIVE_SHA256 = '2560548591e3a726c88549b6dc9d226995616c26874d601c69fee8b9eee9d730'


def read_data(path):
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == ARCHIVE_SHA256
    with ZipFile(path) as z:
        raw = z.read('vowdata.dat')
    rows = []
    for line in raw.decode('ascii').splitlines():
        vals = line.split()
        if not vals or not re.fullmatch(r'[mwbg]\d{2}[a-z]{2}', vals[0]):
            continue
        assert len(vals) == 16 and vals[0][3:] in VOWELS
        nums = [int(v) for v in vals[1:]]
        rows.append({'token': vals[0], 'speaker': vals[0][:3], 'vowel': vals[0][3:],
                     'group': GROUP[vals[0][0]], 'x': nums[2:4], 'observed': min(nums[2:4]) > 0})
    assert len({r['token'] for r in rows}) == len(rows)
    by = defaultdict(list)
    for r in rows:
        by[r['speaker']].append(r)
    assert len(rows) == 1668 and len(by) == 139
    assert all(sorted(r['vowel'] for r in rr) == sorted(VOWELS) for rr in by.values())
    return rows, {'tokens': len(rows), 'speakers': len(by),
                  'groups': dict(Counter(rr[0]['group'] for rr in by.values())),
                  'paired_missing_by_group': {g: sum(r['group'] == g and not r['observed'] for r in rows) for g in GROUPS},
                  'vowdata_sha256': hashlib.sha256(raw).hexdigest()}


def profiles(rows, group, omit=None):
    out = {}
    for v in VOWELS:
        subset = [r for r in rows if r['group'] == group and r['vowel'] == v and r['speaker'] != omit and r['observed']]
        x = np.asarray([r['x'] for r in subset], dtype=float)
        assert x.shape[0] >= 3 and x.shape[1] == 2
        mu = x.mean(axis=0)
        centered = x - mu
        covariance = centered.T @ centered / (len(x) - 1)
        assert np.allclose(covariance, np.cov(x.T, ddof=1), atol=1e-9, rtol=1e-13)
        sd = np.sqrt(np.diag(covariance))
        out[v] = {'mean': mu, 'covariance': covariance, 'sd': sd, 'n': len(x)}
    return out


def root_psd(matrix):
    values, vectors = np.linalg.eigh(matrix)
    assert values.min() >= -1e-9 * max(1.0, np.max(np.abs(values)))
    return (vectors * np.sqrt(np.maximum(values, 0))) @ vectors.T


def distances(a, b):
    mu, nu, A, B, x, y = a['mean'], b['mean'], a['covariance'], b['covariance'], a['sd'], b['sd']
    M = float((mu - nu) @ (mu - nu))
    T = float(np.trace(A) + np.trace(B))
    prod = x * y
    lower = M + float((x - y) @ (x - y))
    upper = M + T - 2 * max(0., 2 * float(prod.max()) - float(prod.sum()))
    detA, detB = max(float(np.linalg.det(A)), 0.), max(float(np.linalg.det(B)), 0.)
    F = np.sqrt(max(float(np.trace(A @ B)) + 2 * np.sqrt(detA * detB), 0.))
    G = M + T - 2 * float(F)
    C = root_psd(A)
    eigen = M + T - 2 * float(np.trace(root_psd(C @ B @ C)))
    error = abs(G - eigen) / max(1., abs(G))
    assert error < 2e-10, (G, eigen, error)
    tol = 1e-9 * max(1., M + T)
    assert lower - tol <= G <= upper + tol and lower <= upper + tol
    return {'centroid': M, 'lower': lower, 'full': G, 'upper': upper,
            'loose_upper': M + T, 'independent_fidelity_relative_error': error}


def sign(x, scale):
    tolerance = 1e-10 * max(1., scale)
    return 1 if x > tolerance else -1 if x < -tolerance else 0


def order(lo_j, hi_j, lo_k, hi_k):
    s = max(1., abs(lo_j), abs(hi_j), abs(lo_k), abs(hi_k))
    if sign(hi_j - lo_k, s) < 0:
        return -1
    if sign(hi_k - lo_j, s) < 0:
        return 1
    return 0


def evaluate(p):
    ds = {i: {j: distances(p[i], p[j]) for j in VOWELS if j != i} for i in VOWELS}
    outcomes, nearest = [], []
    for i in VOWELS:
        target = ds[i]
        for j, k in combinations(target, 2):
            a, b = target[j], target[k]
            exact = order(a['lower'], a['upper'], b['lower'], b['upper'])
            loose = order(a['lower'], a['loose_upper'], b['lower'], b['loose_upper'])
            retained = sign(a['full'] - b['full'], max(a['full'], b['full']))
            diagonal = sign(a['lower'] - b['lower'], max(a['lower'], b['lower']))
            centroid = sign(a['centroid'] - b['centroid'], max(a['centroid'], b['centroid']))
            assert exact == 0 or exact == retained == diagonal
            assert loose == 0 or loose == exact
            outcomes.append({'reference': i, 'target_j': j, 'target_k': k, 'exact_order': exact,
                             'loose_order': loose, 'full_order': retained, 'diagonal_order': diagonal, 'centroid_order': centroid})
        possible, guaranteed = [], []
        for j, a in target.items():
            others = [b for k, b in target.items() if k != j]
            if all(sign(a['lower'] - b['upper'], max(a['lower'], b['upper'])) < 0 for b in others):
                possible.append(j)
            if all(sign(a['upper'] - b['lower'], max(a['upper'], b['lower'])) < 0 for b in others):
                guaranteed.append(j)
        full = min(target, key=lambda k: target[k]['full'])
        diagonal = min(target, key=lambda k: target[k]['lower'])
        centroid = min(target, key=lambda k: target[k]['centroid'])
        assert full in possible and diagonal in possible
        assert not guaranteed or guaranteed == [full]
        nearest.append({'reference': i, 'possible_unique': possible, 'guaranteed_unique': guaranteed,
                        'full': full, 'diagonal': diagonal, 'centroid': centroid})
    assert len(outcomes) == 660
    full_diag = [x for x in outcomes if x['full_order'] != x['diagonal_order']]
    summary = {'order_questions': len(outcomes), 'exact_certified': sum(x['exact_order'] != 0 for x in outcomes),
               'loose_certified': sum(x['loose_order'] != 0 for x in outcomes),
               'exact_additional': sum(x['exact_order'] != 0 and x['loose_order'] == 0 for x in outcomes),
               'full_diagonal_different_orders': len(full_diag),
               'full_centroid_different_orders': sum(x['full_order'] != x['centroid_order'] for x in outcomes),
               'guaranteed_nearest_references': sum(bool(x['guaranteed_unique']) for x in nearest),
               'diagonal_full_nearest_changes': sum(x['full'] != x['diagonal'] for x in nearest),
               'maximum_fidelity_relative_error': max(x['independent_fidelity_relative_error'] for r in ds.values() for x in r.values())}
    return {'summary': summary, 'distances': ds, 'orders': outcomes, 'nearest': nearest}


def serialize_profiles(p):
    return {v: {k: x.tolist() if isinstance(x, np.ndarray) else x for k, x in rec.items()} for v, rec in p.items()}


def transform_rows(rows, representation):
    if representation == 'raw_hz':
        return rows, {'selection': 'Paired-complete tokens per category; all other tokens retained',
                      'feature_units': 'Hz', 'scaling': 'None'}
    by = defaultdict(list)
    for r in rows:
        by[r['speaker']].append(r)
    keep = {s for s, rr in by.items() if len(rr) == 12 and all(r['observed'] for r in rr)}
    transformed = []
    for speaker in sorted(keep):
        rr = by[speaker]
        x = np.asarray([r['x'] for r in rr], dtype=float)
        if representation == 'lobanov_complete':
            mu = x.mean(axis=0)
            rms = np.sqrt(np.mean((x - mu) ** 2, axis=0))
            assert np.all(rms > 0)
            x = (x - mu) / rms
            assert np.max(abs(x.mean(axis=0))) < 1e-12
            assert np.allclose(np.mean(x ** 2, axis=0), 1, atol=1e-13, rtol=0)
        for r, value in zip(rr, x):
            transformed.append({**r, 'x': value.tolist()})
    return transformed, {'selection': 'Complete 12-category paired steady-state F1/F2 panel',
                         'excluded_speakers': sorted(set(by) - keep),
                         'speakers_by_group': {g: sum(by[s][0]['group'] == g for s in keep) for g in GROUPS},
                         'feature_units': 'Within-speaker formant RMS units' if representation == 'lobanov_complete' else 'Hz',
                         'scaling': 'Separate per-speaker F1/F2 centering and RMS across12 vowels, denominator12' if representation == 'lobanov_complete' else 'None'}


def run(archive, output, jackknife, representation):
    assert not output.exists()
    output.mkdir(parents=True)
    rows, counts = read_data(archive)
    rows, transform = transform_rows(rows, representation)
    result = {'at': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'status': 'EXPLORATORY_BENCHMARK_NOT_YET_SCIENTIFICALLY_ACCEPTED',
              'input': {'archive_sha256': ARCHIVE_SHA256, **counts},
              'environment': {'python': platform.python_version(), 'numpy': np.__version__},
              'representation': representation, 'scale': transform, 'covariance_denominator': 'n-1',
              'measurement': 'F1/F2 at manually selected steady state', 'groups': {}}
    for group in GROUPS:
        p = profiles(rows, group)
        value = evaluate(p)
        value['profiles'] = serialize_profiles(p)
        if jackknife:
            omitted = []
            for speaker in sorted({r['speaker'] for r in rows if r['group'] == group}):
                check = evaluate(profiles(rows, group, omit=speaker))
                omitted.append({'omitted_speaker': speaker, **check['summary'],
                                'order_status_changes_from_full': sum(a['exact_order'] != b['exact_order'] for a, b in zip(value['orders'], check['orders'])),
                                'nearest': check['nearest']})
            value['leave_one_speaker_out'] = omitted
        result['groups'][group] = value
        print(json.dumps({'group': group, **value['summary']}, ensure_ascii=False), flush=True)
    (output / 'results.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    (output / 'source.sha256').write_text(hashlib.sha256(Path(__file__).read_bytes()).hexdigest() + '\n')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--leave-one-speaker-out', action='store_true')
    ap.add_argument('--representation', choices=['raw_hz', 'raw_complete', 'lobanov_complete'], default='raw_hz')
    a = ap.parse_args()
    run(a.archive, a.output, a.leave_one_speaker_out, a.representation)
