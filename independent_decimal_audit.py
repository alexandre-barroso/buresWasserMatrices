"""Independent 80-digit audit of H95 results, without analysis-code imports.

Read public numeric text in its original ZIP. Recompute every main and
leave-one-speaker-out summary with Decimal, retaining exact decimal input.
Only newly computed aggregates and checks are exported.
"""
from collections import defaultdict
from decimal import Decimal as D, getcontext
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from zipfile import ZipFile
import argparse
import datetime
import json
import re

getcontext().prec = 80
ZERO = D(0)
ONE = D(1)
VOWELS = {'iy', 'ih', 'ei', 'eh', 'ae', 'ah', 'aw', 'oa', 'oo', 'uw', 'uh', 'er'}
GROUPS = {'men', 'women', 'children'}
ARCHIVE_SHA256 = '2560548591e3a726c88549b6dc9d226995616c26874d601c69fee8b9eee9d730'


def sign(value):
    return (value > 0) - (value < 0)


def norm_error(a, b):
    return abs(a - D(str(b))) / max(ONE, abs(a))


def profile(rows, group, omit=None):
    sets = defaultdict(list)
    for speaker, vowel, g, x, y in rows:
        if g == group and speaker != omit:
            sets[vowel].append((x, y))
    result = {}
    for vowel, values in sets.items():
        n = len(values)
        mx = sum(v[0] for v in values) / n
        my = sum(v[1] for v in values) / n
        xx = sum((x - mx) ** 2 for x, y in values) / (n - 1)
        yy = sum((y - my) ** 2 for x, y in values) / (n - 1)
        xy = sum((x - mx) * (y - my) for x, y in values) / (n - 1)
        assert xx > 0 and yy > 0 and xx * yy - xy ** 2 > 0
        result[vowel] = {"n": n, "mean": [mx, my], "covariance": [[xx, xy], [xy, yy]], "sd": [xx.sqrt(), yy.sqrt()]}
    return result


def pair(a, b):
    mean = sum((x - y) ** 2 for x, y in zip(a["mean"], b["mean"]))
    ax, ay = a["sd"]
    bx, by = b["sd"]
    low = mean + (ax - bx) ** 2 + (ay - by) ** 2
    A, B = a["covariance"], b["covariance"]
    total = A[0][0] + A[1][1] + B[0][0] + B[1][1]
    high = mean + total - 2 * abs(ax * bx - ay * by)
    trace_product = A[0][0] * B[0][0] + 2 * A[0][1] * B[0][1] + A[1][1] * B[1][1]
    da = A[0][0] * A[1][1] - A[0][1] ** 2
    db = B[0][0] * B[1][1] - B[0][1] ** 2
    fid = (trace_product + 2 * (da * db).sqrt()).sqrt()
    actual = mean + total - 2 * fid
    assert ZERO <= low <= actual <= high
    assert abs((high - low) - 4 * min(ax * bx, ay * by)) < D("1e-65")
    return {"centroid": mean, "lower": low, "full": actual, "upper": high, "loose_upper": mean + total}


def evaluate(p, expected=None):
    assert set(p) == VOWELS
    codes = sorted(p)
    ds = {i: {} for i in codes}
    for i, j in combinations(codes, 2):
        ds[i][j] = ds[j][i] = pair(p[i], p[j])
    states = {}
    nearest = {}
    margins = []
    distance_error = ZERO
    profile_error = ZERO
    for i in codes:
        others = sorted(ds[i])
        for j, k in combinations(others, 2):
            a, b = ds[i][j], ds[i][k]
            strict = -1 if a["upper"] < b["lower"] else 1 if b["upper"] < a["lower"] else 0
            loose = -1 if a["loose_upper"] < b["lower"] else 1 if b["loose_upper"] < a["lower"] else 0
            values = {"exact_order": strict, "loose_order": loose, "full_order": sign(a["full"] - b["full"]), "diagonal_order": sign(a["lower"] - b["lower"]), "centroid_order": sign(a["centroid"] - b["centroid"])}
            assert not strict or strict == values["full_order"] == values["diagonal_order"]
            assert not loose or loose == strict
            states[(i, j, k)] = values
            for x, y, label in [(a["upper"], b["lower"], "upper_j_lower_k"), (b["upper"], a["lower"], "upper_k_lower_j"), (a["lower"], b["upper"], "possible_nearest"), (a["loose_upper"], b["lower"], "loose_j_k"), (b["loose_upper"], a["lower"], "loose_k_j"), (a["full"], b["full"], "full"), (a["lower"], b["lower"], "diagonal"), (a["centroid"], b["centroid"], "centroid")]:
                margins.append({"reference": i, "j": j, "k": k, "comparison": label, "absolute": abs(x - y), "relative": abs(x - y) / max(ONE, abs(x), abs(y))})
        possible = [j for j in others if all(ds[i][j]["lower"] < ds[i][k]["upper"] for k in others if k != j)]
        guaranteed = [j for j in others if all(ds[i][j]["upper"] < ds[i][k]["lower"] for k in others if k != j)]
        full = min(others, key=lambda j: ds[i][j]["full"])
        diagonal = min(others, key=lambda j: ds[i][j]["lower"])
        centroid = min(others, key=lambda j: ds[i][j]["centroid"])
        assert full in possible and diagonal in possible
        nearest[i] = {"possible_unique": possible, "guaranteed_unique": guaranteed, "full": full, "diagonal": diagonal, "centroid": centroid}
    summaries = {
        "order_questions": len(states),
        "exact_certified": sum(v["exact_order"] != 0 for v in states.values()),
        "loose_certified": sum(v["loose_order"] != 0 for v in states.values()),
        "exact_additional": sum(v["exact_order"] != 0 and v["loose_order"] == 0 for v in states.values()),
        "full_diagonal_different_orders": sum(v["full_order"] != v["diagonal_order"] for v in states.values()),
        "full_centroid_different_orders": sum(v["full_order"] != v["centroid_order"] for v in states.values()),
        "guaranteed_nearest_references": sum(bool(v["guaranteed_unique"]) for v in nearest.values()),
        "diagonal_full_nearest_changes": sum(v["full"] != v["diagonal"] for v in nearest.values())
    }
    if expected:
        for k, v in summaries.items():
            assert v == expected["summary"][k], (k, v, expected["summary"][k])
        seen_orders = set()
        for o in expected.get("orders", []):
            i, j, k = o["reference"], o["target_j"], o["target_k"]
            reverse = j > k
            canonical = (i, k, j) if reverse else (i, j, k)
            assert canonical not in seen_orders
            seen_orders.add(canonical)
            got = states[(i, k, j) if reverse else (i, j, k)]
            for key, v in got.items():
                assert (-v if reverse else v) == o[key], (i, j, k, key)
        if "orders" in expected:
            assert seen_orders == set(states)
        assert len(expected["nearest"]) == 12
        assert {n['reference'] for n in expected['nearest']} == VOWELS
        for n in expected.get("nearest", []):
            got = nearest[n["reference"]]
            for k, v in got.items():
                assert (sorted(n[k]) if isinstance(v, list) else n[k]) == v, (n["reference"], k)
        if "distances" in expected:
            assert set(expected['distances']) == VOWELS
            assert set(expected['profiles']) == VOWELS
        for i, vals in expected.get("distances", {}).items():
            assert set(vals) == VOWELS - {i}
            for j, vals2 in vals.items():
                for key in ds[i][j]:
                    error = norm_error(ds[i][j][key], vals2[key])
                    assert error < D("5e-12"), (i, j, key, error)
                    distance_error = max(distance_error, error)
        for i, vals in expected.get("profiles", {}).items():
            assert p[i]["n"] == vals["n"]
            for key in ["mean", "sd"]:
                for x, y in zip(p[i][key], vals[key]):
                    profile_error = max(profile_error, norm_error(x, y))
            for row1, row2 in zip(p[i]["covariance"], vals["covariance"]):
                for x, y in zip(row1, row2):
                    profile_error = max(profile_error, norm_error(x, y))
            assert profile_error < D("5e-12")
    smallest = min(margins, key=lambda m: m["relative"])
    # All primary and omission signs are farther from zero than the analysis's
    # floating threshold; this check does not reuse that threshold to decide.
    assert smallest["relative"] > D("1e-10"), smallest
    return summaries, states, nearest, {"minimum_scaled_decision_margin": smallest, "maximum_distance_relative_difference": distance_error, "maximum_profile_relative_difference": profile_error}


def nearest_witnesses(p, nearest):
    """Check concrete outer-product endpoints for every possible unique winner.

    The reference is a*a^T, generally different from its observed covariance.
    In two dimensions the selected target uses b*b^T; every other target uses
    (b1,-b2)*(b1,-b2)^T. These are unrestricted real PSD completions.
    """
    checked = []
    for i, record in nearest.items():
        for j in record['possible_unique']:
            ds = {}
            u = p[i]['sd']
            for k in sorted(VOWELS - {i}):
                rho = ONE if k == j else -ONE
                v = [p[k]['sd'][0], rho * p[k]['sd'][1]]
                value = sum((x-y)**2 for x,y in zip(p[i]['mean'],p[k]['mean']))
                value += sum(x*x for x in u) + sum(x*x for x in v)
                value -= 2 * abs(sum(x*y for x,y in zip(u,v)))
                endpoint = pair(p[i],p[k])['lower' if k == j else 'upper']
                assert abs(value-endpoint) < D('1e-65') * max(ONE,abs(endpoint))
                ds[k] = value
            gap = min(ds[k]-ds[j] for k in ds if k != j)
            assert gap > 0
            checked.append({'reference':i,'unique_nearest':j,'minimum_gap':str(gap)})
    return checked


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--archive", type=Path, required=True)
    ap.add_argument("--results-root", type=Path, required=True,
                    help="Directory containing raw_hz, raw_complete and lobanov_complete/results.json")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, 'Run without -O; assertions are verification obligations'
    assert not args.output.exists(), 'Choose a new output file'
    input_hash = sha256(args.archive.read_bytes()).hexdigest()
    assert input_hash == ARCHIVE_SHA256
    rows = []
    with ZipFile(args.archive) as archive:
        for line in archive.read("vowdata.dat").decode("ascii").splitlines():
            v = line.split()
            if v and re.fullmatch(r"[mwbg][0-9]{2}[a-z]{2}", v[0]):
                assert len(v) == 16
                rows.append((v[0][:3], v[0][3:], {"m": "men", "w": "women", "b": "children", "g": "children"}[v[0][0]], D(v[3]), D(v[4])))
    panel = defaultdict(list)
    for row in rows:
        panel[row[0]].append(row)
    assert len(rows) == 1668 and len(panel) == 139
    assert len({r[:2] for r in rows}) == len(rows)
    assert all(len(rr) == 12 and {r[1] for r in rr} == VOWELS for rr in panel.values())
    complete = {s for s, rr in panel.items() if len(rr) == 12 and all(r[3] > 0 and r[4] > 0 for r in rr)}
    representation_rows = {"raw_hz": [r for r in rows if r[3] > 0 and r[4] > 0], "raw_complete": [r for r in rows if r[0] in complete], "lobanov_complete": []}
    for speaker in sorted(complete):
        rr = panel[speaker]
        mean = [sum(r[i] for r in rr) / 12 for i in [3, 4]]
        rms = [(sum((r[i + 3] - mean[i]) ** 2 for r in rr) / 12).sqrt() for i in [0, 1]]
        for r in rr:
            representation_rows["lobanov_complete"].append((*r[:3], (r[3] - mean[0]) / rms[0], (r[4] - mean[1]) / rms[1]))
    result = {"status": "PASS_INDEPENDENT_80_DIGIT_RECOMPUTATION", "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "precision_decimal_digits": getcontext().prec, "input_sha256": input_hash, "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(), "representations": {}, "failures": [], "limits": ["Finite numerical validation, not a Python-to-Lean proof.", "Decimal arithmetic uses rounded irrational square roots; it is not a certified interval-arithmetic package.", "No perceptual, population, general acoustic validity or novelty certification."]}
    coverage = {'main_cohorts':0, 'speaker_omissions':0, 'order_questions':0, 'main_nearest_witnesses':0}
    for representation, rr in representation_rows.items():
        path = args.results_root / representation / "results.json"
        observed = json.loads(path.read_text())
        assert observed['representation'] == representation
        assert observed['input']['archive_sha256'] == input_hash
        assert set(observed['groups']) == GROUPS
        entry = {"compared_results_sha256": sha256(path.read_bytes()).hexdigest(), "groups": {}}
        for group, expected in observed["groups"].items():
            p = profile(rr, group)
            summary, states, nearest, checks = evaluate(p, expected)
            witnesses = nearest_witnesses(p, nearest)
            item = {"summary": summary, "nearest": nearest, "numerical_checks": checks,
                    "nearest_witnesses":witnesses, "leave_one_speaker_out": []}
            coverage['main_cohorts'] += 1
            coverage['order_questions'] += len(states)
            coverage['main_nearest_witnesses'] += len(witnesses)
            speakers = {r[0] for r in rr if r[2] == group}
            assert len(expected['leave_one_speaker_out']) == len(speakers)
            assert {r['omitted_speaker'] for r in expected['leave_one_speaker_out']} == speakers
            for omit in expected["leave_one_speaker_out"]:
                s = omit["omitted_speaker"]
                su, st, ne, ch = evaluate(profile(rr, group, s), {"summary": omit, "nearest": omit["nearest"]})
                changes = sum(st[k]["exact_order"] != states[k]["exact_order"] for k in states)
                assert changes == omit["order_status_changes_from_full"]
                coverage['speaker_omissions'] += 1
                coverage['order_questions'] += len(st)
                item["leave_one_speaker_out"].append({"omitted_speaker": s, "summary": su, "order_status_changes_from_full": changes, "numerical_checks": ch})
            entry["groups"][group] = item
            print(json.dumps({"representation": representation, "group": group, "status": "PASS", "main_order_questions": len(states), "leave_one_speaker_out_runs": len(item["leave_one_speaker_out"])}), flush=True)
        result["representations"][representation] = entry
    assert coverage == {'main_cohorts':9, 'speaker_omissions':399,
                        'order_questions':269280, 'main_nearest_witnesses':133}, coverage
    result['coverage'] = coverage
    assert sha256(args.archive.read_bytes()).hexdigest() == input_hash
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2, default=str) + "\n")
    print(json.dumps({"status": result["status"], "output_sha256": sha256(args.output.read_bytes()).hexdigest()}), flush=True)


if __name__ == "__main__":
    main()
