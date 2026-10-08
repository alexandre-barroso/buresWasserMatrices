#!/usr/bin/env python3
"""Validate derived benchmark records and export the tables/figure-data CSVs.

This file never loads individual observations. Without a supplied public
archive, these are consistency checks on recorded aggregates, not a rerun of
the empirical analysis. Float comparisons use a declared relative tolerance.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import csv
import json
import math

REPRESENTATIONS = ('raw_hz', 'raw_complete', 'lobanov_complete')
GROUPS = ('men', 'women', 'children')
VOWELS = ('iy', 'ih', 'ei', 'eh', 'ae', 'ah', 'aw', 'oa', 'oo', 'uw', 'uh', 'er')
INPUT_SHA256 = '2560548591e3a726c88549b6dc9d226995616c26874d601c69fee8b9eee9d730'
SUMMARY_FIELDS = ('order_questions', 'exact_certified', 'loose_certified', 'exact_additional',
                  'full_diagonal_different_orders', 'full_centroid_different_orders',
                  'guaranteed_nearest_references', 'diagonal_full_nearest_changes')
EXPECTED_TOTALS = {
    'raw_hz': (1980, 1945, 1851, 94, 1, 8, 27, 0),
    'raw_complete': (1980, 1943, 1849, 94, 1, 11, 27, 0),
    'lobanov_complete': (1980, 1928, 1879, 49, 0, 1, 33, 0),
}


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


def compare(a, b, locator='root'):
    """Compare every substantive field, allowing only bounded float roundoff."""
    if isinstance(a, dict):
        assert isinstance(b, dict) and set(a) == set(b), locator
        for key in a:
            if locator == 'root' and key in ('at', 'environment', 'status'):
                continue
            compare(a[key], b[key], locator+'.'+key)
    elif isinstance(a, list):
        assert isinstance(b, list) and len(a) == len(b), locator
        for i, (x,y) in enumerate(zip(a,b)):
            compare(x,y,f'{locator}[{i}]')
    elif type(a) is float:
        assert type(b) in (float,int) and math.isfinite(a) and math.isfinite(b), locator
        assert abs(a-b) <= 5e-12*max(1.,abs(a),abs(b)), (locator,a,b)
    else:
        assert type(a) is type(b) and a == b, (locator,a,b)


def csv_out(path, rows, fields=None):
    assert rows
    with path.open('w', newline='') as f:
        writer=csv.DictWriter(f, fieldnames=fields or list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def export(results_root, output, compare_with=None):
    assert __debug__, 'Run without -O'
    assert not output.exists(), 'Choose a new output directory'
    output.mkdir(parents=True)
    summaries, totals, samples, nearest_rows, omissions, plot_rows = [], [], [], [], [], []
    files, compare_files = {}, {}
    total_omissions=0
    for rep in REPRESENTATIONS:
        path=results_root/rep/'results.json'
        doc=json.loads(path.read_text())
        files[rep]=digest(path)
        assert doc['representation'] == rep and doc['covariance_denominator'] == 'n-1'
        assert doc['input']['archive_sha256'] == INPUT_SHA256
        assert doc['input']['tokens'] == 1668 and doc['input']['speakers'] == 139
        assert set(doc['groups']) == set(GROUPS)
        if compare_with:
            ref=compare_with/rep/'results.json'
            compare(doc,json.loads(ref.read_text()))
            compare_files[rep]=digest(ref)
        for group in GROUPS:
            g=doc['groups'][group]
            s=g['summary']
            assert set(g['profiles']) == set(VOWELS)
            assert len(g['orders']) == s['order_questions'] == 660
            keys=[(o['reference'],*sorted((o['target_j'],o['target_k']))) for o in g['orders']]
            assert len(set(keys)) == 660
            assert all(i in VOWELS and j in VOWELS and k in VOWELS and len({i,j,k}) == 3 for i,j,k in keys)
            assert s['exact_certified'] == sum(o['exact_order'] != 0 for o in g['orders'])
            assert s['loose_certified'] == sum(o['loose_order'] != 0 for o in g['orders'])
            assert s['exact_additional'] == sum(o['exact_order'] != 0 and o['loose_order'] == 0 for o in g['orders'])
            assert s['full_diagonal_different_orders'] == sum(o['full_order'] != o['diagonal_order'] for o in g['orders'])
            assert s['full_centroid_different_orders'] == sum(o['full_order'] != o['centroid_order'] for o in g['orders'])
            assert len(g['nearest']) == 12 and {n['reference'] for n in g['nearest']} == set(VOWELS)
            assert s['guaranteed_nearest_references'] == sum(bool(n['guaranteed_unique']) for n in g['nearest'])
            assert s['diagonal_full_nearest_changes'] == sum(n['full'] != n['diagonal'] for n in g['nearest'])
            assert s['maximum_fidelity_relative_error'] < 2e-10
            summaries.append({'representation':rep,'group':group,**{k:s[k] for k in SUMMARY_FIELDS}})
            for vowel,p in g['profiles'].items():
                samples.append({'representation':rep,'group':group,'vowel':vowel,'n':p['n']})
            for n in g['nearest']:
                nearest_rows.append({'representation':rep,'group':group,'reference':n['reference'],
                    'possible_unique':' '.join(n['possible_unique']),
                    'guaranteed_unique':' '.join(n['guaranteed_unique']),
                    'retained_covariance':n['full'],'diagonal':n['diagonal'],'centroid':n['centroid']})
                if rep == 'raw_hz' and not n['guaranteed_unique']:
                    for j in n['possible_unique']:
                        d=g['distances'][n['reference']][j]
                        plot_rows.append({'group':group,'reference':n['reference'],'target':j,
                            'lower_Hz2':d['lower'],'upper_Hz2':d['upper'],'retained_Hz2':d['full'],
                            'retained_nearest':j == n['full']})
            expected_n = {'men':45,'women':48,'children':46} if rep=='raw_hz' else {'men':45,'women':46,'children':39}
            loo=g['leave_one_speaker_out']
            assert len(loo) == expected_n[group]
            assert len({r['omitted_speaker'] for r in loo}) == len(loo)
            total_omissions += len(loo)
            for x in loo:
                assert x['order_questions'] == 660
                assert x['exact_certified'] >= x['loose_certified']
                assert x['exact_additional'] == x['exact_certified'] - x['loose_certified']
                omissions.append({'representation':rep,'group':group,'omitted_speaker':x['omitted_speaker'],
                    **{k:x[k] for k in SUMMARY_FIELDS},'order_status_changes_from_full':x['order_status_changes_from_full']})
        total={k:sum(doc['groups'][g]['summary'][k] for g in GROUPS) for k in SUMMARY_FIELDS}
        assert tuple(total[k] for k in SUMMARY_FIELDS) == EXPECTED_TOTALS[rep], (rep,total)
        totals.append({'representation':rep,**total})
    assert total_omissions == 399
    assert len({(r['group'],r['reference']) for r in plot_rows}) == 9
    for name,rows in [('summary_by_group',summaries),('summary_totals',totals),('sample_sizes',samples),
                      ('nearest_categories',nearest_rows),('speaker_omissions',omissions),('vowel_intervals',plot_rows)]:
        csv_out(output/(name+'.csv'),rows)
    report={'status':'PASS_RECORDED_AGGREGATE_CONSISTENCY' if not compare_with else 'PASS_REPRODUCED_AGGREGATES_MATCH_REVIEWED_RECORDS',
            'inputs':files,'compared_with':compare_files,'main_cohorts':9,'speaker_omissions':399,
            'plotted_references':9,'plotted_intervals':len(plot_rows),
            'csv_files':{p.name:digest(p) for p in sorted(output.glob('*.csv'))},
            'limits':['No raw observations are loaded by this exporter.',
                      'Stored-result consistency does not by itself reproduce an empirical result.',
                      'Float tolerance for cross-runtime comparison is 5e-12 times max(1,abs(x),abs(y)).']}
    (output/'artifact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results-root',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--compare-with',type=Path)
    a=ap.parse_args()
    print(json.dumps(export(a.results_root,a.output,a.compare_with)))
