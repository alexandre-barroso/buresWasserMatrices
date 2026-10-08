# Exact covariance-completion intervals and vowel-summary audits

This repository contains original Lean proofs and independent computations for a precise information question: which Gaussian-moment distance comparisons are determined by category means and marginal standard deviations in fixed shared coordinates? The empirical example uses paired steady-state F1/F2 measurements from the public Hillenbrand et al. (1995) archive.

The real PSD theorem gives the entire compatible Bures squared-distance interval, a single rank-at-most-one reference attaining all independently selected target distances, exact order criteria, and necessary and sufficient possible/guaranteed nearest-category criteria. Zero coordinates and singular matrices are included. The target index set is arbitrary; the result concerns distances from one reference, not a freely chosen matrix of all pairwise distances.

The empirical audit uses finite-dataset means and sample covariances (denominator n−1). It compares marginal-summary bounds with the Gaussian models defined by retained covariance. It does not compute Wasserstein distances between empirical distributions or validate a perceptual or phonological metric. The normalized sensitivity uses an unrestricted transformed-summary Gaussian model; covariance completions need not preserve additional rowwise normalization identities.

## Files

| File | Role |
| --- | --- |
| Six `*.lean` modules | 85 original theorems and 14 definitions; accepted chain ends at `NearestCriteria` |
| `theorem_map.json`, `THEOREMS.md` | Exact declaration names, source hashes, assumptions and formal limits |
| `exact_checks.py` | Synthetic exact-rational PSD, attainment and common-reference checks |
| `analyze_vowel_summaries.py` | Byte-identical reviewed NumPy analysis; reads public numeric ZIP text without extracting it |
| `independent_decimal_audit.py` | Separate 80-digit arithmetic, all nine main cohorts and 399 speaker omissions; no NumPy/analysis imports |
| `benchmark_artifacts.py` | Complete substantive-result comparisons and six table/figure-data CSV exports |
| `generate_vowel_figure.py` | Original five-format figure exporter with portable input/output arguments |
| `expected/` | Newly computed aggregate results and CSVs; no individual source measurements or audio |
| `verify.py` | Single verification entry point, with optional archive and figure stages |
| `environment.json`, requirements and Lake files | Pinned software/dependency versions |
| `DATA.md`, `PROVENANCE.json` | Input access, exact hashes, analysis choices and source continuity |
| `author_only/CITATION.cff` | Named sole-author citation metadata; omit the entire directory from a blind snapshot |

No third-party source libraries, reference full texts, raw archive, audio, serialized R objects, private input files, or build caches are included. The snapshot carries no publication URL, release DOI or license grant. Generated verification logs belong outside the repository. Original plot exports use the named author unless `--anonymous-figures` is selected; that flag alone does not anonymize repository sources or the author-only directory.

## Pinned environment

Formal verification, rational checks, aggregate CSV checks and the Decimal audit require Python 3.11 or newer and its standard library. The selected installed environment for the full pipeline is Python 3.12.3, NumPy 2.4.4 and Matplotlib 3.10.9; the earlier proof/Decimal review also used Python 3.12.14. Optional dependency pins are in `requirements-benchmark.txt` and `requirements-figures.txt`. Install them in a chosen external environment if needed. Do not run with Python `-O`: assertions are active verification obligations.

Use [Lean 4.34.0](https://github.com/leanprover/lean4/releases/tag/v4.34.0), commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, including its bundled Lake and `leanchecker`. The verifier takes the existing toolchain directory explicitly and performs no global installation.

Use the official [Mathlib v4.34.0 release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.34.0), commit `5ed2965256430c3649e86755f9576b54eca72435`. All eight transitive dependency commits are pinned in `environment.json` and `lake-manifest.json`. Keep the prepared checkout outside this repository. For a new checkout, ordinary public network access and adequate storage are required:

```sh
git clone --depth 1 --branch v4.34.0 https://github.com/leanprover-community/mathlib4 ../bures-mathlib
cd ../bures-mathlib
```

With the pinned toolchain's `bin` on `PATH`, set `MATHLIB_CACHE_DIR` and `LAKE_CACHE_DIR` inside the external checkout or another chosen work directory, then obtain the official compiled imports:

```sh
lake exe cache get Mathlib/Analysis/Matrix/Order.lean Mathlib/LinearAlgebra/Matrix/Rank.lean Mathlib/Analysis/InnerProductSpace/Trace.lean Mathlib/LinearAlgebra/Isomorphisms.lean Mathlib/Algebra/BigOperators/Fin.lean Mathlib/Tactic/FieldSimp.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/Positivity.lean Mathlib/Tactic/FinCases.lean Mathlib/Tactic/Abel.lean
```

The original tagged dependency manifest must remain unchanged. The verifier checks its hash, every dependency commit and tracked-source cleanliness. It accepts neither arbitrary newer libraries nor changes hidden behind the same release tag.

## One verification entry point

From this repository, supply existing dependencies and a **new output directory outside the repository**:

```sh
python3 verify.py --toolchain /path/to/lean-4.34.0 --mathlib-root ../bures-mathlib --output ../verification/run-001
```

The command checks the complete file manifest/checksums, performs finite exact checks and recorded-aggregate consistency checks, clean-builds all six original modules into the new output directory, prints all 99 elaborated statements and their transitive axioms, and runs `leanchecker --fresh --verbose NearestCriteria`. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. A failure exits nonzero and produces `failure.json` when an output directory was created. No project proof `.olean` is reused.

Without an archive, the report explicitly says `NOT_RUN_NO_BENCHMARK_ARCHIVE`; it does not claim the empirical results were regenerated. To reproduce the whole benchmark, acquire the exact public ZIP described in `DATA.md` and pass its external path:

```sh
python3 verify.py --toolchain /path/to/lean-4.34.0 --mathlib-root ../bures-mathlib --benchmark-archive ../inputs/h95-alldata.zip --output ../verification/run-002
```

This reruns all three representations, including every speaker omission, compares every substantive output field with the reviewed aggregates (integers and categories exactly; floating fields with tolerance `5e-12 * max(1,abs(x),abs(y))`), then independently recomputes 269,280 order questions with 80-digit Decimal arithmetic. It also checks all 133 concrete possible-nearest witnesses. Coverage assertions enforce nine full cohorts, 399 omissions and the complete category/speaker sets. All stages use the selected Python interpreter.

Add `--figures` to either command to export PDF, PNG, JPG, EPS and SVG from the frozen reviewed raw-frequency aggregates. PNG/JPG use 900 dpi. The plotting stage checks that its CSV is byte-identical to `expected/tables/vowel_intervals.csv`; independent visual inspection remains required. Figure export does not require the raw ZIP. Add `--anonymous-figures` for neutral figure author metadata.

The standalone plotting interface is:

```sh
python3 generate_vowel_figure.py --results expected/raw_hz/results.json --output-dir ../figures/run-001
```

Every output directory must be fresh. The commands read the supplied ZIP in place and do not extract, modify or copy it. No network access, publication or account operation is performed by `verify.py`.

## What a passing report establishes

The formal chain proves the explicit real matrix-square-root trace objective and its interval/order/nearest statements. Fresh replay uses the official **same Lean kernel**, not an independent kernel implementation. Gaussian probability laws, a Python-to-Lean bridge, the manuscript's positive-definite limiting argument and other separately supported examples are outside this certificate.

The benchmark checks finite-data arithmetic and reporting decisions. They do not establish population inference, confidence levels, perception, causation, novelty or general acoustic metric superiority. Decimal square roots are rounded; this is not certified interval arithmetic. Omission analyses are deterministic sensitivity checks, not a bootstrap or confidence interval. A possible-nearest witness changes the reference covariance to `aaᵀ`, generally different from the retained reference covariance.

The stored result files preserve the original exploratory creation status verbatim. The separate verifier report records the actual reproduction/audit outcome without rewriting those historical result bytes. The CI workflow is configuration only; it does not attest to hosted execution and its default run does not download the benchmark or export figures.
