# Finite exact checks

`exact_checks.py` is original code using `fractions.Fraction`; it reads no external dataset and runs no inherited scripts. Every input is synthetic. The complete verification invokes it automatically. A separate focused run is:

```sh
python3 exact_checks.py --output ../verification/exact-only.json
```

The output file must not already exist. Do not use Python's `-O` option. A failed assertion causes a nonzero exit.

For each two-coordinate standard-deviation vector, coordinates range exhaustively over `0, 1/2, 1, 2`. For each pair of such vectors, both within-matrix correlations range over `-1, -2/3, -1/3, 0, 1/3, 2/3, 1`. This gives `16² × 7² = 12,544` PSD pairs, including zero variances and singular correlations. The checker uses the two-dimensional identity `F(A,B)² = tr(AB) + 2 sqrt(det(A)det(B))`. All comparisons eliminate the remaining square root by squaring only after checking the required signs. This identity is mathematical input to the finite checker; the checker does not itself prove it for all matrices.

For each diagonal-profile pair, nine equally spaced rational fidelity values from `κ` to `S` are realized against the same rank-one reference. This gives `16² × 9 = 2,304` constructions. The target correlation is solved directly and checked to lie in `[-1,1]`; the determinant and reference quadratic form are then checked exactly. A zero product is handled separately.

A three-target construction checks all `9³ = 729` tuples for a fixed reference profile `(1,2)` and target profiles `(2,1)`, `(1/2,3/2)`, `(0,2)`. It checks each direct quadratic form against the selected squared fidelity while keeping the same reference vector.

Two additional examples check the exact Gram matrix built from planar rows `(3,0)`, `(0,4)`, `(-3,-4)`, which has zero resultant, and the minimum absolute sum of three signs, which is one. The latter numerical enumeration supports the real rank-one limitation once its rank-one classification is supplied mathematically; it does not itself classify all real PSD matrices.

These counts and examples are deterministic. Repeated values in degenerate intervals are intentionally retained. They do not constitute a numerical survey of all dimensions, an empirical experiment, an independent Gaussian Wasserstein implementation or a formal Python-to-Lean bridge. The unbounded central result is established by the separate Lean chain.

## Public-vowel arithmetic checks

`independent_decimal_audit.py` independently parses the pinned ZIP into exact decimal integers and recomputes sample moments, two-dimensional fidelity, exact interval endpoints, every comparison and every nearest set. It imports no NumPy analysis code. Square roots use 80-digit Decimal arithmetic; this is high-precision validation, not interval arithmetic or a formal bridge. Positive definiteness of every tested sample covariance is asserted, so clamping cannot hide a non-PSD sample in the reviewed runs.

Coverage is asserted, not inferred from success: nine full cohorts and 399 leave-one-speaker-out cohorts, each with 660 order questions, giving 269,280 questions. All main order/nearest records, profiles and distances are checked. Omission outputs contain summary counts and nearest sets rather than full order vectors; the independent checker recomputes each full vector and compares all exported counts, nearest sets and status-change counts. It cannot compare an unexported per-question omission record. It checks every decision margin against the floating analysis threshold without using that threshold to choose a sign.

All 133 possible-nearest constructions in the main cohorts are evaluated directly as real outer-product covariances against a common `aaᵀ` reference, using `abs(dot(a,v))` for fidelity. A selected target uses correlation +1 and all competitors correlation −1 in the two-coordinate model. The strict nearest gaps and endpoint equalities are checked. These witnesses belong to the unrestricted completion model, including in the normalized sensitivity.

`benchmark_artifacts.py` checks the complete stored aggregate inventory and exports six deterministic CSVs, including all nine non-guaranteed primary references and all 20 possible-nearest intervals plotted for them. Its no-archive mode is labeled aggregate consistency only. A reproduced analysis is compared against every substantive stored field; runtime timestamps, environment and the historical creation-status label are the only top-level exceptions.

The plot exporter reads the reviewed raw-frequency aggregate file and writes PDF, PNG, JPG, EPS and SVG. CSV equality is checked byte for byte; raster exports use 900 dpi. The command leaves visual quality assessment to production review. Missing optional dependencies, mismatched archive hashes, incomplete coverage, modified proof sources and numerical disagreements produce nonzero failures.
