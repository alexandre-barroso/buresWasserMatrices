# Theorem and result map

Let `a,b ≥ 0` coordinatewise, let `S = Σᵢ aᵢbᵢ`, and let `κ = max(0, 2 maxᵢ aᵢbᵢ - S)`. For fixed real means define `M = Σᵢ(μᵢ-νᵢ)²`, `L = M + Σᵢ(aᵢ-bᵢ)²`, and `U = M + Σᵢ(aᵢ²+bᵢ²) - 2κ`.

`completion a A` means actual real `Matrix.PosSemidef` together with `A i i = (a i)^2`. `fidelity A B` is `tr sqrt(sqrt(A) B sqrt(A))`. `buresSqWithMean` is `M + tr A + tr B - 2 fidelity A B`. Positive dimension is represented by `Fin (d+1)` for arbitrary natural `d`. All-zero and singular cases are included.

| Result | Declaration |
| --- | --- |
| Every compatible arbitrary PSD pair satisfies `κ ≤ F(A,B) ≤ S` | `CovarianceEnclosure.fidelity_enclosure` |
| Every `f ∈ [κ,S]` is the resultant length of real planar vectors with edge lengths `aᵢbᵢ` | `PlanarCompletion.planar_resultant_exists` |
| The rank-one reference identity includes `a=0` | `CovarianceCompletion.fidelity_outer` |
| Planar rows produce an actual PSD target with the exact diagonal and rank at most two | `CovarianceCompletion.planar_covariance_witness` |
| A value `t` is attainable over both completion fibers if and only if `L ≤ t ≤ U` | `CovarianceInterval.complete_image` |
| The same full image is attained with the literal fixed `aaᵀ` and target rank at most two | `CovarianceInterval.fixed_reference_image` |
| A common reference of rank at most one supports all independently chosen interval values at once | `CovarianceInterval.common_reference_attainment` |
| The entire common-reference image equals the Cartesian product | `CovarianceInterval.common_reference_product_image` |
| For distinct targets, universal strict order iff `Uⱼ < Lₖ` | `CovarianceOrder.universal_strict_order_iff` |
| For distinct targets, universal nonstrict order iff `Uⱼ ≤ Lₖ` | `CovarianceOrder.universal_nonstrict_order_iff` |
| One strict order is attainable iff `Lⱼ < Uₖ` | `CovarianceOrder.strict_order_possible_iff` |
| Both strict orders are attainable iff `Lⱼ < Uₖ` and `Lₖ < Uⱼ` | `CovarianceOrder.both_strict_orders_iff` |

The enclosure makes no rank assumption on the arbitrary input completions. The low-rank properties are conclusions for attaining witnesses. The product statement permits arbitrary index types and therefore includes any finite target family; it does not impose target-to-target distances. The order declarations explicitly require distinct indices.

The formal proof defines `traceNorm C = tr sqrt(CᵀC)`, derives its needed duality and triangle properties through a real polar isometry, and uses the canonical product `sqrt(B) sqrt(A)`. It does not assume an unproved general nuclear-norm factor identity. The planar proof uses an explicit inductive construction with guarded zero cases. The six modules are original proof code; their Mathlib dependencies provide the underlying verified real analysis, linear algebra and functional calculus.

`theorem_map.json` lists all 99 original declarations and frozen source hashes. These hashes must be deliberately revised, with a new clean verification, if a proof source changes. No claim is made that this certificate formalizes Gaussian probability measures, the general arbitrary-factor identity, the point-identification support characterization, the positive-definite approximation argument, every all-pairs/rank example, or the non-Gaussian quantile example. Those require separately labeled evidence.

## Nearest-category extension

For a selected target `j`, comparisons range over every `k ≠ j`. With fixed means and nonnegative standard deviations in `Fin (d+1)`, the predicates quantify actual real PSD completions for a single shared reference and every target:

| Result | Declaration |
| --- | --- |
| The same `aaᵀ` attains the selected lower endpoint and every competing upper endpoint, with rank≤2 targets | `CovarianceNearest.selected_lower_other_upper_attainment` |
| Some compatible shared-reference family makes `j` weakly nearest iff every `Lⱼ ≤ Uₖ` | `CovarianceNearest.possible_weak_nearest_iff` |
| Some compatible shared-reference family makes `j` uniquely nearest iff every `Lⱼ < Uₖ` | `CovarianceNearest.possible_unique_nearest_iff` |
| Every compatible shared-reference family makes `j` weakly nearest iff every `Uⱼ ≤ Lₖ` | `CovarianceNearest.guaranteed_weak_nearest_iff` |
| Every compatible shared-reference family makes `j` uniquely nearest iff every `Uⱼ < Lₖ` | `CovarianceNearest.guaranteed_unique_nearest_iff` |

There are 85 theorem declarations and 14 definitions. The five nearest declarations add no new assumptions about rank, positive variances or an observed fixed covariance. A target type with decidable equality is used; finite families are included. A singleton target family gives the appropriate vacuous nearest conditions. These statements do not require target-to-target distances and do not impose sampling, support or normalization constraints.
