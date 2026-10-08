import OrderCriteria

set_option autoImplicit false

open Matrix CovarianceCompletion CovarianceInterval CovarianceOrder

namespace CovarianceNearest

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem selected_lower_other_upper_attainment
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j : ι) :
    ∃ B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      (∀ q, completion (b q) (B q) ∧ (B q).rank ≤ 2) ∧
      buresSqWithMean μ₀ (μ j) (outer a) (B j) = lower μ₀ (μ j) a (b j) ∧
      ∀ k, k ≠ j →
        buresSqWithMean μ₀ (μ k) (outer a) (B k) = upper μ₀ (μ k) a (b k) := by
  let t : ι → ℝ := fun q => if q = j then lower μ₀ (μ j) a (b j)
    else upper μ₀ (μ q) a (b q)
  have ht : ∀ q, lower μ₀ (μ q) a (b q) ≤ t q ∧ t q ≤ upper μ₀ (μ q) a (b q) := by
    intro q
    by_cases hq : q = j
    · subst q
      simpa [t] using And.intro (le_refl (lower μ₀ (μ j) a (b j)))
        (lower_le_upper μ₀ (μ j) a (b j) ha (hb j))
    · simpa [t, hq] using And.intro (lower_le_upper μ₀ (μ q) a (b q) ha (hb q))
        (le_refl (upper μ₀ (μ q) a (b q)))
  obtain ⟨B, _, _, hB⟩ := common_reference_attainment μ₀ a μ b ha hb t ht
  refine ⟨B, fun q => ⟨(hB q).1, (hB q).2.1⟩, ?_, ?_⟩
  · simpa [t] using (hB j).2.2
  · intro k hkj
    simpa [t, hkj] using (hB k).2.2

theorem possible_weak_nearest_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j : ι) :
    (∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ (∀ q, completion (b q) (B q)) ∧
      ∀ k, k ≠ j → buresSqWithMean μ₀ (μ j) A (B j) ≤
        buresSqWithMean μ₀ (μ k) A (B k)) ↔
      ∀ k, k ≠ j → lower μ₀ (μ j) a (b j) ≤ upper μ₀ (μ k) a (b k) := by
  constructor
  · rintro ⟨A, B, hA, hB, h⟩ k hkj
    exact (objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j)).1.trans
      ((h k hkj).trans (objective_enclosure μ₀ (μ k) a (b k) ha (hb k) hA (hB k)).2)
  · intro h
    obtain ⟨B, hB, hj, hk⟩ := selected_lower_other_upper_attainment μ₀ a μ b ha hb j
    refine ⟨outer a, B, outer_completion a, fun q => (hB q).1, ?_⟩
    intro k hkj
    simpa only [hj, hk k hkj] using h k hkj

theorem possible_unique_nearest_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j : ι) :
    (∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ (∀ q, completion (b q) (B q)) ∧
      ∀ k, k ≠ j → buresSqWithMean μ₀ (μ j) A (B j) <
        buresSqWithMean μ₀ (μ k) A (B k)) ↔
      ∀ k, k ≠ j → lower μ₀ (μ j) a (b j) < upper μ₀ (μ k) a (b k) := by
  constructor
  · rintro ⟨A, B, hA, hB, h⟩ k hkj
    exact lt_of_le_of_lt (objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j)).1
      (lt_of_lt_of_le (h k hkj) (objective_enclosure μ₀ (μ k) a (b k) ha (hb k) hA (hB k)).2)
  · intro h
    obtain ⟨B, hB, hj, hk⟩ := selected_lower_other_upper_attainment μ₀ a μ b ha hb j
    refine ⟨outer a, B, outer_completion a, fun q => (hB q).1, ?_⟩
    intro k hkj
    simpa only [hj, hk k hkj] using h k hkj

theorem guaranteed_weak_nearest_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j : ι) :
    (∀ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A → (∀ q, completion (b q) (B q)) →
      ∀ k, k ≠ j → buresSqWithMean μ₀ (μ j) A (B j) ≤
        buresSqWithMean μ₀ (μ k) A (B k)) ↔
      ∀ k, k ≠ j → upper μ₀ (μ j) a (b j) ≤ lower μ₀ (μ k) a (b k) := by
  constructor
  · intro h k hkj
    exact (universal_nonstrict_order_iff μ₀ a μ b ha hb j k (Ne.symm hkj)).mp
      (fun A B hA hB => h A B hA hB k hkj)
  · intro h A B hA hB k hkj
    exact (universal_nonstrict_order_iff μ₀ a μ b ha hb j k (Ne.symm hkj)).mpr
      (h k hkj) A B hA hB

theorem guaranteed_unique_nearest_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j : ι) :
    (∀ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A → (∀ q, completion (b q) (B q)) →
      ∀ k, k ≠ j → buresSqWithMean μ₀ (μ j) A (B j) <
        buresSqWithMean μ₀ (μ k) A (B k)) ↔
      ∀ k, k ≠ j → upper μ₀ (μ j) a (b j) < lower μ₀ (μ k) a (b k) := by
  constructor
  · intro h k hkj
    exact (universal_strict_order_iff μ₀ a μ b ha hb j k (Ne.symm hkj)).mp
      (fun A B hA hB => h A B hA hB k hkj)
  · intro h A B hA hB k hkj
    exact (universal_strict_order_iff μ₀ a μ b ha hb j k (Ne.symm hkj)).mpr
      (h k hkj) A B hA hB

end CovarianceNearest

#print axioms CovarianceNearest.selected_lower_other_upper_attainment
#print axioms CovarianceNearest.possible_weak_nearest_iff
#print axioms CovarianceNearest.possible_unique_nearest_iff
#print axioms CovarianceNearest.guaranteed_weak_nearest_iff
#print axioms CovarianceNearest.guaranteed_unique_nearest_iff
