import CompleteInterval

set_option autoImplicit false

open Matrix CovarianceCompletion CovarianceInterval

namespace CovarianceOrder

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem two_targets_attainment
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i)
    (j k : ι) (hjk : j ≠ k) (s t : ℝ)
    (hs : lower μ₀ (μ j) a (b j) ≤ s ∧ s ≤ upper μ₀ (μ j) a (b j))
    (ht : lower μ₀ (μ k) a (b k) ≤ t ∧ t ≤ upper μ₀ (μ k) a (b k)) :
    ∃ B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      (∀ q, completion (b q) (B q) ∧ (B q).rank ≤ 2) ∧
      buresSqWithMean μ₀ (μ j) (outer a) (B j) = s ∧
      buresSqWithMean μ₀ (μ k) (outer a) (B k) = t := by
  let v : ι → ℝ := fun q => if q = j then s else if q = k then t else lower μ₀ (μ q) a (b q)
  have hv : ∀ q, lower μ₀ (μ q) a (b q) ≤ v q ∧ v q ≤ upper μ₀ (μ q) a (b q) := by
    intro q
    by_cases hqj : q = j
    · subst q
      simpa [v] using hs
    by_cases hqk : q = k
    · subst q
      simpa [v, Ne.symm hjk] using ht
    · simp only [v, ite_eq_right hqj, ite_eq_right hqk]
      exact ⟨le_rfl, lower_le_upper μ₀ (μ q) a (b q) ha (hb q)⟩
  obtain ⟨B, _, _, hB⟩ := common_reference_attainment μ₀ a μ b ha hb v hv
  refine ⟨B, fun q => ⟨(hB q).1, (hB q).2.1⟩, ?_, ?_⟩
  · simpa [v] using (hB j).2.2
  · simpa [v, Ne.symm hjk] using (hB k).2.2

theorem universal_strict_order_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j k : ι) (hjk : j ≠ k) :
    (∀ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A → (∀ q, completion (b q) (B q)) →
      buresSqWithMean μ₀ (μ j) A (B j) < buresSqWithMean μ₀ (μ k) A (B k)) ↔
      upper μ₀ (μ j) a (b j) < lower μ₀ (μ k) a (b k) := by
  constructor
  · intro h
    obtain ⟨B, hB, hj, hk⟩ := two_targets_attainment μ₀ a μ b ha hb j k hjk
      (upper μ₀ (μ j) a (b j)) (lower μ₀ (μ k) a (b k))
      ⟨lower_le_upper μ₀ (μ j) a (b j) ha (hb j), le_rfl⟩
      ⟨le_rfl, lower_le_upper μ₀ (μ k) a (b k) ha (hb k)⟩
    simpa only [hj, hk] using h (outer a) B (outer_completion a) (fun q => (hB q).1)
  · intro h A B hA hB
    exact lt_of_le_of_lt (objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j)).2
      (lt_of_lt_of_le h (objective_enclosure μ₀ (μ k) a (b k) ha (hb k) hA (hB k)).1)

theorem universal_nonstrict_order_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j k : ι) (hjk : j ≠ k) :
    (∀ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A → (∀ q, completion (b q) (B q)) →
      buresSqWithMean μ₀ (μ j) A (B j) ≤ buresSqWithMean μ₀ (μ k) A (B k)) ↔
      upper μ₀ (μ j) a (b j) ≤ lower μ₀ (μ k) a (b k) := by
  constructor
  · intro h
    obtain ⟨B, hB, hj, hk⟩ := two_targets_attainment μ₀ a μ b ha hb j k hjk
      (upper μ₀ (μ j) a (b j)) (lower μ₀ (μ k) a (b k))
      ⟨lower_le_upper μ₀ (μ j) a (b j) ha (hb j), le_rfl⟩
      ⟨le_rfl, lower_le_upper μ₀ (μ k) a (b k) ha (hb k)⟩
    simpa only [hj, hk] using h (outer a) B (outer_completion a) (fun q => (hB q).1)
  · intro h A B hA hB
    exact (objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j)).2.trans
      (h.trans (objective_enclosure μ₀ (μ k) a (b k) ha (hb k) hA (hB k)).1)

theorem strict_order_possible_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j k : ι) (hjk : j ≠ k) :
    (∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ (∀ q, completion (b q) (B q)) ∧
      buresSqWithMean μ₀ (μ j) A (B j) < buresSqWithMean μ₀ (μ k) A (B k)) ↔
      lower μ₀ (μ j) a (b j) < upper μ₀ (μ k) a (b k) := by
  constructor
  · rintro ⟨A, B, hA, hB, h⟩
    exact lt_of_le_of_lt (objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j)).1
      (lt_of_lt_of_le h (objective_enclosure μ₀ (μ k) a (b k) ha (hb k) hA (hB k)).2)
  · intro h
    obtain ⟨B, hB, hj, hk⟩ := two_targets_attainment μ₀ a μ b ha hb j k hjk
      (lower μ₀ (μ j) a (b j)) (upper μ₀ (μ k) a (b k))
      ⟨le_rfl, lower_le_upper μ₀ (μ j) a (b j) ha (hb j)⟩
      ⟨lower_le_upper μ₀ (μ k) a (b k) ha (hb k), le_rfl⟩
    exact ⟨outer a, B, outer_completion a, fun q => (hB q).1, by simpa only [hj, hk]⟩

theorem both_strict_orders_iff
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ q i, 0 ≤ b q i) (j k : ι) (hjk : j ≠ k) :
    ((∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ (∀ q, completion (b q) (B q)) ∧
      buresSqWithMean μ₀ (μ j) A (B j) < buresSqWithMean μ₀ (μ k) A (B k)) ∧
    (∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ (∀ q, completion (b q) (B q)) ∧
      buresSqWithMean μ₀ (μ k) A (B k) < buresSqWithMean μ₀ (μ j) A (B j))) ↔
    (lower μ₀ (μ j) a (b j) < upper μ₀ (μ k) a (b k) ∧
      lower μ₀ (μ k) a (b k) < upper μ₀ (μ j) a (b j)) := by
  rw [strict_order_possible_iff μ₀ a μ b ha hb j k hjk,
    strict_order_possible_iff μ₀ a μ b ha hb k j (Ne.symm hjk)]

end CovarianceOrder

#print axioms CovarianceOrder.universal_strict_order_iff
#print axioms CovarianceOrder.universal_nonstrict_order_iff
#print axioms CovarianceOrder.both_strict_orders_iff
