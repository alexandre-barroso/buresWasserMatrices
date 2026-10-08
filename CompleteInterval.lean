import RankOneBridge
import PlanarResultant
import GlobalEnclosure

set_option autoImplicit false

open Matrix CovarianceCompletion
open scoped BigOperators

namespace CovarianceInterval

variable {d : ℕ}

def overlap (a b : Fin (d + 1) → ℝ) : ℝ := ∑ i, a i * b i

noncomputable def residual (a b : Fin (d + 1) → ℝ) : ℝ :=
  max 0 (2 * Finset.univ.sup' Finset.univ_nonempty (fun i => a i * b i) - overlap a b)

def total (μ ν a b : Fin (d + 1) → ℝ) : ℝ :=
  sqNorm (μ - ν) + ∑ i, ((a i) ^ 2 + (b i) ^ 2)

def lower (μ ν a b : Fin (d + 1) → ℝ) : ℝ :=
  sqNorm (μ - ν) + ∑ i, (a i - b i) ^ 2

noncomputable def upper (μ ν a b : Fin (d + 1) → ℝ) : ℝ :=
  total μ ν a b - 2 * residual a b

theorem lower_eq_total_sub (μ ν a b : Fin (d + 1) → ℝ) :
    lower μ ν a b = total μ ν a b - 2 * overlap a b := by
  unfold lower total overlap
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  ring

theorem residual_bounds (a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ residual a b ∧ residual a b ≤ overlap a b := by
  have h := PlanarCompletion.maxWeight_nonneg_le_sum (fun i => a i * b i)
    (fun i => mul_nonneg (ha i) (hb i))
  rw [PlanarCompletion.maxWeight_eq_sup' _ (fun i => mul_nonneg (ha i) (hb i))] at h
  have hs : 0 ≤ overlap a b := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hb i))
  exact ⟨le_max_left _ _, max_le hs (by dsimp [overlap] at *; linarith [h.2])⟩

theorem lower_le_upper (μ ν a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    lower μ ν a b ≤ upper μ ν a b := by
  rw [lower_eq_total_sub]
  unfold upper
  linarith [(residual_bounds a b ha hb).2]

theorem lower_nonneg (μ ν a b : Fin (d + 1) → ℝ) : 0 ≤ lower μ ν a b :=
  add_nonneg (sqNorm_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem objective_eq_total (μ ν a b : Fin (d + 1) → ℝ)
    {A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hA : completion a A) (hB : completion b B) :
    buresSqWithMean μ ν A B = total μ ν a b - 2 * fidelity A B := by
  unfold buresSqWithMean total
  rw [completion_trace a hA, completion_trace b hB, Finset.sum_add_distrib]
  ring

theorem objective_enclosure (μ ν a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hA : completion a A) (hB : completion b B) :
    lower μ ν a b ≤ buresSqWithMean μ ν A B ∧
      buresSqWithMean μ ν A B ≤ upper μ ν a b := by
  have h := CovarianceEnclosure.fidelity_enclosure a b ha hb hA hB
  change residual a b ≤ fidelity A B ∧ fidelity A B ≤ overlap a b at h
  rw [objective_eq_total μ ν a b hA hB, lower_eq_total_sub]
  unfold upper
  constructor <;> linarith [h.1, h.2]

theorem fixed_reference_fidelity_attainment (a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (f : ℝ)
    (hlo : residual a b ≤ f) (hhi : f ≤ overlap a b) :
    ∃ B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      completion b B ∧ B.rank ≤ 2 ∧ fidelity (outer a) B = f := by
  obtain ⟨z, hz, hsum⟩ := PlanarCompletion.planar_resultant_exists
    (fun i => a i * b i) (fun i => mul_nonneg (ha i) (hb i)) f hlo hhi
  obtain ⟨B, hB, hdiag, hrank, hfid⟩ := planar_covariance_witness a b z
    ((residual_bounds a b ha hb).1.trans hlo) hz hsum
  exact ⟨B, ⟨hB, hdiag⟩, hrank, hfid⟩

theorem fixed_reference_attainment (μ ν a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (t : ℝ)
    (hlo : lower μ ν a b ≤ t) (hhi : t ≤ upper μ ν a b) :
    ∃ B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      completion b B ∧ B.rank ≤ 2 ∧ buresSqWithMean μ ν (outer a) B = t := by
  let f := (total μ ν a b - t) / 2
  have hflo : residual a b ≤ f := by dsimp [f, upper] at *; linarith
  have hfhi : f ≤ overlap a b := by
    rw [lower_eq_total_sub] at hlo
    dsimp [f]
    linarith
  obtain ⟨B, hB, hrank, hfid⟩ := fixed_reference_fidelity_attainment a b ha hb f hflo hfhi
  refine ⟨B, hB, hrank, ?_⟩
  rw [objective_eq_total μ ν a b (outer_completion a) hB, hfid]
  dsimp [f]
  ring

theorem fixed_reference_image (μ ν a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (t : ℝ) :
    (∃ B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      completion b B ∧ B.rank ≤ 2 ∧ buresSqWithMean μ ν (outer a) B = t) ↔
      lower μ ν a b ≤ t ∧ t ≤ upper μ ν a b := by
  constructor
  · rintro ⟨B, hB, _, rfl⟩
    exact objective_enclosure μ ν a b ha hb (outer_completion a) hB
  · rintro ⟨hlo, hhi⟩
    exact fixed_reference_attainment μ ν a b ha hb t hlo hhi

theorem complete_image (μ ν a b : Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (t : ℝ) :
    (∃ A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      completion a A ∧ completion b B ∧ buresSqWithMean μ ν A B = t) ↔
      lower μ ν a b ≤ t ∧ t ≤ upper μ ν a b := by
  constructor
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact objective_enclosure μ ν a b ha hb hA hB
  · rintro ⟨hlo, hhi⟩
    obtain ⟨B, hB, _, ht⟩ := fixed_reference_attainment μ ν a b ha hb t hlo hhi
    exact ⟨outer a, B, outer_completion a, hB, ht⟩

theorem common_reference_attainment {ι : Type*}
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j i, 0 ≤ b j i) (t : ι → ℝ)
    (ht : ∀ j, lower μ₀ (μ j) a (b j) ≤ t j ∧ t j ≤ upper μ₀ (μ j) a (b j)) :
    ∃ B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      completion a (outer a) ∧ (outer a).rank ≤ 1 ∧
      ∀ j, completion (b j) (B j) ∧ (B j).rank ≤ 2 ∧
        buresSqWithMean μ₀ (μ j) (outer a) (B j) = t j := by
  have h := fun j => fixed_reference_attainment μ₀ (μ j) a (b j) ha (hb j) (t j)
    (ht j).1 (ht j).2
  exact ⟨fun j => Classical.choose (h j), outer_completion a, outer_rank_le_one a,
    fun j => Classical.choose_spec (h j)⟩

theorem common_reference_product_image {ι : Type*}
    (μ₀ a : Fin (d + 1) → ℝ) (μ b : ι → Fin (d + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j i, 0 ≤ b j i) (t : ι → ℝ) :
    (∃ (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (B : ι → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      completion a A ∧ ∀ j, completion (b j) (B j) ∧
        buresSqWithMean μ₀ (μ j) A (B j) = t j) ↔
      (∀ j, lower μ₀ (μ j) a (b j) ≤ t j ∧ t j ≤ upper μ₀ (μ j) a (b j)) := by
  constructor
  · rintro ⟨A, B, hA, hB⟩ j
    have h := objective_enclosure μ₀ (μ j) a (b j) ha (hb j) hA (hB j).1
    simpa only [(hB j).2] using h
  · intro ht
    obtain ⟨B, hA, _, hB⟩ := common_reference_attainment μ₀ a μ b ha hb t ht
    exact ⟨outer a, B, hA, fun j => ⟨(hB j).1, (hB j).2.2⟩⟩

end CovarianceInterval

#print axioms CovarianceInterval.complete_image
#print axioms CovarianceInterval.fixed_reference_image
#print axioms CovarianceInterval.common_reference_attainment
#print axioms CovarianceInterval.common_reference_product_image
