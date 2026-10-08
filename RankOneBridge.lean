import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Original proof work for the covariance-completion review. This file proves a
rank-one-reference matrix-square-root bridge; it does not claim the global
fidelity enclosure or the polygon attainment theorem.
-/

open Matrix
open scoped MatrixOrder

namespace CovarianceCompletion

variable {n : Type*} [Fintype n]

def outer (a : n → ℝ) : Matrix n n ℝ := vecMulVec a a

def sqNorm (a : n → ℝ) : ℝ := a ⬝ᵥ a

noncomputable def fidelity [DecidableEq n] (A B : Matrix n n ℝ) : ℝ :=
  (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).trace

theorem outer_posSemidef (a : n → ℝ) : (outer a).PosSemidef := by
  simpa [outer] using posSemidef_vecMulVec_self_star a

omit [Fintype n] in
theorem outer_diagonal (a : n → ℝ) (i : n) : outer a i i = (a i) ^ 2 := by
  simp [outer, vecMulVec, pow_two]

theorem outer_rank_le_one (a : n → ℝ) : (outer a).rank ≤ 1 :=
  rank_vecMulVec_le a a

theorem sqNorm_nonneg (a : n → ℝ) : 0 ≤ sqNorm a := by
  simpa [sqNorm] using dotProduct_star_self_nonneg a

theorem sqNorm_eq_zero_iff (a : n → ℝ) : sqNorm a = 0 ↔ a = 0 :=
  dotProduct_self_eq_zero

theorem sqNorm_pos {a : n → ℝ} (ha : a ≠ 0) : 0 < sqNorm a := by
  exact lt_of_le_of_ne (sqNorm_nonneg a) (Ne.symm ((sqNorm_eq_zero_iff a).not.mpr ha))

theorem outer_mul_self (a : n → ℝ) : outer a * outer a = sqNorm a • outer a := by
  simp only [outer, sqNorm, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem outer_sandwich (a : n → ℝ) (B : Matrix n n ℝ) :
    outer a * B * outer a = (a ⬝ᵥ (B *ᵥ a)) • outer a := by
  simp only [outer, vecMulVec_mul, vecMul_vecMulVec, vecMulVec_smul,
    dotProduct_mulVec]

theorem trace_outer (a : n → ℝ) : (outer a).trace = sqNorm a :=
  trace_vecMulVec a a

variable [DecidableEq n]

theorem sqrt_outer (a : n → ℝ) :
    CFC.sqrt (outer a) = (Real.sqrt (sqNorm a))⁻¹ • outer a := by
  by_cases ha : a = 0
  · subst a
    simp [outer, sqNorm]
  have hq := sqNorm_pos ha
  have hs : Real.sqrt (sqNorm a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  apply CFC.sqrt_unique
  · rw [smul_mul_smul, outer_mul_self, smul_smul]
    have hc : (Real.sqrt (sqNorm a))⁻¹ * (Real.sqrt (sqNorm a))⁻¹ * sqNorm a = 1 := by
      field_simp
      exact (Real.sq_sqrt hq.le).symm
    rw [hc, one_smul]
  · exact ((outer_posSemidef a).smul (inv_nonneg.2 (Real.sqrt_nonneg _))).nonneg

theorem sqrt_smul_outer (a : n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • outer a) = Real.sqrt c • CFC.sqrt (outer a) := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul, CFC.sqrt_mul_sqrt_self _ (outer_posSemidef a).nonneg,
      Real.mul_self_sqrt hc]
  · exact ((CFC.sqrt_nonneg (outer a)).posSemidef.smul (Real.sqrt_nonneg c)).nonneg

theorem trace_sqrt_outer (a : n → ℝ) :
    (CFC.sqrt (outer a)).trace = Real.sqrt (sqNorm a) := by
  rw [sqrt_outer, trace_smul, trace_outer]
  change (Real.sqrt (sqNorm a))⁻¹ * sqNorm a = _
  by_cases hq : sqNorm a = 0
  · simp [hq]
  have hs : Real.sqrt (sqNorm a) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (sqNorm_nonneg a) (Ne.symm hq)))
  field_simp
  exact (Real.sq_sqrt (sqNorm_nonneg a)).symm

theorem fidelity_outer (a : n → ℝ) {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    fidelity (outer a) B = Real.sqrt (a ⬝ᵥ (B *ᵥ a)) := by
  by_cases ha : a = 0
  · subst a
    simp [fidelity, outer]
  have hq := sqNorm_pos ha
  have hs : Real.sqrt (sqNorm a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have ht : 0 ≤ a ⬝ᵥ (B *ᵥ a) := by
    simpa using hB.dotProduct_mulVec_nonneg a
  have hc : 0 ≤ (Real.sqrt (sqNorm a))⁻¹ * (Real.sqrt (sqNorm a))⁻¹ *
      (a ⬝ᵥ (B *ᵥ a)) := by positivity
  unfold fidelity
  simp only [sqrt_outer, Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_sandwich]
  rw [← mul_assoc, sqrt_smul_outer a hc, trace_smul, trace_sqrt_outer]
  change Real.sqrt ((Real.sqrt (sqNorm a))⁻¹ * (Real.sqrt (sqNorm a))⁻¹ *
    (a ⬝ᵥ (B *ᵥ a))) * Real.sqrt (sqNorm a) = _
  rw [← Real.sqrt_mul hc]
  congr 1
  field_simp
  nlinarith [Real.sq_sqrt hq.le]

def gram {p : Type*} [Fintype p] (Y : Matrix n p ℝ) : Matrix n n ℝ := Y * Yᵀ

omit [DecidableEq n] in
theorem gram_posSemidef {p : Type*} [Fintype p] (Y : Matrix n p ℝ) :
    (gram Y).PosSemidef := by
  have ht : Yᴴ = Yᵀ := by ext i j; simp
  simpa only [gram, ht] using posSemidef_self_mul_conjTranspose Y

omit [Fintype n] [DecidableEq n] in
theorem gram_diagonal {p : Type*} [Fintype p] (Y : Matrix n p ℝ) (i : n) :
    gram Y i i = ∑ k, (Y i k) ^ 2 := by
  simp [gram, Matrix.mul_apply, pow_two]

omit [DecidableEq n] in
theorem gram_rank_le {p : Type*} [Fintype p] (Y : Matrix n p ℝ) :
    (gram Y).rank ≤ Fintype.card p :=
  (rank_mul_le_left Y Yᵀ).trans (rank_le_card_width Y)

theorem fidelity_outer_gram {p : Type*} [Fintype p] (a : n → ℝ) (Y : Matrix n p ℝ) :
    fidelity (outer a) (gram Y) = Real.sqrt (sqNorm (a ᵥ* Y)) := by
  rw [fidelity_outer a (gram_posSemidef Y)]
  unfold gram sqNorm
  rw [← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

theorem rank_two_gram_witness (a b : n → ℝ) (Y : Matrix n (Fin 2) ℝ)
    {f : ℝ} (hf : 0 ≤ f)
    (hdiag : ∀ i, (Y i 0) ^ 2 + (Y i 1) ^ 2 = (b i) ^ 2)
    (hlen : (∑ i, a i * Y i 0) ^ 2 + (∑ i, a i * Y i 1) ^ 2 = f ^ 2) :
    ∃ B : Matrix n n ℝ, B.PosSemidef ∧ (∀ i, B i i = (b i) ^ 2) ∧
      B.rank ≤ 2 ∧ fidelity (outer a) B = f := by
  refine ⟨gram Y, gram_posSemidef Y, ?_, ?_, ?_⟩
  · intro i
    simpa only [gram_diagonal, Fin.sum_univ_two] using hdiag i
  · simpa only [Fintype.card_fin] using gram_rank_le Y
  · rw [fidelity_outer_gram]
    have hsq : sqNorm (a ᵥ* Y) = f ^ 2 := by
      simpa only [sqNorm, dotProduct, Fin.sum_univ_two, Matrix.vecMul, pow_two] using hlen
    rw [hsq, Real.sqrt_sq hf]

noncomputable def planarRows (a b : n → ℝ) (z : Matrix n (Fin 2) ℝ) : Matrix n (Fin 2) ℝ :=
  fun i k => if a i = 0 then ![b i, 0] k else z i k / a i

omit [Fintype n] [DecidableEq n] in
theorem planarRows_properties (a b : n → ℝ) (z : Matrix n (Fin 2) ℝ)
    (hz : ∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = (a i * b i) ^ 2) :
    (∀ i, (planarRows a b z i 0) ^ 2 + (planarRows a b z i 1) ^ 2 = (b i) ^ 2) ∧
    (∀ i k, a i * planarRows a b z i k = z i k) := by
  constructor
  · intro i
    by_cases ha : a i = 0
    · simp [planarRows, ha]
    · simp only [planarRows, ite_eq_right ha, div_pow]
      field_simp
      nlinarith [hz i]
  · intro i k
    by_cases ha : a i = 0
    · have hi := hz i
      rw [ha] at hi
      norm_num at hi
      have h0 : z i 0 = 0 := by nlinarith only [hi, sq_nonneg (z i 1)]
      have h1 : z i 1 = 0 := by nlinarith only [hi, sq_nonneg (z i 0)]
      fin_cases k <;> simp [planarRows, ha, h0, h1]
    · simp only [planarRows, ite_eq_right ha]
      field_simp

theorem planar_covariance_witness (a b : n → ℝ) (z : Matrix n (Fin 2) ℝ)
    {f : ℝ} (hf : 0 ≤ f)
    (hz : ∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = (a i * b i) ^ 2)
    (hsum : (∑ i, z i 0) ^ 2 + (∑ i, z i 1) ^ 2 = f ^ 2) :
    ∃ B : Matrix n n ℝ, B.PosSemidef ∧ (∀ i, B i i = (b i) ^ 2) ∧
      B.rank ≤ 2 ∧ fidelity (outer a) B = f := by
  obtain ⟨hdiag, hmul⟩ := planarRows_properties a b z hz
  apply rank_two_gram_witness a b (planarRows a b z) hf hdiag
  simpa only [hmul] using hsum

def completion (b : n → ℝ) (B : Matrix n n ℝ) : Prop :=
  B.PosSemidef ∧ ∀ i, B i i = (b i) ^ 2

omit [DecidableEq n] in
theorem outer_completion (a : n → ℝ) : completion a (outer a) :=
  ⟨outer_posSemidef a, outer_diagonal a⟩

omit [DecidableEq n] in
theorem completion_trace (b : n → ℝ) {B : Matrix n n ℝ} (hB : completion b B) :
    B.trace = ∑ i, (b i) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, hB.2]

/-- This is the covariance/mean formula; equality to the measure-theoretic
Gaussian Wasserstein distance is an explicit external theorem bridge. -/
noncomputable def buresSqWithMean (μ ν : n → ℝ) (A B : Matrix n n ℝ) : ℝ :=
  sqNorm (μ - ν) + A.trace + B.trace - 2 * fidelity A B

theorem planar_distance_witness (μ ν a b : n → ℝ) (z : Matrix n (Fin 2) ℝ)
    {f : ℝ} (hf : 0 ≤ f)
    (hz : ∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = (a i * b i) ^ 2)
    (hsum : (∑ i, z i 0) ^ 2 + (∑ i, z i 1) ^ 2 = f ^ 2) :
    ∃ B : Matrix n n ℝ, completion b B ∧ B.rank ≤ 2 ∧
      buresSqWithMean μ ν (outer a) B =
        sqNorm (μ - ν) + (∑ i, ((a i) ^ 2 + (b i) ^ 2)) - 2 * f := by
  obtain ⟨B, hB, hdiag, hrank, hfid⟩ := planar_covariance_witness a b z hf hz hsum
  refine ⟨B, ⟨hB, hdiag⟩, hrank, ?_⟩
  unfold buresSqWithMean
  rw [completion_trace a (outer_completion a), completion_trace b ⟨hB, hdiag⟩,
    hfid, Finset.sum_add_distrib]
  ring

theorem fidelity_outer_outer (a b : n → ℝ) :
    fidelity (outer a) (outer b) = |a ⬝ᵥ b| := by
  rw [fidelity_outer a (outer_posSemidef b)]
  have hq : a ⬝ᵥ (outer b *ᵥ a) = (a ⬝ᵥ b) ^ 2 := by
    simp [outer, vecMulVec_mulVec, dotProduct, Finset.mul_sum,
      pow_two, mul_comm, mul_left_comm]
  rw [hq, Real.sqrt_sq_eq_abs]

theorem lower_endpoint_attained (μ ν a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    completion a (outer a) ∧ completion b (outer b) ∧
      buresSqWithMean μ ν (outer a) (outer b) =
        sqNorm (μ - ν) + ∑ i, (a i - b i) ^ 2 := by
  refine ⟨outer_completion a, outer_completion b, ?_⟩
  have hs : 0 ≤ a ⬝ᵥ b := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hb i))
  unfold buresSqWithMean
  rw [completion_trace a (outer_completion a), completion_trace b (outer_completion b),
    fidelity_outer_outer, abs_of_nonneg hs]
  unfold dotProduct
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  ring

theorem common_reference_planar_witness {ι : Type*}
    (μ₀ a : n → ℝ) (μ b : ι → n → ℝ) (z : ι → Matrix n (Fin 2) ℝ) (f : ι → ℝ)
    (hf : ∀ j, 0 ≤ f j)
    (hz : ∀ j i, (z j i 0) ^ 2 + (z j i 1) ^ 2 = (a i * b j i) ^ 2)
    (hsum : ∀ j, (∑ i, z j i 0) ^ 2 + (∑ i, z j i 1) ^ 2 = (f j) ^ 2) :
    ∃ B : ι → Matrix n n ℝ,
      completion a (outer a) ∧ (outer a).rank ≤ 1 ∧
      ∀ j, completion (b j) (B j) ∧ (B j).rank ≤ 2 ∧
        buresSqWithMean μ₀ (μ j) (outer a) (B j) =
          sqNorm (μ₀ - μ j) + (∑ i, ((a i) ^ 2 + (b j i) ^ 2)) - 2 * f j := by
  have h := fun j => planar_distance_witness μ₀ (μ j) a (b j) (z j) (hf j) (hz j) (hsum j)
  exact ⟨fun j => Classical.choose (h j), outer_completion a, outer_rank_le_one a,
    fun j => Classical.choose_spec (h j)⟩

theorem three_equal_variances_zero_fidelity :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      completion (fun _ => 1) B ∧ B.rank ≤ 2 ∧ fidelity (outer (fun _ => 1)) B = 0 := by
  let z : Matrix (Fin 3) (Fin 2) ℝ :=
    ![![1, 0], ![-1/2, Real.sqrt 3 / 2], ![-1/2, -Real.sqrt 3 / 2]]
  have hz : ∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = ((1 : ℝ) * 1) ^ 2 := by
    intro i
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    fin_cases i <;> norm_num [z] <;> nlinarith only [hs]
  have hsum : (∑ i, z i 0) ^ 2 + (∑ i, z i 1) ^ 2 = (0 : ℝ) ^ 2 := by
    norm_num [z, Fin.sum_univ_three]
    ring
  obtain ⟨B, hB, hd, hr, hf⟩ :=
    planar_covariance_witness (fun _ => 1) (fun _ => 1) z (by norm_num) hz hsum
  exact ⟨B, ⟨hB, hd⟩, hr, hf⟩

end CovarianceCompletion

#print axioms CovarianceCompletion.sqrt_outer
#print axioms CovarianceCompletion.sqrt_smul_outer
#print axioms CovarianceCompletion.trace_sqrt_outer
#print axioms CovarianceCompletion.fidelity_outer
#print axioms CovarianceCompletion.fidelity_outer_gram
#print axioms CovarianceCompletion.rank_two_gram_witness
#print axioms CovarianceCompletion.planar_covariance_witness
#print axioms CovarianceCompletion.planar_distance_witness
#print axioms CovarianceCompletion.lower_endpoint_attained
#print axioms CovarianceCompletion.common_reference_planar_witness
#print axioms CovarianceCompletion.three_equal_variances_zero_fidelity
