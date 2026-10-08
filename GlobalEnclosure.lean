import RankOneBridge
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

set_option autoImplicit false

open Matrix
open scoped MatrixOrder InnerProductSpace

namespace CovarianceEnclosure

theorem isometry_factor_of_norm_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H C : E →ₗ[ℝ] E) (h : ∀ x, ‖C x‖ = ‖H x‖) :
    ∃ U : E →ₗᵢ[ℝ] E, ∀ x, U (H x) = C x := by
  have hker : LinearMap.ker H ≤ LinearMap.ker C := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [h x, LinearMap.mem_ker.mp hx, norm_zero]
  let L₀ : LinearMap.range H →ₗ[ℝ] E :=
    ((LinearMap.ker H).liftQ C hker).comp H.quotKerEquivRange.symm.toLinearMap
  have hL (x : E) : L₀ ⟨H x, LinearMap.mem_range_self H x⟩ = C x := by
    simp [L₀, LinearMap.quotKerEquivRange_symm_apply_image]
  let L : LinearMap.range H →ₗᵢ[ℝ] E :=
    { toLinearMap := L₀
      norm_map' := by
        intro y
        obtain ⟨x, hx⟩ := y.property
        have hy : y = ⟨H x, LinearMap.mem_range_self H x⟩ := Subtype.ext hx.symm
        rw [hy, hL]
        exact h x }
  refine ⟨L.extend, fun x => ?_⟩
  exact (L.extend_apply ⟨H x, LinearMap.mem_range_self H x⟩).trans (hL x)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem real_conjTranspose (A : Matrix n n ℝ) : Aᴴ = Aᵀ := by ext i j; simp

theorem euclideanLin_mul (A B : Matrix n n ℝ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  exact Matrix.toLin_mul (EuclideanSpace.basisFun n ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis (EuclideanSpace.basisFun n ℝ).toBasis A B

theorem euclideanLin_adjoint (A : Matrix n n ℝ) :
    A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, real_conjTranspose]

theorem norm_sq_euclideanLin (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ^ 2 = inner ℝ x ((Aᵀ * A).toEuclideanLin x) := by
  rw [euclideanLin_mul, LinearMap.comp_apply, ← euclideanLin_adjoint,
    LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem trace_euclideanLin (A : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) A.toEuclideanLin = A.trace :=
  Matrix.trace_toLin_eq A (EuclideanSpace.basisFun n ℝ).toBasis

omit [DecidableEq n] in
theorem gram_posSemidef (C : Matrix n n ℝ) : (Cᵀ * C).PosSemidef := by
  simpa only [real_conjTranspose] using posSemidef_conjTranspose_mul_self C

theorem exists_polar_isometry (C : Matrix n n ℝ) :
    ∃ U : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ n,
      ∀ x, U ((CFC.sqrt (Cᵀ * C)).toEuclideanLin x) = C.toEuclideanLin x := by
  apply isometry_factor_of_norm_eq
  intro x
  have hP := gram_posSemidef C
  have hH := (CFC.sqrt_nonneg (Cᵀ * C)).posSemidef
  have ht : (CFC.sqrt (Cᵀ * C))ᵀ = CFC.sqrt (Cᵀ * C) := by
    simpa only [real_conjTranspose] using hH.isHermitian.eq
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_euclideanLin, norm_sq_euclideanLin, ht,
    CFC.sqrt_mul_sqrt_self _ hP.nonneg]

noncomputable def traceNorm (C : Matrix n n ℝ) : ℝ := (CFC.sqrt (Cᵀ * C)).trace

theorem eigenvector_euclideanLin {H : Matrix n n ℝ} (hH : H.IsHermitian) (i : n) :
    H.toEuclideanLin (hH.eigenvectorBasis i) = hH.eigenvalues i • hH.eigenvectorBasis i := by
  ext k
  exact congrFun (hH.mulVec_eigenvectorBasis i) k

theorem trace_isometries_posSemidef_le (H : Matrix n n ℝ) (hH : H.PosSemidef)
    (U V : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ n) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n)
      (V.adjoint.comp (U.toLinearMap.comp H.toEuclideanLin)) ≤ H.trace := by
  let b := hH.isHermitian.eigenvectorBasis
  rw [LinearMap.trace_eq_sum_inner _ b, hH.isHermitian.trace_eq_sum_eigenvalues]
  apply Finset.sum_le_sum
  intro i _
  have heig : H.toEuclideanLin (b i) = hH.isHermitian.eigenvalues i • b i :=
    eigenvector_euclideanLin hH.isHermitian i
  have hv : ‖V (b i)‖ = 1 := by rw [V.norm_map]; exact b.orthonormal.1 i
  have hu : ‖U (b i)‖ = 1 := by rw [U.norm_map]; exact b.orthonormal.1 i
  have hi : inner ℝ (V (b i)) (U (b i)) ≤ 1 := by
    simpa only [hv, hu, one_mul] using real_inner_le_norm (V (b i)) (U (b i))
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, heig,
    LinearMap.map_smul, LinearIsometry.coe_toLinearMap, inner_smul_right]
  simpa using mul_le_mul_of_nonneg_left hi (hH.eigenvalues_nonneg i)

theorem traceNorm_dual_upper (C : Matrix n n ℝ)
    (V : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ n) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) (V.adjoint.comp C.toEuclideanLin) ≤ traceNorm C := by
  obtain ⟨U, hU⟩ := exists_polar_isometry C
  have hC : C.toEuclideanLin =
      U.toLinearMap.comp (CFC.sqrt (Cᵀ * C)).toEuclideanLin := by
    apply LinearMap.ext
    intro x
    exact (hU x).symm
  rw [hC]
  exact trace_isometries_posSemidef_le (CFC.sqrt (Cᵀ * C))
    (CFC.sqrt_nonneg _).posSemidef U V

theorem traceNorm_dual_attained (C : Matrix n n ℝ) :
    ∃ U : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ n,
      LinearMap.trace ℝ (EuclideanSpace ℝ n) (U.adjoint.comp C.toEuclideanLin) = traceNorm C := by
  obtain ⟨U, hU⟩ := exists_polar_isometry C
  have hC : C.toEuclideanLin =
      U.toLinearMap.comp (CFC.sqrt (Cᵀ * C)).toEuclideanLin := by
    apply LinearMap.ext
    intro x
    exact (hU x).symm
  refine ⟨U, ?_⟩
  rw [hC, ← LinearMap.comp_assoc, U.adjoint_comp_self', LinearMap.id_comp, trace_euclideanLin]
  rfl

theorem traceNorm_nonneg (C : Matrix n n ℝ) : 0 ≤ traceNorm C :=
  (CFC.sqrt_nonneg (Cᵀ * C)).posSemidef.trace_nonneg

theorem traceNorm_add_le (C D : Matrix n n ℝ) : traceNorm (C + D) ≤ traceNorm C + traceNorm D := by
  obtain ⟨U, hU⟩ := traceNorm_dual_attained (C + D)
  rw [← hU, map_add, LinearMap.comp_add, map_add]
  exact add_le_add (traceNorm_dual_upper C U) (traceNorm_dual_upper D U)

theorem traceNorm_neg (C : Matrix n n ℝ) : traceNorm (-C) = traceNorm C := by
  simp [traceNorm]

theorem traceNorm_sub_le (C D : Matrix n n ℝ) : traceNorm (C - D) ≤ traceNorm C + traceNorm D := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le C (-D)

theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (Z : ι → Matrix n n ℝ) :
    traceNorm (∑ i ∈ s, Z i) ≤ ∑ i ∈ s, traceNorm (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem traceNorm_vecMulVec (x y : n → ℝ) :
    traceNorm (vecMulVec x y) =
      Real.sqrt (CovarianceCompletion.sqNorm x) * Real.sqrt (CovarianceCompletion.sqNorm y) := by
  unfold traceNorm
  rw [transpose_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  change (CFC.sqrt (CovarianceCompletion.sqNorm x • CovarianceCompletion.outer y)).trace = _
  rw [CovarianceCompletion.sqrt_smul_outer y (CovarianceCompletion.sqNorm_nonneg x),
    trace_smul, CovarianceCompletion.trace_sqrt_outer]
  rfl

theorem traceNorm_sum_reverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : ι → Matrix n n ℝ) (j : ι) :
    2 * traceNorm (Z j) - (∑ i, traceNorm (Z i)) ≤ traceNorm (∑ i, Z i) := by
  have heq : (∑ i, Z i) - (∑ i ∈ Finset.univ.erase j, Z i) = Z j := by
    rw [← Finset.univ.sum_erase_add Z (Finset.mem_univ j)]
    abel
  have hsub := traceNorm_sub_le (∑ i, Z i) (∑ i ∈ Finset.univ.erase j, Z i)
  rw [heq] at hsub
  have hsum := traceNorm_sum_le (Finset.univ.erase j) Z
  have hnum := Finset.univ.sum_erase_add (fun i => traceNorm (Z i)) (Finset.mem_univ j)
  linarith

omit [DecidableEq n] in
theorem mul_eq_sum_vecMulVec (X Y : Matrix n n ℝ) :
    X * Y = ∑ k, vecMulVec (fun i => X i k) (Y k) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec]

theorem sqrt_transpose {A : Matrix n n ℝ} : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  simpa only [real_conjTranspose] using (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq

theorem sqrt_col_sq {A : Matrix n n ℝ} (hA : A.PosSemidef) (j : n) :
    CovarianceCompletion.sqNorm (fun i => CFC.sqrt A i j) = A j j := by
  have hs := congrFun₂ (CFC.sqrt_mul_sqrt_self A hA.nonneg) j j
  have ht := sqrt_transpose (A := A)
  have hsymm (i : n) : CFC.sqrt A i j = CFC.sqrt A j i := congrFun₂ ht j i
  simpa only [CovarianceCompletion.sqNorm, dotProduct, Matrix.mul_apply, hsymm] using hs

theorem sqrt_row_sq {A : Matrix n n ℝ} (hA : A.PosSemidef) (j : n) :
    CovarianceCompletion.sqNorm (CFC.sqrt A j) = A j j := by
  have hs := congrFun₂ (CFC.sqrt_mul_sqrt_self A hA.nonneg) j j
  have ht := sqrt_transpose (A := A)
  have hsymm (i : n) : CFC.sqrt A i j = CFC.sqrt A j i := congrFun₂ ht j i
  simpa only [CovarianceCompletion.sqNorm, dotProduct, Matrix.mul_apply, hsymm] using hs

theorem fidelity_eq_traceNorm {A B : Matrix n n ℝ} (hB : B.PosSemidef) :
    CovarianceCompletion.fidelity A B = traceNorm (CFC.sqrt B * CFC.sqrt A) := by
  unfold CovarianceCompletion.fidelity traceNorm
  rw [transpose_mul, sqrt_transpose, sqrt_transpose,
    mul_assoc (CFC.sqrt A) (CFC.sqrt B) (CFC.sqrt B * CFC.sqrt A),
    ← mul_assoc (CFC.sqrt B) (CFC.sqrt B) (CFC.sqrt A),
    CFC.sqrt_mul_sqrt_self B hB.nonneg, ← mul_assoc]

theorem fidelity_coordinate_bounds (a b : n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {A B : Matrix n n ℝ} (hA : CovarianceCompletion.completion a A)
    (hB : CovarianceCompletion.completion b B) :
    0 ≤ CovarianceCompletion.fidelity A B ∧
      CovarianceCompletion.fidelity A B ≤ (∑ i, a i * b i) ∧
      (∀ j, 2 * (a j * b j) - (∑ i, a i * b i) ≤ CovarianceCompletion.fidelity A B) := by
  let Z : n → Matrix n n ℝ := fun k =>
    vecMulVec (fun i => CFC.sqrt B i k) (CFC.sqrt A k)
  have hZ (k : n) : traceNorm (Z k) = a k * b k := by
    dsimp [Z]
    rw [traceNorm_vecMulVec, sqrt_col_sq hB.1, sqrt_row_sq hA.1,
      hA.2 k, hB.2 k, Real.sqrt_sq (ha k), Real.sqrt_sq (hb k), mul_comm]
  have hF : CovarianceCompletion.fidelity A B = traceNorm (∑ k, Z k) := by
    rw [fidelity_eq_traceNorm hB.1, mul_eq_sum_vecMulVec]
  rw [hF]
  refine ⟨traceNorm_nonneg _, ?_, ?_⟩
  · simpa only [hZ] using traceNorm_sum_le Finset.univ Z
  · intro j
    simpa only [hZ] using traceNorm_sum_reverse Z j

theorem fidelity_enclosure [Nonempty n] (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {A B : Matrix n n ℝ} (hA : CovarianceCompletion.completion a A)
    (hB : CovarianceCompletion.completion b B) :
    max 0 (2 * Finset.univ.sup' Finset.univ_nonempty (fun i => a i * b i) -
      (∑ i, a i * b i)) ≤ CovarianceCompletion.fidelity A B ∧
      CovarianceCompletion.fidelity A B ≤ (∑ i, a i * b i) := by
  obtain ⟨h0, hhi, hlo⟩ := fidelity_coordinate_bounds a b ha hb hA hB
  refine ⟨max_le h0 ?_, hhi⟩
  have hm : Finset.univ.sup' Finset.univ_nonempty (fun i => a i * b i) ≤
      (CovarianceCompletion.fidelity A B + (∑ i, a i * b i)) / 2 := by
    apply Finset.sup'_le
    intro i _
    linarith [hlo i]
  linarith

end CovarianceEnclosure

#print axioms CovarianceEnclosure.isometry_factor_of_norm_eq
#print axioms CovarianceEnclosure.exists_polar_isometry
#print axioms CovarianceEnclosure.trace_isometries_posSemidef_le
#print axioms CovarianceEnclosure.traceNorm_add_le
#print axioms CovarianceEnclosure.traceNorm_vecMulVec
#print axioms CovarianceEnclosure.fidelity_enclosure
