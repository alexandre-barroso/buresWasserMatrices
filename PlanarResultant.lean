import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open scoped BigOperators

namespace PlanarCompletion

theorem two_vector_step (r c f : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hf : 0 ≤ f)
    (hlo : |r - c| ≤ f) (hhi : f ≤ r + c) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = c ^ 2 ∧ (r + x) ^ 2 + y ^ 2 = f ^ 2 := by
  by_cases hr0 : r = 0
  · have hfc : f = c := by
      simp only [hr0, zero_add, zero_sub, abs_neg, abs_of_nonneg hc] at hlo hhi
      exact le_antisymm hhi hlo
    subst r
    subst f
    exact ⟨c, 0, by ring, by ring⟩
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hd : 0 < 2 * r := by linarith
  have htriangle := abs_le.mp hlo
  have hlowsq : (r - c) ^ 2 ≤ f ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ f - r + c)
      (by linarith : 0 ≤ f + r - c)]
  have hhighsq : f ^ 2 ≤ (r + c) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ r + c - f)
      (by linarith : 0 ≤ r + c + f)]
  let x := (f ^ 2 - r ^ 2 - c ^ 2) / (2 * r)
  have hxl : -c ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hd).2
    nlinarith
  have hxu : x ≤ c := by
    dsimp [x]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hrad : 0 ≤ c ^ 2 - x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ c - x) (by linarith : 0 ≤ c + x)]
  have hx : 2 * r * x = f ^ 2 - r ^ 2 - c ^ 2 := by
    dsimp [x]
    field_simp
  refine ⟨x, Real.sqrt (c ^ 2 - x ^ 2), ?_, ?_⟩ <;>
    nlinarith [Real.sq_sqrt hrad]

theorem rotate_resultant_to_axis {ι : Type*} [Fintype ι]
    (z : ι → Fin 2 → ℝ) {f : ℝ} (hf : 0 ≤ f)
    (hsum : (∑ i, z i 0) ^ 2 + (∑ i, z i 1) ^ 2 = f ^ 2) :
    ∃ w : ι → Fin 2 → ℝ,
      (∀ i, (w i 0) ^ 2 + (w i 1) ^ 2 = (z i 0) ^ 2 + (z i 1) ^ 2) ∧
      (∑ i, w i 0) = f ∧ (∑ i, w i 1) = 0 := by
  let u := ∑ i, z i 0
  let v := ∑ i, z i 1
  by_cases hf0 : f = 0
  · have hu : u = 0 := by dsimp [u, v] at *; nlinarith [sq_nonneg (∑ i, z i 1)]
    have hv : v = 0 := by dsimp [u, v] at *; nlinarith [sq_nonneg (∑ i, z i 0)]
    exact ⟨z, fun _ => rfl, by simpa [u, hf0] using hu, by simpa [v] using hv⟩
  let c := u / f
  let s := v / f
  have hunit : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    field_simp
    exact hsum
  have hfirst : c * u + s * v = f := by
    dsimp [c, s]
    field_simp
    nlinarith only [hsum]
  have hsecond : -s * u + c * v = 0 := by dsimp [c, s]; ring
  let w : ι → Fin 2 → ℝ := fun i => ![c * z i 0 + s * z i 1, -s * z i 0 + c * z i 1]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    change (c * z i 0 + s * z i 1) ^ 2 + (-s * z i 0 + c * z i 1) ^ 2 = _
    calc
      _ = (c ^ 2 + s ^ 2) * ((z i 0) ^ 2 + (z i 1) ^ 2) := by ring
      _ = _ := by rw [hunit, one_mul]
  · simpa [w, Finset.sum_add_distrib, ← Finset.mul_sum, u, v] using hfirst
  · simpa [w, Finset.sum_add_distrib, ← Finset.mul_sum, u, v] using hsecond

def maxWeight : {d : ℕ} → (Fin d → ℝ) → ℝ
  | 0, _ => 0
  | d + 1, w => max (w 0) (maxWeight (fun i : Fin d => w i.succ))

theorem maxWeight_nonneg_le_sum {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ maxWeight w ∧ maxWeight w ≤ ∑ i, w i := by
  induction d with
  | zero => simp [maxWeight]
  | succ d ih =>
    have ht := ih (fun i => w i.succ) (fun i => hw i.succ)
    have hu : 0 ≤ ∑ i : Fin d, w i.succ := Finset.sum_nonneg (fun i _ => hw i.succ)
    have hc := hw 0
    rw [maxWeight, Fin.sum_univ_succ]
    exact ⟨(hw 0).trans (le_max_left _ _), max_le (by linarith) (by linarith)⟩

theorem lower_step (c m u : ℝ) (hc : 0 ≤ c) :
    max 0 (2 * max c m - (c + u)) =
      max 0 (max (max 0 (2 * m - u) - c) (c - u)) := by
  simp only [max_def]
  split_ifs <;> linarith

theorem choose_prefix_length (ell u c f : ℝ) (hlu : ell ≤ u)
    (hc : 0 ≤ c) (hf : 0 ≤ f)
    (hlo : max 0 (max (ell - c) (c - u)) ≤ f) (hhi : f ≤ u + c) :
    ∃ r, ell ≤ r ∧ r ≤ u ∧ |r - c| ≤ f ∧ f ≤ r + c := by
  have hlf : ell - c ≤ f := (le_max_left _ _).trans ((le_max_right _ _).trans hlo)
  have hcf : c - u ≤ f := (le_max_right _ _).trans ((le_max_right _ _).trans hlo)
  have habsu : |f - c| ≤ u := abs_le.mpr ⟨by linarith, by linarith⟩
  have habsfc : |f - c| ≤ f + c := abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨max ell |f-c|, le_max_left _ _, max_le hlu habsu, ?_, ?_⟩
  · apply abs_le.mpr
    constructor
    · have hn := neg_le_abs (f - c)
      have hm := le_max_right ell |f-c|
      linarith
    · have hm : max ell |f-c| ≤ f + c := max_le (by linarith) habsfc
      linarith
  · have hn := le_abs_self (f-c)
    have hm := le_max_right ell |f-c|
    linarith

theorem attainable_normalized {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ℝ) (hlo : max 0 (2 * maxWeight w - ∑ i, w i) ≤ f)
    (hhi : f ≤ ∑ i, w i) :
    ∃ z : Fin d → Fin 2 → ℝ,
      (∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = (w i) ^ 2) ∧
      (∑ i, z i 0) = f ∧ (∑ i, z i 1) = 0 := by
  have hf : 0 ≤ f := (le_max_left _ _).trans hlo
  induction d generalizing f with
  | zero =>
    have hf0 : f = 0 := by simpa using le_antisymm hhi hf
    refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩ <;> simp_all
  | succ d ih =>
    let tail : Fin d → ℝ := fun i => w i.succ
    let c := w 0
    let u := ∑ i, tail i
    let m := maxWeight tail
    let ell := max 0 (2 * m - u)
    have hc : 0 ≤ c := hw 0
    have htail : ∀ i, 0 ≤ tail i := fun i => hw i.succ
    have hm := maxWeight_nonneg_le_sum tail htail
    have hu : 0 ≤ u := Finset.sum_nonneg (fun i _ => htail i)
    have hell : 0 ≤ ell := le_max_left _ _
    have hellu : ell ≤ u := max_le hu (by dsimp [m, u] at *; linarith [hm.2])
    have hsumw : (∑ i, w i) = c + u := by simp [c, u, tail, Fin.sum_univ_succ]
    have hmaxw : maxWeight w = max c m := rfl
    have hrec : max 0 (max (ell - c) (c - u)) ≤ f := by
      dsimp [ell]
      rw [← lower_step c m u hc]
      simpa only [hmaxw, hsumw] using hlo
    obtain ⟨r, hrl, hru, hrf, hfr⟩ :=
      choose_prefix_length ell u c f hellu hc hf hrec (by linarith [hsumw])
    have hr : 0 ≤ r := hell.trans hrl
    obtain ⟨z, hz, hx, hy⟩ := ih tail htail r hrl hru hr
    obtain ⟨x, y, hxy, hresult⟩ := two_vector_step r c f hr hc hf hrf hfr
    let raw : Fin (d + 1) → Fin 2 → ℝ := Fin.cons ![x, y] z
    have hraw : ∀ i, (raw i 0) ^ 2 + (raw i 1) ^ 2 = (w i) ^ 2 := by
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa [raw, c] using hxy
      · simpa [raw, tail] using hz k
    have hrawx : (∑ i, raw i 0) = x + r := by simp [raw, Fin.sum_univ_succ, hx]
    have hrawy : (∑ i, raw i 1) = y := by simp [raw, Fin.sum_univ_succ, hy]
    have hrawlen : (∑ i, raw i 0) ^ 2 + (∑ i, raw i 1) ^ 2 = f ^ 2 := by
      rw [hrawx, hrawy]
      simpa only [add_comm x r] using hresult
    obtain ⟨out, hout, houtx, houty⟩ := rotate_resultant_to_axis raw hf hrawlen
    exact ⟨out, fun i => (hout i).trans (hraw i), houtx, houty⟩

theorem le_maxWeight {d : ℕ} (w : Fin d → ℝ) (i : Fin d) : w i ≤ maxWeight w := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases (le_max_left _ _) (fun j => ?_) i
    exact (ih (fun k => w k.succ) j).trans (le_max_right _ _)

theorem maxWeight_le {d : ℕ} (w : Fin d → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hw : ∀ i, w i ≤ t) : maxWeight w ≤ t := by
  induction d with
  | zero => exact ht
  | succ d ih => exact max_le (hw 0) (ih (fun i => w i.succ) (fun i => hw i.succ))

theorem maxWeight_eq_sup' {d : ℕ} (w : Fin (d + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    maxWeight w = Finset.univ.sup' Finset.univ_nonempty w := by
  apply le_antisymm
  · apply maxWeight_le w
    · exact (hw 0).trans (Finset.le_sup' w (Finset.mem_univ 0))
    · intro i
      exact Finset.le_sup' w (Finset.mem_univ i)
  · exact Finset.sup'_le Finset.univ_nonempty w (fun i _ => le_maxWeight w i)

theorem planar_resultant_exists {d : ℕ} (w : Fin (d + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ℝ)
    (hlo : max 0 (2 * Finset.univ.sup' Finset.univ_nonempty w - ∑ i, w i) ≤ f)
    (hhi : f ≤ ∑ i, w i) :
    ∃ z : Fin (d + 1) → Fin 2 → ℝ,
      (∀ i, (z i 0) ^ 2 + (z i 1) ^ 2 = (w i) ^ 2) ∧
      (∑ i, z i 0) ^ 2 + (∑ i, z i 1) ^ 2 = f ^ 2 := by
  obtain ⟨z, hz, hx, hy⟩ := attainable_normalized w hw f
    (by simpa only [maxWeight_eq_sup' w hw] using hlo) hhi
  exact ⟨z, hz, by rw [hx, hy]; ring⟩

end PlanarCompletion

#print axioms PlanarCompletion.two_vector_step
#print axioms PlanarCompletion.rotate_resultant_to_axis
#print axioms PlanarCompletion.lower_step
#print axioms PlanarCompletion.choose_prefix_length
#print axioms PlanarCompletion.attainable_normalized
#print axioms PlanarCompletion.maxWeight_eq_sup'
#print axioms PlanarCompletion.planar_resultant_exists
