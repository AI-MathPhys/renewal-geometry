/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# From Loewner bounds on a Hessian to gradient bounds on a convex set

Infrastructure for the convex-chart form of `thm:supp-action-stationarity`
(emergent-spacetime manuscript).  On a convex set `Θ` of a real inner product space, let
`g : E → E` be a gradient field with derivative `H x : E →L[ℝ] E` at every point of `Θ` (the
Hessian).  Quadratic-form (Loewner) bounds on `H` are converted into the gradient-level
inequalities used by the proximal estimates, with no global hypothesis:

* `inner_sub_bounds_of_hessian`: if `lo ≤ ⟪H x v, v⟫ ≤ hi` at `v = a - b` for every `x ∈ Θ`,
  then `lo ≤ ⟪g a - g b, a - b⟫ ≤ hi` (mean value theorem along the segment);
* `norm_apply_le_of_symmetric_form`: a symmetric operator with `|⟪T v, v⟫| ≤ c ‖v‖²` has
  `‖T v‖ ≤ c ‖v‖` (polarization);
* `norm_sub_le_of_hessian`: symmetric Hessians with `|⟪H x v, v⟫| ≤ c ‖v‖²` on `Θ` make `g`
  `c`-Lipschitz on `Θ` (mean value inequality on the convex set);
* `hessian_symmetric_of_hasGradientAt`: the derivative at `x` of a gradient field that is a
  genuine gradient of a scalar function near `x` is a symmetric operator (Schwarz);
* `floor_of_inner_sub_ge`: a gradient field that is `c`-strongly monotone on `Θ` has the
  quadratic first-order floor `f y - f a - ⟪g a, y - a⟫ ≥ (c/2) ‖y - a‖²` for `a, y ∈ Θ`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace RenewalGeometry
namespace HessianBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivative of `t ↦ ⟪g (b + t • v), v⟫` along an affine segment. -/
theorem hasDerivAt_inner_segment (g : E → E) (H : E →L[ℝ] E) (b v : E) (t : ℝ)
    (hg : HasFDerivAt g H (b + t • v)) :
    HasDerivAt (fun s : ℝ => ⟪g (b + s • v), v⟫) ⟪H v, v⟫ t := by
  have hpath : HasDerivAt (fun s : ℝ => b + s • v) v t := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) t := (hasDerivAt_id t).smul_const v
    rw [one_smul] at h1
    exact h1.const_add b
  have h2 : HasDerivAt (fun s : ℝ => g (b + s • v)) (H v) t := hg.comp_hasDerivAt t hpath
  have h3 := h2.inner ℝ (hasDerivAt_const t v)
  simpa using h3

/-- **Mean-value bounds from the Hessian quadratic form**: if `lo ≤ ⟪H x v, v⟫ ≤ hi` for
`v = a - b` and every `x ∈ Θ` (convex, `a, b ∈ Θ`, `H x` the derivative of `g` at `x`), then
`lo ≤ ⟪g a - g b, a - b⟫ ≤ hi`. -/
theorem inner_sub_bounds_of_hessian {Θ : Set E} (hΘ : Convex ℝ Θ) {g : E → E}
    {H : E → E →L[ℝ] E} (hH : ∀ x ∈ Θ, HasFDerivAt g (H x) x) {a b : E} (ha : a ∈ Θ)
    (hb : b ∈ Θ) {lo hi : ℝ} (hlo : ∀ x ∈ Θ, lo ≤ ⟪H x (a - b), a - b⟫)
    (hhi : ∀ x ∈ Θ, ⟪H x (a - b), a - b⟫ ≤ hi) :
    lo ≤ ⟪g a - g b, a - b⟫ ∧ ⟪g a - g b, a - b⟫ ≤ hi := by
  set v := a - b with hv
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, b + t • v ∈ Θ := fun t ht => hΘ.add_smul_sub_mem hb ha ht
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ⟪g (b + s • v), v⟫) ⟪H (b + t • v) v, v⟫ t :=
    fun t ht => hasDerivAt_inner_segment g _ b v t (hH _ (hmem t ht))
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => ⟪g (b + s • v), v⟫)
    (fun t => ⟪H (b + t • v) v, v⟫) zero_lt_one
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t (Ioo_subset_Icc_self ht))
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hceq
  have hend : ⟪g (b + v), v⟫ - ⟪g b, v⟫ = ⟪g a - g b, a - b⟫ := by
    rw [hv, add_sub_cancel, inner_sub_left]
  rw [hend] at hceq
  have hcmem := hmem c (Ioo_subset_Icc_self hc)
  exact ⟨hceq ▸ hlo _ hcmem, hceq ▸ hhi _ hcmem⟩

/-- Polarization: a symmetric operator with `|⟪T v, v⟫| ≤ c ‖v‖²` (`c ≥ 0`) satisfies
`‖T v‖ ≤ c ‖v‖`. -/
theorem norm_apply_le_of_symmetric_form (T : E →L[ℝ] E)
    (hsymm : ∀ v w, ⟪T v, w⟫ = ⟪v, T w⟫) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ v, |⟪T v, v⟫| ≤ c * ‖v‖ ^ 2) (v : E) : ‖T v‖ ≤ c * ‖v‖ := by
  -- polarization bound `4⟪T v, w⟫ ≤ 2c(‖v‖² + ‖w‖²)`
  have hpol : ∀ w, 4 * ⟪T v, w⟫ ≤ 2 * c * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    intro w
    have h1 : ⟪T (v + w), v + w⟫ - ⟪T (v - w), v - w⟫ = 4 * ⟪T v, w⟫ := by
      have hs : ⟪T w, v⟫ = ⟪T v, w⟫ := by rw [hsymm w v, real_inner_comm]
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hs]
      ring
    have h2 := (abs_le.mp (hc (v + w))).2
    have h3 := (abs_le.mp (hc (v - w))).1
    have hpar : ‖v + w‖ ^ 2 + ‖v - w‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    nlinarith
  rcases hc0.lt_or_eq with hcpos | hczero
  · have h := hpol (c⁻¹ • T v)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hcpos)] at h
    have hsq : ‖T v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
      have hci : c⁻¹ * c = 1 := inv_mul_cancel₀ hcpos.ne'
      have key : 2 * c⁻¹ * ‖T v‖ ^ 2 ≤ 2 * c * ‖v‖ ^ 2 := by
        have : 4 * (c⁻¹ * ‖T v‖ ^ 2) ≤ 2 * c * (‖v‖ ^ 2 + (c⁻¹ * ‖T v‖) ^ 2) := h
        have e : 2 * c * (c⁻¹ * ‖T v‖) ^ 2 = 2 * c⁻¹ * ‖T v‖ ^ 2 := by
          field_simp
        nlinarith
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ c / 2)
      have e1 : c / 2 * (2 * c⁻¹ * ‖T v‖ ^ 2) = ‖T v‖ ^ 2 := by field_simp
      have e2 : c / 2 * (2 * c * ‖v‖ ^ 2) = (c * ‖v‖) ^ 2 := by ring
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  · subst hczero
    have h := hpol (T v)
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖T v‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖T v‖ = 0 := by nlinarith [norm_nonneg (T v)]
    rw [this, zero_mul]

/-- The operator-norm form of `norm_apply_le_of_symmetric_form`. -/
theorem opNorm_le_of_symmetric_form (T : E →L[ℝ] E)
    (hsymm : ∀ v w, ⟪T v, w⟫ = ⟪v, T w⟫) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ v, |⟪T v, v⟫| ≤ c * ‖v‖ ^ 2) : ‖T‖ ≤ c :=
  T.opNorm_le_bound hc0 (norm_apply_le_of_symmetric_form T hsymm hc0 hc)

/-- **Lipschitz bound on the chart from a symmetric Hessian bound**: if the derivative
`H x` of `g` is symmetric with `|⟪H x v, v⟫| ≤ c ‖v‖²` at every `x ∈ Θ` (convex), then
`‖g a - g b‖ ≤ c ‖a - b‖` for `a, b ∈ Θ`. -/
theorem norm_sub_le_of_hessian {Θ : Set E} (hΘ : Convex ℝ Θ) {g : E → E}
    {H : E → E →L[ℝ] E} (hH : ∀ x ∈ Θ, HasFDerivAt g (H x) x)
    (hsymm : ∀ x ∈ Θ, ∀ v w, ⟪H x v, w⟫ = ⟪v, H x w⟫) {c : ℝ}
    (hc : ∀ x ∈ Θ, ∀ v, |⟪H x v, v⟫| ≤ c * ‖v‖ ^ 2) {a b : E} (ha : a ∈ Θ) (hb : b ∈ Θ) :
    ‖g a - g b‖ ≤ c * ‖a - b‖ := by
  rcases le_or_gt 0 c with hc0 | hcneg
  · exact hΘ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hH x hx).hasFDerivWithinAt)
      (fun x hx => opNorm_le_of_symmetric_form (H x) (hsymm x hx) hc0 (hc x hx)) hb ha
  · have h := hc a ha (a - b)
    have h0 : ‖a - b‖ ^ 2 ≤ 0 := by
      have := abs_nonneg ⟪H a (a - b), a - b⟫
      nlinarith [sq_nonneg ‖a - b‖]
    have hab : a - b = 0 := by
      have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
      exact norm_eq_zero.mp this
    rw [sub_eq_zero.mp hab]
    simp

/-- The inner-product currying `v ↦ ⟪v, ·⟫` as a real continuous linear map. -/
noncomputable def realInnerCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w : E => ⟪v, w⟫) (fun v₁ v₂ w => inner_add_left v₁ v₂ w)
      (fun c v w => real_inner_smul_left v w c) (fun v w₁ w₂ => inner_add_right v w₁ w₂)
      (fun c v w => real_inner_smul_right v w c))
    1 (fun v w => by
      simp only [LinearMap.mk₂_apply, one_mul]
      exact abs_real_inner_le_norm v w)

@[simp] theorem realInnerCLM_apply (v w : E) : realInnerCLM v w = ⟪v, w⟫ := rfl

/-- **Schwarz symmetry of the Hessian**: if `f` has gradient `g y` at every `y` near `x` and
`g` has derivative `H` at `x`, then `H` is symmetric. -/
theorem hessian_symmetric_of_hasGradientAt [CompleteSpace E] {f : E → ℝ} {g : E → E}
    {H : E →L[ℝ] E} {x : E} (hf : ∀ᶠ y in 𝓝 x, HasGradientAt f (g y) y)
    (hx : HasFDerivAt g H x) (v w : E) : ⟪H v, w⟫ = ⟪v, H w⟫ := by
  have h1 : ∀ᶠ y in 𝓝 x, HasFDerivAt f (realInnerCLM (g y)) y := by
    filter_upwards [hf] with y hy
    have h := hy.hasFDerivAt
    have heq : (realInnerCLM (g y) : E →L[ℝ] ℝ) = InnerProductSpace.toDual ℝ E (g y) := by
      ext w
      simp [InnerProductSpace.toDual_apply_apply]
    rw [heq]
    exact h
  have h2 : HasFDerivAt (fun y => realInnerCLM (g y)) (realInnerCLM.comp H) x :=
    (realInnerCLM (E := E)).hasFDerivAt.comp x hx
  have h3 := second_derivative_symmetric_of_eventually h1 h2 v w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, realInnerCLM_apply] at h3
  rw [h3, real_inner_comm]

/-- **First-order quadratic floor on a convex set**: if `f` has gradient `g x` at every
`x ∈ Θ` and `g` is `c`-strongly monotone on `Θ`, then
`f y - f a - ⟪g a, y - a⟫ ≥ (c/2) ‖y - a‖²` for `a, y ∈ Θ`. -/
theorem floor_of_inner_sub_ge [CompleteSpace E] {Θ : Set E} (hΘ : Convex ℝ Θ) {f : E → ℝ}
    {g : E → E} (hg : ∀ x ∈ Θ, HasGradientAt f (g x) x) {c : ℝ}
    (hmono : ∀ x ∈ Θ, ∀ y ∈ Θ, c * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) {a y : E}
    (ha : a ∈ Θ) (hy : y ∈ Θ) :
    c / 2 * ‖y - a‖ ^ 2 ≤ f y - f a - ⟪g a, y - a⟫ := by
  set v := y - a with hv
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, a + t • v ∈ Θ := fun t ht => hΘ.add_smul_sub_mem ha hy ht
  set χ : ℝ → ℝ := fun t => f (a + t • v) - t * ⟪g a, v⟫ - c / 2 * t ^ 2 * ‖v‖ ^ 2 with hχ
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt χ (⟪g (a + t • v), v⟫ - ⟪g a, v⟫ - c * t * ‖v‖ ^ 2) t := by
    intro t ht
    have hpath : HasDerivAt (fun s : ℝ => a + s • v) v t := by
      have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) t :=
        (hasDerivAt_id t).smul_const v
      rw [one_smul] at h1
      exact h1.const_add a
    have hf := (hg _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t hpath
    rw [InnerProductSpace.toDual_apply_apply] at hf
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪g a, v⟫) ⟪g a, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g a, v⟫
    have h3 : HasDerivAt (fun s : ℝ => c / 2 * s ^ 2 * ‖v‖ ^ 2) (c * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (c / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      rw [h21, pow_one]
      push_cast
      ring
    exact (hf.sub h2).sub h3
  have hmonoχ : MonotoneOn χ (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun t => ⟪g (a + t • v), v⟫ - ⟪g a, v⟫ - c * t * ‖v‖ ^ 2)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hder t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have hm := hmono (a + t • v) (hmem t (Ioo_subset_Icc_self ht)) a ha
      rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1, mul_pow, inner_sub_left] at hm
      have : c * t * ‖v‖ ^ 2 ≤ ⟪g (a + t • v), v⟫ - ⟪g a, v⟫ := by
        by_contra hcon
        push Not at hcon
        have := mul_lt_mul_of_pos_left hcon ht.1
        nlinarith
      linarith
  have h01 := hmonoχ (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [hχ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

end HessianBounds
end RenewalGeometry
