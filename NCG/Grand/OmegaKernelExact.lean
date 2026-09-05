/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.BkmMonotonicityExact

/-!
# The Kubo transform kernel

Step (B5) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
record defines the BKM metric through the Kubo transform
`Ω_σ(X) = ∫₀¹ σ^{1−s} X σ^s ds`, whose spectral kernel is

`∫₀¹ a^{1−s} b^s ds = (a − b)/(log a − log b)`,

the **reciprocal** of the BKM kernel — identifying the spectral form
`bkmForm` with the record's `Tr(v Ω_σ⁻¹(v))`.

* `interp_eq_exp`: the exponential form of the integrand;
* `integral_interp_ne`, `integral_interp_diag`: closed forms by the FTC;
* `kubo_mul_bkmKernel`: **the reciprocal identity**.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace NCG
namespace QRE

/-! ### The exponential form -/

theorem interp_eq_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℝ) :
    a ^ (1 - s) * b ^ s =
      Real.exp (Real.log a + s * (Real.log b - Real.log a)) := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
  congr 1
  ring

theorem interp_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s : ℝ => a ^ (1 - s) * b ^ s) volume 0 1 := by
  have hcong : (fun s : ℝ => a ^ (1 - s) * b ^ s) = fun s =>
      Real.exp (Real.log a + s * (Real.log b - Real.log a)) :=
    funext fun s => interp_eq_exp ha hb s
  rw [hcong]
  exact (Real.continuous_exp.comp (continuous_const.add
    (continuous_id.mul continuous_const))).continuousOn.intervalIntegrable

/-! ### Closed forms -/

/-- Closed form of the Kubo kernel, distinct arguments:
`∫₀¹ a^{1−s} b^s ds = (a − b)/(log a − log b)`. -/
theorem integral_interp_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    ∫ s in (0:ℝ)..1, a ^ (1 - s) * b ^ s =
      (a - b) / (Real.log a - Real.log b) := by
  set c : ℝ := Real.log b - Real.log a with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    refine sub_ne_zero_of_ne fun h => hab ?_
    rw [← Real.exp_log ha, ← Real.exp_log hb, h]
  have hcong : ∀ s ∈ Set.uIcc (0:ℝ) 1, a ^ (1 - s) * b ^ s =
      Real.exp (Real.log a + s * c) := fun s _ => interp_eq_exp ha hb s
  rw [intervalIntegral.integral_congr hcong]
  have hF : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u => Real.exp (Real.log a + u * c) / c)
        (Real.exp (Real.log a + s * c)) s := by
    intro s _
    have h1 : HasDerivAt (fun u : ℝ => Real.log a + u * c) c s := by
      simpa using ((hasDerivAt_id s).mul_const c).const_add (Real.log a)
    have h2 := (h1.exp).div_const c
    have hval : Real.exp (Real.log a + s * c) * c / c =
        Real.exp (Real.log a + s * c) :=
      mul_div_cancel_right₀ _ hcne
    rw [← hval]
    exact h2
  have hint : IntervalIntegrable
      (fun s : ℝ => Real.exp (Real.log a + s * c)) volume 0 1 :=
    (Real.continuous_exp.comp (continuous_const.add
      (continuous_id.mul continuous_const))).continuousOn.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  have h1 : Real.log a + 1 * c = Real.log b := by
    rw [hc]
    ring
  have h0 : Real.log a + 0 * c = Real.log a := by ring
  rw [h1, h0, Real.exp_log hb, Real.exp_log ha]
  rw [div_sub_div_same, hc]
  rw [show b - a = -(a - b) from by ring,
    show Real.log b - Real.log a = -(Real.log a - Real.log b) from by
      ring,
    neg_div_neg_eq]

/-- Closed form of the Kubo kernel, equal arguments. -/
theorem integral_interp_diag {a : ℝ} (ha : 0 < a) :
    ∫ s in (0:ℝ)..1, a ^ (1 - s) * a ^ s = a := by
  have hcong : ∀ s ∈ Set.uIcc (0:ℝ) 1, a ^ (1 - s) * a ^ s = a := by
    intro s _
    rw [← Real.rpow_add ha]
    norm_num
  rw [intervalIntegral.integral_congr hcong]
  simp

/-! ### The reciprocal identity -/

/-- **The Kubo kernel is the reciprocal of the BKM kernel**:
`(∫₀¹ a^{1−s} b^s ds) · k(a,b) = 1`. -/
theorem kubo_mul_bkmKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s in (0:ℝ)..1, a ^ (1 - s) * b ^ s) * bkmKernel a b = 1 := by
  rcases eq_or_ne a b with rfl | hab
  · rw [integral_interp_diag ha, bkmKernel, if_pos rfl]
    exact mul_inv_cancel₀ ha.ne'
  · rw [integral_interp_ne ha hb hab, bkmKernel, if_neg hab]
    have hlne : Real.log a - Real.log b ≠ 0 := by
      refine sub_ne_zero_of_ne fun h => hab ?_
      rw [← Real.exp_log ha, ← Real.exp_log hb, h]
    have habne : a - b ≠ 0 := sub_ne_zero_of_ne hab
    field_simp

end QRE
end NCG
