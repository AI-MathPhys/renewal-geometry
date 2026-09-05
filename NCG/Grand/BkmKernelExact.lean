/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ResolventFormExact

/-!
# The BKM kernel and its resolvent integral

Step (B2) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
scalar layer of the resolvent representation.  The Bogoliubov–Kubo–Mori
kernel is the divided difference of the logarithm,

`k(a,b) = (log a − log b)/(a − b)` (diagonal value `a⁻¹`),

and it is the improper integral of the resolvent product:

`∫₀^∞ ds/((a+s)(b+s)) = k(a,b)`.

* `bkmKernel`: the kernel, with symmetry and positivity;
* `integral_resolvent_prod_ne`, `integral_resolvent_prod_eq`: closed
  forms of the truncated integrals by the FTC;
* `tendsto_integral_resolvent`: **the boxed limit identity**.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace NCG
namespace QRE

/-! ### The kernel -/

/-- The BKM kernel: the divided difference of `log`. -/
noncomputable def bkmKernel (a b : ℝ) : ℝ :=
  if a = b then a⁻¹ else (Real.log a - Real.log b) / (a - b)

theorem bkmKernel_symm (a b : ℝ) : bkmKernel a b = bkmKernel b a := by
  unfold bkmKernel
  rcases eq_or_ne a b with rfl | hab
  · rfl
  · rw [if_neg hab, if_neg hab.symm]
    rw [show Real.log a - Real.log b = -(Real.log b - Real.log a) by ring,
      show a - b = -(b - a) by ring, neg_div_neg_eq]

theorem bkmKernel_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < bkmKernel a b := by
  unfold bkmKernel
  rcases eq_or_ne a b with rfl | hab
  · rw [if_pos rfl]
    exact inv_pos.mpr ha
  · rw [if_neg hab]
    rcases lt_or_gt_of_ne hab with h | h
    · have hlog : Real.log a < Real.log b := Real.log_lt_log ha h
      apply div_pos_of_neg_of_neg <;> linarith
    · have hlog : Real.log b < Real.log a := Real.log_lt_log hb h
      apply div_pos <;> linarith

/-! ### Truncated integrals in closed form -/

theorem hasDerivAt_log_shift {c s : ℝ} (hcs : 0 < c + s) :
    HasDerivAt (fun t : ℝ => Real.log (c + t)) ((c + s)⁻¹) s := by
  have h1 : HasDerivAt (fun t : ℝ => c + t) 1 s := by
    simpa using (hasDerivAt_id s).const_add c
  have h2 := h1.log hcs.ne'
  simpa [one_div] using h2

theorem resolvent_prod_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun s => ((a + s) * (b + s))⁻¹) volume 0 R := by
  apply ContinuousOn.intervalIntegrable
  have hmem : ∀ s ∈ Set.uIcc (0 : ℝ) R, (a + s) * (b + s) ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hR] at hs
    have hs0 : 0 ≤ s := hs.1
    have h1 : 0 < a + s := by linarith
    have h2 : 0 < b + s := by linarith
    positivity
  exact (((continuousOn_const.add continuousOn_id).mul
    (continuousOn_const.add continuousOn_id)).inv₀ hmem)

/-- Closed form of the truncated resolvent integral, distinct arguments. -/
theorem integral_resolvent_prod_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) {R : ℝ} (hR : 0 ≤ R) :
    ∫ s in (0:ℝ)..R, ((a + s) * (b + s))⁻¹ =
      (Real.log (b + R) - Real.log (a + R)) / (a - b) -
        (Real.log b - Real.log a) / (a - b) := by
  have hab' : a - b ≠ 0 := sub_ne_zero_of_ne hab
  have hF : ∀ s ∈ Set.uIcc (0:ℝ) R,
      HasDerivAt (fun t => (Real.log (b + t) - Real.log (a + t)) / (a - b))
        (((a + s) * (b + s))⁻¹) s := by
    intro s hs
    rw [Set.uIcc_of_le hR] at hs
    have hs0 : 0 ≤ s := hs.1
    have has : 0 < a + s := by linarith
    have hbs : 0 < b + s := by linarith
    have h3 := ((hasDerivAt_log_shift hbs).sub
      (hasDerivAt_log_shift has)).div_const (a - b)
    have hval : ((b + s)⁻¹ - (a + s)⁻¹) / (a - b) =
        ((a + s) * (b + s))⁻¹ := by
      rw [inv_sub_inv hbs.ne' has.ne',
        show (a + s) - (b + s) = a - b from by ring,
        div_div, mul_comm ((b + s) * (a + s)) (a - b),
        div_mul_eq_div_div, div_self hab', mul_comm (b + s) (a + s),
        one_div]
    rw [← hval]
    exact h3
  rw [integral_eq_sub_of_hasDerivAt hF
    (resolvent_prod_integrable ha hb hR)]
  rw [add_zero, add_zero]

/-- Closed form of the truncated resolvent integral, equal arguments. -/
theorem integral_resolvent_prod_eq {a : ℝ} (ha : 0 < a) {R : ℝ}
    (hR : 0 ≤ R) :
    ∫ s in (0:ℝ)..R, ((a + s) * (a + s))⁻¹ = a⁻¹ - (a + R)⁻¹ := by
  have hF : ∀ s ∈ Set.uIcc (0:ℝ) R,
      HasDerivAt (fun t => -((a + t)⁻¹)) (((a + s) * (a + s))⁻¹) s := by
    intro s hs
    rw [Set.uIcc_of_le hR] at hs
    have hs0 : 0 ≤ s := hs.1
    have has : 0 < a + s := by linarith
    have h1 : HasDerivAt (fun t : ℝ => a + t) 1 s := by
      simpa using (hasDerivAt_id s).const_add a
    have h2 := ((hasDerivAt_inv has.ne').comp s h1).neg
    have hval : -(-((a + s) ^ 2)⁻¹ * 1) = ((a + s) * (a + s))⁻¹ := by
      rw [mul_one, neg_neg, sq]
    rw [← hval]
    exact h2
  rw [integral_eq_sub_of_hasDerivAt hF
    (resolvent_prod_integrable ha ha hR)]
  rw [add_zero]
  ring

/-! ### The boxed limit identity -/

theorem tendsto_log_ratio_shift {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun R : ℝ => Real.log (b + R) - Real.log (a + R)) atTop
      (𝓝 0) := by
  have hev : ∀ᶠ R : ℝ in atTop,
      Real.log (b + R) - Real.log (a + R) =
        Real.log (1 + (b - a) / (a + R)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    have has : 0 < a + R := by linarith
    have hbs : 0 < b + R := by linarith
    rw [← Real.log_div hbs.ne' has.ne']
    congr 1
    field_simp
    ring
  have hlim : Tendsto (fun R : ℝ => 1 + (b - a) / (a + R)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun R : ℝ => a + R) atTop atTop :=
      tendsto_atTop_add_const_left _ a tendsto_id
    have h2 : Tendsto (fun R : ℝ => (b - a) / (a + R)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp h1).const_mul (b - a)
    have h3 := h2.const_add (1 : ℝ)
    simpa using h3
  have hlog : Tendsto (fun R : ℝ =>
      Real.log (1 + (b - a) / (a + R))) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto
    have h2 := h.comp hlim
    simpa [Function.comp_def] using h2
  have heq : (fun R : ℝ => Real.log (b + R) - Real.log (a + R)) =ᶠ[atTop]
      fun R => Real.log (1 + (b - a) / (a + R)) := hev
  exact Tendsto.congr' heq.symm hlog

/-- **The resolvent integral representation of the BKM kernel**:
`∫₀^R ds/((a+s)(b+s)) → k(a,b)` as `R → ∞`. -/
theorem tendsto_integral_resolvent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun R : ℝ => ∫ s in (0:ℝ)..R, ((a + s) * (b + s))⁻¹) atTop
      (𝓝 (bkmKernel a b)) := by
  rcases eq_or_ne a b with rfl | hab
  · have hev : ∀ᶠ R : ℝ in atTop,
        a⁻¹ - (a + R)⁻¹ =
          ∫ s in (0:ℝ)..R, ((a + s) * (a + s))⁻¹ := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      exact (integral_resolvent_prod_eq ha hR).symm
    have h1 : Tendsto (fun R : ℝ => a + R) atTop atTop :=
      tendsto_atTop_add_const_left _ a tendsto_id
    have h2 : Tendsto (fun R : ℝ => a⁻¹ - (a + R)⁻¹) atTop
        (𝓝 (a⁻¹)) := by
      have h3 := (tendsto_inv_atTop_zero.comp h1).const_sub (a⁻¹)
      simpa using h3
    rw [show bkmKernel a a = a⁻¹ from if_pos rfl]
    have heq : (fun R : ℝ => a⁻¹ - (a + R)⁻¹) =ᶠ[atTop]
        fun R => ∫ s in (0:ℝ)..R, ((a + s) * (a + s))⁻¹ := hev
    exact Tendsto.congr' heq h2
  · have hev : ∀ᶠ R : ℝ in atTop,
        (Real.log (b + R) - Real.log (a + R)) / (a - b) -
          (Real.log b - Real.log a) / (a - b) =
          ∫ s in (0:ℝ)..R, ((a + s) * (b + s))⁻¹ := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      exact (integral_resolvent_prod_ne ha hb hab hR).symm
    have hlim : Tendsto (fun R : ℝ =>
        (Real.log (b + R) - Real.log (a + R)) / (a - b) -
          (Real.log b - Real.log a) / (a - b)) atTop
        (𝓝 ((Real.log a - Real.log b) / (a - b))) := by
      have h1 := (tendsto_log_ratio_shift ha hb).div_const (a - b)
      have h2 := h1.sub_const ((Real.log b - Real.log a) / (a - b))
      have h3 : (0 : ℝ) / (a - b) -
          (Real.log b - Real.log a) / (a - b) =
          (Real.log a - Real.log b) / (a - b) := by
        rw [zero_div, zero_sub, ← neg_div, neg_sub]
      rwa [h3] at h2
    rw [show bkmKernel a b =
      (Real.log a - Real.log b) / (a - b) from if_neg hab]
    have heq : (fun R : ℝ =>
        (Real.log (b + R) - Real.log (a + R)) / (a - b) -
          (Real.log b - Real.log a) / (a - b)) =ᶠ[atTop]
        fun R => ∫ s in (0:ℝ)..R, ((a + s) * (b + s))⁻¹ := hev
    exact Tendsto.congr' heq hlim

end QRE
end NCG
