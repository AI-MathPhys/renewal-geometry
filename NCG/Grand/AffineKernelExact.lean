/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.QuadFormConvexExact

/-!
# The affine integral representation of the BKM kernel

Step (B3b) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
compact **affine** representation

`k(a,b) = ∫₀¹ dt / (t·a + (1−t)·b)`,

whose denominator is affine in `(a,b)` — the key to joint convexity of
the BKM form through the Schur lemma `quadForm_convex`.

* `affine_pos`: positivity of the convex combination;
* `integral_affine_ne`, `integral_affine_diag`: closed forms by the FTC;
* `integral_affine`: **the boxed representation**.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace NCG
namespace QRE

/-! ### Positivity of the affine denominator -/

theorem affine_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 < t * a + (1 - t) * b := by
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · rw [← h0]
    simpa using hb
  · have h1 : 0 < t * a := mul_pos hpos ha
    have h2 : 0 ≤ (1 - t) * b := mul_nonneg (by linarith) hb.le
    linarith

theorem affine_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t => (t * a + (1 - t) * b)⁻¹) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, t * a + (1 - t) * b ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact (affine_pos ha hb ht.1 ht.2).ne'
  exact ((((continuousOn_id.mul continuousOn_const)).add
    ((continuousOn_const.sub continuousOn_id).mul
      continuousOn_const)).inv₀ hmem)

/-! ### Closed forms -/

/-- Closed form of the affine integral, distinct arguments. -/
theorem integral_affine_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b)⁻¹ =
      (Real.log a - Real.log b) / (a - b) := by
  have hab' : a - b ≠ 0 := sub_ne_zero_of_ne hab
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (b + s * (a - b)) / (a - b))
        ((t * a + (1 - t) * b)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hden : 0 < b + t * (a - b) := by
      have := affine_pos ha hb ht.1 ht.2
      linarith [this]
    have h1 : HasDerivAt (fun s : ℝ => b + s * (a - b)) (a - b) t := by
      simpa using ((hasDerivAt_id t).mul_const (a - b)).const_add b
    have h2 := (h1.log hden.ne').div_const (a - b)
    have hval : (a - b) / (b + t * (a - b)) / (a - b) =
        (t * a + (1 - t) * b)⁻¹ := by
      rw [div_div, mul_comm (b + t * (a - b)) (a - b),
        div_mul_eq_div_div, div_self hab', one_div]
      congr 1
      ring
    rw [← hval]
    exact h2
  have hint := affine_integrable ha hb
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  have h0 : b + (0:ℝ) * (a - b) = b := by ring
  have h1 : b + (1:ℝ) * (a - b) = a := by ring
  rw [h0, h1, div_sub_div_same]

/-- Closed form of the affine integral, equal arguments. -/
theorem integral_affine_diag {a : ℝ} (_ha : 0 < a) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * a)⁻¹ = a⁻¹ := by
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      (t * a + (1 - t) * a)⁻¹ = a⁻¹ := by
    intro t _
    congr 1
    ring
  rw [intervalIntegral.integral_congr hcongr]
  simp

/-! ### The boxed representation -/

/-- **The affine integral representation of the BKM kernel**:
`∫₀¹ dt/(t·a + (1−t)·b) = k(a,b)`. -/
theorem integral_affine {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b)⁻¹ = bkmKernel a b := by
  rcases eq_or_ne a b with rfl | hab
  · rw [integral_affine_diag ha]
    exact (if_pos rfl).symm
  · rw [integral_affine_ne ha hb hab]
    exact (if_neg hab).symm

end QRE
end NCG
