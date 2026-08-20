/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScalarImplicitEulerBounds

/-!
# Scalar Euler transform of one positive resolvent

If `r = (b + a)⁻¹` is a spectral value of one positive-shift resolvent, then every Euler
root at time `t` can be written using only `r`.  The resulting power is exactly the standard
implicit-Euler multiplier at energy `a = r⁻¹ - b`.  The dimension-free scalar Euler estimate
therefore transfers uniformly to the whole resolvent interval `[0, b⁻¹]`, including the spectral
endpoint `r = 0`.
-/

noncomputable section

namespace NCG.ImplicitEuler

/-- The Euler root at shift `k / t`, expressed through a resolvent value at the reference shift
`b`. -/
def resolventEulerRoot (b t : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ((((k : ℝ) / t) * r) / (1 + (((k : ℝ) / t) - b) * r))

/-- The heat multiplier represented by a positive reference-resolvent value.  At the possible
spectral endpoint `r = 0`, the multiplier is defined by its continuous limiting value. -/
def resolventHeatMultiplier (b t r : ℝ) : ℝ :=
  if r = 0 then 0 else Real.exp (-(t * (r⁻¹ - b)))

/-- Away from the endpoint zero, the one-resolvent Euler root is the ordinary implicit-Euler
root for energy `r⁻¹ - b`. -/
theorem resolventEulerRoot_eq_inv_one_add
    (b t r : ℝ) (k : ℕ) (ht : 0 < t) (hk : 0 < k) (hr : 0 < r) :
    resolventEulerRoot b t k r =
      (1 + t * (r⁻¹ - b) / (k : ℝ))⁻¹ := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold resolventEulerRoot
  field_simp
  ring

/-- The power of the transformed root is exactly the standard scalar implicit-Euler
multiplier. -/
theorem resolventEulerRoot_pow_eq_multiplier
    (b t r : ℝ) (k : ℕ) (ht : 0 < t) (hk : 0 < k) (hr : 0 < r) :
    resolventEulerRoot b t k r ^ k = multiplier k (t * (r⁻¹ - b)) := by
  rw [resolventEulerRoot_eq_inv_one_add b t r k ht hk hr]
  rfl

/-- A resolvent value in `[0,b⁻¹]` corresponds to a nonnegative energy. -/
theorem resolventEnergy_nonneg
    {b r : ℝ} (hr : 0 < r) (hrb : r ≤ b⁻¹) :
    0 ≤ r⁻¹ - b := by
  exact sub_nonneg.mpr (le_inv_of_le_inv₀ hr hrb)

/-- Uniform one-resolvent Euler approximation on the full positive resolvent interval. -/
theorem abs_resolventEulerRoot_pow_sub_heat_le_inv_sqrt
    (b t r : ℝ) (k : ℕ) (ht : 0 < t)
    (hk : 0 < k) (hr : 0 ≤ r) (hrb : r ≤ b⁻¹) :
    |resolventEulerRoot b t k r ^ k - resolventHeatMultiplier b t r| ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  by_cases hr0 : r = 0
  · subst r
    simp [resolventEulerRoot, resolventHeatMultiplier, zero_pow hk.ne']
  · have hrPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have henergy : 0 ≤ r⁻¹ - b := resolventEnergy_nonneg hrPos hrb
    have hy : 0 ≤ t * (r⁻¹ - b) := mul_nonneg ht.le henergy
    rw [resolventEulerRoot_pow_eq_multiplier b t r k ht hk hrPos]
    simp only [resolventHeatMultiplier, hr0, if_false]
    exact abs_multiplier_sub_exp_neg_le_inv_sqrt hk hy

end NCG.ImplicitEuler
