/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact-rational certification kit (SM_emergence numeric certificates)

Elementary bracketing lemmas used by the CKM/PMNS decimal-panel
certificates: square-root brackets from squared rational endpoints,
and Taylor polynomial brackets for `arctan` on `[0, ∞)` (degree 15
below, degree 17 above), obtained from the mean value inequality for
`arctan x - P x` whose derivative is `± x^{16 or 18} / (1 + x²)`.

Together with Mathlib's `Real.pi_gt_d20` / `Real.pi_lt_d20` these
certify decimal degree panels for angles given exact rational
tangents.
-/

namespace NCG

/-- Lower square-root bracket from a squared rational endpoint. -/
theorem le_sqrt_of_sq_le {a c : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ c) :
    a ≤ Real.sqrt c := by
  rw [← Real.sqrt_sq ha]
  exact Real.sqrt_le_sqrt h

/-- Upper square-root bracket from a squared rational endpoint. -/
theorem sqrt_le_of_le_sq {b c : ℝ} (hb : 0 ≤ b) (h : c ≤ b ^ 2) :
    Real.sqrt c ≤ b := by
  rw [← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h

/-- Two-sided square-root bracket. -/
theorem sqrt_mem_Icc {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : a ^ 2 ≤ c) (h2 : c ≤ b ^ 2) :
    a ≤ Real.sqrt c ∧ Real.sqrt c ≤ b :=
  ⟨le_sqrt_of_sq_le ha h1, sqrt_le_of_le_sq hb h2⟩

/-- The degree-15 lower Taylor polynomial of `arctan`. -/
noncomputable def atanLow (u : ℝ) : ℝ :=
  u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11
    + u ^ 13 / 13 - u ^ 15 / 15

/-- The degree-17 upper Taylor polynomial of `arctan`. -/
noncomputable def atanHigh (u : ℝ) : ℝ := atanLow u + u ^ 17 / 17

private theorem hasDerivAt_atanLow (x : ℝ) :
    HasDerivAt atanLow
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14)
      x := by
  unfold atanLow
  have h := (((((((hasDerivAt_id' x).fun_sub
    ((hasDerivAt_pow 3 x).div_const 3)).fun_add
    ((hasDerivAt_pow 5 x).div_const 5)).fun_sub
    ((hasDerivAt_pow 7 x).div_const 7)).fun_add
    ((hasDerivAt_pow 9 x).div_const 9)).fun_sub
    ((hasDerivAt_pow 11 x).div_const 11)).fun_add
    ((hasDerivAt_pow 13 x).div_const 13)).fun_sub
    ((hasDerivAt_pow 15 x).div_const 15)
  exact h.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_atanHigh (x : ℝ) :
    HasDerivAt atanHigh
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14
        + x ^ 16) x := by
  unfold atanHigh
  have h := (hasDerivAt_atanLow x).fun_add
    ((hasDerivAt_pow 17 x).div_const 17)
  exact h.congr_deriv (by push_cast; ring)

/-- `arctan` dominates its degree-15 Taylor polynomial on `[0, ∞)`. -/
theorem atanLow_le_arctan {u : ℝ} (hu : 0 ≤ u) :
    atanLow u ≤ Real.arctan u := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y => Real.arctan y - atanLow y)
        (x ^ 16 / (1 + x ^ 2)) x := by
    intro x
    have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
    have h := (Real.hasDerivAt_arctan x).fun_sub (hasDerivAt_atanLow x)
    exact h.congr_deriv (by field_simp; ring)
  have hmono : MonotoneOn (fun y => Real.arctan y - atanLow y)
      (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · exact fun x _ => ((hderiv x).continuousAt).continuousWithinAt
    · exact fun x _ =>
        ((hderiv x).differentiableAt).differentiableWithinAt
    · intro x _
      rw [(hderiv x).deriv]
      positivity
  have h0 : Real.arctan 0 - atanLow 0 = 0 := by simp [atanLow]
  have := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  simp only [h0] at this
  linarith [this]

/-- `arctan` is dominated by its degree-17 Taylor polynomial on
`[0, ∞)`. -/
theorem arctan_le_atanHigh {u : ℝ} (hu : 0 ≤ u) :
    Real.arctan u ≤ atanHigh u := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y => atanHigh y - Real.arctan y)
        (x ^ 18 / (1 + x ^ 2)) x := by
    intro x
    have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
    have h := (hasDerivAt_atanHigh x).fun_sub (Real.hasDerivAt_arctan x)
    exact h.congr_deriv (by field_simp; ring)
  have hmono : MonotoneOn (fun y => atanHigh y - Real.arctan y)
      (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · exact fun x _ => ((hderiv x).continuousAt).continuousWithinAt
    · exact fun x _ =>
        ((hderiv x).differentiableAt).differentiableWithinAt
    · intro x _
      rw [(hderiv x).deriv]
      positivity
  have h0 : atanHigh 0 - Real.arctan 0 = 0 := by
    simp [atanHigh, atanLow]
  have := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  simp only [h0] at this
  linarith [this]

/-- For `t > 0`, `arctan t = π/2 - arctan t⁻¹`: rational brackets for
`arctan t⁻¹` and `π` certify the degree panel of `arctan t`. -/
theorem arctan_inv_eq {t : ℝ} (ht : 0 < t) :
    Real.arctan t = Real.pi / 2 - Real.arctan t⁻¹ := by
  rw [Real.arctan_inv_of_pos ht]
  ring

end NCG
