/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Scalar bounds for implicit Euler approximation

The scalar implicit-Euler multiplier `(1 + y/N)⁻ᴺ` differs from `exp (-y)` through the logarithmic
defect `y - N log (1 + y/N)`.  This file begins the model-independent quantitative estimate by
bounding that defect above and below for `N > 0` and `y ≥ 0`.
-/

noncomputable section
open Filter Topology


namespace NCG.ImplicitEuler

/-- The logarithmic implicit-Euler defect is nonnegative. -/
theorem logDefect_nonneg {N y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) :
    0 ≤ y - N * Real.log (1 + y / N) := by
  have hbase : 0 < 1 + y / N := by positivity
  have hlog := Real.log_le_sub_one_of_pos hbase
  have hscaled : N * Real.log (1 + y / N) ≤ N * ((1 + y / N) - 1) :=
    mul_le_mul_of_nonneg_left hlog hN.le
  have hsimplify : N * ((1 + y / N) - 1) = y := by
    field_simp
    ring
  linarith

/-- The logarithmic implicit-Euler defect is bounded by a rational quadratic remainder. -/
theorem logDefect_le {N y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) :
    y - N * Real.log (1 + y / N) ≤ y ^ 2 / (y + 2 * N) := by
  have hx : 0 ≤ y / N := div_nonneg hy hN.le
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hscaled :
      N * (2 * (y / N) / (y / N + 2)) ≤ N * Real.log (1 + y / N) :=
    mul_le_mul_of_nonneg_left hlog hN.le
  have hdenom : 0 < y + 2 * N := by positivity
  have halgebra :
      y - N * (2 * (y / N) / (y / N + 2)) = y ^ 2 / (y + 2 * N) := by
    field_simp
    ring
  rw [← halgebra]
  linarith

/-- Scalar implicit-Euler multiplier at positive integer order. -/
def multiplier (k : ℕ) (y : ℝ) : ℝ :=
  (1 + y / (k : ℝ))⁻¹ ^ k

/-- The implicit-Euler multiplier is the exponential of the logarithmic discretization exponent. -/
theorem multiplier_eq_exp {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y =
      Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : 0 < 1 + y / (k : ℝ) := by positivity
  unfold multiplier
  rw [← Real.exp_log (inv_pos.mpr hbase), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  ring

/-- The implicit-Euler multiplier lies above the heat multiplier. -/
theorem exp_neg_le_multiplier {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ multiplier k y := by
  rw [multiplier_eq_exp hk hy, Real.exp_le_exp]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  linarith [logDefect_nonneg hkR hy]

/-- The multiplier error is controlled by the multiplier times the logarithmic defect. -/
theorem multiplier_sub_exp_neg_le_mul_logDefect
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y - Real.exp (-y) ≤
      multiplier k y * (y - (k : ℝ) * Real.log (1 + y / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let d := y - (k : ℝ) * Real.log (1 + y / (k : ℝ))
  have hd : 0 ≤ d := logDefect_nonneg hkR hy
  have hexp :
      Real.exp (-y) =
        Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) * Real.exp (-d) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  rw [multiplier_eq_exp hk hy, hexp]
  have hone : 1 - Real.exp (-d) ≤ d := by
    linarith [Real.one_sub_le_exp_neg d]
  calc
    Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) -
        Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) * Real.exp (-d) =
      Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) *
        (1 - Real.exp (-d)) := by ring
    _ ≤ Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) * d :=
      mul_le_mul_of_nonneg_left hone (Real.exp_nonneg _)
    _ = Real.exp (-(k : ℝ) * Real.log (1 + y / (k : ℝ))) *
        (y - (k : ℝ) * Real.log (1 + y / (k : ℝ))) := rfl
/-- Combined two-sided control of the logarithmic implicit-Euler defect. -/
theorem logDefect_mem_Icc {N y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) :
    y - N * Real.log (1 + y / N) ∈ Set.Icc 0 (y ^ 2 / (y + 2 * N)) :=
  ⟨logDefect_nonneg hN hy, logDefect_le hN hy⟩

/-- Bernoulli's inequality bounds the implicit-Euler multiplier by the reciprocal linear tail. -/
theorem multiplier_le_inv_one_add {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y ≤ (1 + y)⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : 0 ≤ y / (k : ℝ) := div_nonneg hy hkR.le
  have hbern :
      1 + (k : ℝ) * (y / (k : ℝ)) ≤ (1 + y / (k : ℝ)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hsimplify : 1 + (k : ℝ) * (y / (k : ℝ)) = 1 + y := by
    field_simp
  rw [hsimplify] at hbern
  unfold multiplier
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hbern
/-- The scalar Euler error is bounded by the rationalized logarithmic remainder. -/
theorem multiplier_sub_exp_neg_le_rational
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y - Real.exp (-y) ≤
      (1 + y)⁻¹ * (y ^ 2 / (y + 2 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmult : 0 ≤ multiplier k y := by
    unfold multiplier
    positivity
  have hrat : 0 ≤ y ^ 2 / (y + 2 * (k : ℝ)) := by positivity
  calc
    multiplier k y - Real.exp (-y) ≤
        multiplier k y * (y - (k : ℝ) * Real.log (1 + y / (k : ℝ))) :=
      multiplier_sub_exp_neg_le_mul_logDefect hk hy
    _ ≤ multiplier k y * (y ^ 2 / (y + 2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left (logDefect_le hkR hy) hmult
    _ ≤ (1 + y)⁻¹ * (y ^ 2 / (y + 2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right (multiplier_le_inv_one_add hk hy) hrat

/-- A source-dependent linear-over-order scalar implicit-Euler error bound. -/
theorem multiplier_sub_exp_neg_le_div
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y - Real.exp (-y) ≤ y / (2 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h₁ : 0 < 1 + y := by positivity
  have h₂ : 0 < y + 2 * (k : ℝ) := by positivity
  have hrewrite :
      (1 + y)⁻¹ * (y ^ 2 / (y + 2 * (k : ℝ))) =
        y ^ 2 / ((1 + y) * (y + 2 * (k : ℝ))) := by
    field_simp
  calc
    multiplier k y - Real.exp (-y) ≤
        (1 + y)⁻¹ * (y ^ 2 / (y + 2 * (k : ℝ))) :=
      multiplier_sub_exp_neg_le_rational hk hy
    _ = y ^ 2 / ((1 + y) * (y + 2 * (k : ℝ))) := hrewrite
    _ ≤ y / (2 * (k : ℝ)) := by
      rw [div_le_div_iff₀ (mul_pos h₁ h₂) (by positivity)]
      nlinarith [mul_nonneg hy (mul_nonneg h₁.le h₂.le)]
/-- The scalar Euler error is also bounded by the reciprocal linear tail. -/
theorem multiplier_sub_exp_neg_le_inv_one_add
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    multiplier k y - Real.exp (-y) ≤ (1 + y)⁻¹ := by
  calc
    multiplier k y - Real.exp (-y) ≤ multiplier k y := by
      linarith [Real.exp_pos (-y)]
    _ ≤ (1 + y)⁻¹ := multiplier_le_inv_one_add hk hy

/-- Uniform scalar implicit-Euler error with an explicit inverse-square-root rate. -/
theorem abs_multiplier_sub_exp_neg_le_inv_sqrt
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) :
    |multiplier k y - Real.exp (-y)| ≤ (Real.sqrt (k : ℝ))⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  have hsquare : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) :=
    Real.sq_sqrt hkR.le
  rw [abs_of_nonneg (sub_nonneg.mpr (exp_neg_le_multiplier hk hy))]
  by_cases hsmall : y ≤ Real.sqrt (k : ℝ)
  · calc
      multiplier k y - Real.exp (-y) ≤ y / (2 * (k : ℝ)) :=
        multiplier_sub_exp_neg_le_div hk hy
      _ ≤ (Real.sqrt (k : ℝ))⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        have hproduct :
            (Real.sqrt (k : ℝ))⁻¹ * (2 * (k : ℝ)) =
              2 * Real.sqrt (k : ℝ) := by
          field_simp
          nlinarith
        rw [hproduct]
        linarith
  · have htail : Real.sqrt (k : ℝ) ≤ 1 + y := by
      have : Real.sqrt (k : ℝ) < y := lt_of_not_ge hsmall
      linarith
    exact (multiplier_sub_exp_neg_le_inv_one_add hk hy).trans
      (inv_anti₀ hsqrt htail)
/-- Explicit scalar rate indexed from zero by using Euler order one above the index. -/
def errorRate (m : ℕ) : ℝ :=
  (Real.sqrt ((m : ℝ) + 1))⁻¹

theorem errorRate_nonneg (m : ℕ) : 0 ≤ errorRate m := by
  unfold errorRate
  positivity

theorem errorRate_tendsto_zero : Tendsto errorRate atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))

/-- Zero-indexed version of the uniform scalar implicit-Euler estimate. -/
theorem abs_multiplier_succ_sub_exp_neg_le_errorRate
    (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |multiplier (m + 1) y - Real.exp (-y)| ≤ errorRate m := by
  simpa [errorRate, Nat.cast_add, Nat.cast_one] using
    (abs_multiplier_sub_exp_neg_le_inv_sqrt (k := m + 1) (Nat.succ_pos m) hy)

end NCG.ImplicitEuler
