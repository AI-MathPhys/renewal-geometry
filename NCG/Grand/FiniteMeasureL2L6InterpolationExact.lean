/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact L2--L6 interpolation on a measure space

This file supplies the concrete Hölder estimate used in the Palatini coframe
limit.  It is stated first at the `lintegral` level, so it applies to norms of
vector- and tensor-valued fields without committing to a particular spacetime
cylinder model.
-/

open MeasureTheory

noncomputable section

namespace NCG.FiniteMeasureL2L6Interpolation

/-- For every exponent between `2` and `6`, weighted Hölder interpolates its
power integral between the quadratic and sextic power integrals.  The weights
are explicit and add to one. -/
theorem lintegral_rpow_interpolate_two_six
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ENNReal) (hf : AEMeasurable f μ)
    (q : ℝ) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    (∫⁻ x, f x ^ q ∂μ) ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ ((6 - q) / 4) *
        (∫⁻ x, f x ^ (6 : ℝ) ∂μ) ^ ((q - 2) / 4) := by
  have ha : 0 ≤ (6 - q) / 4 := by linarith
  have hb : 0 ≤ (q - 2) / 4 := by linarith
  have hab : (6 - q) / 4 + (q - 2) / 4 = 1 := by ring
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (f := fun x => f x ^ (2 : ℝ))
    (g := fun x => f x ^ (6 : ℝ))
    (hf.pow_const _) (hf.pow_const _) ha hb hab
  calc
    (∫⁻ x, f x ^ q ∂μ) =
        ∫⁻ x, (f x ^ (2 : ℝ)) ^ ((6 - q) / 4) *
          (f x ^ (6 : ℝ)) ^ ((q - 2) / 4) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add_of_nonneg _ _
          (mul_nonneg (by norm_num) ha) (mul_nonneg (by norm_num) hb)]
      congr 1
      ring
    _ ≤ (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ ((6 - q) / 4) *
        (∫⁻ x, f x ^ (6 : ℝ) ∂μ) ^ ((q - 2) / 4) := hholder

/-- Palatini specialization: if `p > 3/2`, the conjugate-pairing exponent
`q = 2p/(p-1)` lies between `2` and `6`, and its Hölder weights simplify to
the displayed rational functions of `p`. -/
theorem palatini_lintegral_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ENNReal) (hf : AEMeasurable f μ)
    (p : ℝ) (hp : 3 / 2 < p) :
    (∫⁻ x, f x ^ (2 * p / (p - 1)) ∂μ) ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ ((2 * p - 3) / (2 * (p - 1))) *
        (∫⁻ x, f x ^ (6 : ℝ) ∂μ) ^ (1 / (2 * (p - 1))) := by
  have hpone : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hpone
  have hq2 : 2 ≤ 2 * p / (p - 1) := by
    exact (le_div_iff₀ hden).2 (by linarith)
  have hq6 : 2 * p / (p - 1) ≤ 6 := by
    exact (div_le_iff₀ hden).2 (by linarith)
  have h := lintegral_rpow_interpolate_two_six f hf
    (2 * p / (p - 1)) hq2 hq6
  have haeq : (6 - 2 * p / (p - 1)) / 4 =
      (2 * p - 3) / (2 * (p - 1)) := by
    field_simp
    ring
  have hbeq : (2 * p / (p - 1) - 2) / 4 =
      1 / (2 * (p - 1)) := by
    field_simp
    ring
  rw [haeq, hbeq] at h
  exact h

/-- Norm-level form of the same estimate, using Mathlib's real-exponent
extended `Lp` seminorm.  This is the direct bridge from the power-integral
estimate to a spacetime-cylinder field norm. -/
theorem eLpNorm'_interpolate_two_six
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) (hf : AEStronglyMeasurable f μ)
    (q : ℝ) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    eLpNorm' f q μ ≤
      (eLpNorm' f 2 μ) ^ ((6 - q) / (2 * q)) *
        (eLpNorm' f 6 μ) ^ (3 * (q - 2) / (2 * q)) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hqinv : 0 ≤ 1 / q := by positivity
  have hinterp := lintegral_rpow_interpolate_two_six
    (fun x => ‖f x‖ₑ) hf.enorm q hq2 hq6
  have hroot := ENNReal.rpow_le_rpow hinterp hqinv
  have hnorm :
      (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) ^ (1 / q) ≤
        ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^
            ((6 - q) / (2 * q)) *
          ((∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ)) ^
            (3 * (q - 2) / (2 * q)) := by
    calc
      (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) ^ (1 / q) ≤
        ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((6 - q) / 4) *
          (∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^ ((q - 2) / 4)) ^
            (1 / q) := hroot
      _ = ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^
          ((6 - q) / (2 * q)) *
        ((∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ)) ^
          (3 * (q - 2) / (2 * q)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqinv,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        calc
          (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^
                ((6 - q) / 4 * (1 / q)) *
              (∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^
                ((q - 2) / 4 * (1 / q)) =
            (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^
                ((1 / 2) * ((6 - q) / (2 * q))) *
              (∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^
                ((1 / 6) * (3 * (q - 2) / (2 * q))) := by
                  congr 1 <;> field_simp <;> ring
          _ = ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^
                ((6 - q) / (2 * q)) *
              ((∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ)) ^
                (3 * (q - 2) / (2 * q)) := by
                  rw [ENNReal.rpow_mul, ENNReal.rpow_mul]
  simpa only [eLpNorm'_eq_lintegral_enorm] using hnorm

/-- Palatini norm specialization with the simplified interpolation weights.
In particular the low-norm exponent is positive exactly when `p > 3/2`. -/
theorem palatini_eLpNorm'_interpolation
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) (hf : AEStronglyMeasurable f μ)
    (p : ℝ) (hp : 3 / 2 < p) :
    eLpNorm' f (2 * p / (p - 1)) μ ≤
      (eLpNorm' f 2 μ) ^ ((2 * p - 3) / (2 * p)) *
        (eLpNorm' f 6 μ) ^ (3 / (2 * p)) := by
  have hpone : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hpone
  have hq2 : 2 ≤ 2 * p / (p - 1) :=
    (le_div_iff₀ hden).2 (by linarith)
  have hq6 : 2 * p / (p - 1) ≤ 6 :=
    (div_le_iff₀ hden).2 (by linarith)
  have h := eLpNorm'_interpolate_two_six f hf
    (2 * p / (p - 1)) hq2 hq6
  have haeq : (6 - 2 * p / (p - 1)) /
      (2 * (2 * p / (p - 1))) = (2 * p - 3) / (2 * p) := by
    field_simp
    ring
  have hbeq : 3 * (2 * p / (p - 1) - 2) /
      (2 * (2 * p / (p - 1))) = 3 / (2 * p) := by
    field_simp
    ring
  rw [haeq, hbeq] at h
  exact h

end NCG.FiniteMeasureL2L6Interpolation
