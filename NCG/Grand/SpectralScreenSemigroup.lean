/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalScreenDavisKahan
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Supported semigroup bounds for spectral screens

A bounded screen multiplier supported below (or above) a spectral threshold
gives the sharp supported exponential estimate.  Continuity is required only
on the spectrum, so threshold indicators are admitted whenever a spectral
gap separates the two pieces.
-/

noncomputable section

namespace NCG.CanonicalScreen

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A screen multiplier supported below `upper` gives the forward supported
semigroup bound. -/
theorem norm_exp_smul_mul_cfc_le_of_support_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (p : ℝ → ℝ) (hp : ContinuousOn p (spectrum ℝ A))
    (hpNorm : ∀ x ∈ spectrum ℝ A, |p x| ≤ 1)
    (hpSupport : ∀ x ∈ spectrum ℝ A, p x ≠ 0 → x ≤ upper)
    (upper t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A) * cfc p A‖ ≤ Real.exp (upper * t) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (a := t • A)]
  rw [← cfc_comp_smul t Real.exp A]
  rw [← cfc_mul (fun x : ℝ => Real.exp (t * x)) p A (by fun_prop) hp]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases hpx : p x = 0
  · simp [hpx, (Real.exp_pos _).le]
  · calc
      Real.exp (t * x) * |p x| ≤ Real.exp (t * x) * 1 :=
        mul_le_mul_of_nonneg_left (hpNorm x hx) (Real.exp_pos _).le
      _ ≤ Real.exp (upper * t) := by
        rw [mul_one]
        apply Real.exp_le_exp.mpr
        nlinarith [hpSupport x hx hpx]

/-- A screen multiplier supported above `lower` gives the backward supported
semigroup bound. -/
theorem norm_cfc_mul_exp_neg_smul_le_of_support_ge
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (p : ℝ → ℝ) (hp : ContinuousOn p (spectrum ℝ A))
    (hpNorm : ∀ x ∈ spectrum ℝ A, |p x| ≤ 1)
    (hpSupport : ∀ x ∈ spectrum ℝ A, p x ≠ 0 → lower ≤ x)
    (lower t : ℝ) (ht : 0 ≤ t) :
    ‖cfc p A * NormedSpace.exp ((-t) • A)‖ ≤ Real.exp (-lower * t) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (a := (-t) • A)]
  rw [← cfc_comp_smul (-t) Real.exp A]
  rw [← cfc_mul p (fun x : ℝ => Real.exp ((-t) * x)) A hp (by fun_prop)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases hpx : p x = 0
  · simp [hpx, (Real.exp_pos _).le]
  · calc
      |p x| * Real.exp (-t * x) ≤ 1 * Real.exp (-t * x) :=
        mul_le_mul_of_nonneg_right (hpNorm x hx) (Real.exp_pos _).le
      _ ≤ Real.exp (-lower * t) := by
        rw [one_mul]
        apply Real.exp_le_exp.mpr
        nlinarith [hpSupport x hx hpx]

end NCG.CanonicalScreen
