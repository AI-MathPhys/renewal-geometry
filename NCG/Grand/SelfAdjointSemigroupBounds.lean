/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SemigroupSylvesterBound
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Spectral bounds for self-adjoint semigroups

Continuous functional calculus converts one-sided spectral bounds for a
self-adjoint operator into the sharp exponential norm estimates used by the
semigroup Sylvester theorem.
-/

noncomputable section

open scoped ComplexConjugate

namespace NCG.SemigroupSylvester

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A spectral upper bound gives the sharp forward-semigroup norm bound. -/
theorem norm_exp_smul_le_exp_of_spectrum_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (upper : ℝ) (hspec : ∀ x ∈ spectrum ℝ A, x ≤ upper)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (upper * t) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (a := t • A)]
  rw [← cfc_comp_smul t Real.exp A]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [hspec x hx]

/-- A spectral lower bound gives the sharp backward-semigroup norm bound. -/
theorem norm_exp_neg_smul_le_exp_of_spectrum_ge
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (lower : ℝ) (hspec : ∀ x ∈ spectrum ℝ A, lower ≤ x)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((-t) • A)‖ ≤ Real.exp (-lower * t) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (a := (-t) • A)]
  rw [← cfc_comp_smul (-t) Real.exp A]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [hspec x hx]

end NCG.SemigroupSylvester
