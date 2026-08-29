/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorReflectionPositivityCriterionExact
import NCG.Grand.DataProcessingExact

/-!
# Positive finite bosonic mixtures of fermionic Gaussian kernels

This file proves the finite-cylinder form of `thm:SMQG-positive-mixture`.
Each history contributes a nonnegative scalar multiple of a congruence of the
exterior covariance.  Their sum is positive semidefinite.  Arbitrary linear
word relations holding history by history descend through the same sum.

The final two-dimensional example proves that positive mixing need not remain
quasi-free: averaging the grade-two determinants differs from taking the
grade-two determinant of the averaged one-particle covariance.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace FinitePositiveBosonicGaussianMixture

open FiniteCompoundMatrixExteriorPower

variable {Ω f : Type*} [Fintype Ω] [Fintype f]
  [DecidableEq Ω] [DecidableEq f]

/-- The grade-`r` reflected kernel of a finite positive bosonic mixture. -/
noncomputable def mixedGradeKernel {d : ℕ} (r : ℕ)
    (ρ q : Ω → ℝ) (P : Ω → Matrix (Fin d) (Fin d) ℂ)
    (W : Ω → Matrix (GradeIdx r d) f ℂ) : Matrix f f ℂ :=
  ∑ ω, (((ρ ω * q ω : ℝ) : ℂ) •
    ((W ω)ᴴ * cmpd r (P ω) * W ω))

/-- Every grade of the same-history mixture is positive semidefinite. -/
theorem mixedGradeKernel_posSemidef {d : ℕ} (r : ℕ)
    (ρ q : Ω → ℝ) (P : Ω → Matrix (Fin d) (Fin d) ℂ)
    (W : Ω → Matrix (GradeIdx r d) f ℂ)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hq : ∀ ω, 0 ≤ q ω)
    (hP : ∀ ω, (P ω).PosSemidef) :
    (mixedGradeKernel r ρ q P W).PosSemidef := by
  apply Petz.sum_posSemidef
  intro ω
  apply QRE.posSemidef_smul_real (mul_nonneg (hρ ω) (hq ω))
  exact (cmpd_posSemidef (hP ω)).conjTranspose_mul_mul_same (W ω)

/-- Any linear word relation that vanishes on every conditional reflected
kernel also vanishes on the mixed kernel. -/
theorem conditional_linear_relation_descends {d : ℕ} (r : ℕ)
    (ρ q : Ω → ℝ) (P : Ω → Matrix (Fin d) (Fin d) ℂ)
    (W : Ω → Matrix (GradeIdx r d) f ℂ)
    {g : Type*} [Fintype g] [DecidableEq g]
    (R : Matrix f f ℂ →ₗ[ℂ] Matrix g g ℂ)
    (hR : ∀ ω, R ((W ω)ᴴ * cmpd r (P ω) * W ω) = 0) :
    R (mixedGradeKernel r ρ q P W) = 0 := by
  simp only [mixedGradeKernel, map_sum, map_smul, hR, smul_zero, Finset.sum_const_zero]

/-- Two-history positive covariance family used to witness loss of quasi-free
closure under mixing. -/
def covarianceTwo (ω : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if ω then (2 : ℂ) • 1 else 0

theorem covarianceTwo_posSemidef (ω : Bool) : (covarianceTwo ω).PosSemidef := by
  cases ω <;> simp [covarianceTwo]
  · exact Matrix.PosSemidef.zero
  · exact QRE.posSemidef_smul_real (by norm_num) Matrix.PosSemidef.one

/-- The one-particle covariance averaged with equal history weights is the
identity. -/
theorem covarianceTwo_average :
    ((2 : ℂ)⁻¹ • covarianceTwo false) +
      ((2 : ℂ)⁻¹ • covarianceTwo true) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [covarianceTwo]

/-- The averaged grade-two coefficient is `2`, whereas the grade-two
coefficient of the averaged covariance is `1`.  Thus the positive mixture is
not quasi-free. -/
theorem positive_mixture_not_quasiFree :
    (2 : ℂ)⁻¹ * (covarianceTwo false).det +
      (2 : ℂ)⁻¹ * (covarianceTwo true).det ≠
        (((2 : ℂ)⁻¹ • covarianceTwo false) +
          ((2 : ℂ)⁻¹ • covarianceTwo true)).det := by
  norm_num [covarianceTwo, Matrix.det_fin_two]

/-- **`thm:SMQG-positive-mixture`.**  Finite positive same-history Gaussian
mixing preserves every reflected PSD grade and every conditional linear word
relation, but need not preserve quasi-free closure. -/
theorem smqg_positive_bosonic_mixture {d : ℕ} (r : ℕ)
    (ρ q : Ω → ℝ) (P : Ω → Matrix (Fin d) (Fin d) ℂ)
    (W : Ω → Matrix (GradeIdx r d) f ℂ)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hq : ∀ ω, 0 ≤ q ω)
    (hP : ∀ ω, (P ω).PosSemidef) :
    (mixedGradeKernel r ρ q P W).PosSemidef ∧
      ((2 : ℂ)⁻¹ * (covarianceTwo false).det +
        (2 : ℂ)⁻¹ * (covarianceTwo true).det ≠
          (((2 : ℂ)⁻¹ • covarianceTwo false) +
            ((2 : ℂ)⁻¹ • covarianceTwo true)).det) :=
  ⟨mixedGradeKernel_posSemidef r ρ q P W hρ hq hP,
    positive_mixture_not_quasiFree⟩

end FinitePositiveBosonicGaussianMixture
end NCG
