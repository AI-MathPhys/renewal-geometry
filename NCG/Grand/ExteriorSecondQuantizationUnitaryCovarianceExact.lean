/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCompoundMatrixExteriorPower

/-!
# Unitary covariance of finite exterior second quantization

This file proves `thm:SMQG-unitary-covariance` on the concrete orthonormal
wedge basis developed in `FiniteCompoundMatrixExteriorPower`.  The
second-quantized operator is the family of compound matrices over all grades.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace ExteriorSecondQuantizationUnitaryCovariance

open FiniteCompoundMatrixExteriorPower

variable {d : ℕ}

/-- The finite exterior second quantization `Γ∧(A)`, grade by grade. -/
noncomputable def exteriorGamma (A : Matrix (Fin d) (Fin d) ℂ) :
    (r : ℕ) → Matrix (GradeIdx r d) (GradeIdx r d) ℂ :=
  fun r => cmpd r A

/-- Compound matrices of a unitary matrix are unitary on every wedge grade. -/
theorem compound_unitary {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : Uᴴ * U = 1) (r : ℕ) :
    (cmpd r U)ᴴ * cmpd r U = 1 := by
  rw [← cmpd_conjTranspose, ← cmpd_mul, hU, cmpd_one]

/-- A compound matrix of a unitary has invertible determinant. -/
theorem compound_unitary_det_isUnit {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : Uᴴ * U = 1) (r : ℕ) : IsUnit (cmpd r U).det := by
  have h := congrArg Matrix.det (compound_unitary hU r)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one (star (cmpd r U).det) (by simpa [mul_comm] using h)

/-- The boxed QG.17 covariance identity on every exterior grade. -/
theorem exteriorGamma_unitary_covariance
    (P U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    exteriorGamma (U * P * Uᴴ) =
      fun r => exteriorGamma U r * exteriorGamma P r * (exteriorGamma U r)ᴴ := by
  funext r
  simp only [exteriorGamma]
  rw [cmpd_mul, cmpd_mul, cmpd_conjTranspose]

/-- Unitary congruence preserves exterior-grade positivity in both directions. -/
theorem exteriorGamma_unitary_posSemidef_iff
    (P U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : ℕ) :
    (exteriorGamma (U * P * Uᴴ) r).PosSemidef ↔
      (exteriorGamma P r).PosSemidef := by
  have hU1 : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  constructor
  · intro h
    have hcong := h.conjTranspose_mul_mul_same (cmpd r U)
    simp only [exteriorGamma] at hcong ⊢
    rw [cmpd_mul, cmpd_mul, cmpd_conjTranspose] at hcong
    have hreassoc :
        (cmpd r U)ᴴ * (cmpd r U * cmpd r P * (cmpd r U)ᴴ) * cmpd r U =
          ((cmpd r U)ᴴ * cmpd r U) * cmpd r P *
            ((cmpd r U)ᴴ * cmpd r U) := by noncomm_ring
    rw [hreassoc, compound_unitary hU1 r, Matrix.one_mul, Matrix.mul_one] at hcong
    exact hcong
  · intro h
    have hcong := h.conjTranspose_mul_mul_same ((cmpd r U)ᴴ)
    simp only [exteriorGamma] at hcong ⊢
    rw [cmpd_mul, cmpd_mul, cmpd_conjTranspose]
    simpa only [Matrix.conjTranspose_conjTranspose] using hcong

/-- Unitary congruence preserves the rank of every exterior grade. -/
theorem exteriorGamma_unitary_rank
    (P U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : ℕ) :
    (exteriorGamma (U * P * Uᴴ) r).rank = (exteriorGamma P r).rank := by
  have hU1 : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hdet : IsUnit (cmpd r U).det := compound_unitary_det_isUnit hU1 r
  have hdetH : IsUnit ((cmpd r U)ᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  simp only [exteriorGamma]
  rw [cmpd_mul, cmpd_mul, cmpd_conjTranspose]
  rw [Matrix.mul_assoc,
    Matrix.rank_mul_eq_right_of_isUnit_det (cmpd r U) _ hdet,
    Matrix.rank_mul_eq_left_of_isUnit_det ((cmpd r U)ᴴ) _ hdetH]

/-- Direct word residuals are invariant after transporting the word synthesis
by the second-quantized unitary. -/
theorem exteriorGamma_unitary_word_residual
    {F : Type*} [Fintype F]
    (P U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (K : Matrix F F ℂ) (W : Matrix (GradeIdx r d) F ℂ) :
    K - Wᴴ * exteriorGamma (U * P * Uᴴ) r * W =
      K - ((cmpd r U)ᴴ * W)ᴴ * exteriorGamma P r * ((cmpd r U)ᴴ * W) := by
  simp only [exteriorGamma]
  rw [cmpd_mul, cmpd_mul, cmpd_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end ExteriorSecondQuantizationUnitaryCovariance
end NCG
