/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PolarEdge
import NCG.Grand.JointSourceUniversality

/-!
# Matrix square-root and polar-decomposition library
  (multiplier library #1 of the Gran-Tensor hard tier)

Thin matrix-language wrappers around Mathlib's continuous
functional calculus on `Matrix n n ℂ` (the `MatrixOrder`
C*-order instances):

* `sqrt_posSemidef`, `sqrt_isHermitian`, `sqrt_mul_self_eq`,
  `sqrt_unique'` — the positive square root and its uniqueness;
* `commute_sqrt`, `commute_of_commute_sq` — commutation
  transfer (the functional-calculus input `[R, P²] = 0 ⟹
  [R, P] = 0` for `P ⪰ 0`, previously a declared hypothesis);
* `sqrt_mulVec_eq_zero_iff` — support/kernel identification
  `ker √A = ker A`;
* `polar_decomposition` — every invertible `F` factors as
  `F = UP` with `U` unitary and `P` positive definite
  hermitian;
* `polar_edge_of_posDef` — the polar edge equivalence
  (`lem:SMST-polar-edge`) with the square-root commutation
  hypothesis discharged: only `P ≻ 0` is assumed.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The CFC square root of a matrix is positive semidefinite. -/
theorem sqrt_posSemidef (A : Matrix n n ℂ) :
    (CFC.sqrt A).PosSemidef :=
  (CFC.sqrt_nonneg A).posSemidef

/-- The CFC square root is hermitian. -/
theorem sqrt_isHermitian (A : Matrix n n ℂ) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (sqrt_posSemidef A).1

/-- `√A · √A = A` for `A ⪰ 0`. -/
theorem sqrt_mul_self_eq (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- The positive square root is unique. -/
theorem sqrt_unique' {A B : Matrix n n ℂ} (hB : B.PosSemidef)
    (h : B * B = A) : CFC.sqrt A = B :=
  CFC.sqrt_unique h hB.nonneg

/-- Commutation transfers from `A` to `√A`. -/
theorem commute_sqrt {A R : Matrix n n ℂ} (h : Commute A R) :
    Commute (CFC.sqrt A) R := by
  rw [CFC.sqrt_eq_cfc]
  exact h.cfc_nnreal _

/-- The polar-edge functional-calculus input, now proved:
commuting with `P²` forces commuting with `P` when `P ⪰ 0`. -/
theorem commute_of_commute_sq {P R : Matrix n n ℂ}
    (hP : P.PosSemidef) (h : R * (P * P) = (P * P) * R) :
    R * P = P * R := by
  have hsq : CFC.sqrt (P * P) = P :=
    sqrt_unique' hP rfl
  have hc : Commute (P * P) R := h.symm
  have hcs := commute_sqrt hc
  rw [hsq] at hcs
  exact hcs.eq.symm

/-- Support identification: `√A x = 0 ↔ A x = 0` for `A ⪰ 0`. -/
theorem sqrt_mulVec_eq_zero_iff {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (x : n → ℂ) :
    CFC.sqrt A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · intro h
    rw [← sqrt_mul_self_eq A hA, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  · intro h
    have h0 : star x ⬝ᵥ (A *ᵥ x) = 0 := by
      rw [h, dotProduct_zero]
    have hg := gram_realization_inner (CFC.sqrt A) x x
    rw [sqrt_isHermitian, sqrt_mul_self_eq A hA] at hg
    exact dotProduct_star_self_eq_zero.mp (hg.trans h0)

/-- The square root of a positive definite matrix is a unit. -/
theorem sqrt_isUnit {A : Matrix n n ℂ} (hA : A.PosDef) :
    IsUnit (CFC.sqrt A) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : IsUnit ((CFC.sqrt A).det * (CFC.sqrt A).det) := by
    rw [← Matrix.det_mul, sqrt_mul_self_eq A hA.posSemidef]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  exact isUnit_of_mul_isUnit_left hdet

/-- The square root of a positive definite matrix is positive
definite. -/
theorem sqrt_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    (CFC.sqrt A).PosDef :=
  (sqrt_posSemidef A).posDef_iff_isUnit.mpr (sqrt_isUnit hA)

/-- The inverse square root is hermitian. -/
theorem sqrt_inv_isHermitian (A : Matrix n n ℂ) :
    ((CFC.sqrt A)⁻¹)ᴴ = (CFC.sqrt A)⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, sqrt_isHermitian]

/-- `(√A)⁻¹ · (√A)⁻¹ = A⁻¹` for `A ≻ 0`. -/
theorem sqrt_inv_mul_sqrt_inv {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := by
  rw [← Matrix.mul_inv_rev, sqrt_mul_self_eq A hA.posSemidef]

/-- Polar decomposition: every invertible matrix is a unitary
times a positive definite hermitian matrix. -/
theorem polar_decomposition {F : Matrix n n ℂ} (hF : IsUnit F) :
    ∃ U P : Matrix n n ℂ, U * Uᴴ = 1 ∧ Uᴴ * U = 1
      ∧ P.PosDef ∧ Pᴴ = P ∧ F = U * P := by
  have hFF : (Fᴴ * F).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self F
  set P := CFC.sqrt (Fᴴ * F) with hPdef
  have hPpsd : P.PosSemidef := sqrt_posSemidef _
  have hP2 : P * P = Fᴴ * F := sqrt_mul_self_eq _ hFF
  have hPu : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hFH : IsUnit Fᴴ := by
      have := hF.star
      rwa [Matrix.star_eq_conjTranspose] at this
    have hdet : IsUnit (P.det * P.det) := by
      rw [← Matrix.det_mul, hP2]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (hFH.mul hF)
    exact isUnit_of_mul_isUnit_left hdet
  have hPpos : P.PosDef := hPpsd.posDef_iff_isUnit.mpr hPu
  have hPH : Pᴴ = P := hPpsd.1
  haveI := hPu.invertible
  have hPinvH : P⁻¹ᴴ = P⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hPH]
  have hUHU : (F * P⁻¹)ᴴ * (F * P⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, hPinvH]
    calc P⁻¹ * Fᴴ * (F * P⁻¹)
        = P⁻¹ * ((Fᴴ * F) * P⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * (P * P⁻¹)) := by
          rw [← hP2]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.mul_inv_of_invertible, Matrix.mul_one,
            Matrix.inv_mul_of_invertible]
  refine ⟨F * P⁻¹, P, mul_eq_one_comm.mp hUHU, hUHU,
    hPpos, hPH, ?_⟩
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
    Matrix.mul_one]

/-- `lem:SMST-polar-edge`, unconditional form: the square-root
commutation input is discharged by `commute_of_commute_sq`;
only positive definiteness of the polar factor is assumed. -/
theorem polar_edge_of_posDef {g : Type*} [Fintype g]
    [DecidableEq g] (U P Rs Rt : Matrix g g ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) (hP : P.PosDef) :
    (Rt * (U * P) = (U * P) * Rs
        ∧ Rs * (U * P)ᴴ = (U * P)ᴴ * Rt)
      ↔ (Rs * (P * P) = (P * P) * Rs
        ∧ Rt = U * Rs * Uᴴ) := by
  haveI := hP.isUnit.invertible
  exact polar_edge U P Rs Rt hU hU' hP.posSemidef.1
    (fun R h => commute_of_commute_sq hP.posSemidef h)

end NCG
