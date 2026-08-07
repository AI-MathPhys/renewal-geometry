/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Positive two-history block factorization
  (`lem:coherence-factorization`, Gran-Tensor manuscript)

* `coherence_factorization`: for `A ≻ 0`, `B ≻ 0`, the block
  matrix `[[A, X], [Xᴴ, B]]` is positive semidefinite **iff**
  `X = √A · C · √B` for a contraction `C`
  (`I - CᴴC ⪰ 0`) — both directions, with the contraction
  produced explicitly as `C = (√A)⁻¹ X (√B)⁻¹` via the Schur
  complement.

Rendering disclosed: the manuscript states the factorization
on the support spaces of general `A, B ⪰ 0`; positive
definiteness renders "restrict to the supports" (on the
supports the compressions are positive definite), which is the
manuscript's own reduction. This discharges the sqrt-blocked
disclosure of `thm:coherence-parameterization`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `lem:coherence-factorization`. -/
theorem coherence_factorization {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (X : Matrix n m ℂ) :
    (Matrix.fromBlocks A X Xᴴ B).PosSemidef
      ↔ ∃ C : Matrix n m ℂ,
          ((1 : Matrix m m ℂ) - Cᴴ * C).PosSemidef
          ∧ X = CFC.sqrt A * C * CFC.sqrt B := by
  haveI := hA.isUnit.invertible
  haveI := (sqrt_isUnit hA).invertible
  haveI := (sqrt_isUnit hB).invertible
  have hsA2 : CFC.sqrt A * CFC.sqrt A = A :=
    sqrt_mul_self_eq A hA.posSemidef
  have hsB2 : CFC.sqrt B * CFC.sqrt B = B :=
    sqrt_mul_self_eq B hB.posSemidef
  have hcA : ∀ Y : Matrix n m ℂ,
      (CFC.sqrt A)⁻¹ * (CFC.sqrt A * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul]
  have hcA' : ∀ Y : Matrix n m ℂ,
      CFC.sqrt A * ((CFC.sqrt A)⁻¹ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  have hcB : ∀ Y : Matrix m m ℂ,
      Y * (CFC.sqrt B)⁻¹ * CFC.sqrt B = Y := fun Y => by
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_one]
  rw [hA.fromBlocks₁₁ X B]
  constructor
  · intro hschur
    refine ⟨(CFC.sqrt A)⁻¹ * X * (CFC.sqrt B)⁻¹, ?_, ?_⟩
    · have hkey : (1 : Matrix m m ℂ)
          - ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt B)⁻¹)ᴴ
            * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt B)⁻¹)
          = ((CFC.sqrt B)⁻¹)ᴴ * (B - Xᴴ * A⁻¹ * X)
              * (CFC.sqrt B)⁻¹ := by
        rw [sqrt_inv_isHermitian B, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, sqrt_inv_isHermitian B,
          sqrt_inv_isHermitian A, Matrix.mul_sub,
          Matrix.sub_mul]
        congr 1
        · rw [show (CFC.sqrt B)⁻¹ * B * (CFC.sqrt B)⁻¹
              = (CFC.sqrt B)⁻¹ * (CFC.sqrt B * CFC.sqrt B)
                * (CFC.sqrt B)⁻¹ from by rw [hsB2],
            ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
            Matrix.one_mul, Matrix.mul_inv_of_invertible]
        · rw [← sqrt_inv_mul_sqrt_inv hA]
          simp only [Matrix.mul_assoc]
      rw [hkey]
      exact hschur.conjTranspose_mul_mul_same _
    · calc X = CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X) :=
            (hcA' X).symm
        _ = CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X)
            * ((CFC.sqrt B)⁻¹ * CFC.sqrt B) := by
            rw [Matrix.inv_mul_of_invertible, Matrix.mul_one]
        _ = CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt B)⁻¹)
            * CFC.sqrt B := by
            simp only [Matrix.mul_assoc]
  · rintro ⟨C, hC, rfl⟩
    have hkey : B - (CFC.sqrt A * C * CFC.sqrt B)ᴴ * A⁻¹
          * (CFC.sqrt A * C * CFC.sqrt B)
        = (CFC.sqrt B)ᴴ
            * ((1 : Matrix m m ℂ) - Cᴴ * C) * CFC.sqrt B := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        sqrt_isHermitian, sqrt_isHermitian, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one]
      congr 1
      · exact hsB2.symm
      · rw [← sqrt_inv_mul_sqrt_inv hA]
        simp only [Matrix.mul_assoc]
        rw [hcA, hcA']
    rw [hkey]
    exact hC.conjTranspose_mul_mul_same _

end NCG
