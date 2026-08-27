/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurAssociativityMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Literal block-matrix Schur associativity

The earlier solve-form theorem identifies the iterated exterior response.  This
file supplies the literal matrix equality with the Schur complement of the
single internal block `I₁ ⊕ I₂`, exactly as displayed in the manuscript.
-/

open Matrix

namespace NCG

/-- Eliminating `I₁` and then `I₂` equals eliminating the full internal
`fromBlocks` matrix in one step. -/
theorem schur_associativity_fromBlocks {E I1 I2 : Type*}
    [Fintype I1] [Fintype I2] [DecidableEq I1] [DecidableEq I2]
    (A : Matrix E E ℂ) (B1 : Matrix E I1 ℂ) (B2 : Matrix E I2 ℂ)
    (C1 : Matrix I1 E ℂ) (C2 : Matrix I2 E ℂ)
    (D11 : Matrix I1 I1 ℂ) (D12 : Matrix I1 I2 ℂ)
    (D21 : Matrix I2 I1 ℂ) (D22 : Matrix I2 I2 ℂ)
    [Invertible D11]
    [Invertible (D22 - D21 * ⅟D11 * D12)] :
    A - fromCols B1 B2 * (fromBlocks D11 D12 D21 D22)⁻¹ * fromRows C1 C2
      = (A - B1 * ⅟D11 * C1)
          - (B2 - B1 * ⅟D11 * D12)
            * ⅟(D22 - D21 * ⅟D11 * D12)
            * (C2 - D21 * ⅟D11 * C1) := by
  letI := fromBlocks₁₁Invertible D11 D12 D21 D22
  rw [← invOf_eq_nonsing_inv (fromBlocks D11 D12 D21 D22),
    invOf_fromBlocks₁₁_eq, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]
  module

end NCG
