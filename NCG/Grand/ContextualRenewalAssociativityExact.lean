/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Contextual renewal associativity

Exact encoding of `thm:GT-contextual-renewal-associativity` (PA.16–PA.18):
for the block sampled transfer
`K = [[A, B, C], [B', D, E], [C', E', F]]` and `z` in the common resolvent
domain, with `R_D = (I - zD)⁻¹`, `A_D = A + zBR_DB'`, `C_D = C + zBR_DE`,
`C_D' = C' + zE'R_DB'`, `F_D = F + zE'R_DE`,

`zA + z² [B C] (I - z [[D,E],[E',F]])⁻¹ [B'; C'] = zA_D + z² C_D (I - zF_D)⁻¹ C_D'`.

The identity is purely algebraic (block Gaussian elimination of the contextual
block followed by the source–escape block), so it is stated for arbitrary
coupling blocks `B', C', E'`; the Hermitian case `B' = B^*`, `C' = C^*`,
`E' = E^*` (real `z`) is the instance used by the record.  The hypotheses
are exactly the two invertibilities entering the nested elimination:
`I - zD` and the contextual Schur complement `I - zF_D`.
-/

open Matrix

namespace NCG
namespace ContextualRenewalAssociativity

variable {m n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- **(PA.18)**: nested block elimination of the complete complement. -/
theorem contextual_renewal_associativity
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix m p ℂ) (D : Matrix n n ℂ)
    (E : Matrix n p ℂ) (F : Matrix p p ℂ) (B' : Matrix n m ℂ) (C' : Matrix p m ℂ)
    (E' : Matrix p n ℂ) (z : ℂ)
    (hD : IsUnit (1 - z • D))
    (hF : IsUnit (1 - z • (F + z • (E' * (1 - z • D)⁻¹ * E)))) :
    z • A + z ^ 2 • (fromCols B C
        * (fromBlocks (1 - z • D) (-(z • E)) (-(z • E')) (1 - z • F))⁻¹
        * fromRows B' C')
      = z • (A + z • (B * (1 - z • D)⁻¹ * B'))
        + z ^ 2 • ((C + z • (B * (1 - z • D)⁻¹ * E))
          * (1 - z • (F + z • (E' * (1 - z • D)⁻¹ * E)))⁻¹
          * (C' + z • (E' * (1 - z • D)⁻¹ * B'))) := by
  -- invertible instances
  cases hD.nonempty_invertible
  set R := (1 - z • D)⁻¹ with hR
  have hRinv : ⅟(1 - z • D) = R := by rw [hR, invOf_eq_nonsing_inv]
  -- the contextual Schur complement
  have hschur : (1 - z • F) - (-(z • E')) * ⅟(1 - z • D) * (-(z • E))
      = 1 - z • (F + z • (E' * R * E)) := by
    rw [hRinv]
    simp only [smul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    module
  haveI hS' : Invertible (1 - z • (F + z • (E' * R * E))) := hF.nonempty_invertible.some
  haveI hS : Invertible ((1 - z • F) - (-(z • E')) * ⅟(1 - z • D) * (-(z • E))) :=
    Invertible.copy hS' _ hschur
  haveI hM := fromBlocks₁₁Invertible (1 - z • D) (-(z • E)) (-(z • E')) (1 - z • F)
  have hSinv : ⅟((1 - z • F) - (-(z • E')) * ⅟(1 - z • D) * (-(z • E)))
      = (1 - z • (F + z • (E' * R * E)))⁻¹ := by
    rw [invOf_eq_nonsing_inv, hschur]
  rw [← invOf_eq_nonsing_inv (fromBlocks _ _ _ _), invOf_fromBlocks₁₁_eq, hSinv, hRinv]
  -- block multiplication
  rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  -- expand and compare
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_neg, smul_smul, Matrix.mul_assoc, neg_neg]
  module

end ContextualRenewalAssociativity
end NCG
