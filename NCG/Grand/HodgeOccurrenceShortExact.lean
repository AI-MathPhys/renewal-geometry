/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMNSHodgeShort
import Mathlib.Analysis.Matrix.Order

/-!
# Exact occurrence-shorted invariant semiregularity

This completes `thm:Hodge-occurrence-short`.  For a positive-semidefinite
Hermitian block Gram matrix with faithful occurrence block, the Schur
complement is positive semidefinite, injectivity of the full Gram map is
equivalent to positive definiteness of that complement, and every vector in
the Schur kernel returns the explicit full-block kernel obstruction.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:Hodge-occurrence-short`, all three clauses. -/
theorem hodge_occurrence_short_exact {P Q : Type} [Fintype P]
    [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (C : Matrix Q Q ℂ) [Invertible C]
    (hC : C.PosDef)
    (hG : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    let S := A - B * C⁻¹ * Bᴴ
    S.PosSemidef
      ∧ (Function.Injective (Matrix.fromBlocks A B Bᴴ C).mulVec ↔
          S.PosDef)
      ∧ (∀ (p : Matrix P Unit ℂ), S * p = 0 →
          A * p + B * (-(C⁻¹ * (Bᴴ * p))) = 0
            ∧ Bᴴ * p + C * (-(C⁻¹ * (Bᴴ * p))) = 0) := by
  dsimp only
  let S : Matrix P P ℂ := A - B * C⁻¹ * Bᴴ
  have hS : S.PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₂₂ A B hC).mp hG
  have hdet : (Matrix.fromBlocks A B Bᴴ C).det = C.det * S.det := by
    simpa [S, Matrix.invOf_eq_nonsing_inv] using
      (Matrix.det_fromBlocks₂₂ A B Bᴴ C)
  have hCdet : C.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit).ne_zero
  have hinj :
      Function.Injective (Matrix.fromBlocks A B Bᴴ C).mulVec ↔ S.PosDef := by
    rw [Matrix.mulVec_injective_iff_isUnit,
      ← hG.posDef_iff_isUnit, hG.posDef_iff_det_ne_zero,
      hdet, mul_ne_zero_iff, hS.posDef_iff_det_ne_zero]
    simp [hCdet]
  refine ⟨hS, hinj, ?_⟩
  intro p hp
  exact hodge_occurrence_short A B C p hp

end NCG
