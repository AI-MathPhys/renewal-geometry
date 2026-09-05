/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Connected edge-action Pythagoras
  (`thm:connected-edge-action-Pythagoras`,
  Gran-Tensor manuscript)

* `connected_edge_action_pythagoras`: for a loaded connected
  edge Hessian `ℍ = [[A,-C],[-Cᴴ,B]] ⪰ 0` with `A ≻ 0`,
  router `U = A⁻¹C` and residual `R = B - CᴴA⁻¹C`:
  (i) the boxed Pythagoras as the exact block congruence
      `ℍ = [[1,0],[-Uᴴ,1]]·[[A,0],[0,R]]·[[1,-U],[0,1]]`
      (the quadratic-form identity
      `⟨(x,y),ℍ(x,y)⟩ = ‖x-Uy‖²_A + ⟨y,Ry⟩`);
  (ii) the residual is positive semidefinite (Schur
      complement of the positive edge Hessian);
  (iii) the residual vanishes exactly when
      `UᴴAU = B` (the router is then `A→B`-metric
      preserving).

The excess connected source dimension `rank R` and the
equal-dimension metric-unitary reading are the manuscript's
dimension bookkeeping over these identities.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:connected-edge-action-Pythagoras`. -/
theorem connected_edge_action_pythagoras {x y : Type*}
    [Fintype x] [Fintype y] [DecidableEq x] [DecidableEq y]
    (A : Matrix x x ℂ) (C : Matrix x y ℂ) (B : Matrix y y ℂ)
    (hA : A.PosDef)
    (hH : (fromBlocks A (-C) (-Cᴴ) B).PosSemidef) :
    -- (i) the exact block congruence (edge Pythagoras)
    fromBlocks A (-C) (-Cᴴ) B
      = fromBlocks 1 0 (-(A⁻¹ * C)ᴴ) 1
        * fromBlocks A 0 0 (B - Cᴴ * A⁻¹ * C)
        * fromBlocks 1 (-(A⁻¹ * C)) 0 1
    -- (ii) the residual is positive
    ∧ (B - Cᴴ * A⁻¹ * C).PosSemidef
    -- (iii) zero residual ↔ metric-preserving router
    ∧ (B - Cᴴ * A⁻¹ * C = 0
        ↔ (A⁻¹ * C)ᴴ * A * (A⁻¹ * C) = B) := by
  haveI := hA.isUnit.invertible
  have hAH : Aᴴ = A := hA.1
  have hAinvH : (A⁻¹)ᴴ = A⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hAH]
  -- the key contraction: `(A⁻¹C)ᴴ·A = Cᴴ`
  have hUA : (A⁻¹ * C)ᴴ * A = Cᴴ := by
    rw [Matrix.conjTranspose_mul, hAinvH, Matrix.mul_assoc,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have hUAU : (A⁻¹ * C)ᴴ * A * (A⁻¹ * C)
      = Cᴴ * A⁻¹ * C := by
    rw [hUA, Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hAC : A * (A⁻¹ * C) = C := by
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  have hUC : (A⁻¹ * C)ᴴ * C = Cᴴ * A⁻¹ * C := by
    rw [Matrix.conjTranspose_mul, hAinvH, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [hAC]
    · simp [Matrix.conjTranspose_mul, hAinvH,
        Matrix.mul_assoc, Matrix.inv_mul_of_invertible]
    · simp only [Matrix.mul_zero, Matrix.mul_one,
        Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg,
        add_zero, zero_add, neg_neg]
      rw [Matrix.mul_assoc, hAC, hUC]
      abel
  · -- Schur complement of the positive edge Hessian
    have h := (Matrix.PosDef.fromBlocks₁₁ (-C) B hA).mp hH
    simpa [Matrix.conjTranspose_neg, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc] using h
  · constructor
    · intro h0
      rw [hUAU]
      have h := sub_eq_zero.mp h0
      rw [← h]
    · intro hmet
      rw [← hUAU, hmet]
      exact sub_self B

end NCG
