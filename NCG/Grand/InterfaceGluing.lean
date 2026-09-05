/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# exact matrix interface gluing
-/

open Matrix

namespace NCG

/-- `thm:interface-gluing`, assembling the solved interface value,
the actual exterior Schur response, and the Feshbach determinant. -/
theorem interface_gluing_exact
    {e i : Type*} [Fintype e] [Fintype i]
    [DecidableEq e] [DecidableEq i]
    (A : Matrix e e ℂ) (K : Matrix e i ℂ) (L : Matrix i e ℂ)
    (H : Matrix i i ℂ) [Invertible H]
    (x : e → ℂ) (u : i → ℂ)
    (hsolve : H *ᵥ u + L *ᵥ x = 0) :
    u = -(H⁻¹ *ᵥ (L *ᵥ x))
    ∧ A *ᵥ x + K *ᵥ u = (A - K * H⁻¹ * L) *ᵥ x
    ∧ Matrix.det (Matrix.fromBlocks A K L H)
      = Matrix.det H * Matrix.det (A - K * H⁻¹ * L) := by
  obtain ⟨hu, hdet⟩ := interface_gluing A K L H x u hsolve
  refine ⟨hu, ?_, hdet⟩
  rw [hu, Matrix.mulVec_neg, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  abel

end NCG
