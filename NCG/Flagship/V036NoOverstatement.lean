/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Updated no-overstatement boundary
  (`prop:master-V036-no-overstatement`, flagship manuscript)

Witness separations for the boundary clauses:

* `stiffness_not_determined`: the HDA reciprocity constraint
  `a_r·b_r = 1` is satisfied by every action stiffness
  `(a, b) = (η⁻¹, η)` — two distinct stiffnesses pass the same
  constraint, so the HDA does not fix `η_r`;
* `residual_not_absorbed`: a positive retained residual is a
  genuine additional sector — a block extension with nonzero
  residual block differs from the residual-free extension
  (block decomposition is faithful), so the residual is not
  absorbed into `χ`;
* `scaling_absorbs_only_unit`: absorbing a residual into the
  coupling would rescale every sector at once — `χ·x = x` for a
  single nonzero sector forces `χ = 1`, so a nontrivial residual
  cannot be traded for a coupling shift.

Rendering disclosed: the remaining clauses (Store–control
entrance not universal, renewal divisibility of face actions not
asserted, numerical residuals retained, no transparent
replacement cut for a full reversible carrier, no global
boundary completion from local equations, no Millennium-sector
estimates) are scope statements about what the integrated
theorem does not claim; the three witness separations proved
here are their checkable finite cores.
-/

open Matrix

namespace NCG

/-- The HDA constraint `a·b = 1` does not determine the action
stiffness: two distinct stiffnesses both satisfy it. -/
theorem stiffness_not_determined :
    ∃ η₁ η₂ : ℝ, 0 < η₁ ∧ 0 < η₂ ∧ η₁ ≠ η₂
      ∧ η₁⁻¹ * η₁ = 1 ∧ η₂⁻¹ * η₂ = 1 := by
  refine ⟨1, 2, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- A positive retained residual is a genuine additional
sector: the block extension with nonzero residual differs from
the residual-free one. -/
theorem residual_not_absorbed {n m : Type*}
    (S : Matrix n n ℂ) (R : Matrix m m ℂ)
    (hR : R ≠ 0) :
    Matrix.fromBlocks S 0 0 R ≠ Matrix.fromBlocks S 0 0 0 := by
  intro h
  apply hR
  have := congrArg Matrix.toBlocks₂₂ h
  simpa [Matrix.toBlocks_fromBlocks₂₂] using this

/-- Absorbing a residual into the coupling rescales every
sector: `χ·x = x` on one nonzero sector forces `χ = 1`. -/
theorem scaling_absorbs_only_unit (χ x : ℝ) (hx : x ≠ 0)
    (h : χ * x = x) : χ = 1 :=
  mul_right_cancel₀ hx (by rw [one_mul]; exact h)

end NCG
