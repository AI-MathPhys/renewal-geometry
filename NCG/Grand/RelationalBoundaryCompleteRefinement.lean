/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalRefinement
import NCG.Grand.BoundaryCompleteVariationalShort

/-!
# Boundary-complete relational refinement

This is the exact RC.21 specialization of the boundary-complete short.  It
also formalizes the data-reduction sentence following RC.21: the effective
old action factors through precisely the three rows `(S,E,K)` and is therefore
independent of any presentation of the eliminated detail basis.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The three-row boundary-complete relational action. -/
noncomputable def relationalBoundaryEffective {H b : Type}
    [Fintype H] [Fintype b] [DecidableEq b]
    (S : Matrix H H ℂ) (E : Matrix b H ℂ) (K : Matrix b b ℂ)
    [Invertible ((1 : Matrix b b ℂ) + K)] : Matrix H H ℂ :=
  S + Eᴴ * (((1 : Matrix b b ℂ) + K)⁻¹ * E)

/-- Equality of the three effective rows is sufficient for equality of the
complete old-sector action; no detail-basis identification occurs. -/
theorem relationalBoundaryEffective_congr {H b : Type}
    [Fintype H] [Fintype b] [DecidableEq b]
    (S S' : Matrix H H ℂ) (E E' : Matrix b H ℂ)
    (K K' : Matrix b b ℂ)
    [Invertible ((1 : Matrix b b ℂ) + K)]
    [Invertible ((1 : Matrix b b ℂ) + K')]
    (hS : S = S') (hE : E = E') (hK : K = K') :
    relationalBoundaryEffective S E K =
      relationalBoundaryEffective S' E' K' := by
  subst S'
  subst E'
  subst K'
  rfl

/-- `cor:relational-boundary-complete-refinement` (RC.21), including the
literal complete-action Schur complement and its three-row factorization. -/
theorem relational_boundary_complete_refinement_exact
    {H T b : Type} [Fintype H] [Fintype T] [Fintype b]
    [DecidableEq H] [DecidableEq T] [DecidableEq b]
    (A : Matrix H H ℂ) (B : Matrix H T ℂ) (D : Matrix T T ℂ)
    (DX : Matrix b H ℂ) (Ddet : Matrix b T ℂ)
    (hD : D.PosDef)
    [Invertible D] [Invertible (boundaryCompleteDetail D Ddet)]
    [Invertible ((1 : Matrix b b ℂ) + boundaryStiffness D Ddet)] :
    boundaryCompleteSchur A B D DX Ddet =
      relationalBoundaryEffective
        (boundaryInteriorShort A B D)
        (boundaryEffectiveRow B D DX Ddet)
        (boundaryStiffness D Ddet)
    ∧ boundaryCompleteMinimizer B D DX Ddet =
        -((boundaryCompleteDetail D Ddet)⁻¹ *
          (boundaryCompleteCoupling B DX Ddet)ᴴ)
    ∧ boundaryCompleteDetail D Ddet *
        boundaryCompleteMinimizer B D DX Ddet =
          -(boundaryCompleteCoupling B DX Ddet)ᴴ := by
  have hpacket := boundary_complete_short_exact_packet
    A B D DX Ddet hD
  exact ⟨hpacket.1, hpacket.2.1, hpacket.2.2.1⟩

end NCG
