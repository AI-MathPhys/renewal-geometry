/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolvent
import NCG.Grand.OperatorGraphResolventPositivity

/-!
# All-shift bounded normal resolvent family

The canonical positive inverse of `A† A + λ I` is extended by zero at
nonpositive shifts, matching the all-real-shift interfaces of the graph Mosco,
heat, and spectral compilers.
-/

open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The canonical bounded normal resolvent, extended by zero at nonpositive
real shifts. -/
noncomputable def boundedOperatorNormalResolventFamily
    (A : H →L[ℂ] F) (lam : ℝ) : H →L[ℂ] H :=
  if hlam : 0 < lam then boundedOperatorNormalResolvent A lam hlam else 0

/-- At every positive shift, the all-shift family solves the strong normal
equation. -/
theorem boundedOperatorNormalResolventFamily_normalEquation
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (f : H) :
    (A† ∘L A) (boundedOperatorNormalResolventFamily A lam f) +
        (lam : ℂ) • boundedOperatorNormalResolventFamily A lam f = f := by
  rw [boundedOperatorNormalResolventFamily, dif_pos hlam]
  exact boundedOperatorNormalResolvent_normalEquation A lam hlam f

/-- At every positive shift, the all-shift family solves the weak bounded graph
resolvent equation. -/
theorem boundedOperatorNormalResolventFamily_resolventEquation
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (f : H) :
    OperatorGraphResolventEquation (⊤ : Submodule ℂ H)
      (boundedOperatorGraphMap A) lam f
      (boundedOperatorNormalResolventFamily A lam f) := by
  rw [boundedOperatorNormalResolventFamily, dif_pos hlam]
  exact boundedOperatorNormalResolvent_resolventEquation A lam hlam f


/-- The canonical positive-shift bounded normal resolvent has the sharp
operator-norm bound `1 / λ`. -/
theorem boundedOperatorNormalResolvent_opNorm_le_inv
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    ‖boundedOperatorNormalResolvent A lam hlam‖ ≤ 1 / lam := by
  exact operatorGraphResolvent_opNorm_le_inv
    (⊤ : Submodule ℂ H) (boundedOperatorGraphMap A)
    (boundedOperatorNormalResolvent A lam hlam) lam hlam
    (boundedOperatorNormalResolvent_resolventEquation A lam hlam)

/-- The canonical positive-shift bounded normal resolvent is symmetric. -/
theorem boundedOperatorNormalResolvent_isSymmetric
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (boundedOperatorNormalResolvent A lam hlam).toLinearMap := by
  exact operatorGraphResolvent_isSymmetric
    (⊤ : Submodule ℂ H) (boundedOperatorGraphMap A) lam
    (boundedOperatorNormalResolvent A lam hlam)
    (boundedOperatorNormalResolvent_resolventEquation A lam hlam)

/-- The all-shift family inherits the sharp norm bound at positive shifts. -/
theorem boundedOperatorNormalResolventFamily_opNorm_le_inv
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    ‖boundedOperatorNormalResolventFamily A lam‖ ≤ 1 / lam := by
  rw [boundedOperatorNormalResolventFamily, dif_pos hlam]
  exact boundedOperatorNormalResolvent_opNorm_le_inv A lam hlam

/-- The all-shift family is symmetric at every positive shift. -/
theorem boundedOperatorNormalResolventFamily_isSymmetric
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (boundedOperatorNormalResolventFamily A lam).toLinearMap := by
  rw [boundedOperatorNormalResolventFamily, dif_pos hlam]
  exact boundedOperatorNormalResolvent_isSymmetric A lam hlam

/-- The canonical positive-shift bounded normal resolvent is a positive
operator. -/
theorem boundedOperatorNormalResolvent_isPositive
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    (boundedOperatorNormalResolvent A lam hlam).IsPositive := by
  exact operatorGraphResolvent_isPositive
    (⊤ : Submodule ℂ H) (boundedOperatorGraphMap A) lam hlam.le
    (boundedOperatorNormalResolvent A lam hlam)
    (boundedOperatorNormalResolvent_resolventEquation A lam hlam)

/-- The all-shift family is positive at every positive shift. -/
theorem boundedOperatorNormalResolventFamily_isPositive
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    (boundedOperatorNormalResolventFamily A lam).IsPositive := by
  rw [boundedOperatorNormalResolventFamily, dif_pos hlam]
  exact boundedOperatorNormalResolvent_isPositive A lam hlam
end NCG.VaryingHilbert
