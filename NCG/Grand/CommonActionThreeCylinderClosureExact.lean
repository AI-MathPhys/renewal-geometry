/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ThreeCylinderTransportExact

/-!
# Common-action three-cylinder closure

The complete finite common-action incidence alternative, including the
canonical polar new writer and transport through an invertible cutoff.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace CommonActionThreeCylinderClosureExact

open ThreeCylinderActionResponse ThreeCylinderTransport GeometricThresholdBank SourceCoercivityInfluence

variable {h d : ℕ}

/-- The complete common-action three-cylinder corollary: incidence is exact,
the zero and nonzero innovation branches are exhaustive, the zero branch is
reducing, the nonzero branch carries the canonical source-minimal polar
writer, and invertible cutoff transport preserves all finite diagnostics. -/
theorem common_action_three_cylinder_closure
    (G : Matrix (Fin d) (Fin d) ℂ) (Y S : Matrix (Fin h) (Fin d) ℂ)
    (T P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : IsUnit V.det) :
    (residual G Y T = 0 ↔
      G = Yᴴ * ((1 : Matrix (Fin h) (Fin h) ℂ) - T) * Y) ∧
    (innovation S P = 0 ∨ innovation S P ≠ 0) ∧
    (innovation S P = 0 → rangeProj S * P = P * rangeProj S) ∧
    ((newWriter S P hP)ᴴ * newWriter S P hP =
      supportProj (innovation_posSemidef S P hP).1) ∧
    (rangeProj S * newWriter S P hP = 0) ∧
    (∀ n : ℕ, moment (S * V) P n = Vᴴ * moment S P n * V) ∧
    ((innovation (S * V) P).rank = (innovation S P).rank) ∧
    (innovation (S * V) P = 0 ↔ innovation S P = 0) := by
  refine ⟨residual_eq_zero_iff G Y T, em _, ?_,
    newWriter_isometry S P hP, rangeProj_mul_newWriter S P hP,
    moment_transport V S P, innovationRank_transport V S P hP hV,
    innovation_zero_transport V S P hP hV⟩
  intro hz
  exact ((innovation_eq_zero_iff S P hP).2).mp
    (((innovation_eq_zero_iff S P hP).1).mp hz)

end CommonActionThreeCylinderClosureExact
end NCG
