/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionK4Selector
import NCG.Grand.K4TwistedExteriorSquareMultiplicity
import NCG.Grand.StandardRepresentationTwistedExteriorSquare

/-!
# Complete dimension-four selector and twisted exterior-square classification

This module joins the arithmetic and Hodge parts of DS.5--DS.6 with the exact
coordinate classification of the twisted exterior-square intertwiner space:
all centred sign-covariant alternating coefficient tensors vanish away from
`N = 4`, while at `N = 4` the generator-equivariant Hom space is generated
uniquely by the explicit invertible Hodge matrix.
-/

open Matrix Finset

namespace NCG

/-- The complete coordinate form of the DS.6 representation-theory clause. -/
theorem dimensionK4_twistedExteriorSquare_classification :
    (∀ (N : ℕ), N ≠ 4 →
      ∀ T : StandardTwistedExteriorTensor (Fin N), T.coeff = 0)
    ∧ (k4TwistedHodgeMatrix.det ≠ 0
      ∧ k4TwistedHodgeMatrix * k4ExteriorSquareTransposition =
          (-k4StandardTransposition) * k4TwistedHodgeMatrix
      ∧ k4TwistedHodgeMatrix * k4ExteriorSquareFourCycle =
          (-k4StandardFourCycle) * k4TwistedHodgeMatrix
      ∧ ∀ B : Matrix (Fin 3) (Fin 3) ℂ,
          B * k4ExteriorSquareTransposition =
              (-k4StandardTransposition) * B →
          B * k4ExteriorSquareFourCycle =
              (-k4StandardFourCycle) * B →
          ∃! α : ℂ, B = α • k4TwistedHodgeMatrix) := by
  refine ⟨fun N hN T =>
    standardTwistedExteriorTensor_zero_of_ne_four hN T, ?_⟩
  refine ⟨?_, k4TwistedHodgeMatrix_intertwines.1,
    k4TwistedHodgeMatrix_intertwines.2, ?_⟩
  · rw [k4TwistedHodgeMatrix_det]
    norm_num
  · intro B hs ht
    exact k4TwistedExteriorSquare_intertwiner_unique B hs ht

/-- `thm:dimension-K4-selector`, with both DS.5 and the full coordinate DS.6
classification included in one theorem. -/
theorem dimension_K4_selector_complete :
    ((∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ),
      Jᵀ = -J → IsUnit J.det → Even n)
    ∧ (∀ N : ℕ, Even N → 3 ≤ N →
        4 ≤ N ∧ 3 ≤ N - 1 ∧ 6 ≤ N.choose 2
        ∧ ((N - 1 = 3 ∧ N.choose 2 = 6) ↔ N = 4))
    ∧ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ),
        Aᵀ * A = 1 → ∀ v w : Fin 3 → ℝ,
        crossProduct (A *ᵥ v) (A *ᵥ w) =
          A.det • (A *ᵥ crossProduct v w)))
    ∧ ((∀ (N : ℕ), N ≠ 4 →
      ∀ T : StandardTwistedExteriorTensor (Fin N), T.coeff = 0)
    ∧ (k4TwistedHodgeMatrix.det ≠ 0
      ∧ k4TwistedHodgeMatrix * k4ExteriorSquareTransposition =
          (-k4StandardTransposition) * k4TwistedHodgeMatrix
      ∧ k4TwistedHodgeMatrix * k4ExteriorSquareFourCycle =
          (-k4StandardFourCycle) * k4TwistedHodgeMatrix
      ∧ ∀ B : Matrix (Fin 3) (Fin 3) ℂ,
          B * k4ExteriorSquareTransposition =
              (-k4StandardTransposition) * B →
          B * k4ExteriorSquareFourCycle =
              (-k4StandardFourCycle) * B →
          ∃! α : ℂ, B = α • k4TwistedHodgeMatrix)) := by
  exact ⟨dimension_K4_selector,
    dimensionK4_twistedExteriorSquare_classification⟩

end NCG
