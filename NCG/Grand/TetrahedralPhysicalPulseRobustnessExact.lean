/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralPulseFrameRobustness

/-!
# Physical-coordinate closure of tetrahedral pulse robustness

The earlier perturbation theorem was stated in normalized coordinates.  Here those coordinates are
identified with the two explicit manuscript pulses by proving their complete coefficient Gram
formula, and the exact physical Gram and robust Loewner/frame margin are bundled together.
-/

namespace NCG
namespace TetrahedralOddPulseFrame

noncomputable section

/-- Physical linear combinations of the unrotated and quarter-turn tetrahedral pulses. -/
def physicalPulseCombination (x : Fin 2 → ℝ) :
    Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ :=
  x 0 • pulseZero + x 1 • pulseQuarterTurn

/-- The complete physical two-pulse Gram is `2 I₂`; this is the exact identification used by
the normalized coordinate synthesis. -/
theorem physicalPulseCombination_gram (x y : Fin 2 → ℝ) :
    hilbertSchmidtInner (physicalPulseCombination x) (physicalPulseCombination y)
      = 2 * (x 0 * y 0 + x 1 * y 1) := by
  norm_num [physicalPulseCombination, hilbertSchmidtInner, pulseZero,
    pulseQuarterTurn, tensorMatrix, spatialTensor, scoreGenerator02,
    scoreGenerator12, Matrix.smul_apply, Matrix.add_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- The exact displayed pulses are linearly independent, so their coordinate realization is
faithful rather than an abstract replacement of the physical relation space. -/
theorem physicalPulseCombination_injective : Function.Injective physicalPulseCombination := by
  intro x y hxy
  have h0 := congrFun (congrFun hxy (0, 2)) (0, 1)
  have h1 := congrFun (congrFun hxy (0, 2)) (0, 0)
  simp [physicalPulseCombination, pulseZero, pulseQuarterTurn, tensorMatrix,
    spatialTensor, scoreGenerator02, scoreGenerator12, Matrix.smul_apply,
    Matrix.add_apply, Fin.isValue] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

end
end TetrahedralOddPulseFrame

/-- Exact physical-pulse instantiation of `cor:SM-tetrahedral-frame-robustness`. -/
theorem tetrahedralPhysicalPulse_frameRobustness
    (measured : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) (ε : ℝ)
    (hperturb : ‖measured - exactTwoPulseCoordinateSynthesis‖ ≤ ε)
    (hε : ε < Real.sqrt 2) :
    TetrahedralOddPulseFrame.hilbertSchmidtInner
        TetrahedralOddPulseFrame.pulseZero
        TetrahedralOddPulseFrame.pulseQuarterTurn = 0
      ∧ TetrahedralOddPulseFrame.hilbertSchmidtInner
        TetrahedralOddPulseFrame.pulseZero
        TetrahedralOddPulseFrame.pulseZero = 2
      ∧ TetrahedralOddPulseFrame.hilbertSchmidtInner
        TetrahedralOddPulseFrame.pulseQuarterTurn
        TetrahedralOddPulseFrame.pulseQuarterTurn = 2
      ∧ Function.Injective TetrahedralOddPulseFrame.physicalPulseCombination
      ∧ ∀ y : EuclideanSpace ℝ (Fin 2),
        (Real.sqrt 2 - ε) ^ 2 * ‖y‖ ^ 2 ≤ ‖measured.adjoint y‖ ^ 2 := by
  obtain ⟨horth, hzero, hquarter⟩ :=
    TetrahedralOddPulseFrame.twoPulse_exact_orthogonal_frame
  exact ⟨horth, hzero, hquarter,
    TetrahedralOddPulseFrame.physicalPulseCombination_injective,
    tetrahedralTwoPulse_frameRobustness measured ε hperturb hε⟩

end NCG
