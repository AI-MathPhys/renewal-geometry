/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProjectionAndReturnIdentities

/-!
# Flat word relations and action descent

Full finite-dimensional encoding of
`cor:GT-flat-word-action-compatibility` (NL.4h--NL.4i).
-/

open Matrix

namespace NCG
namespace FlatWordActionCompatibility

open FiniteProjectionAndReturnIdentities

/-- The one-letter extension is flat precisely when its residual synthesis
vanishes, hence precisely when the new word panel factors through the old one.
-/
theorem flat_extension_iff {h b c : Type*} [Fintype h] [Fintype b]
    [Fintype c] (V : Matrix h c ℝ) (W : Matrix h b ℝ)
    (T : Matrix b c ℝ) :
    matrixEnergy (V - W * T) = 0 ↔ V = W * T := by
  rw [matrixEnergy_eq_zero_iff]
  exact sub_eq_zero

/-- On the flat branch, annihilation of the word relation `(-Tf,f)` by the
two block rows of the action Gram is equivalent to the two descent identities
`J=GT` and `K=TᵀGT` in (NL.4h). -/
theorem action_annihilates_flat_relation_iff
    {b c : Type*} [Fintype b] [Fintype c]
    (G : Matrix b b ℝ) (T : Matrix b c ℝ)
    (J : Matrix b c ℝ) (K : Matrix c c ℝ)
    (hG : Gᵀ = G) :
    (G * (-T) + J = 0 ∧ Jᵀ * (-T) + K = 0) ↔
      J = G * T ∧ K = Tᵀ * G * T := by
  constructor
  · rintro ⟨hhead, htail⟩
    have hJ : J = G * T := by
      rw [Matrix.mul_neg] at hhead
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg, add_comm] using hhead)
    have hK : K = Jᵀ * T := by
      rw [Matrix.mul_neg] at htail
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg, add_comm] using htail)
    refine ⟨hJ, ?_⟩
    rw [hK, hJ, Matrix.transpose_mul, hG, Matrix.mul_assoc]
  · rintro ⟨rfl, rfl⟩
    constructor
    · rw [Matrix.mul_neg]
      abel
    · rw [Matrix.transpose_mul, hG, Matrix.mul_neg]
      simp only [Matrix.mul_assoc]
      abel

/-- A positive NL.4i defect rules out simultaneous realization of the flat
word relation and the proposed action panel on one carrier. -/
theorem positive_defect_is_common_carrier_failure
    {b c : Type*} [Fintype b] [Fintype c]
    (G : Matrix b b ℝ) (T : Matrix b c ℝ)
    (J : Matrix b c ℝ) (K : Matrix c c ℝ)
    (hpositive : 0 < matrixEnergy (J - G * T)
      + matrixEnergy (K - Tᵀ * G * T)) :
    ¬(J = G * T ∧ K = Tᵀ * G * T) := by
  intro hphysical
  have hzero :=
    (flat_word_action_defect_zero_iff G T J K).2 hphysical
  linarith

end FlatWordActionCompatibility
end NCG
