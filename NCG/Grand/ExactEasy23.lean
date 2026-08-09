/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandOneRouting

/-!
# Exact EASY batch 23: one grading-changing routing relation
-/

open Matrix

namespace NCG

/-- `exp(-iπ Z/4)` written in its exact algebraic form. -/
noncomputable def gradingPhase : Matrix (Fin 2) (Fin 2) ℂ :=
  !![invSqrt2 * (1 - Complex.I), 0;
     0, invSqrt2 * (1 + Complex.I)]

theorem gradingPhase_unitary : gradingPhase * gradingPhaseᴴ = 1 := by
  have hs : (starRingEnd ℂ) invSqrt2 = invSqrt2 := invSqrt2_star
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradingPhase, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, hs] <;>
    ring_nf <;> rw [invSqrt2_sq, Complex.I_sq] <;> norm_num <;> ring

/-- Phase conjugation supplies the second transverse Pauli axis. -/
theorem gradingPhase_conj_X :
    gradingPhase * clockX * gradingPhaseᴴ = clockY := by
  have hs : (starRingEnd ℂ) invSqrt2 = invSqrt2 := invSqrt2_star
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradingPhase, clockX, clockY, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, hs] <;>
    ring_nf <;> rw [invSqrt2_sq, Complex.I_sq] <;> norm_num <;> ring

/-- `prop:SM-one-routing`, including the previously missing
phase-conjugation clause. -/
theorem sm_one_routing_exact :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      M * clockZ = clockZ * M ↔ M 0 1 = 0 ∧ M 1 0 = 0)
    ∧ gradingPhase * gradingPhaseᴴ = 1
    ∧ gradingPhase * clockX * gradingPhaseᴴ = clockY
    ∧ StarAlgebra.adjoin ℂ
      ({clockX, clockY, clockZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  exact ⟨grading_even_iff, gradingPhase_unitary,
    gradingPhase_conj_X, sm_one_routing⟩

end NCG
