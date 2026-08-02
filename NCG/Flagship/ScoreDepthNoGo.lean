/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-step score effects do not determine score depth
  (`prop:score-effect-depth-no-go-master`, flagship manuscript)

The manuscript's explicit counterexample on `ℂ²`: with
`A = |0⟩⟨0|`, the Lüders success map `ℐ_L(ρ) = AρA` and the
measure-and-prepare success map `ℐ_P(ρ) = Tr(Aρ)|1⟩⟨1|` have the
same one-step effect — both succeed with probability `Tr(Aρ)` on
every state — but starting from `|0⟩⟨0|` the Lüders instrument
succeeds twice with probability one while the prepare-`|1⟩`
instrument succeeds twice with probability zero
(`score_effect_depth_no_go`).
-/

open Matrix

namespace NCG

/-- The success effect `A = |0⟩⟨0|`. -/
noncomputable def scoreA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The prepared state `|1⟩⟨1|`. -/
noncomputable def scoreE1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The Lüders success map. -/
noncomputable def luedersMap (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  scoreA * ρ * scoreA

/-- The measure-and-prepare success map. -/
noncomputable def prepareMap (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (scoreA * ρ).trace • scoreE1

/-- `prop:score-effect-depth-no-go-master`: the two instruments
have the same one-step effect on every state but different
two-step success probabilities from `|0⟩⟨0|`. -/
theorem score_effect_depth_no_go :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (luedersMap ρ).trace = (scoreA * ρ).trace
        ∧ (prepareMap ρ).trace = (scoreA * ρ).trace)
    ∧ (luedersMap (luedersMap scoreA)).trace = 1
    ∧ (prepareMap (prepareMap scoreA)).trace = 0 := by
  refine ⟨fun ρ => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [luedersMap]
    simp [scoreA, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · rw [prepareMap, Matrix.trace_smul]
    have h1 : scoreE1.trace = 1 := by
      simp [scoreE1, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    rw [h1, smul_eq_mul, mul_one]
  · have hA : luedersMap scoreA = scoreA := by
      rw [luedersMap]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [scoreA, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hA, hA]
    simp [scoreA, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · have h1 : prepareMap scoreA = scoreE1 := by
      rw [prepareMap]
      have htr : (scoreA * scoreA).trace = 1 := by
        simp [scoreA, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fin.sum_univ_two]
      rw [htr, one_smul]
    have h2 : prepareMap scoreE1 = 0 := by
      rw [prepareMap]
      have htr : (scoreA * scoreE1).trace = 0 := by
        simp [scoreA, scoreE1, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two]
      rw [htr, zero_smul]
    rw [h1, h2, Matrix.trace_zero]

end NCG
