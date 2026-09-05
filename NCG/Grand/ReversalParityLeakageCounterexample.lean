/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordNativeProvenance
import NCG.Grand.SameHistoryProvenancePythagoras

/-!
# Reversal parity alone does not close finite provenance

The record-native provenance corollary also warns that odd reversal parity is
not by itself a provenance certificate.  The two-dimensional example below
has a one-dimensional protected pair range and an orthogonal odd copy.  Its
writer is reversal odd but has nonzero pair-span leakage.
-/

open Matrix

namespace NCG

/-- A concrete orthogonal odd copy proves that reversal parity alone is
insufficient: the writer is odd, but lies entirely outside the protected pair
range and is nonzero. -/
theorem reversalParity_alone_insufficient_for_pairProvenance :
    ∃ (Θ P : Matrix (Fin 2) (Fin 2) ℂ)
      (X : Matrix (Fin 2) Unit ℂ),
      Θᴴ = Θ ∧ Θ * Θ = 1 ∧
      Pᴴ = P ∧ P * P = P ∧ Θ * P = P * Θ ∧
      Θ * X = -X ∧ (1 - P) * X = X ∧ X ≠ 0 := by
  let Θ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
  let X : Matrix (Fin 2) Unit ℂ := fun i _ => if i = 1 then 1 else 0
  refine ⟨Θ, P, X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Θ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Θ, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [P]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Θ, P, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change _ = -(X i j)
    fin_cases i <;> simp [Θ, X]
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [P, X]
  · intro h
    have := congrFun (congrFun h (1 : Fin 2)) Unit.unit
    simpa [X] using this

end NCG
