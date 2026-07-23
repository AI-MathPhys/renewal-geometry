/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The real-even division condition (algebraic cores)

**Theorem `thm:real-even-division-selects-three`**: among odd spatial
ranks, requiring the real even Clifford subalgebra to be a *division*
algebra selects `d = 3`, where `Cl⁰₃ ≅ ℍ`.  The two algebraic cores
proved here:

* the quaternions have no zero divisors
  (`NCG.quaternion_mul_eq_zero`) — the `d = 3` even subalgebra passes
  the division condition;
* `M₂(ℂ)` has explicit zero divisors
  (`NCG.matrix_two_zero_divisors`) — the matrix even subalgebras
  appearing for odd `d ≥ 5` fail it.

The even-subalgebra identifications `Cl⁰₃ ≅ ℍ` and
`Cl⁰_d ≅ matrix algebra` for `d ≥ 5` are the noted Wedderburn steps.
-/

open scoped Quaternion

namespace NCG

/-- **Theorem `thm:real-even-division-selects-three` (division side)**:
the quaternions — the `d = 3` real even Clifford subalgebra — have no
zero divisors. -/
theorem quaternion_mul_eq_zero (a b : ℍ[ℝ]) :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  mul_eq_zero

/-- **Theorem `thm:real-even-division-selects-three` (failure side)**:
`M₂(ℂ)` has explicit zero divisors — the diagonal idempotents
`E₀₀·E₁₁ = 0` — so the matrix even subalgebras of odd rank `d ≥ 5`
fail the division condition. -/
theorem matrix_two_zero_divisors :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A ≠ 0 ∧ B ≠ 0 ∧ A * B = 0 := by
  refine ⟨Matrix.single 0 0 1, Matrix.single 1 1 1,
    ?_, ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    simp at h11
  · apply Matrix.single_mul_single_of_ne
    decide

end NCG
