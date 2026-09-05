/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# One-clock score collision and the fair dephasing channel
  (`lem:one-clock-score-collision`, Gran-Tensor manuscript)

* `score_collision`: the single-clock score Kraus operators
  `K_m = ½(I - imZ)` satisfy the boxed fair-coin identity
  `K_m*K_m = ½I` (each score result has probability `½` for
  every input), the quarter-rotation identity
  `(√2K_m)² = -imZ` — the algebraic form of
  `√2K_m = e^{-imπZ/4}` — and forgetting the transient score
  gives the boxed dephasing channel
  `D_Z(X) = Σ_m K_m X K_m* = ½(X + ZXZ)`.

Rendering disclosed: the derivation of `K_m` from the
controlled-`Z` circuit and the `y_m` resolution is the
manuscript's circuit bookkeeping; the retained-mark clause
(conditional branch unitary) is the writer nondemolition
identity of the canonical writer.
-/

open Matrix

set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NCG

/-- The single-clock score Kraus operator `K_m = ½(I - imZ)`. -/
noncomputable def collideK (m : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - ((m : ℂ) * Complex.I) • clockZ)

set_option linter.flexible false in
/-- `lem:one-clock-score-collision`: fair POVM, quarter
rotation, and the dephasing channel. -/
theorem score_collision (m : ℤ) (hm : m = 1 ∨ m = -1)
    (Xm : Matrix (Fin 2) (Fin 2) ℂ) :
    ((collideK m)ᴴ * collideK m = (1 / 2 : ℂ) • 1)
    ∧ ((2 : ℂ) • (collideK m * collideK m)
      = (-((m : ℂ) * Complex.I)) • clockZ)
    ∧ (collideK 1 * Xm * (collideK 1)ᴴ
        + collideK (-1) * Xm * (collideK (-1))ᴴ
      = (1 / 2 : ℂ) • (Xm + clockZ * Xm * clockZ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hm with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [collideK, clockZ, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply,
        Matrix.conjTranspose_apply] <;>
      try (ring_nf) <;>
      try (simp [Complex.I_sq]) <;>
      try ring_nf
  · rcases hm with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [collideK, clockZ, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply] <;>
      try (ring_nf) <;>
      try (simp [Complex.I_sq]) <;>
      try ring_nf
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [collideK, clockZ, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.conjTranspose_apply] <;>
      try (ring_nf) <;>
      try (simp [Complex.I_sq]) <;>
      try ring_nf

end NCG
