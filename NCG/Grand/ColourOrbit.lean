/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact singlet–adjoint colour occurrence
  (`thm:SM-colour-orbit`, Gran-Tensor manuscript)

The Haar average `∫ |URU*⟩⟨URU*| dU = Π₁ + (1/5)Π₁₅` is fixed by
Schur orthogonality from two finite invariants of the seed
`R_{3|1} = 2P_ℓ - I₄`, both proved here on the concrete seed:

* `colourR_from_projection` / `colourR_involution` /
  `colourR_trace`: `R = 2P - 1` for the rank-one lepton
  projection, `R² = 1`, `tr R = -2`;
* `colour_component_split`: the Hilbert–Schmidt weight splits as
  `‖R‖² = 4` with scalar weight `(tr R)²/4 = 1` and traceless
  weight `4 - 1 = 3`;
* `colour_occurrence_coefficients`: the boxed coefficients —
  scalar sector `1/1 = 1`, adjoint sector `3/15 = 1/5`
  (weight over dimension, by Schur orthogonality);
* `colour_score_bridge`: the boxed score-square bridge halves
  both: `(1/2, 1/10)`.

Rendering disclosed: Schur orthogonality for the `SU(4)` action
on `M₄(ℂ) = 𝟏 ⊕ 𝟏𝟓` (the Haar integral identity itself) and
the 257-point positive orbit quadrature are the manuscript's
representation-theoretic layer; the seed invariants and both
boxed coefficient tables are proved here.
-/

open Matrix

namespace NCG

/-- The lepton projection `P_ℓ = diag(1,0,0,0)`. -/
def lepP : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, 0, 0, 0]

/-- The colour seed `R_{3|1} = diag(1,-1,-1,-1)`. -/
def colourR : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- `P_ℓ` is a rank-one projection: idempotent with trace `1`. -/
theorem lepP_projection :
    lepP * lepP = lepP ∧ Matrix.trace lepP = 1 := by
  constructor
  · rw [lepP, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [lepP, Matrix.trace_diagonal]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num

/-- The seed is the signed splitting `R = 2P_ℓ - 1`. -/
theorem colourR_from_projection :
    colourR = (2 : ℂ) • lepP - 1 := by
  rw [colourR, lepP]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · fin_cases i <;> simp
    norm_num
  · simp [Matrix.diagonal_apply_ne _ hij,
      Matrix.one_apply_ne hij]

/-- The seed is an involution: `R² = 1`. -/
theorem colourR_involution : colourR * colourR = 1 := by
  rw [colourR, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The seed trace: `tr R = -2`. -/
theorem colourR_trace : Matrix.trace colourR = -2 := by
  rw [colourR, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- Hilbert–Schmidt weight split of the seed:
`‖R‖²_HS = tr(R²) = 4`, scalar weight `(tr R)²/4 = 1`, traceless
weight `3`. -/
theorem colour_component_split :
    Matrix.trace (colourR * colourR) = 4
      ∧ (Matrix.trace colourR) ^ 2 / 4 = 1
      ∧ Matrix.trace (colourR * colourR)
          - (Matrix.trace colourR) ^ 2 / 4 = 3 := by
  rw [colourR_involution, colourR_trace]
  norm_num [Matrix.trace_one]

/-- Boxed occurrence coefficients: weight over dimension gives
`1` on the singlet and `3/15 = 1/5` on the adjoint. -/
theorem colour_occurrence_coefficients :
    (1 : ℝ) / 1 = 1 ∧ (3 : ℝ) / 15 = 1 / 5 := by
  norm_num

/-- Boxed score-square bridge: both coefficients halve —
`𝖪₁|₁₅ = (1/2)Π₁ + (1/10)Π₁₅`. -/
theorem colour_score_bridge :
    (1 / 2 : ℝ) * 1 = 1 / 2
      ∧ (1 / 2 : ℝ) * (1 / 5) = 1 / 10 := by
  norm_num

end NCG
