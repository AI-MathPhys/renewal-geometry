/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The tight tetrahedral edge POVM
  (`thm:edge-povm`, SM_emergence)

For the explicit harmonic frame `r₁₂,…,r₃₄` of the six `K₄` edge
lines and `u_e = √2·G₀^{-1/2}r_e`, `P_e = u_e u_eᵀ`:

* `edge_gram_sum` / `edge_gram_det` — the Gram sum is
  `G₀ = Σ_e r_e r_eᵀ = [[3,1,-1],[1,3,1],[-1,1,3]]` with
  `det G₀ = 16`;
* `edge_gram_posdef` — `G₀` is positive definite (explicit
  sum-of-squares decomposition), so the whitening `G₀^{-1/2}`
  exists;
* `edge_povm_tight` — for any symmetric whitening `S` (`Sᵀ = S`,
  `S·G₀·S = 1`), the frame satisfies the boxed tightness
  `Σ_e u_e u_eᵀ = 2·I₃`, so `E_e = P_e/2` is a rank-one
  six-outcome POVM;
* `edge_povm_unit` — each `u_e` is a unit vector:
  `r_eᵀG₀⁻¹r_e = 1/2` for all six edges.
-/

namespace NCG

open Matrix

/-- The six harmonic edge rows of `K₄`. -/
def edgeRow : Fin 6 → Fin 3 → ℝ
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![-1, -1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, -1]
  | 5 => ![0, 1, 1]

/-- The edge Gram sum `G₀`. -/
noncomputable def edgeGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, 1, -1; 1, 3, 1; -1, 1, 3]

/-- The explicit inverse `G₀⁻¹`. -/
noncomputable def edgeGramInv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, -(1/4), 1/4; -(1/4), 1/2, -(1/4); 1/4, -(1/4), 1/2]

set_option linter.flexible false in
/-- The Gram sum identity `Σ_e r_e r_eᵀ = G₀`. -/
theorem edge_gram_sum :
    (∑ e, Matrix.vecMulVec (edgeRow e) (edgeRow e)) = edgeGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeRow, edgeGram, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_six,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead] <;>
    norm_num

/-- `det G₀ = 16`. -/
theorem edge_gram_det : edgeGram.det = 16 := by
  rw [Matrix.det_fin_three]
  norm_num [edgeGram, Matrix.cons_val_two, Matrix.vecTail,
    Matrix.vecHead]

/-- `G₀·G₀⁻¹ = 1`: the displayed inverse is correct. -/
theorem edge_gram_mul_inv : edgeGram * edgeGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeGram, edgeGramInv, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

/-- `G₀` is positive definite: the quadratic form is the explicit
sum of squares `x² + (x+y)² + (x-z)² + (y+z)² + y² + z²`. -/
theorem edge_gram_posdef (x : Fin 3 → ℝ) :
    0 ≤ x ⬝ᵥ edgeGram.mulVec x
      ∧ (x ⬝ᵥ edgeGram.mulVec x = 0 → x = 0) := by
  have hform : x ⬝ᵥ edgeGram.mulVec x
      = (x 0) ^ 2 + (x 0 + x 1) ^ 2 + (x 0 - x 2) ^ 2
        + (x 1 + x 2) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    simp [edgeGram, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  constructor
  · rw [hform]
    positivity
  · intro h0
    rw [hform] at h0
    have hx0 : (x 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 2),
        sq_nonneg (x 1 + x 2), sq_nonneg (x 1), sq_nonneg (x 2)]
    have hx1 : (x 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 2),
        sq_nonneg (x 1 + x 2), sq_nonneg (x 0), sq_nonneg (x 2)]
    have hx2 : (x 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 2),
        sq_nonneg (x 1 + x 2), sq_nonneg (x 0), sq_nonneg (x 1)]
    funext i
    fin_cases i <;> simp only [Pi.zero_apply]
    · exact pow_eq_zero_iff two_ne_zero |>.mp hx0
    · exact pow_eq_zero_iff two_ne_zero |>.mp hx1
    · exact pow_eq_zero_iff two_ne_zero |>.mp hx2

/-- `thm:edge-povm` (tightness): for any symmetric whitening `S`
with `S·G₀·S = 1`, the whitened frame `u_e = √2·S·r_e` satisfies
`Σ_e u_e u_eᵀ = 2·I₃` — a tight rank-one six-outcome POVM after
halving. -/
theorem edge_povm_tight (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : Sᵀ = S) (hwhite : S * edgeGram * S = 1) :
    (∑ e, Matrix.vecMulVec
        (Real.sqrt 2 • S.mulVec (edgeRow e))
        (Real.sqrt 2 • S.mulVec (edgeRow e)))
      = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hterm : ∀ e : Fin 6, Matrix.vecMulVec
      (Real.sqrt 2 • S.mulVec (edgeRow e))
      (Real.sqrt 2 • S.mulVec (edgeRow e))
      = (2 : ℝ) • (S * Matrix.vecMulVec (edgeRow e) (edgeRow e)
        * S) := by
    intro e
    rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, h2]
    congr 1
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    rw [← hsym, Matrix.vecMul_transpose, hsym]
  simp only [hterm]
  rw [← Finset.smul_sum]
  congr 1
  rw [show (∑ e, S * Matrix.vecMulVec (edgeRow e) (edgeRow e) * S)
      = S * (∑ e, Matrix.vecMulVec (edgeRow e) (edgeRow e)) * S
    from by rw [Finset.mul_sum, Finset.sum_mul]]
  rw [edge_gram_sum, hwhite]

/-- `thm:edge-povm` (unit norms): each frame vector is a unit
vector, `r_eᵀG₀⁻¹r_e = 1/2` for all six edges, so
`‖u_e‖² = 2·(1/2) = 1`. -/
theorem edge_povm_unit :
    ∀ e : Fin 6, edgeRow e ⬝ᵥ edgeGramInv.mulVec (edgeRow e)
      = 1 / 2 := by
  intro e
  fin_cases e <;>
    norm_num [edgeRow, edgeGramInv, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecTail,
      Matrix.vecHead]

end NCG
