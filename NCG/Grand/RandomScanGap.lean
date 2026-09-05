/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Random-scan scheduling can close independent local gaps
  (`cth:random-scan-gap`, Gran-Tensor manuscript)

* `random_scan_gap` (two-cell witness + the boxed scaling):
  (i) the random-scan operator `½(C⊗1 + 1⊗C)` of two
      independent cells `C = diag(1,q)` is diagonal with
      entries `(w_i + w_j)/2`;
  (ii) on the complement of the all-fixed sector the boxed
      norm is attained: the mixed cell `(0,1)` is an exact
      `(1+q)/2`-eigenvector and every complement vector obeys
      the quadratic bound with constant `(1+q)/2`
      `= 1 - (1-q)/2`;
  (iii) the boxed general-`N` scaling identity
      `((N-1) + q)/N = 1 - (1-q)/N`.

Hence independent local gaps (`q < 1`) and zero inter-cell
influence do not give a volume-uniform global gap under a
fixed-rate random-scan clock; the `N`-cell tensor bookkeeping
is the manuscript's iteration of the two-cell computation.
-/

open Matrix
open scoped Kronecker

set_option linter.unnecessarySeqFocus false

namespace NCG

/-- `cth:random-scan-gap`. -/
theorem random_scan_gap (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    -- (i) the random-scan operator is diagonal
    (2⁻¹ : ℝ) • (Matrix.diagonal ![1, q] ⊗ₖ 1
        + (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ⊗ₖ Matrix.diagonal ![1, q])
      = Matrix.diagonal
          (fun p : Fin 2 × Fin 2 =>
            (![1, q] p.1 + ![1, q] p.2) / 2)
    -- (ii) exact eigenvector and complement bound
    ∧ (Matrix.diagonal (fun p : Fin 2 × Fin 2 =>
          (![1, q] p.1 + ![1, q] p.2) / 2)
        *ᵥ Pi.single ((0 : Fin 2), (1 : Fin 2)) 1
        = ((1 + q) / 2)
          • Pi.single ((0 : Fin 2), (1 : Fin 2)) 1)
    ∧ (∀ v : Fin 2 × Fin 2 → ℝ, v (0, 0) = 0 →
        (Matrix.diagonal (fun p : Fin 2 × Fin 2 =>
            (![1, q] p.1 + ![1, q] p.2) / 2) *ᵥ v)
          ⬝ᵥ (Matrix.diagonal (fun p : Fin 2 × Fin 2 =>
            (![1, q] p.1 + ![1, q] p.2) / 2) *ᵥ v)
        ≤ ((1 + q) / 2) ^ 2 * (v ⬝ᵥ v))
    -- (iii) the boxed general-N scaling identity
    ∧ (∀ N : ℕ, 1 ≤ N →
        ((N : ℝ) - 1 + q) / N = 1 - (1 - q) / N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.smul_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
      Matrix.one_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [hik, hjl] <;> ring
  · rw [Matrix.diagonal_mulVec_single]
    funext y
    by_cases hy : y = ((0 : Fin 2), (1 : Fin 2))
    · subst hy
      norm_num [Pi.single_apply]
    · simp [hy]
  · intro v hv
    have hq2 : q ^ 2 ≤ ((1 + q) / 2) ^ 2 := by
      nlinarith [mul_nonneg
        (by linarith : (0:ℝ) ≤ 3 * q + 1)
        (by linarith : (0:ℝ) ≤ 1 - q)]
    simp only [dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.mulVec_diagonal,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hv]
    nlinarith [sq_nonneg (v (0, 1)), sq_nonneg (v (1, 0)),
      sq_nonneg (v (1, 1)),
      mul_le_mul_of_nonneg_right hq2
        (sq_nonneg (v (1, 1)))]
  · intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    field_simp
    ring

end NCG
