/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Private-provenance fingerprint and reset factorization
  (`cor:private-provenance-fingerprint`,
  Gran-Tensor manuscript)

* `private_provenance_fingerprint`: the retained private
  source Gram `G_priv = [[1,1/5],[1/5,1]]`:
  (i) eigenvalues `6/5` and `4/5` with the explicit sum and
      difference eigenvectors;
  (ii) the centered contrast `(r₀-r₁)/√2` has squared source
      norm exactly `4/5`;
  (iii) the completed-reset factorization
      `G_reset = ½·I_end ⊗ G_priv` entrywise: the fresh
      endpoint and the old private provenance are independent
      source factors at the completed cut (endpoint-diagonal,
      private-block `½G_priv`).
-/

open Matrix
open scoped Kronecker

set_option linter.unusedSimpArgs false

namespace NCG

/-- `cor:private-provenance-fingerprint`. -/
theorem private_provenance_fingerprint :
    -- (i) the eigenvalue pair (6/5, 4/5)
    (!![1, 1/5; 1/5, 1] : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ ![1, 1]
      = (6/5 : ℚ) • ![1, 1]
    ∧ (!![1, 1/5; 1/5, 1] : Matrix (Fin 2) (Fin 2) ℚ)
        *ᵥ ![1, -1] = (4/5 : ℚ) • ![1, -1]
    -- (ii) the centered contrast has squared norm 4/5
    ∧ (2 : ℚ)⁻¹ * (![1, -1] ⬝ᵥ
        ((!![1, 1/5; 1/5, 1] : Matrix (Fin 2) (Fin 2) ℚ)
          *ᵥ ![1, -1])) = 4/5
    -- (iii) the reset source factors endpoint ⊗ private
    ∧ (∀ h h' i j : Fin 2,
        ((2 : ℚ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℚ)
            ⊗ₖ !![1, 1/5; 1/5, 1])) (h, i) (h', j)
          = if h = h'
            then (2 : ℚ)⁻¹ * !![1, 1/5; 1/5, 1] i j
            else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Fin.sum_univ_two] <;> norm_num
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Fin.sum_univ_two] <;> norm_num
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    norm_num
  · intro h h' i j
    by_cases hh : h = h' <;>
      simp [hh, Matrix.kroneckerMap_apply, Matrix.one_apply,
        mul_comm]

end NCG
