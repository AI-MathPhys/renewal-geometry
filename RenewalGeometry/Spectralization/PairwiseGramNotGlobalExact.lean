/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pairwise positivity need not give a joint realization

Paper `predictive_spectral_geometry`, label `cth:supp-pairwise-not-global`:
the `3 × 3` correlation matrix `eq:supp-three-block-counterexample`
```
  1    -3/4  -3/4
 -3/4   1    -3/4
 -3/4  -3/4   1
```
has every `2 × 2` principal block positive definite
(`RenewalGeometry.pairwiseCounterexampleGram_principal_block_posDef`) but has
eigenvalue `-1/2` (`RenewalGeometry.pairwiseCounterexampleGram_hasEigenvalue`),
hence is not positive semidefinite
(`RenewalGeometry.pairwiseCounterexampleGram_not_posSemidef`).
-/

open Matrix

namespace RenewalGeometry

/-- The `3 × 3` correlation matrix of `eq:supp-three-block-counterexample`. -/
noncomputable def pairwiseCounterexampleGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -3/4, -3/4; -3/4, 1, -3/4; -3/4, -3/4, 1]

/-- The all-ones vector is an eigenvector with eigenvalue `-1/2`. -/
theorem pairwiseCounterexampleGram_mulVec_ones :
    pairwiseCounterexampleGram *ᵥ ![1, 1, 1] = (-1/2 : ℝ) • ![1, 1, 1] := by
  ext i
  fin_cases i <;>
    simp [pairwiseCounterexampleGram, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- **Proposition `cth:supp-pairwise-not-global` (eigenvalue `-1/2`).** -/
theorem pairwiseCounterexampleGram_hasEigenvalue :
    Module.End.HasEigenvalue (Matrix.toLin' pairwiseCounterexampleGram) (-1/2 : ℝ) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 1, 1]) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact pairwiseCounterexampleGram_mulVec_ones
  · intro h
    have := congrFun h 0
    simp at this

/-- **Proposition `cth:supp-pairwise-not-global` (no joint positive Gram).**
The matrix is not positive semidefinite: the quadratic form is `-3/2` on the
all-ones vector. -/
theorem pairwiseCounterexampleGram_not_posSemidef :
    ¬ pairwiseCounterexampleGram.PosSemidef := by
  intro h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  have := h.2 ![1, 1, 1]
  rw [pairwiseCounterexampleGram_mulVec_ones] at this
  simp [dotProduct, Fin.sum_univ_three] at this
  norm_num at this

/-- The common `2 × 2` principal block `!![1, -3/4; -3/4, 1]` is positive
definite: `xᵀ B x = (x₀ - 3x₁/4)² + 7x₁²/16`. -/
theorem pairwiseCounterexampleBlock_posDef :
    (!![1, -3/4; -3/4, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hq : star x ⬝ᵥ ((!![1, -3/4; -3/4, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x)
        = (x 0 - 3/4 * x 1) ^ 2 + 7/16 * (x 1) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [hq]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro h0
        apply hx
        ext i
        fin_cases i <;> simp [h0, h1]
      rw [h1]
      have : 0 < x 0 ^ 2 := by positivity
      nlinarith
    · have : 0 < x 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 - 3/4 * x 1)]

/-- **Proposition `cth:supp-pairwise-not-global` (pairwise positivity).** Every
`2 × 2` principal block of the counterexample is positive definite. -/
theorem pairwiseCounterexampleGram_principal_block_posDef (i j : Fin 3) (hij : i ≠ j) :
    (pairwiseCounterexampleGram.submatrix ![i, j] ![i, j]).PosDef := by
  have hblock : pairwiseCounterexampleGram.submatrix ![i, j] ![i, j]
      = !![1, -3/4; -3/4, 1] := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (ext a b; fin_cases a <;> fin_cases b <;> simp [pairwiseCounterexampleGram])
  rw [hblock]
  exact pairwiseCounterexampleBlock_posDef

end RenewalGeometry
