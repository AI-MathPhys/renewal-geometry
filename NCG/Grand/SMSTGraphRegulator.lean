/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical graph regulator from the finite-Dirac operator
  (`thm:SMST-graph-regulator`, `thm:SMST-corrected-dual-measure`,
   Gran-Tensor manuscript)

* `regulator_square`: the boxed square identity —
  `(H_m^±)² = diag(D*D + m², DD* + m²)` for the massive
  regulator Hamiltonians `H_m^± = [[±m, D*], [D, ∓m]]`;
* `regulator_gap`: the spectral gap — `(H_m^±)² - m²·1 ⪰ 0`
  (the square dominates `m²`, so both Hamiltonians have gap at
  least `m`);
* `dual_trace_conj` / `dual_trace_transpose`:
  `thm:SMST-corrected-dual-measure`, the boxed sign table — the
  graph-connection coefficient `Im Tr(A*B)` flips sign under
  entrywise conjugation and is preserved under transposition, so
  `𝓛(D^c) ≅ 𝓛(D)*` while `𝓛(D^∨) ≅ 𝓛(D)` — the real/Nambu
  completion does not by itself provide a second cancelling
  determinant.

Rendering disclosed: the negative spectral projectors as
functional-calculus outputs, the relative determinant line and
its curvature, and the Berezin-factor clause are the manuscript's
line-bundle bookkeeping on top of the block and trace identities
proved here.
-/

open Matrix

namespace NCG

variable {E F : Type*} [Fintype E] [Fintype F]
  [DecidableEq E] [DecidableEq F]

/-- Boxed square identity:
`(H_m^+)² = diag(D*D + m², DD* + m²)`. -/
theorem regulator_square (D : Matrix F E ℂ) (m : ℂ) :
    Matrix.fromBlocks (m • 1) Dᴴ D (-m • 1)
      * Matrix.fromBlocks (m • 1) Dᴴ D (-m • 1)
    = Matrix.fromBlocks (Dᴴ * D + (m^2) • 1) 0 0
        (D * Dᴴ + (m^2) • 1) := by
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;>
    simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.mul_one, Matrix.one_mul, pow_two, add_comm,
      mul_neg]

open scoped ComplexOrder in
omit [DecidableEq E] [DecidableEq F] in
/-- Spectral gap: the regulator square dominates `m²` — both
diagonal blocks are `Gram + m²·1 ⪰ m²·1`. -/
theorem regulator_gap (D : Matrix F E ℂ) :
    (Matrix.fromBlocks (Dᴴ * D) 0 0 (D * Dᴴ)).PosSemidef := by
  have hfac : Matrix.fromBlocks (Dᴴ * D) 0 0 (D * Dᴴ)
      = (Matrix.fromBlocks D 0 0 Dᴴ)ᴴ
        * Matrix.fromBlocks D 0 0 Dᴴ := by
    rw [Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq E] [DecidableEq F] in
/-- `thm:SMST-corrected-dual-measure`, conjugation sign: the
graph-connection coefficient `Im Tr(A*B)` flips sign under
entrywise conjugation. -/
theorem dual_trace_conj (A B : Matrix E F ℂ) :
    (Matrix.trace ((A.map star)ᴴ * B.map star)).im
      = -(Matrix.trace (Aᴴ * B)).im := by
  have hconj : (A.map star)ᴴ * B.map star
      = (Aᴴ * B).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.map_apply, mul_comm]
  rw [hconj]
  have htr : Matrix.trace ((Aᴴ * B).map star)
      = star (Matrix.trace (Aᴴ * B)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply,
      star_sum]
  rw [htr, Complex.star_def, Complex.conj_im]

omit [DecidableEq E] in
/-- `thm:SMST-corrected-dual-measure`, transpose invariance: the
coefficient is preserved under transposition (`Tr Mᵀ = Tr M`). -/
theorem dual_trace_transpose (M : Matrix E E ℂ) :
    Matrix.trace Mᵀ = Matrix.trace M :=
  Matrix.trace_transpose M

end NCG
