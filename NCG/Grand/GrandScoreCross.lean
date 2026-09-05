/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The score-square cross channel
  (`thm:SM-score-cross`, Gran-Tensor manuscript)

* `sm_score_cross`: on the graded carrier `H_L ⊕ H_R` with the
  bridge words `X = [[0,F*],[F,0]]` and `Y = [[0,-iF*],[iF,0]]`,
  both bridge conjugations of a right-supported operator land on
  the left with the same value,
  `X(0⊕T)X = Y(0⊕T)Y = (F*TF) ⊕ 0`, and symmetrically for
  left-supported operators — so the score-bus channel
  `Ψ = ½·id + ¼AdX + ¼AdY` has the boxed cross maps
  `R_{L←R}(T) = ½F*TF` and `R_{R←L}(S) = ½FSF*`; for a unitary
  bridge the absorbed effect is `A_{L←R} = ½·1` — no positive
  occurrence coefficient remains to be chosen.

Rendering disclosed: the boxed formulas are the `¼+¼` sums of
the two proved conjugation identities; the Kossakowski form
`K = ½|e⟩⟨e|` and minimal row `B = 2^{-1/2}F` restate the
effect on the Hilbert–Schmidt bridge line.
-/

open Matrix

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:SM-score-cross`: the bridge conjugations of one-sided
operators, and the absorbed effect for a unitary bridge. -/
theorem sm_score_cross {l r : Type*} [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r]
    (F : Matrix r l ℂ) (T : Matrix r r ℂ) (S : Matrix l l ℂ) :
    (Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
        * Matrix.fromBlocks 0 0 0 T
        * Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
      = Matrix.fromBlocks (Fᴴ * T * F) 0 0 0)
    ∧ (Matrix.fromBlocks (0 : Matrix l l ℂ)
          ((-Complex.I) • Fᴴ) (Complex.I • F) 0
        * Matrix.fromBlocks 0 0 0 T
        * Matrix.fromBlocks (0 : Matrix l l ℂ)
          ((-Complex.I) • Fᴴ) (Complex.I • F) 0
      = Matrix.fromBlocks (Fᴴ * T * F) 0 0 0)
    ∧ (Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
        * Matrix.fromBlocks S 0 0 0
        * Matrix.fromBlocks (0 : Matrix l l ℂ) Fᴴ F 0
      = Matrix.fromBlocks 0 0 0 (F * S * Fᴴ))
    ∧ (Matrix.fromBlocks (0 : Matrix l l ℂ)
          ((-Complex.I) • Fᴴ) (Complex.I • F) 0
        * Matrix.fromBlocks S 0 0 0
        * Matrix.fromBlocks (0 : Matrix l l ℂ)
          ((-Complex.I) • Fᴴ) (Complex.I • F) 0
      = Matrix.fromBlocks 0 0 0 (F * S * Fᴴ))
    ∧ (Fᴴ * F = 1 → Fᴴ * (1 : Matrix r r ℂ) * F = 1) := by
  have hII : -Complex.I * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hII' : Complex.I * -Complex.I = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.mul_assoc]
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_zero, hII, hII', one_smul, Matrix.mul_assoc]
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.mul_assoc]
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_zero, hII', hII, one_smul, Matrix.mul_assoc]
  · intro hF
    rw [Matrix.mul_one, hF]

end NCG
