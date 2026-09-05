/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.HoeffdingSupport
import NCG.Grand.ScoreContinuum

/-!
# canonical primitive Hoeffding carrier

This file instantiates the four-cell Hoeffding theorem on the canonical
one-dimensional constant plus three-dimensional score carrier and verifies
the manuscript's concrete score-Gram tensor frame window.
-/

set_option linter.unusedSimpArgs false
set_option linter.defProp false
set_option linter.unnecessarySeqFocus false

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

noncomputable def primitiveConstant : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => if i = 0 then 1 else 0

noncomputable def primitiveScoreProjection : Matrix (Fin 4) (Fin 4) ℂ :=
  1 - primitiveConstant

lemma primitive_projection_relations :
    primitiveConstant + primitiveScoreProjection = 1
    ∧ primitiveConstant * primitiveScoreProjection = 0
    ∧ primitiveScoreProjection * primitiveConstant = 0
    ∧ Matrix.trace primitiveConstant = 1
    ∧ Matrix.trace primitiveScoreProjection = 3 := by
  have hE2 : primitiveConstant * primitiveConstant = primitiveConstant := by
    rw [primitiveConstant, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  refine ⟨by simp [primitiveScoreProjection], ?_, ?_, ?_, ?_⟩
  · simp [primitiveScoreProjection, Matrix.mul_sub, hE2]
  · simp [primitiveScoreProjection, Matrix.sub_mul, hE2]
  · simp [primitiveConstant, Matrix.trace_diagonal, Fin.sum_univ_four]
  · rw [primitiveScoreProjection, Matrix.trace_sub, Matrix.trace_one]
    simp [primitiveConstant, Matrix.trace_diagonal, Fin.sum_univ_four]
    norm_num

noncomputable def primitive_hoeffding_support_canonical :=
  primitive_hoeffding_support primitiveConstant primitiveScoreProjection
    primitive_projection_relations.1
    primitive_projection_relations.2.1
    primitive_projection_relations.2.2.1
    primitive_projection_relations.2.2.2.1
    primitive_projection_relations.2.2.2.2

lemma scoreGram_psd : scoreGram.PosSemidef := by
  unfold scoreGram
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> rw [RCLike.le_iff_re_im] <;> constructor <;> norm_num

lemma scoreGram_lower :
    (scoreGram - ((176 / 225 : ℝ) : ℂ) • 1).PosSemidef := by
  have heq : scoreGram - ((176 / 225 : ℝ) : ℂ) • 1
      = Matrix.diagonal ![(0 : ℂ), 49 / 225, 49 / 225] := by
    unfold scoreGram
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply] <;> norm_num
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> rw [RCLike.le_iff_re_im] <;> constructor <;> norm_num

lemma scoreGram_upper :
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) - scoreGram).PosSemidef := by
  have heq : (1 : Matrix (Fin 3) (Fin 3) ℂ) - scoreGram
      = Matrix.diagonal ![((49 / 225 : ℝ) : ℂ), 0, 0] := by
    unfold scoreGram
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply] <;> norm_num
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> rw [RCLike.le_iff_re_im] <;> constructor <;> norm_num

theorem primitive_score_tensor_frame_window :
    ((scoreGram ⊗ₖ scoreGram)
        - ((((176 / 225 : ℝ) : ℂ) * ((176 / 225 : ℝ) : ℂ))) • 1).PosSemidef
    ∧ ((1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
        - scoreGram ⊗ₖ scoreGram).PosSemidef := by
  exact hoeffding_frame_window scoreGram ((176 / 225 : ℝ) : ℂ)
    scoreGram_psd (by
      rw [RCLike.le_iff_re_im]
      constructor <;> norm_num) scoreGram_lower scoreGram_upper

end NCG
