/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples

/-!
# Writer-cone and hypocoercive finite countermodels

Structural completions of `cth:SM-writer-Gram-no-cone` and
`cth:GT-symmetric-null-positive-decay`.
-/

open Matrix Finset

namespace NCG
namespace WriterConeAndHypocoerciveCountermodels

open FiniteCalibrationAndDynamicalCounterexamples

/-! ## Equal coefficient Grams, opposite physical cones -/

def positiveWriter (z : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal z

def reversedWriter (z : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![z 0, -z 1]

def positiveWriterCoefficient : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => Matrix.diagonal ![1, 0]
  | 1 => Matrix.diagonal ![0, 1]

def reversedWriterCoefficient : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => Matrix.diagonal ![1, 0]
  | 1 => Matrix.diagonal ![0, -1]

def coefficientGram (C : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j ↦ Matrix.trace ((C i)ᵀ * C j)

theorem writer_coefficient_grams_equal_identity :
    coefficientGram positiveWriterCoefficient = 1
      ∧ coefficientGram reversedWriterCoefficient = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [coefficientGram, positiveWriterCoefficient,
      reversedWriterCoefficient, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.diagonal_apply]

theorem positiveWriter_posSemidef_iff (z : Fin 2 → ℝ) :
    (positiveWriter z).PosSemidef ↔ 0 ≤ z 0 ∧ 0 ≤ z 1 := by
  rw [positiveWriter, Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i <;> assumption

theorem reversedWriter_posSemidef_iff (z : Fin 2 → ℝ) :
    (reversedWriter z).PosSemidef ↔ 0 ≤ z 0 ∧ z 1 ≤ 0 := by
  rw [reversedWriter, Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    · simpa using h₀
    · simpa using h₁

/-- `cth:SM-writer-Gram-no-cone`: identical scalar coefficient geometry does
not determine the matrix-order cone. -/
theorem equal_grams_but_opposite_writer_cones :
    coefficientGram positiveWriterCoefficient =
        coefficientGram reversedWriterCoefficient
      ∧ (∀ z, (positiveWriter z).PosSemidef ↔ 0 ≤ z 0 ∧ 0 ≤ z 1)
      ∧ (∀ z, (reversedWriter z).PosSemidef ↔ 0 ≤ z 0 ∧ z 1 ≤ 0)
      ∧ (positiveWriter ![1, 1]).PosSemidef
      ∧ ¬(reversedWriter ![1, 1]).PosSemidef := by
  refine ⟨writer_coefficient_grams_equal_identity.1.trans
      writer_coefficient_grams_equal_identity.2.symm,
    positiveWriter_posSemidef_iff, reversedWriter_posSemidef_iff, ?_, ?_⟩
  · exact (positiveWriter_posSemidef_iff _).2 (by norm_num)
  · rw [reversedWriter_posSemidef_iff]
    norm_num

/-! ## Strict hypocoercive decay with a null symmetric floor -/

theorem hypocoerciveObservability_posDef :
    (!![1, 0; 0, (1 : ℚ) / 4] : Matrix (Fin 2) (Fin 2) ℚ).PosDef := by
  have hdiag : (!![1, 0; 0, (1 : ℚ) / 4] : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (1 : ℚ) / 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]
  rw [hdiag, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem hypGenerator_characteristic (lambda : ℚ) :
    Matrix.det (lambda • (1 : Matrix (Fin 2) (Fin 2) ℚ) - hypGenerator)
        = (lambda + 1 / 2) ^ 2 := by
  simp [hypGenerator, symmetricAction, circulation, Matrix.det_fin_two,
    Matrix.one_apply]
  ring

/-- `cth:GT-symmetric-null-positive-decay`, including the missing determinant
and spectral-stability conclusion. -/
theorem symmetric_null_with_strict_hypocoercive_decay :
    symmetricAction *ᵥ ![0, 1] = 0
      ∧ (symmetricAction + circulationᴴ * symmetricAction * circulation)
          = !![1, 0; 0, 1 / 4]
      ∧ (!![1, 0; 0, (1 : ℚ) / 4] : Matrix (Fin 2) (Fin 2) ℚ).PosDef
      ∧ (∀ lambda : ℚ,
          Matrix.det (lambda • (1 : Matrix (Fin 2) (Fin 2) ℚ) - hypGenerator)
            = (lambda + 1 / 2) ^ 2)
      ∧ (∀ lambda : ℚ,
          Matrix.det (lambda • (1 : Matrix (Fin 2) (Fin 2) ℚ) - hypGenerator) = 0
            ↔ lambda = -1 / 2) := by
  refine ⟨symmetric_null_can_have_positive_hypocoercive_observability.1,
    symmetric_null_can_have_positive_hypocoercive_observability.2.1,
    hypocoerciveObservability_posDef, hypGenerator_characteristic, ?_⟩
  intro lambda
  rw [hypGenerator_characteristic]
  constructor
  · intro h
    have : lambda + 1 / 2 = 0 := sq_eq_zero_iff.mp h
    linarith
  · rintro rfl
    norm_num

end WriterConeAndHypocoerciveCountermodels
end NCG
