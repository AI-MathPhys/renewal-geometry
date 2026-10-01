/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weak defect spectrum

Covers `lem:weak-naturality-spectrum` of the spacetime–gauge duality paper.

The weak naturality generators are the matrix units `F₁₂, F₂₁ ∈ M₂(ℂ)`
(`eq:six-naturality-generators`); on `ℂ² ⊗ ℂ²` the ladder operators are
`L₊ = F₁₂ ⊗ I + I ⊗ F₁₂`, `L₋ = F₂₁ ⊗ I + I ⊗ F₂₁`, and the weak defect operator is
`H_W = L₊ L₋ + L₋ L₊`.

* `weakDefect_charpoly`: `χ_{H_W} = X (X - 2)² (X - 4)`, i.e.
  `spec H_W = {0⁽¹⁾, 2⁽²⁾, 4⁽¹⁾}` with multiplicities (`eq:weak-naturality-spectrum`).
* `weakDefect_mulVec_eq_zero_iff`: the zero eigenspace is the alternating line
  `ℂ (w₁ ⊗ w₂ − w₂ ⊗ w₁)`.
* `weakDefect_transpose`, `weakDefect_transpose_charpoly`: the dual-space (transposed)
  version has the same operator and spectrum.
* `weakDefect_isHermitian`: `H_W` is Hermitian.
-/

open Matrix Polynomial
open scoped Kronecker

namespace RenewalGeometry

/-- The weak generator `F₁₂ = |w₁⟩⟨w₂|`. -/
def weakF12 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The weak generator `F₂₁ = |w₂⟩⟨w₁|`. -/
def weakF21 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The raising ladder `L₊ = F₁₂ ⊗ I + I ⊗ F₁₂` on `ℂ² ⊗ ℂ²`. -/
def weakLPlus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weakF12 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakF12

/-- The lowering ladder `L₋ = F₂₁ ⊗ I + I ⊗ F₂₁` on `ℂ² ⊗ ℂ²`. -/
def weakLMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weakF21 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakF21

/-- The weak defect operator `H_W = L₊ L₋ + L₋ L₊` (`eq:naturality-tensor-sum`). -/
def weakDefect : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weakLPlus * weakLMinus + weakLMinus * weakLPlus

/-- The weak defect operator in the product basis `(w₁w₁, w₁w₂, w₂w₁, w₂w₂)`. -/
def weakDefectFin4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![2, 0, 0, 0; 0, 2, 2, 0; 0, 2, 2, 0; 0, 0, 0, 2]

/-- The alternating weak covector `w₁ ⊗ w₂ − w₂ ⊗ w₁`. -/
def weakAlternating : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

theorem weakDefect_apply (p q : Fin 2 × Fin 2) :
    weakDefect p q = weakDefectFin4 (finProdFinEquiv p) (finProdFinEquiv q) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [weakDefect, weakLPlus, weakLMinus, weakF12, weakF21, weakDefectFin4,
      Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, finProdFinEquiv] <;> norm_num

theorem weakDefect_eq_reindex :
    weakDefect = Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm weakDefectFin4 := by
  ext p q
  rw [weakDefect_apply]
  simp

theorem weakDefectFin4_charpoly :
    weakDefectFin4.charpoly = X * (X - 2) ^ 2 * (X - 4) := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.charmatrix_apply,
    weakDefectFin4, Matrix.submatrix_apply, Fin.succAbove, Polynomial.C_ofNat]
  ring

/-- **Weak defect spectrum (`lem:weak-naturality-spectrum`).**  The characteristic
polynomial of `H_W` is `X (X − 2)² (X − 4)`: `spec H_W = {0⁽¹⁾, 2⁽²⁾, 4⁽¹⁾}` with
multiplicities (`eq:weak-naturality-spectrum`). -/
theorem weakDefect_charpoly :
    weakDefect.charpoly = X * (X - 2) ^ 2 * (X - 4) := by
  rw [weakDefect_eq_reindex, Matrix.charpoly_reindex, weakDefectFin4_charpoly]

/-- The dual-space (transposed) version of `H_W` is the same matrix. -/
theorem weakDefect_transpose : weakDefectᵀ = weakDefect := by
  ext p q
  rw [Matrix.transpose_apply, weakDefect_apply, weakDefect_apply]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [weakDefectFin4, finProdFinEquiv]

/-- Transposition onto the dual space preserves the spectral calculation. -/
theorem weakDefect_transpose_charpoly :
    (weakDefectᵀ).charpoly = X * (X - 2) ^ 2 * (X - 4) := by
  rw [Matrix.charpoly_transpose, weakDefect_charpoly]

/-- `H_W` is Hermitian. -/
theorem weakDefect_isHermitian : weakDefect.IsHermitian := by
  ext p q
  rw [Matrix.conjTranspose_apply, weakDefect_apply, weakDefect_apply]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [weakDefectFin4, finProdFinEquiv]

theorem weakDefect_mulVec_apply (x : Fin 2 × Fin 2 → ℂ) :
    weakDefect *ᵥ x = fun p =>
      if p = (0, 0) then 2 * x (0, 0)
      else if p = (1, 1) then 2 * x (1, 1)
      else 2 * x (0, 1) + 2 * x (1, 0) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      weakDefect_apply, weakDefectFin4, finProdFinEquiv]

/-- **Kernel clause of `lem:weak-naturality-spectrum`.**  The zero eigenspace of `H_W`
is the alternating weak covector line `ℂ (w₁ ⊗ w₂ − w₂ ⊗ w₁)`. -/
theorem weakDefect_mulVec_eq_zero_iff (x : Fin 2 × Fin 2 → ℂ) :
    weakDefect *ᵥ x = 0 ↔ ∃ c : ℂ, x = c • weakAlternating := by
  rw [weakDefect_mulVec_apply]
  constructor
  · intro h
    have h00 := congrFun h (0, 0)
    have h11 := congrFun h (1, 1)
    have h01 := congrFun h (0, 1)
    simp at h00 h11 h01
    have h10 : x (1, 0) = -x (0, 1) := by linear_combination h01 / 2
    refine ⟨x (0, 1), ?_⟩
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [weakAlternating, h00, h11, h10]
  · rintro ⟨c, rfl⟩
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [weakAlternating]

/-- The alternating covector is annihilated by both ladders. -/
theorem weakLPlus_mulVec_alternating : weakLPlus *ᵥ weakAlternating = 0 := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [weakLPlus, weakF12, weakAlternating, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem weakLMinus_mulVec_alternating : weakLMinus *ᵥ weakAlternating = 0 := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [weakLMinus, weakF21, weakAlternating, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

end RenewalGeometry
