/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.TwoCellSplitting

/-!
# Shared-edge cross Gram and chiral sandwich
  (`thm:shared-edge-sandwich`, SM manuscript)

The one-cell flag basis `(h, u, v)` of `H¹(K₄)` is embedded into
the two cells of `G₂` by the isometries `J_A` (cell `{0,1,2,3}`,
edges `0–5`) and `J_B = J_A ∘ σ` (cell `{0,1,4,5}`, via the cell
exchange).  The embeddings overlap only on the shared edge `01`,
whose flag row is `(0, 1/√2, 0)`, giving the boxed rank-one cross
Gram

  `C = J_A† J_B = diag(0, 1/2, 0)`

(`cross_gram`; both `J`'s are isometries, `gram_JA`/`gram_JB`).
On the doubled coefficient space with metric
`G = [[I, C], [C, I]]` (the Gram of the pair embedding), the
normalized even/odd triplets are
`P_± = (I; ±I)·[2(I ± C)]^{-1/2}` with the explicit diagonal
normalizers, and sandwiching the exchange-odd cell-local operator
`diag(M, -M)` between them in the `G`-metric gives the boxed

  `Y(M) = P₊† G diag(M,-M) P₋ = (I+C)^{1/2} M (I-C)^{-1/2}`,
  `(I+C)^{1/2} = diag(1, √(3/2), 1)`, `(I-C)^{-1/2} = diag(1, √2, 1)`

(`shared_edge_sandwich`; the `G`-metric adjoint realizes the
manuscript's "sandwiching between the normalized even and odd
triplets", disclosed).  The flag matrices are real; the Gram
identities are stated over `ℝ` and the sandwich over `ℂ` with the
same rational-plus-square-root diagonals (disclosed model choice).
-/

open Matrix

namespace NCG

/-- The normalized face-circulation flag column `h` on the cell-A
edges. -/
noncomputable def flagH : Fin 11 → ℝ :=
  ![0, 0, 0, Real.sqrt 3 / 3, -(Real.sqrt 3) / 3, Real.sqrt 3 / 3,
    0, 0, 0, 0, 0]

/-- The normalized port flag column `u = √2·q₀₁`. -/
noncomputable def flagU : Fin 11 → ℝ :=
  ![Real.sqrt 2 / 2, -(Real.sqrt 2) / 4, -(Real.sqrt 2) / 4,
    Real.sqrt 2 / 4, Real.sqrt 2 / 4, 0, 0, 0, 0, 0, 0]

/-- The third flag column `v`: the normalized component of `q₀₂`
orthogonal to `u` in `W₂`. -/
noncomputable def flagV : Fin 11 → ℝ :=
  ![0, Real.sqrt 6 / 4, -(Real.sqrt 6) / 4, -(Real.sqrt 6) / 12,
    Real.sqrt 6 / 12, Real.sqrt 6 / 6, 0, 0, 0, 0, 0]

/-- The flag embedding of cell A. -/
noncomputable def cellJA : Matrix (Fin 11) (Fin 3) ℝ :=
  Matrix.of fun e j => ![flagH, flagU, flagV] j e

/-- The flag embedding of cell B, through the cell exchange. -/
noncomputable def cellJB : Matrix (Fin 11) (Fin 3) ℝ :=
  Matrix.of fun e j => ![flagH, flagU, flagV] j (sigmaE e)

set_option linter.flexible false in
/-- `J_A` is an isometry. -/
lemma gram_JA : cellJAᴴ * cellJA = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 :=
    Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellJA, flagH, flagU, flagV, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    first
      | linear_combination h2 / 2
      | linear_combination h3 / 3
      | linear_combination h6 / 6
      | ring

set_option linter.flexible false in
/-- `J_B` is an isometry. -/
lemma gram_JB : cellJBᴴ * cellJB = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 :=
    Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellJB, flagH, flagU, flagV, sigmaE, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    first
      | linear_combination h2 / 2
      | linear_combination h3 / 3
      | linear_combination h6 / 6
      | ring

set_option linter.flexible false in
/-- `thm:shared-edge-sandwich`, boxed cross Gram: the two flag
embeddings overlap only on the shared edge, giving
`C = J_A†J_B = diag(0, 1/2, 0)`. -/
theorem cross_gram :
    cellJAᴴ * cellJB = Matrix.diagonal ![0, 1 / 2, 0] := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellJA, cellJB, flagH, flagU, flagV, sigmaE,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
  linear_combination h2 / 4

/-! ### The chiral sandwich on the doubled space -/

/-- The cross Gram as a complex diagonal. -/
noncomputable def crossC : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![0, 1 / 2, 0]

/-- The even normalizer `[2(I+C)]^{-1/2} = diag(1/√2, 1/√3, 1/√2)`. -/
noncomputable def evenN : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![(Real.sqrt 2 : ℂ) / 2, (Real.sqrt 3 : ℂ) / 3,
    (Real.sqrt 2 : ℂ) / 2]

/-- The odd normalizer `[2(I-C)]^{-1/2} = diag(1/√2, 1, 1/√2)`. -/
noncomputable def oddN : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![(Real.sqrt 2 : ℂ) / 2, 1, (Real.sqrt 2 : ℂ) / 2]

/-- `(I+C)^{1/2} = diag(1, √(3/2), 1) = diag(1, √6/2, 1)`. -/
noncomputable def sqrtIpC : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, (Real.sqrt 6 : ℂ) / 2, 1]

/-- `(I-C)^{-1/2} = diag(1, √2, 1)`. -/
noncomputable def invSqrtImC : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, (Real.sqrt 2 : ℂ), 1]

set_option linter.flexible false in
/-- The normalizers square to `[2(I±C)]^{-1}`, and the displayed
square roots square to `I±C` and `(I-C)⁻¹`. -/
lemma normalizer_squares :
    (evenN * evenN * ((2 : ℂ) • (1 + crossC)) = 1)
    ∧ (oddN * oddN * ((2 : ℂ) • (1 - crossC)) = 1)
    ∧ (sqrtIpC * sqrtIpC = 1 + crossC)
    ∧ (invSqrtImC * invSqrtImC * (1 - crossC) = 1) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 :=
    Real.mul_self_sqrt (by norm_num)
  have c2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast congrArg Complex.ofReal h2
  have c3 : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast congrArg Complex.ofReal h3
  have c6 : (Real.sqrt 6 : ℂ) * (Real.sqrt 6 : ℂ) = 6 := by
    exact_mod_cast congrArg Complex.ofReal h6
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [evenN, oddN, sqrtIpC, invSqrtImC, crossC,
          Matrix.diagonal, Matrix.one_apply, Matrix.mul_apply] <;>
        first
          | linear_combination c2 / 2
          | linear_combination c3 / 3
          | linear_combination c6 / 4
          | linear_combination c2
          | ring

set_option linter.flexible false in
/-- `thm:shared-edge-sandwich`, boxed sandwich formula: on the
doubled space with Gram metric `G = [[I,C],[C,I]]`, the `G`-metric
sandwich of the exchange-odd operator `diag(M,-M)` between the
normalized even and odd triplets is
`Y(M) = (I+C)^{1/2} M (I-C)^{-1/2}`. -/
theorem shared_edge_sandwich (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (Matrix.fromRows evenN evenN)ᴴ
        * Matrix.fromBlocks 1 crossC crossC 1
        * Matrix.fromBlocks M 0 0 (-M)
        * Matrix.fromRows oddN (-oddN)
      = sqrtIpC * M * invSqrtImC := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have c2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast congrArg Complex.ofReal h2
  have h32 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3) 2]
    norm_num
  have c32 : (Real.sqrt 3 : ℂ) * (Real.sqrt 2 : ℂ) = (Real.sqrt 6 : ℂ) := by
    exact_mod_cast congrArg Complex.ofReal h32
  have h62 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6) 2,
      show (6 * 2 : ℝ) = 2 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (by positivity) 3,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have c62 : (Real.sqrt 6 : ℂ) * (Real.sqrt 2 : ℂ)
      = 2 * (Real.sqrt 3 : ℂ) := by
    exact_mod_cast congrArg Complex.ofReal h62
  -- collapse the block products
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  -- the two column blocks are the same explicit diagonal
  have hX : evenNᴴ * (1 : Matrix (Fin 3) (Fin 3) ℂ)
      + evenNᴴ * crossC
      = Matrix.diagonal ![(Real.sqrt 2 : ℂ) / 2,
          (Real.sqrt 3 : ℂ) / 2, (Real.sqrt 2 : ℂ) / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenN, crossC, Matrix.diagonal, Matrix.mul_apply,
        Matrix.conjTranspose_apply, map_ofNat]
    ring
  have hX' : evenNᴴ * crossC
      + evenNᴴ * (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = Matrix.diagonal ![(Real.sqrt 2 : ℂ) / 2,
          (Real.sqrt 3 : ℂ) / 2, (Real.sqrt 2 : ℂ) / 2] := by
    rw [add_comm]
    exact hX
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg]
  rw [hX, hX']
  -- entrywise scalar identities between the diagonal products
  have hsc : ∀ i j : Fin 3,
      2 * (![(Real.sqrt 2 : ℂ) / 2, (Real.sqrt 3 : ℂ) / 2,
          (Real.sqrt 2 : ℂ) / 2] i)
        * (![(Real.sqrt 2 : ℂ) / 2, 1, (Real.sqrt 2 : ℂ) / 2] j)
      = (![1, (Real.sqrt 6 : ℂ) / 2, 1] i)
        * (![1, (Real.sqrt 2 : ℂ), 1] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      first
        | linear_combination c2 / 2
        | linear_combination c32 / 2
        | linear_combination (-1 / 2 : ℂ) * c62
        | ring
  simp only [oddN, sqrtIpC, invSqrtImC]
  ext i j
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_mul]
  linear_combination (M i j) * hsc i j

end NCG
