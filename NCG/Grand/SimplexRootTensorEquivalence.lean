/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionMetricCount

/-!
# Explicit simplex root-tensor equivalence

This supplies the constructive surjectivity missing from the original metric
count: a symmetric zero-row-sum matrix is recovered by assigning half its
negative off-diagonal entries to the ordered root tensors.  Thus no appeal to
an unstated dimension count is needed.
-/

open Matrix Finset

namespace NCG

/-- The simplex root `e_j-e_i`. -/
def simplexRoot {N : ℕ} (i j : Fin N) : Fin N → ℝ := fun k =>
  (if k = j then 1 else 0) - (if k = i then 1 else 0)

/-- Ordered-pair normalization of the root-tensor transform. -/
def simplexRootTensorTransform {N : ℕ} (a : Fin N → Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ∑ p ∈ Finset.univ.offDiag,
    a p.1 p.2 • vecMulVec (simplexRoot p.1 p.2) (simplexRoot p.1 p.2)

/-- Symmetric edge weights, represented on ordered pairs with a zero diagonal. -/
@[ext] structure SimplexEdgeWeights (N : ℕ) where
  weight : Fin N → Fin N → ℝ
  symmetric : ∀ i j, weight i j = weight j i
  diagonal_zero : ∀ i, weight i i = 0

/-- Symmetric ambient matrices whose constant direction is null; these are the
ambient representatives of `Sym(W_N)`. -/
@[ext] structure MeanZeroSymmetricMatrix (N : ℕ) where
  matrix : Matrix (Fin N) (Fin N) ℝ
  symmetric : matrixᵀ = matrix
  zero_row_sum : matrix *ᵥ (fun _ => 1) = 0

/-- Root tensors send symmetric edge weights into `Sym(W_N)`. -/
def edgeWeightsToMeanZeroMatrix {N : ℕ} (a : SimplexEdgeWeights N) :
    MeanZeroSymmetricMatrix N where
  matrix := simplexRootTensorTransform a.weight
  symmetric := by
    unfold simplexRootTensorTransform simplexRoot
    exact (dimension_metric_count a.weight a.symmetric).1
  zero_row_sum := by
    unfold simplexRootTensorTransform simplexRoot
    exact (dimension_metric_count a.weight a.symmetric).2.1

/-- Explicit inverse coefficient formula: minus one half of every
off-diagonal matrix entry. -/
noncomputable def meanZeroMatrixToEdgeWeights {N : ℕ} (M : MeanZeroSymmetricMatrix N) :
    SimplexEdgeWeights N where
  weight := fun i j => if i = j then 0 else -(M.matrix i j) / 2
  symmetric := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, if_false]
      have hentry := congr_fun (congr_fun M.symmetric j) i
      simpa only [Matrix.transpose_apply] using congrArg (fun x : ℝ => -x / 2) hentry
  diagonal_zero := by simp

/-- Off-diagonal entries of the reconstructed transform agree with the target
matrix. -/
theorem reconstructedRootTensor_offDiagonal {N : ℕ}
    (M : MeanZeroSymmetricMatrix N) {i j : Fin N} (hij : i ≠ j) :
    simplexRootTensorTransform (meanZeroMatrixToEdgeWeights M).weight i j =
      M.matrix i j := by
  have hsym := (meanZeroMatrixToEdgeWeights M).symmetric
  have hrecover :=
    (dimension_metric_count (meanZeroMatrixToEdgeWeights M).weight hsym).2.2.1
  rw [show simplexRootTensorTransform (meanZeroMatrixToEdgeWeights M).weight i j =
      -(2 * (meanZeroMatrixToEdgeWeights M).weight i j) by
    unfold simplexRootTensorTransform simplexRoot
    exact hrecover i j hij]
  simp only [meanZeroMatrixToEdgeWeights, hij, if_false]
  ring

/-- Constructive surjectivity onto symmetric zero-row-sum matrices. -/
theorem edgeWeightsToMeanZeroMatrix_rightInverse {N : ℕ}
    (M : MeanZeroSymmetricMatrix N) :
    edgeWeightsToMeanZeroMatrix (meanZeroMatrixToEdgeWeights M) = M := by
  apply MeanZeroSymmetricMatrix.ext
  ext i j
  by_cases hij : i ≠ j
  · exact reconstructedRootTensor_offDiagonal M hij
  · have hij' : i = j := not_ne_iff.mp hij
    subst j
    let T := simplexRootTensorTransform (meanZeroMatrixToEdgeWeights M).weight
    have hTzero : T *ᵥ (fun _ => 1) = 0 :=
      (edgeWeightsToMeanZeroMatrix (meanZeroMatrixToEdgeWeights M)).zero_row_sum
    have hrowT : ∑ k, T i k = 0 := by
      have h := congrFun hTzero i
      simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using h
    have hrowM : ∑ k, M.matrix i k = 0 := by
      have h := congrFun M.zero_row_sum i
      simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using h
    have hrest : ∑ k ∈ Finset.univ.erase i, T i k =
        ∑ k ∈ Finset.univ.erase i, M.matrix i k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      exact reconstructedRootTensor_offDiagonal M hki.symm
    have hsplitT := Finset.sum_erase_add Finset.univ (fun k => T i k)
      (Finset.mem_univ i)
    have hsplitM := Finset.sum_erase_add Finset.univ (fun k => M.matrix i k)
      (Finset.mem_univ i)
    change T i i = M.matrix i i
    linarith

/-- Explicit injectivity on the symmetric zero-diagonal coefficient space. -/
theorem meanZeroMatrixToEdgeWeights_leftInverse {N : ℕ}
    (a : SimplexEdgeWeights N) :
    meanZeroMatrixToEdgeWeights (edgeWeightsToMeanZeroMatrix a) = a := by
  apply SimplexEdgeWeights.ext
  funext i j
  by_cases hij : i = j
  · subst j
    simp [meanZeroMatrixToEdgeWeights, a.diagonal_zero]
  · have hrecover := (dimension_metric_count a.weight a.symmetric).2.2.1 i j hij
    simp only [meanZeroMatrixToEdgeWeights, hij, if_false,
      edgeWeightsToMeanZeroMatrix]
    rw [show simplexRootTensorTransform a.weight i j = -(2 * a.weight i j) by
      unfold simplexRootTensorTransform simplexRoot
      exact hrecover]
    ring

/-- The root-tensor map is an explicit equivalence, not merely an injective map
with a matching informal dimension count. -/
noncomputable def simplexRootTensorEquiv (N : ℕ) :
    SimplexEdgeWeights N ≃ MeanZeroSymmetricMatrix N where
  toFun := edgeWeightsToMeanZeroMatrix
  invFun := meanZeroMatrixToEdgeWeights
  left_inv := meanZeroMatrixToEdgeWeights_leftInverse
  right_inv := edgeWeightsToMeanZeroMatrix_rightInverse

/-- Exact DS.4 bundle: explicit equivalence plus the coefficient count valid in
every simplex dimension. -/
theorem dimension_metric_tomography_explicit (N : ℕ) :
    Nonempty (SimplexEdgeWeights N ≃ MeanZeroSymmetricMatrix N)
      ∧ Nat.choose N 2 = N * (N - 1) / 2 := by
  refine ⟨⟨simplexRootTensorEquiv N⟩, ?_⟩
  rw [Nat.choose_two_right]

end NCG
