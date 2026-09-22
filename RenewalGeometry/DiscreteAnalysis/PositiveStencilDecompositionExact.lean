/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive `d²`-direction stencil decomposition

Paper `predictive_spectral_geometry`, label `lem:supp-positive-decomposition`:
a symmetric matrix `A` in the stencil window `eq:supp-stencil-window`
(`|A i j| < η` off the diagonal, `A i i > (d - 1) η`) decomposes as
```
 A = Σ_i w_i e_i e_iᵀ + Σ_{i<j} [ w⁺_ij (e_i+e_j)(e_i+e_j)ᵀ + w⁻_ij (e_i-e_j)(e_i-e_j)ᵀ ]
```
with the strictly positive weights `w_i = A i i - (d-1) η`,
`w^±_ij = (η ± A i j)/2` of `eq:supp-stencil-weights`
(`RenewalGeometry.positive_stencil_decomposition`).  The index type is any
finite linearly ordered type (`Fin d` in the paper); the matrix identity itself
needs only symmetry (`RenewalGeometry.stencilDecomposition_eq`).
-/

open Matrix Finset

namespace RenewalGeometry

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The coordinate direction `e_i`. -/
def stencilUnit (i : ι) : ι → ℝ := Pi.single i 1

/-- The diagonal weight `w_i = A_ii - (d-1) η` of `eq:supp-stencil-weights`. -/
def stencilDiagonalWeight (A : Matrix ι ι ℝ) (η : ℝ) (i : ι) : ℝ :=
  A i i - ((Fintype.card ι : ℝ) - 1) * η

/-- The weight `w⁺_ij = (η + A_ij)/2` of `eq:supp-stencil-weights`. -/
noncomputable def stencilPlusWeight (A : Matrix ι ι ℝ) (η : ℝ) (i j : ι) : ℝ := (η + A i j) / 2

/-- The weight `w⁻_ij = (η - A_ij)/2` of `eq:supp-stencil-weights`. -/
noncomputable def stencilMinusWeight (A : Matrix ι ι ℝ) (η : ℝ) (i j : ι) : ℝ := (η - A i j) / 2

/-- The `(i, j)` pair term of `eq:supp-positive-decomposition`, nonzero only
for `i < j`. -/
noncomputable def stencilPairTerm (A : Matrix ι ι ℝ) (η : ℝ) (i j : ι) : Matrix ι ι ℝ :=
  if i < j then
    stencilPlusWeight A η i j • vecMulVec (stencilUnit i + stencilUnit j)
        (stencilUnit i + stencilUnit j)
      + stencilMinusWeight A η i j • vecMulVec (stencilUnit i - stencilUnit j)
        (stencilUnit i - stencilUnit j)
  else 0

/-- The right-hand side of `eq:supp-positive-decomposition`. -/
noncomputable def stencilDecomposition (A : Matrix ι ι ℝ) (η : ℝ) : Matrix ι ι ℝ :=
  ∑ i, stencilDiagonalWeight A η i • vecMulVec (stencilUnit i) (stencilUnit i)
    + ∑ i, ∑ j, stencilPairTerm A η i j

omit [Fintype ι] in
theorem stencilUnit_apply (i k : ι) : stencilUnit i k = if k = i then 1 else 0 := by
  simp [stencilUnit, Pi.single_apply]

theorem stencilPairTerm_apply (A : Matrix ι ι ℝ) (η : ℝ) (i j k l : ι) :
    stencilPairTerm A η i j k l =
      if i < j then
        stencilPlusWeight A η i j * ((if k = i then 1 else 0) + (if k = j then 1 else 0))
          * ((if l = i then 1 else 0) + (if l = j then 1 else 0))
        + stencilMinusWeight A η i j * ((if k = i then 1 else 0) - (if k = j then 1 else 0))
          * ((if l = i then 1 else 0) - (if l = j then 1 else 0))
      else 0 := by
  unfold stencilPairTerm
  by_cases h : i < j
  · simp only [if_pos h, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply,
      Pi.sub_apply, stencilUnit_apply, smul_eq_mul]
    ring
  · simp only [if_neg h, Matrix.zero_apply]

/-- Entrywise form of the pair sum on the diagonal. -/
theorem stencilPairTerm_apply_diag (A : Matrix ι ι ℝ) (η : ℝ) (i j k : ι) :
    stencilPairTerm A η i j k k =
      (if k = i then (if i < j then η else 0) else 0)
        + (if k = j then (if i < j then η else 0) else 0) := by
  rw [stencilPairTerm_apply]
  unfold stencilPlusWeight stencilMinusWeight
  split_ifs <;> subst_vars <;>
    first | (exact absurd ‹_ < _› (lt_irrefl _)) | ring1 | simp_all

/-- Entrywise form of the pair sum off the diagonal (uses `k ≠ l`). -/
theorem stencilPairTerm_apply_offDiag (A : Matrix ι ι ℝ) (η : ℝ) (i j k l : ι)
    (hkl : k ≠ l) :
    stencilPairTerm A η i j k l =
      (if k = i then (if l = j then (if i < j then A i j else 0) else 0) else 0)
        + (if l = i then (if k = j then (if i < j then A i j else 0) else 0) else 0) := by
  rw [stencilPairTerm_apply]
  unfold stencilPlusWeight stencilMinusWeight
  split_ifs <;> subst_vars <;>
    first | (exact absurd rfl hkl) | (exact absurd ‹_ < _› (lt_irrefl _)) | ring1 | simp_all

/-- Counting the directions through `k`: `#{j : k < j} + #{i : i < k} = d - 1`,
in real-valued indicator form. -/
theorem sum_lt_indicator_add (k : ι) (η : ℝ) :
    (∑ j, if k < j then η else 0) + (∑ i, if i < k then η else 0)
      = ((Fintype.card ι : ℝ) - 1) * η := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i, ((if k < i then η else 0) + (if i < k then η else 0))
      = η - (if i = k then η else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp
  ring

/-- **`eq:supp-positive-decomposition` (identity).** For a symmetric `A`, the
weighted stencil sum reproduces `A`; no window hypothesis is needed for the
identity itself. -/
theorem stencilDecomposition_eq (A : Matrix ι ι ℝ) (η : ℝ) (hA : A.IsSymm) :
    stencilDecomposition A η = A := by
  ext k l
  unfold stencilDecomposition
  rw [Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply]
  have hdiag : ∑ i, (stencilDiagonalWeight A η i • vecMulVec (stencilUnit i) (stencilUnit i)) k l
      = if k = l then stencilDiagonalWeight A η k else 0 := by
    simp only [Matrix.smul_apply, vecMulVec_apply, stencilUnit_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      simp [Finset.sum_ite_eq']
    · rw [if_neg hkl]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hk : k = i
      · subst hk
        simp [Ne.symm hkl]
      · simp [hk]
  rw [hdiag]
  by_cases hkl : k = l
  · subst hkl
    simp_rw [stencilPairTerm_apply_diag]
    rw [if_pos rfl]
    simp_rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq]
    rw [sum_lt_indicator_add]
    unfold stencilDiagonalWeight
    ring
  · rw [if_neg hkl, zero_add]
    simp_rw [stencilPairTerm_apply_offDiag A η _ _ k l hkl]
    simp_rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq]
    rcases lt_or_gt_of_ne hkl with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le, hA.apply k l]

/-- Diagonal weights are positive in the stencil window. -/
theorem stencilDiagonalWeight_pos (A : Matrix ι ι ℝ) (η : ℝ)
    (hdiag : ∀ i, ((Fintype.card ι : ℝ) - 1) * η < A i i) (i : ι) :
    0 < stencilDiagonalWeight A η i := by
  unfold stencilDiagonalWeight
  linarith [hdiag i]

/-- Off-diagonal `+` weights are positive in the stencil window. -/
theorem stencilPlusWeight_pos (A : Matrix ι ι ℝ) (η : ℝ)
    (hoff : ∀ i j, i ≠ j → |A i j| < η) (i j : ι) (hij : i ≠ j) :
    0 < stencilPlusWeight A η i j := by
  unfold stencilPlusWeight
  have := (abs_lt.mp (hoff i j hij)).1
  linarith

/-- Off-diagonal `−` weights are positive in the stencil window. -/
theorem stencilMinusWeight_pos (A : Matrix ι ι ℝ) (η : ℝ)
    (hoff : ∀ i j, i ≠ j → |A i j| < η) (i j : ι) (hij : i ≠ j) :
    0 < stencilMinusWeight A η i j := by
  unfold stencilMinusWeight
  have := (abs_lt.mp (hoff i j hij)).2
  linarith

/-- **Lemma `lem:supp-positive-decomposition`.** In the stencil window
`eq:supp-stencil-window` every weight of `eq:supp-stencil-weights` is strictly
positive and `A` equals the weighted `d²`-direction sum
`eq:supp-positive-decomposition`. -/
theorem positive_stencil_decomposition (A : Matrix ι ι ℝ) (η : ℝ) (hA : A.IsSymm)
    (hη : 0 < η) (hoff : ∀ i j, i ≠ j → |A i j| < η)
    (hdiag : ∀ i, ((Fintype.card ι : ℝ) - 1) * η < A i i) :
    (∀ i, 0 < stencilDiagonalWeight A η i) ∧
      (∀ i j, i ≠ j → 0 < stencilPlusWeight A η i j) ∧
      (∀ i j, i ≠ j → 0 < stencilMinusWeight A η i j) ∧
      A = ∑ i, stencilDiagonalWeight A η i • vecMulVec (stencilUnit i) (stencilUnit i)
        + ∑ i, ∑ j, stencilPairTerm A η i j := by
  refine ⟨stencilDiagonalWeight_pos A η hdiag, stencilPlusWeight_pos A η hoff,
    stencilMinusWeight_pos A η hoff, ?_⟩
  have _ := hη
  exact (stencilDecomposition_eq A η hA).symm

end RenewalGeometry
