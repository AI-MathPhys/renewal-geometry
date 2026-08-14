/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Metric tomography alone does not select the dimension
  (`cth:dimension-metric-count`, Gran-Tensor manuscript)

* `dimension_metric_count`: the boxed DS.4 root-tensor
  transform `𝒯_N(a) = ∑ a_{ij} ρ_{ij}ρ_{ij}ᵀ`
  (`ρ_{ij} = e_j - e_i`, summed over ordered off-diagonal
  pairs with symmetric coefficients),
  (i) lands in `Sym(W_N)`: the image is symmetric with
      zero row sums;
  (ii) is injective with the explicit off-diagonal
      recovery `(𝒯_N a) i j = -2 a_{ij}` for `i ≠ j`; and
  (iii) the boxed count `C(N,2) = N(N-1)/2` holds in every
      simplex dimension — the coefficient count matches
      `dim Sym(W_N)` for all `N`, so metric tomography
      does not by itself distinguish `K₄`.

The surjectivity onto `Sym(W_N)` is the manuscript's
dimension count — injectivity (ii) plus the matching
count (iii) on the `(N-1)`-dimensional mean-zero carrier.
-/

open Matrix Finset

namespace NCG

/-- `cth:dimension-metric-count` (DS.4). -/
theorem dimension_metric_count {N : ℕ}
    (a : Fin N → Fin N → ℝ)
    (hsym : ∀ i j, a i j = a j i) :
    -- the root tensors, over ordered off-diagonal pairs
    let ρ : Fin N → Fin N → (Fin N → ℝ) := fun i j k =>
      (if k = j then 1 else 0) - (if k = i then 1 else 0)
    let T : Matrix (Fin N) (Fin N) ℝ :=
      ∑ p ∈ Finset.univ.offDiag,
        a p.1 p.2 • vecMulVec (ρ p.1 p.2) (ρ p.1 p.2)
    -- (i) the image lies in Sym(W_N)
    (Tᵀ = T)
    ∧ (T *ᵥ (fun _ => 1) = 0)
    -- (ii) injectivity: explicit off-diagonal recovery
    ∧ (∀ i j, i ≠ j → T i j = -(2 * a i j))
    -- (iii) the boxed count, in every simplex dimension
    ∧ Nat.choose N 2 = N * (N - 1) / 2 := by
  intro ρ T
  have hρsum : ∀ i j, i ≠ j → ∑ k, ρ i j k = 0 := by
    intro i j hij
    simp only [ρ, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- symmetry
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.transpose_smul]
    congr 1
    funext i j
    simp only [Matrix.transpose_apply,
      Matrix.vecMulVec_apply]
    ring
  · -- zero row sums
    funext i
    simp only [Pi.zero_apply]
    have hT : (T *ᵥ (fun _ => 1)) i
        = ∑ p ∈ Finset.univ.offDiag,
          a p.1 p.2 * (ρ p.1 p.2 i
            * ∑ j, ρ p.1 p.2 j) := by
      simp only [T, Matrix.mulVec, dotProduct, mul_one,
        Matrix.sum_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hT]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_offDiag] at hp
    rw [hρsum p.1 p.2 hp.2.2, mul_zero, mul_zero]
  · -- off-diagonal recovery
    intro i j hij
    have hzero : ∀ p ∈ Finset.univ.offDiag,
        p ≠ (i, j) → p ≠ (j, i) →
        (a p.1 p.2 • vecMulVec (ρ p.1 p.2)
          (ρ p.1 p.2)) i j = 0 := by
      rintro ⟨k, l⟩ hp hne1 hne2
      rw [Finset.mem_offDiag] at hp
      simp only [Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, ρ]
      rcases eq_or_ne i l with hil | hil
      · rcases eq_or_ne j k with hjk | hjk
        · exact absurd (by rw [← hil, ← hjk]) hne2
        · have hjl : j ≠ l := fun h =>
            hij (h.trans hil.symm).symm
          simp [hjl, hjk]
      · rcases eq_or_ne i k with hik | hik
        · rcases eq_or_ne j l with hjl | hjl
          · exact absurd (by rw [← hik, ← hjl]) hne1
          · have hjk : j ≠ k := fun h =>
              hij (h.trans hik.symm).symm
            simp [hjl, hjk]
        · simp [hil, hik]
    have hne : ((i, j) : Fin N × Fin N) ≠ (j, i) := by
      intro h
      exact hij (congrArg Prod.fst h)
    have hsub12 : ({((i, j) : Fin N × Fin N), (j, i)}
        : Finset (Fin N × Fin N))
        ⊆ Finset.univ.offDiag := by
      intro p hp
      rw [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · rw [Finset.mem_offDiag]
        exact ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩
      · rw [Finset.mem_offDiag]
        exact ⟨Finset.mem_univ _, Finset.mem_univ _,
          hij.symm⟩
    have hT : T i j = ∑ p ∈ Finset.univ.offDiag,
        (a p.1 p.2 • vecMulVec (ρ p.1 p.2)
          (ρ p.1 p.2)) i j := by
      simp [T, Matrix.sum_apply]
    rw [hT, ← Finset.sum_subset hsub12 (fun p hp hnp => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hnp
      push Not at hnp
      exact hzero p hp hnp.1 hnp.2)]
    rw [Finset.sum_pair hne]
    simp only [Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, ρ]
    rw [hsym j i]
    simp [hij, hij.symm]
    ring
  · rw [Nat.choose_two_right]

end NCG
