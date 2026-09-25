/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Lossless elimination of a regular column block
(abstract matrix content of `cor:supp-exact-transverse-elimination`,
`eq:supp-exact-rank-split`, `eq:supp-exact-Gram-split`; emergent-spacetime manuscript)

For a partitioned source `F = [A G]` (`Matrix.fromCols A G`) with `Aᵀ A` invertible,
put `C = (Aᵀ A)⁻¹ Aᵀ G` (`elimCoeff`) and `Ḡ = G − A C` (`residualCols`).

* `fromCols_mul_blockUnit`: the unimodular triangular column operation
  `[A G] · [[I, −C], [0, I]] = [A Ḡ]` (`blockUnit`, determinant `1`);
* `transpose_mul_residualCols`: `Aᵀ Ḡ = 0` (orthogonal column ranges);
* `rank_fromCols_of_transpose_mul_eq_zero`: `rank [A B] = rank A + rank B` whenever
  `Aᵀ B = 0` (column spaces are orthogonal, hence in direct sum);
* `rank_fromCols_eq_add_rank_residualCols` (**`eq:supp-exact-rank-split`**, abstract form):
  `rank [A G] = rank A + rank Ḡ`;
* `blockUnit_congruence` (**`eq:supp-exact-Gram-split`**, abstract form): for a symmetric
  `K` with `K A = A/2`,
  `Uᵀ ([A G]ᵀ K [A G]) U = diag(½ Aᵀ A, Ḡᵀ K Ḡ)` with `U = [[I, −C], [0, I]]`.

The paper's corollary is the instance `A = A_h` (transverse source), `G = G_h`,
`K = K₀⁻¹`, with `rank A_h = 2(V − 1)` and `K₀⁻¹ A_h = A_h/2` supplied by
`thm:supp-exact-transverse`; these two facts enter here only as hypotheses
(`rank_fromCols_eq_of_rank_left`, `blockUnit_congruence`).
-/

open Matrix

noncomputable section

namespace RenewalGeometry.LosslessColumnElimination

variable {n a g : Type*} [Fintype n] [Fintype a] [Fintype g] [DecidableEq a] [DecidableEq g]

/-- The elimination coefficient `C = (Aᵀ A)⁻¹ Aᵀ G`. -/
def elimCoeff (A : Matrix n a ℝ) (G : Matrix n g ℝ) : Matrix a g ℝ := (Aᵀ * A)⁻¹ * (Aᵀ * G)

/-- The residual columns `Ḡ = G − A C = (I − Π_A) G`. -/
def residualCols (A : Matrix n a ℝ) (G : Matrix n g ℝ) : Matrix n g ℝ := G - A * elimCoeff A G

/-- The unimodular column operation `U = [[I, −C], [0, I]]`. -/
def blockUnit (C : Matrix a g ℝ) : Matrix (a ⊕ g) (a ⊕ g) ℝ := fromBlocks 1 (-C) 0 1

theorem det_blockUnit (C : Matrix a g ℝ) : (blockUnit C).det = 1 := by
  unfold blockUnit
  rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]

theorem isUnit_det_blockUnit (C : Matrix a g ℝ) : IsUnit (blockUnit C).det := by
  rw [det_blockUnit]; exact isUnit_one

/-- The column operation produces `[A Ḡ]` from `[A G]`. -/
theorem fromCols_mul_blockUnit (A : Matrix n a ℝ) (G : Matrix n g ℝ) :
    fromCols A G * blockUnit (elimCoeff A G) = fromCols A (residualCols A G) := by
  unfold blockUnit residualCols
  rw [fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_neg,
    Matrix.mul_one, neg_add_eq_sub]

/-- `Aᵀ Ḡ = 0`: the residual columns are orthogonal to the range of `A`. -/
theorem transpose_mul_residualCols (A : Matrix n a ℝ) (G : Matrix n g ℝ)
    (hA : IsUnit (Aᵀ * A).det) : Aᵀ * residualCols A G = 0 := by
  unfold residualCols elimCoeff
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hA,
    Matrix.one_mul, sub_self]

/-! ### Rank additivity for orthogonal column ranges -/

/-- The column space of `[A B]` is the sum of the column spaces. -/
theorem range_fromCols_mulVecLin {b : Type*} [Fintype b] (A : Matrix n a ℝ) (B : Matrix n b ℝ) :
    LinearMap.range (fromCols A B).mulVecLin
      = LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    rw [mulVecLin_apply, fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨v ∘ Sum.inl, rfl⟩ ⟨v ∘ Sum.inr, rfl⟩
  · intro hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨y, ⟨u, rfl⟩, z, ⟨w, rfl⟩, rfl⟩ := hx
    refine ⟨Sum.elim u w, ?_⟩
    rw [mulVecLin_apply, fromCols_mulVec_sumElim]
    rfl

/-- Orthogonal column ranges intersect trivially. -/
theorem range_inf_eq_bot_of_transpose_mul_eq_zero {b : Type*} [Fintype b] (A : Matrix n a ℝ)
    (B : Matrix n b ℝ) (hAB : Aᵀ * B = 0) :
    LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
  rw [mulVecLin_apply] at hu hw
  have hx : x ⬝ᵥ x = 0 := by
    have hBA : Bᵀ * A = 0 := by
      have := congrArg transpose hAB
      rwa [transpose_mul, transpose_transpose, transpose_zero] at this
    have h : (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hBA, zero_mulVec,
        zero_dotProduct]
    rw [hu, hw] at h
    exact h
  rw [Submodule.mem_bot]
  exact dotProduct_self_eq_zero.mp hx

/-- `rank [A B] = rank A + rank B` when `Aᵀ B = 0`. -/
theorem rank_fromCols_of_transpose_mul_eq_zero {b : Type*} [Fintype b] (A : Matrix n a ℝ)
    (B : Matrix n b ℝ) (hAB : Aᵀ * B = 0) :
    (fromCols A B).rank = A.rank + B.rank := by
  unfold Matrix.rank
  rw [range_fromCols_mulVecLin]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin)
    (LinearMap.range B.mulVecLin)
  rw [range_inf_eq_bot_of_transpose_mul_eq_zero A B hAB, finrank_bot, add_zero] at h
  exact h

/-- **`eq:supp-exact-rank-split`**, abstract form: `rank [A G] = rank A + rank Ḡ`. -/
theorem rank_fromCols_eq_add_rank_residualCols (A : Matrix n a ℝ) (G : Matrix n g ℝ)
    (hA : IsUnit (Aᵀ * A).det) :
    (fromCols A G).rank = A.rank + (residualCols A G).rank := by
  rw [← rank_mul_eq_left_of_isUnit_det (blockUnit (elimCoeff A G)) (fromCols A G)
    (isUnit_det_blockUnit _), fromCols_mul_blockUnit]
  exact rank_fromCols_of_transpose_mul_eq_zero A _ (transpose_mul_residualCols A G hA)

/-- `eq:supp-exact-rank-split` with the transverse rank `rank A = 2(V − 1)` supplied as a
hypothesis (the conclusion of `thm:supp-exact-transverse`). -/
theorem rank_fromCols_eq_of_rank_left (A : Matrix n a ℝ) (G : Matrix n g ℝ)
    (hA : IsUnit (Aᵀ * A).det) (V : ℕ) (hrank : A.rank = 2 * (V - 1)) :
    (fromCols A G).rank = 2 * (V - 1) + (residualCols A G).rank := by
  rw [rank_fromCols_eq_add_rank_residualCols A G hA, hrank]

/-! ### The signed Gram congruence -/

/-- `[A Ḡ]ᵀ K [A Ḡ]` in block form. -/
theorem transpose_mul_mul_fromCols (A : Matrix n a ℝ) (B : Matrix n g ℝ) (K : Matrix n n ℝ) :
    (fromCols A B)ᵀ * K * fromCols A B
      = fromBlocks (Aᵀ * K * A) (Aᵀ * K * B) (Bᵀ * K * A) (Bᵀ * K * B) := by
  rw [transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]

/-- **`eq:supp-exact-Gram-split`**, abstract form: for symmetric `K` with `K A = A/2`,
the column operation `U` is a congruence
`Uᵀ ([A G]ᵀ K [A G]) U = diag(½ Aᵀ A, Ḡᵀ K Ḡ)`. -/
theorem blockUnit_congruence (A : Matrix n a ℝ) (G : Matrix n g ℝ) (K : Matrix n n ℝ)
    (hA : IsUnit (Aᵀ * A).det) (hKt : Kᵀ = K) (hKA : K * A = (1 / 2 : ℝ) • A) :
    (blockUnit (elimCoeff A G))ᵀ * ((fromCols A G)ᵀ * K * fromCols A G)
        * blockUnit (elimCoeff A G)
      = fromBlocks ((1 / 2 : ℝ) • (Aᵀ * A)) 0 0
          ((residualCols A G)ᵀ * K * residualCols A G) := by
  have hU : (blockUnit (elimCoeff A G))ᵀ * ((fromCols A G)ᵀ * K * fromCols A G)
      * blockUnit (elimCoeff A G)
      = (fromCols A G * blockUnit (elimCoeff A G))ᵀ * K
          * (fromCols A G * blockUnit (elimCoeff A G)) := by
    rw [transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hU, fromCols_mul_blockUnit, transpose_mul_mul_fromCols]
  have hAG := transpose_mul_residualCols A G hA
  have h11 : Aᵀ * K * A = (1 / 2 : ℝ) • (Aᵀ * A) := by
    rw [Matrix.mul_assoc, hKA, Matrix.mul_smul]
  have h12 : Aᵀ * K * residualCols A G = 0 := by
    rw [← hKt, ← transpose_mul, hKA, transpose_smul, Matrix.smul_mul, hAG, smul_zero]
  have h21 : (residualCols A G)ᵀ * K * A = 0 := by
    have := congrArg transpose h12
    rw [transpose_mul, transpose_mul, transpose_transpose, hKt, transpose_zero] at this
    rw [Matrix.mul_assoc]
    exact this
  rw [h11, h12, h21]

end RenewalGeometry.LosslessColumnElimination

end
