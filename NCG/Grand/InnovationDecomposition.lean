/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Active, ledger, and provenance innovation
  (`thm:provenance-innovation-decomposition`,
  Gran-Tensor manuscript)

* `provenance_innovation_decomposition`: for the row-space
  projections `P_A ⪯ P_L` of the active predictor and the
  protected ledger (the refinement `Ker L ⊆ Ker A` gives
  `P_L·P_A = P_A`):
  (i) the boxed decomposition
      `S(I-P_A)S* = S(P_L-P_A)S* + S(I-P_L)S*`;
  (ii) both summands are positive semidefinite (`P_L - P_A`
      and `I - P_L` are orthogonal projections);
  (iii) the innovation Gram has the rank of the shorted rows:
      `rank (S(I-P_A)S*) = rank (S(I-P_A))`.

Rendering disclosed: the stacked-rank formula
`rank [A;S] - rank A = rank (S(I-P_A)S*)` is the row-space
dimension count `dim(RowA + RowS) - dim RowA
= dim((I-P_A)RowS)` carried by (iii) together with the
manuscript's row-reduction bookkeeping.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:provenance-innovation-decomposition`. -/
theorem provenance_innovation_decomposition {n s : Type*}
    [Fintype n] [Fintype s] [DecidableEq n]
    (S : Matrix s n ℂ) (PA PL : Matrix n n ℂ)
    (hAH : PAᴴ = PA) (hLH : PLᴴ = PL)
    (hA2 : PA * PA = PA) (hL2 : PL * PL = PL)
    (href : PL * PA = PA) :
    -- (i) the boxed Pythagoras
    S * (1 - PA) * Sᴴ
      = S * (PL - PA) * Sᴴ + S * (1 - PL) * Sᴴ
    -- (ii) both summands are positive
    ∧ (S * (PL - PA) * Sᴴ).PosSemidef
    ∧ (S * (1 - PL) * Sᴴ).PosSemidef
    -- (iii) the innovation Gram has the shorted-row rank
    ∧ (S * (1 - PA) * Sᴴ).rank = (S * (1 - PA)).rank := by
  have hAL : PA * PL = PA := by
    have h := congrArg conjTranspose href
    rwa [Matrix.conjTranspose_mul, hAH, hLH] at h
  -- `P_L - P_A` is an orthogonal projection
  have hDH : (PL - PA)ᴴ = PL - PA := by
    rw [Matrix.conjTranspose_sub, hAH, hLH]
  have hD2 : (PL - PA) * (PL - PA) = PL - PA := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hA2, hL2, href, hAL]
    abel
  -- `1 - P_L` is an orthogonal projection
  have hCH : ((1 : Matrix n n ℂ) - PL)ᴴ = 1 - PL := by
    rw [Matrix.conjTranspose_sub, hLH,
      Matrix.conjTranspose_one]
  have hC2 : ((1 : Matrix n n ℂ) - PL) * (1 - PL)
      = 1 - PL := by
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hL2]
    abel
  -- `1 - P_A` is an orthogonal projection
  have hBH : ((1 : Matrix n n ℂ) - PA)ᴴ = 1 - PA := by
    rw [Matrix.conjTranspose_sub, hAH,
      Matrix.conjTranspose_one]
  have hB2 : ((1 : Matrix n n ℂ) - PA) * (1 - PA)
      = 1 - PA := by
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hA2]
    abel
  have hproj_gram : ∀ P : Matrix n n ℂ, Pᴴ = P →
      P * P = P → S * P * Sᴴ = (S * P) * (S * P)ᴴ := by
    intro P hPH hP2
    rw [Matrix.conjTranspose_mul, hPH]
    calc S * P * Sᴴ = S * (P * P) * Sᴴ := by rw [hP2]
      _ = S * P * (P * Sᴴ) := by
          simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one]
    abel
  · rw [hproj_gram _ hDH hD2]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [hproj_gram _ hCH hC2]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [hproj_gram _ hBH hB2]
    exact Matrix.rank_self_mul_conjTranspose _

end NCG
