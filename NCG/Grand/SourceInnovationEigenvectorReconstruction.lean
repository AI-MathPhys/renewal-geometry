/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Source-innovation rank and eigenvector reconstruction

This file completes `thm:source-innovation`: the Schur short is the Gram of
the orthogonal innovation rows, has exactly their rank, and every eigenvector
with nonzero eigenvalue reconstructs a nonzero missing source direction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The part of `S₁` orthogonal to the range of `S₀`. -/
noncomputable def sourceInnovationMap {h e₀ e₁ : ℕ}
    (S₀ : Matrix (Fin h) (Fin e₀) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ) : Matrix (Fin h) (Fin e₁) ℂ :=
  (1 - sourceRangeProjection S₀) * S₁

/-- The source Schur short is exactly the innovation Gram. -/
theorem sourceSchurResidual_eq_innovationGram {h e₀ e₁ : ℕ}
    (S₀ : Matrix (Fin h) (Fin e₀) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ) :
    sourceSchurResidual S₀ S₁ =
      (sourceInnovationMap S₀ S₁)ᴴ * sourceInnovationMap S₀ S₁ := by
  let P := sourceRangeProjection S₀
  obtain ⟨hPH, hP2, -⟩ :=
    (sourceGramPseudoinverse_projection S₀).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  rw [sourceSchurResidual_eq_orthogonalResidual]
  change S₁ᴴ * (1 - P) * S₁ =
    ((1 - P) * S₁)ᴴ * ((1 - P) * S₁)
  rw [Matrix.conjTranspose_mul, hQH]
  calc
    S₁ᴴ * (1 - P) * S₁ = S₁ᴴ * ((1 - P) * (1 - P)) * S₁ := by
      rw [hQ2]
    _ = S₁ᴴ * (1 - P) * ((1 - P) * S₁) := by
      simp only [Matrix.mul_assoc]

/-- The rank of the Schur short is the dimension of the orthogonal innovation
range. -/
theorem sourceSchurResidual_rank_eq_innovationRank {h e₀ e₁ : ℕ}
    (S₀ : Matrix (Fin h) (Fin e₀) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ) :
    (sourceSchurResidual S₀ S₁).rank =
      (sourceInnovationMap S₀ S₁).rank := by
  rw [sourceSchurResidual_eq_innovationGram]
  exact Matrix.rank_conjTranspose_mul_self _

/-- Innovation directions are orthogonal to the previous source range. -/
theorem sourceInnovationMap_orthogonal {h e₀ e₁ : ℕ}
    (S₀ : Matrix (Fin h) (Fin e₀) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ) :
    S₀ᴴ * sourceInnovationMap S₀ S₁ = 0 := by
  let P := sourceRangeProjection S₀
  obtain ⟨hPH, -, hPS₀⟩ :=
    (sourceGramPseudoinverse_projection S₀).2.2.2
  change Pᴴ = P at hPH
  change P * S₀ = S₀ at hPS₀
  have hS₀P : S₀ᴴ * P = S₀ᴴ := by
    calc
      S₀ᴴ * P = (P * S₀)ᴴ := by
        rw [Matrix.conjTranspose_mul, hPH]
      _ = S₀ᴴ := by rw [hPS₀]
  simp only [sourceInnovationMap, P, ← Matrix.mul_assoc,
    Matrix.mul_sub, Matrix.mul_one, hS₀P, sub_self, Matrix.zero_mul]

/-- A nonzero-eigenvalue spectral vector of the Schur short reconstructs an
explicit nonzero missing source direction. -/
theorem sourceInnovation_eigenvector_reconstructs_direction {h e₀ e₁ : ℕ}
    (S₀ : Matrix (Fin h) (Fin e₀) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (x : Fin e₁ → ℂ) (eigenvalue : ℂ)
    (hx : x ≠ 0) (heigenvalue : eigenvalue ≠ 0)
    (heigen : sourceSchurResidual S₀ S₁ *ᵥ x = eigenvalue • x) :
    sourceInnovationMap S₀ S₁ *ᵥ x ≠ 0 ∧
      S₀ᴴ *ᵥ (sourceInnovationMap S₀ S₁ *ᵥ x) = 0 := by
  have hgram := sourceSchurResidual_eq_innovationGram S₀ S₁
  constructor
  · intro hzero
    have hleft : sourceSchurResidual S₀ S₁ *ᵥ x = 0 := by
      rw [hgram, ← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]
    rw [heigen] at hleft
    exact (smul_ne_zero heigenvalue hx) hleft
  · rw [Matrix.mulVec_mulVec, sourceInnovationMap_orthogonal,
      Matrix.zero_mulVec]

end NCG
