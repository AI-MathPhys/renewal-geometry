/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProvenanceInnovationRank
import NCG.Grand.SameHistoryProvenancePythagoras
import NCG.Upstream.PrimitiveWeight
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Exact source Schur residual

This file proves the singular, finite-dimensional source Schur theorem from
the Gran-Tensor manuscript.  The Moore--Penrose inverse of the source Gram
matrix is constructed by Hermitian functional calculus, so no invertibility
or faithful-source hypothesis is imposed.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

private noncomputable def sourceSpectralPseudoinverse (x : ℝ) : ℝ :=
  if x = 0 then 0 else x⁻¹

private noncomputable def sourceSpectralSupport (x : ℝ) : ℝ :=
  if x = 0 then 0 else 1

/-- The Moore--Penrose inverse of the Gram matrix `Sᴴ * S`, constructed by
spectral functional calculus. -/
noncomputable def sourceGramPseudoinverse {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  (Matrix.posSemidef_conjTranspose_mul_self S).isHermitian.cfc
    sourceSpectralPseudoinverse

/-- The orthogonal projection onto the range of a finite source map. -/
noncomputable def sourceRangeProjection {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin h) (Fin h) ℂ :=
  S * sourceGramPseudoinverse S * Sᴴ

/-- Finite-dimensional range inclusion, expressed by factorization through
the first source map. -/
def SourceRangeIncluded {h e₁ e₂ : ℕ}
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ)
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ) : Prop :=
  ∃ T : Matrix (Fin e₁) (Fin e₂) ℂ, S₂ = S₁ * T

/-- The exact source Schur residual `D - Bᴴ A† B`. -/
noncomputable def sourceSchurResidual {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) : Matrix (Fin e₂) (Fin e₂) ℂ :=
  S₂ᴴ * S₂ - (S₁ᴴ * S₂)ᴴ * sourceGramPseudoinverse S₁ * (S₁ᴴ * S₂)

set_option maxHeartbeats 800000 in
-- The spectral functional-calculus normalization needs a larger elaboration budget.
/-- The spectral Gram inverse satisfies the Penrose equations, and its source
formula is the orthogonal range projection. -/
theorem sourceGramPseudoinverse_projection {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) :
    let X := Sᴴ * S
    let J := sourceGramPseudoinverse S
    let P := sourceRangeProjection S
    Jᴴ = J ∧ X * J * X = X ∧ J * X * J = J ∧
      Pᴴ = P ∧ P * P = P ∧ P * S = S := by
  let X : Matrix (Fin e) (Fin e) ℂ := Sᴴ * S
  have hX : X.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S
  let hXH : X.IsHermitian := hX.isHermitian
  let J : Matrix (Fin e) (Fin e) ℂ := hXH.cfc sourceSpectralPseudoinverse
  let p : Matrix (Fin e) (Fin e) ℂ := hXH.cfc sourceSpectralSupport
  have hJH : Jᴴ = J :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH sourceSpectralPseudoinverse
  have hXJ : X * J = p := by
    calc
      X * J = hXH.cfc id * hXH.cfc sourceSpectralPseudoinverse := by
        rw [Upstream.PrimitiveWeight.cfc_id' hXH]
      _ = hXH.cfc (fun x => x * sourceSpectralPseudoinverse x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceSpectralSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [sourceSpectralPseudoinverse, sourceSpectralSupport, hz]
      _ = p := rfl
  have hpH : pᴴ = p :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH sourceSpectralSupport
  have hJX : J * X = p := by
    have ht := congrArg conjTranspose hXJ
    rw [Matrix.conjTranspose_mul, hJH, hXH] at ht
    rw [hpH] at ht
    exact ht
  have hp2 : p * p = p := by
    calc
      p * p = hXH.cfc
          (fun x => sourceSpectralSupport x * sourceSpectralSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceSpectralSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        simp [sourceSpectralSupport]
      _ = p := rfl
  have hXp : X * p = X := by
    calc
      X * p = hXH.cfc id * hXH.cfc sourceSpectralSupport := by
        rw [Upstream.PrimitiveWeight.cfc_id' hXH]
      _ = hXH.cfc (fun x => x * sourceSpectralSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [sourceSpectralSupport, hz]
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hpX : p * X = X := by
    have ht := congrArg conjTranspose hXp
    rw [Matrix.conjTranspose_mul, hpH, hXH] at ht
    exact ht
  have hSp : S * p = S := by
    let Y : Matrix (Fin h) (Fin e) ℂ := S * (1 - p)
    have hY2 : Yᴴ * Y = 0 := by
      calc
        Yᴴ * Y = (1 - p) * X * (1 - p) := by
          dsimp only [Y, X]
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_one, hpH]
          simp only [Matrix.mul_assoc]
        _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, hpX, Matrix.mul_sub,
            Matrix.mul_one]
          simp
    have hY : Y = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hY2
    dsimp only [Y] at hY
    rw [Matrix.mul_sub, Matrix.mul_one] at hY
    exact (sub_eq_zero.mp hY).symm
  have hXJX : X * J * X = X := by rw [hXJ, hpX]
  have hJXJ : J * X * J = J := by
    calc
      J * X * J = hXH.cfc
          (fun x => sourceSpectralSupport x * sourceSpectralPseudoinverse x) := by
        rw [hJX]
        exact Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceSpectralPseudoinverse := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [sourceSpectralPseudoinverse, sourceSpectralSupport, hz]
      _ = J := rfl
  have hSJX : S * J * X = S := by
    rw [Matrix.mul_assoc, hJX, hSp]
  have hproj := gram_pinv_range_projection S J hJH hXJX hJXJ hSJX
  change Jᴴ = J ∧ X * J * X = X ∧ J * X * J = J ∧
    (S * J * Sᴴ)ᴴ = S * J * Sᴴ ∧
    (S * J * Sᴴ) * (S * J * Sᴴ) = S * J * Sᴴ ∧
    (S * J * Sᴴ) * S = S
  exact ⟨hJH, hXJX, hJXJ, hproj.1, hproj.2.1, hproj.2.2⟩

/-- The Schur expression equals the Gram matrix of the orthogonal residual. -/
theorem sourceSchurResidual_eq_orthogonalResidual {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    sourceSchurResidual S₁ S₂ =
      S₂ᴴ * (1 - sourceRangeProjection S₁) * S₂ := by
  simp only [sourceSchurResidual, sourceRangeProjection,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul]

/-- The exact source Schur residual is positive semidefinite. -/
theorem sourceSchurResidual_posSemidef {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    (sourceSchurResidual S₁ S₂).PosSemidef := by
  let P := sourceRangeProjection S₁
  let R : Matrix (Fin h) (Fin e₂) ℂ := (1 - P) * S₂
  obtain ⟨hPH, hP2, _⟩ :=
    (sourceGramPseudoinverse_projection S₁).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  rw [sourceSchurResidual_eq_orthogonalResidual]
  have hgram : Rᴴ * R = S₂ᴴ * (1 - P) * S₂ := by
    dsimp only [R]
    rw [Matrix.conjTranspose_mul, hQH]
    calc
      S₂ᴴ * (1 - P) * ((1 - P) * S₂)
          = S₂ᴴ * (((1 - P) * (1 - P)) * S₂) := by
              simp only [Matrix.mul_assoc]
      _ = S₂ᴴ * (1 - P) * S₂ := by
        rw [hQ2]
        simp only [Matrix.mul_assoc]
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Vanishing of the Schur residual is exactly inclusion of source ranges. -/
theorem sourceSchurResidual_eq_zero_iff_rangeIncluded {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    sourceSchurResidual S₁ S₂ = 0 ↔ SourceRangeIncluded S₂ S₁ := by
  let P := sourceRangeProjection S₁
  let Q : Matrix (Fin h) (Fin h) ℂ := 1 - P
  let R : Matrix (Fin h) (Fin e₂) ℂ := Q * S₂
  obtain ⟨hPH, hP2, hPS₁⟩ :=
    (sourceGramPseudoinverse_projection S₁).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  change P * S₁ = S₁ at hPS₁
  have hQH : Qᴴ = Q := by
    dsimp only [Q]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hres : sourceSchurResidual S₁ S₂ = Rᴴ * R := by
    rw [sourceSchurResidual_eq_orthogonalResidual]
    dsimp only [R]
    rw [Matrix.conjTranspose_mul, hQH]
    calc
      S₂ᴴ * Q * S₂ = S₂ᴴ * (Q * S₂) := Matrix.mul_assoc _ _ _
      _ = S₂ᴴ * ((Q * Q) * S₂) := by rw [hQ2]
      _ = S₂ᴴ * (Q * (Q * S₂)) := by rw [Matrix.mul_assoc]
      _ = S₂ᴴ * Q * (Q * S₂) := (Matrix.mul_assoc _ _ _).symm
  constructor
  · intro hzero
    have hR : R = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp (hres ▸ hzero)
    have hPS₂ : P * S₂ = S₂ := by
      dsimp only [R, Q] at hR
      rw [Matrix.sub_mul, Matrix.one_mul] at hR
      exact (sub_eq_zero.mp hR).symm
    refine ⟨sourceGramPseudoinverse S₁ * S₁ᴴ * S₂, ?_⟩
    simpa only [P, sourceRangeProjection, Matrix.mul_assoc] using hPS₂.symm
  · rintro ⟨T, rfl⟩
    have hQS₁ : Q * S₁ = 0 := by
      dsimp only [Q]
      rw [Matrix.sub_mul, Matrix.one_mul, hPS₁, sub_self]
    have hR : R = 0 := by
      dsimp only [R]
      rw [← Matrix.mul_assoc, hQS₁, Matrix.zero_mul]
    rw [hres, hR, Matrix.conjTranspose_zero, Matrix.zero_mul]

/-- Rank of the source range projection equals rank of the source map. -/
theorem sourceRangeProjection_rank {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) :
    (sourceRangeProjection S).rank = S.rank := by
  have hfix := (sourceGramPseudoinverse_projection S).2.2.2.2.2
  change sourceRangeProjection S * S = S at hfix
  apply le_antisymm
  · simp only [sourceRangeProjection, Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left S _
  · have hle := Matrix.rank_mul_le_left (sourceRangeProjection S) S
    rwa [hfix] at hle

/-- The block Gram rank increment is the rank of the exact Schur residual. -/
theorem sourceSchurResidual_rank_increment {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    (Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
        ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)).rank - (S₁ᴴ * S₁).rank
      = (sourceSchurResidual S₁ S₂).rank := by
  let P := sourceRangeProjection S₁
  let C : Matrix (Fin h) (Fin e₁ ⊕ Fin e₂) ℂ := Matrix.fromCols S₁ S₂
  let R : Matrix (Fin h) (Fin e₂) ℂ := (1 - P) * S₂
  obtain ⟨hPH, hP2, hPS₁⟩ :=
    (sourceGramPseudoinverse_projection S₁).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  change P * S₁ = S₁ at hPS₁
  have hblock : Cᴴ * C = Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
      ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂) := by
    dsimp only [C]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hstack := stacked_rank_innovation S₁.transpose S₂.transpose P.transpose
    (by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hP2)
    (by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hPS₁)
    (by simpa using sourceRangeProjection_rank S₁)
  have hCtranspose : C.transpose = Matrix.fromRows S₁.transpose S₂.transpose := by
    simpa only [C] using Matrix.transpose_fromCols S₁ S₂
  have hRtranspose : R.transpose = S₂.transpose * (1 - P.transpose) := by
    dsimp only [R]
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one]
  have hleft :
      (Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
        ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)).rank - (S₁ᴴ * S₁).rank
        = C.rank - S₁.rank := by
    rw [← hblock, Matrix.rank_conjTranspose_mul_self,
      Matrix.rank_conjTranspose_mul_self]
  have hmiddle : C.rank - S₁.rank = R.rank := by
    rw [← Matrix.rank_transpose C, hCtranspose,
      ← Matrix.rank_transpose S₁, ← Matrix.rank_transpose R, hRtranspose]
    exact hstack
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hresGram : sourceSchurResidual S₁ S₂ = Rᴴ * R := by
    rw [sourceSchurResidual_eq_orthogonalResidual]
    dsimp only [R]
    rw [Matrix.conjTranspose_mul, hQH]
    calc
      S₂ᴴ * (1 - P) * S₂ = S₂ᴴ * ((1 - P) * S₂) :=
        Matrix.mul_assoc _ _ _
      _ = S₂ᴴ * (((1 - P) * (1 - P)) * S₂) := by rw [hQ2]
      _ = S₂ᴴ * ((1 - P) * ((1 - P) * S₂)) := by
        rw [Matrix.mul_assoc]
      _ = S₂ᴴ * (1 - P) * ((1 - P) * S₂) :=
        (Matrix.mul_assoc _ _ _).symm
  rw [hleft, hmiddle, hresGram, Matrix.rank_conjTranspose_mul_self]

/-- `thm:source-Schur`: the exact singular source Schur identity, positivity,
range criterion, and rank increment formula. -/
theorem exact_source_schur_residual {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    sourceSchurResidual S₁ S₂ =
        S₂ᴴ * (1 - sourceRangeProjection S₁) * S₂
    ∧ (sourceSchurResidual S₁ S₂).PosSemidef
    ∧ (sourceSchurResidual S₁ S₂ = 0 ↔ SourceRangeIncluded S₂ S₁)
    ∧ (Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
          ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)).rank - (S₁ᴴ * S₁).rank
        = (sourceSchurResidual S₁ S₂).rank :=
  ⟨sourceSchurResidual_eq_orthogonalResidual S₁ S₂,
    sourceSchurResidual_posSemidef S₁ S₂,
    sourceSchurResidual_eq_zero_iff_rangeIncluded S₁ S₂,
    sourceSchurResidual_rank_increment S₁ S₂⟩

end NCG
