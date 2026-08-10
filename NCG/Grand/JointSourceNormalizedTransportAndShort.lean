/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.SchurCluster
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.PositiveBlockContractionFactorization
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Normalized joint-source transport and the universal short

This file proves the singular-support clauses of the joint-source short
theorem: the normalized Moore--Penrose cross transport, its contraction and
principal-angle singular-value data, both mutual range tests, and the exact
Anderson--Trapp variational short.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

private noncomputable def sourceSpectralPseudoinverseSqrt (x : ℝ) : ℝ :=
  if x = 0 then 0 else (Real.sqrt x)⁻¹

private noncomputable def sourceNormalizedSupport (x : ℝ) : ℝ :=
  if x = 0 then 0 else 1

/-- The Moore--Penrose inverse square root of a source Gram matrix. -/
noncomputable def sourceGramPseudoinverseSqrt {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  (Matrix.posSemidef_conjTranspose_mul_self S).isHermitian.cfc
    sourceSpectralPseudoinverseSqrt

/-- The support-normalized source embedding `S (SᴴS)^{†/2}`. -/
noncomputable def normalizedSourceEmbedding {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin h) (Fin e) ℂ :=
  S * sourceGramPseudoinverseSqrt S

/-- The normalized cross transport
`G₂^{†/2} (S₂ᴴS₁) G₁^{†/2}`. -/
noncomputable def normalizedSourceCrossTransport {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  sourceGramPseudoinverseSqrt S₂ * (S₂ᴴ * S₁) *
    sourceGramPseudoinverseSqrt S₁

/-- The principal-angle cosine sequence of two source ranges: by definition,
these are the singular values of their normalized cross transport. -/
noncomputable def sourcePrincipalAngleCosines {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) : ℕ →₀ ℝ :=
  (normalizedSourceCrossTransport S₁ S₂).toEuclideanLin.singularValues

set_option maxHeartbeats 1200000 in
-- The functional-calculus support identities require a larger elaboration budget.
/-- A support-normalized source embedding is a partial isometry. -/
theorem normalizedSourceEmbedding_partialIsometry {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) :
    normalizedSourceEmbedding S *
        ((normalizedSourceEmbedding S)ᴴ * normalizedSourceEmbedding S) =
      normalizedSourceEmbedding S := by
  let X : Matrix (Fin e) (Fin e) ℂ := Sᴴ * S
  have hX : X.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S
  let hXH : X.IsHermitian := hX.isHermitian
  let P : Matrix (Fin e) (Fin e) ℂ := hXH.cfc Real.sqrt
  let Pd : Matrix (Fin e) (Fin e) ℂ :=
    hXH.cfc sourceSpectralPseudoinverseSqrt
  let p : Matrix (Fin e) (Fin e) ℂ := hXH.cfc sourceNormalizedSupport
  have hP2 : P * P = X := by
    calc
      P * P = hXH.cfc (fun x => Real.sqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        exact Real.mul_self_sqrt (hX.eigenvalues_nonneg i)
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hPdP : Pd * P = p := by
    calc
      Pd * P = hXH.cfc
          (fun x => sourceSpectralPseudoinverseSqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz, hs]
      _ = p := rfl
  have hPPd : P * Pd = p := by
    calc
      P * Pd = hXH.cfc
          (fun x => Real.sqrt x * sourceSpectralPseudoinverseSqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz, hs]
      _ = p := rfl
  have hp2 : p * p = p := by
    calc
      p * p = hXH.cfc
          (fun x => sourceNormalizedSupport x * sourceNormalizedSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        simp [sourceNormalizedSupport]
      _ = p := rfl
  have hPdH : Pdᴴ = Pd :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH
      sourceSpectralPseudoinverseSqrt
  have hPdp : Pd * p = Pd := by
    calc
      Pd * p = hXH.cfc
          (fun x => sourceSpectralPseudoinverseSqrt x * sourceNormalizedSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceSpectralPseudoinverseSqrt := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz]
      _ = Pd := rfl
  have hUtU : (S * Pd)ᴴ * (S * Pd) = p := by
    calc
      (S * Pd)ᴴ * (S * Pd) = Pd * X * Pd := by
        rw [Matrix.conjTranspose_mul, hPdH]
        simp only [X, Matrix.mul_assoc]
      _ = Pd * (P * P) * Pd := by rw [hP2]
      _ = (Pd * P) * (P * Pd) := by simp only [Matrix.mul_assoc]
      _ = p * p := by rw [hPdP, hPPd]
      _ = p := hp2
  change (S * Pd) * ((S * Pd)ᴴ * (S * Pd)) = S * Pd
  rw [hUtU, Matrix.mul_assoc, hPdp]

set_option maxHeartbeats 1200000 in
-- This is the final-projection companion to the preceding polar identity.
/-- The final projection of the support-normalized embedding fixes the original
source.  Thus `normalizedSourceEmbedding S` has exactly the same range as `S`,
including when the source Gram is singular. -/
theorem normalizedSourceEmbedding_finalProjection_source {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) :
    (normalizedSourceEmbedding S * (normalizedSourceEmbedding S)ᴴ) * S = S := by
  let X : Matrix (Fin e) (Fin e) ℂ := Sᴴ * S
  have hX : X.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S
  let hXH : X.IsHermitian := hX.isHermitian
  let P : Matrix (Fin e) (Fin e) ℂ := hXH.cfc Real.sqrt
  let D : Matrix (Fin e) (Fin e) ℂ :=
    hXH.cfc sourceSpectralPseudoinverseSqrt
  let p : Matrix (Fin e) (Fin e) ℂ := hXH.cfc sourceNormalizedSupport
  have hP2 : P * P = X := by
    calc
      P * P = hXH.cfc (fun x => Real.sqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        exact Real.mul_self_sqrt (hX.eigenvalues_nonneg i)
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hDP : D * P = p := by
    calc
      D * P = hXH.cfc
          (fun x => sourceSpectralPseudoinverseSqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz, hs]
      _ = p := rfl
  have hPD : P * D = p := by
    calc
      P * D = hXH.cfc
          (fun x => Real.sqrt x * sourceSpectralPseudoinverseSqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [sourceSpectralPseudoinverseSqrt, sourceNormalizedSupport, hz, hs]
      _ = p := rfl
  have hp2 : p * p = p := by
    calc
      p * p = hXH.cfc
          (fun x => sourceNormalizedSupport x * sourceNormalizedSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc sourceNormalizedSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        simp [sourceNormalizedSupport]
      _ = p := rfl
  have hDH : Dᴴ = D :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH
      sourceSpectralPseudoinverseSqrt
  have hpH : pᴴ = p :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH sourceNormalizedSupport
  have hXp : X * p = X := by
    calc
      X * p = hXH.cfc id * hXH.cfc sourceNormalizedSupport := by
        rw [Upstream.PrimitiveWeight.cfc_id' hXH]
      _ = hXH.cfc (fun x => x * sourceNormalizedSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [sourceNormalizedSupport, hz]
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hpX : p * X = X := by
    have ht := congrArg Matrix.conjTranspose hXp
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
  change ((S * D) * (S * D)ᴴ) * S = S
  rw [Matrix.conjTranspose_mul, hDH]
  calc
    (S * D * (D * Sᴴ)) * S = S * (D * D * X) := by
      simp only [X, Matrix.mul_assoc]
    _ = S * (D * D * (P * P)) := by rw [hP2]
    _ = S * (D * ((D * P) * P)) := by
      simp only [Matrix.mul_assoc]
    _ = S * (D * ((P * D) * P)) := by rw [hDP, hPD]
    _ = S * ((D * P) * (D * P)) := by
      simp only [Matrix.mul_assoc]
    _ = S * (p * p) := by rw [hDP]
    _ = S * p := by rw [hp2]
    _ = S := hSp

/-- The normalized cross transport is the cross product of the two normalized
partial-isometry embeddings. -/
theorem normalizedSourceCrossTransport_eq_embeddings {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    normalizedSourceCrossTransport S₁ S₂ =
      (normalizedSourceEmbedding S₂)ᴴ * normalizedSourceEmbedding S₁ := by
  have hJ₁ : (sourceGramPseudoinverseSqrt S₁)ᴴ =
      sourceGramPseudoinverseSqrt S₁ :=
    Upstream.PrimitiveWeight.cfc_isHermitian
      (Matrix.posSemidef_conjTranspose_mul_self S₁).isHermitian _
  have hJ₂ : (sourceGramPseudoinverseSqrt S₂)ᴴ =
      sourceGramPseudoinverseSqrt S₂ :=
    Upstream.PrimitiveWeight.cfc_isHermitian
      (Matrix.posSemidef_conjTranspose_mul_self S₂).isHermitian _
  simp only [normalizedSourceCrossTransport, normalizedSourceEmbedding,
    Matrix.conjTranspose_mul, hJ₂, Matrix.mul_assoc]

/-- The Moore--Penrose normalized cross transport is a contraction. -/
theorem normalizedSourceCrossTransport_contraction {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) -
      (normalizedSourceCrossTransport S₁ S₂)ᴴ *
        normalizedSourceCrossTransport S₁ S₂).PosSemidef := by
  rw [normalizedSourceCrossTransport_eq_embeddings]
  exact partialIsometry_cross_contraction
    (normalizedSourceEmbedding S₁) (normalizedSourceEmbedding S₂)
    (normalizedSourceEmbedding_partialIsometry S₁)
    (normalizedSourceEmbedding_partialIsometry S₂)

/-- The singular values of normalized cross transport are, definitionally,
the principal-angle cosines of the two finite source ranges. -/
theorem normalizedTransport_singularValues_eq_principalAngleCosines {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    (normalizedSourceCrossTransport S₁ S₂).toEuclideanLin.singularValues =
      sourcePrincipalAngleCosines S₁ S₂ := rfl

/-- Equality of source ranges is mutual finite-dimensional factorization. -/
def SourceRangesCoincide {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) : Prop :=
  SourceRangeIncluded S₁ S₂ ∧ SourceRangeIncluded S₂ S₁

/-- Both exact Schur residuals vanish exactly when the source ranges coincide. -/
theorem mutualSourceResiduals_eq_zero_iff_rangesCoincide {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    (sourceSchurResidual S₂ S₁ = 0 ∧ sourceSchurResidual S₁ S₂ = 0) ↔
      SourceRangesCoincide S₁ S₂ := by
  rw [sourceSchurResidual_eq_zero_iff_rangeIncluded,
    sourceSchurResidual_eq_zero_iff_rangeIncluded]
  rfl

/-- The Anderson--Trapp short is the one-sided source residual: it is the
universal lower bound of the joint quadratic form, attained by the
Moore--Penrose least-squares compensation. -/
theorem jointSource_andersonTrapp_short {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    let G₁ := S₁ᴴ * S₁
    let G₂ := S₂ᴴ * S₂
    let C₂₁ := S₂ᴴ * S₁
    let R := sourceSchurResidual S₂ S₁
    let M := Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂
    R.PosSemidef ∧
      (∀ (x : Fin n → ℂ) (y : Fin m → ℂ),
        star x ⬝ᵥ (R *ᵥ x) ≤
          star (Sum.elim x y) ⬝ᵥ (M *ᵥ Sum.elim x y)) ∧
      (∀ x : Fin n → ℂ,
        let y := -((sourceGramPseudoinverse S₂ * C₂₁) *ᵥ x)
        star (Sum.elim x y) ⬝ᵥ (M *ᵥ Sum.elim x y) =
          star x ⬝ᵥ (R *ᵥ x)) := by
  dsimp only
  let G₁ := S₁ᴴ * S₁
  let G₂ := S₂ᴴ * S₂
  let C₂₁ := S₂ᴴ * S₁
  let J₂ := sourceGramPseudoinverse S₂
  let Z : Matrix (Fin m) (Fin n) ℂ := J₂ * C₂₁
  obtain ⟨hJH, _, hJGJ, _, _, hPS₂⟩ :=
    sourceGramPseudoinverse_projection S₂
  change J₂ᴴ = J₂ at hJH
  change J₂ * G₂ * J₂ = J₂ at hJGJ
  have hSJG : S₂ * J₂ * G₂ = S₂ := by
    change (S₂ * J₂ * S₂ᴴ) * S₂ = S₂ at hPS₂
    simpa only [G₂, Matrix.mul_assoc] using hPS₂
  have hGJS : G₂ * J₂ * S₂ᴴ = S₂ᴴ := by
    have ht := congrArg Matrix.conjTranspose hSJG
    have ht' : G₂ᴴ * J₂ᴴ * S₂ᴴ = S₂ᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using ht
    have hG₂H : G₂ᴴ = G₂ := by
      dsimp only [G₂]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hG₂H, hJH] at ht'
    exact ht'
  have hZ : G₂ * Z = (C₂₁ᴴ)ᴴ := by
    calc
      G₂ * Z = (G₂ * J₂ * S₂ᴴ) * S₁ := by
        dsimp only [Z, C₂₁]
        simp only [Matrix.mul_assoc]
      _ = S₂ᴴ * S₁ := by rw [hGJS]
      _ = (C₂₁ᴴ)ᴴ := by
        dsimp only [C₂₁]
        rw [Matrix.conjTranspose_conjTranspose]
  have hblock :
      (Matrix.fromCols S₁ S₂)ᴴ * Matrix.fromCols S₁ S₂ =
        Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂ := by
    dsimp only [G₁, G₂, C₂₁]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hM : (Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂).PosSemidef := by
    rw [← hblock]
    exact Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols S₁ S₂)
  have hM' : (Matrix.fromBlocks G₁ C₂₁ᴴ (C₂₁ᴴ)ᴴ G₂).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hM
  have hs := schur_short G₁ C₂₁ᴴ G₂ Z hZ hM'
  have hzterm : Zᴴ * G₂ * Z = C₂₁ᴴ * J₂ * C₂₁ := by
    dsimp only [Z]
    rw [Matrix.conjTranspose_mul, hJH]
    calc
      C₂₁ᴴ * J₂ * G₂ * (J₂ * C₂₁)
          = C₂₁ᴴ * (J₂ * G₂ * J₂) * C₂₁ := by
              simp only [Matrix.mul_assoc]
      _ = C₂₁ᴴ * J₂ * C₂₁ := by rw [hJGJ]
  have hshort : G₁ - Zᴴ * G₂ * Z = sourceSchurResidual S₂ S₁ := by
    rw [hzterm]
    rfl
  rw [hshort] at hs
  simpa only [Z, J₂, C₂₁, Matrix.conjTranspose_conjTranspose] using hs

/-- `thm:joint-source-short`: mutual singular Schur residuals, exact range
tests, normalized contraction/principal-angle data, and the universal short. -/
theorem joint_source_short_exact {h n m : ℕ}
    (S₁ : Matrix (Fin h) (Fin n) ℂ)
    (S₂ : Matrix (Fin h) (Fin m) ℂ) :
    (sourceSchurResidual S₂ S₁ =
      S₁ᴴ * (1 - sourceRangeProjection S₂) * S₁) ∧
    (sourceSchurResidual S₁ S₂ =
      S₂ᴴ * (1 - sourceRangeProjection S₁) * S₂) ∧
    (sourceSchurResidual S₂ S₁).PosSemidef ∧
    (sourceSchurResidual S₁ S₂).PosSemidef ∧
    ((sourceSchurResidual S₂ S₁ = 0 ∧ sourceSchurResidual S₁ S₂ = 0) ↔
      SourceRangesCoincide S₁ S₂) ∧
    ((1 : Matrix (Fin n) (Fin n) ℂ) -
      (normalizedSourceCrossTransport S₁ S₂)ᴴ *
        normalizedSourceCrossTransport S₁ S₂).PosSemidef ∧
    ((normalizedSourceCrossTransport S₁ S₂).toEuclideanLin.singularValues =
      sourcePrincipalAngleCosines S₁ S₂) :=
  ⟨sourceSchurResidual_eq_orthogonalResidual S₂ S₁,
    sourceSchurResidual_eq_orthogonalResidual S₁ S₂,
    sourceSchurResidual_posSemidef S₂ S₁,
    sourceSchurResidual_posSemidef S₁ S₂,
    mutualSourceResiduals_eq_zero_iff_rangesCoincide S₁ S₂,
    normalizedSourceCrossTransport_contraction S₁ S₂,
    normalizedTransport_singularValues_eq_principalAngleCosines S₁ S₂⟩

end NCG
