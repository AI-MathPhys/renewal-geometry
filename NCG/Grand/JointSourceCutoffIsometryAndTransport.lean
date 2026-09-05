/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceCutoff
import NCG.Grand.JointSourceRangeUnitary
import NCG.Grand.JointSourceNormalizedTransportAndShort

/-!
# Joint-source cutoff isometry and normalized transport

This file gives the singular-support form of the strict joint-source cutoff
functor.  It packages the Gram-quotient map as a unique inner-preserving linear
map between minimal source ranges, proves strict composition, and proves the
Moore--Penrose-whitened transport naturality and its exact Hilbert--Schmidt
defect criterion.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The range of a product `T * J` includes canonically in the range of `T`. -/
def matrixProductRangeInclusion {h eX eY : Type*}
    [Fintype eX] [Fintype eY]
    (T : Matrix h eY ℂ) (J : Matrix eY eX ℂ) :
    LinearMap.range (T * J).mulVecLin →ₗ[ℂ] LinearMap.range T.mulVecLin where
  toFun x := ⟨x.1, by
    obtain ⟨u, hu⟩ := x.2
    refine ⟨J *ᵥ u, ?_⟩
    change T *ᵥ (J *ᵥ u) = x.1
    rw [Matrix.mulVec_mulVec]
    exact hu⟩
  map_add' _ _ := by ext <;> rfl
  map_smul' _ _ := by ext <;> rfl

/-- Complete Gram compression produces a unique map between the two minimal
source ranges.  It fixes every source coefficient and preserves the ambient
inner product, so it is the manuscript's cutoff isometry. -/
theorem existsUnique_jointSourceRangeCutoffIsometry
    {hX hY eX eY : Type*}
    [Fintype hX] [Fintype hY] [Fintype eX] [Fintype eY]
    (T_X : Matrix hX eX ℂ) (T_Y : Matrix hY eY ℂ)
    (J : Matrix eY eX ℂ)
    (hGram : T_Xᴴ * T_X = (T_Y * J)ᴴ * (T_Y * J)) :
    ∃! U : LinearMap.range T_X.mulVecLin →ₗ[ℂ]
        LinearMap.range T_Y.mulVecLin,
      (∀ u : eX → ℂ,
        U (T_X.mulVecLin.rangeRestrict u) =
          T_Y.mulVecLin.rangeRestrict (J *ᵥ u)) ∧
      (∀ x y : LinearMap.range T_X.mulVecLin,
        star (x : hX → ℂ) ⬝ᵥ (y : hX → ℂ) =
          star (U x : hY → ℂ) ⬝ᵥ (U y : hY → ℂ)) := by
  classical
  obtain ⟨V, ⟨hV, hinner⟩, hVunique⟩ :=
    joint_source_unique_range_unitary T_X (T_Y * J) hGram
  let I := matrixProductRangeInclusion T_Y J
  let U : LinearMap.range T_X.mulVecLin →ₗ[ℂ]
      LinearMap.range T_Y.mulVecLin := I.comp V.toLinearMap
  have hU : ∀ u : eX → ℂ,
      U (T_X.mulVecLin.rangeRestrict u) =
        T_Y.mulVecLin.rangeRestrict (J *ᵥ u) := by
    intro u
    apply Subtype.ext
    change ((I (V (T_X.mulVecLin.rangeRestrict u)) :
      LinearMap.range T_Y.mulVecLin) : hY → ℂ) = T_Y *ᵥ (J *ᵥ u)
    rw [hV u]
    change (T_Y * J) *ᵥ u = T_Y *ᵥ (J *ᵥ u)
    rw [Matrix.mulVec_mulVec]
  have hUinner : ∀ x y : LinearMap.range T_X.mulVecLin,
      star (x : hX → ℂ) ⬝ᵥ (y : hX → ℂ) =
        star (U x : hY → ℂ) ⬝ᵥ (U y : hY → ℂ) := by
    intro x y
    change star (x : hX → ℂ) ⬝ᵥ (y : hX → ℂ) =
      star (V x : hY → ℂ) ⬝ᵥ (V y : hY → ℂ)
    exact hinner x y
  refine ⟨U, ⟨hU, hUinner⟩, ?_⟩
  intro W hW
  apply LinearMap.ext
  rintro ⟨_, ⟨u, rfl⟩⟩
  change W (T_X.mulVecLin.rangeRestrict u) =
    U (T_X.mulVecLin.rangeRestrict u)
  rw [hW.1 u, hU u]

/-- Cutoff maps compose strictly: the composite and the direct map agree on
every source generator, which spans the minimal range. -/
theorem jointSourceRangeCutoff_strictComposition
    {hX hY hZ eX eY eZ : Type*}
    [Fintype hX] [Fintype hY] [Fintype hZ]
    [Fintype eX] [Fintype eY] [Fintype eZ]
    (T_X : Matrix hX eX ℂ) (T_Y : Matrix hY eY ℂ)
    (T_Z : Matrix hZ eZ ℂ)
    (J_YX : Matrix eY eX ℂ) (J_ZY : Matrix eZ eY ℂ)
    (U_YX : LinearMap.range T_X.mulVecLin →ₗ[ℂ]
      LinearMap.range T_Y.mulVecLin)
    (U_ZY : LinearMap.range T_Y.mulVecLin →ₗ[ℂ]
      LinearMap.range T_Z.mulVecLin)
    (U_ZX : LinearMap.range T_X.mulVecLin →ₗ[ℂ]
      LinearMap.range T_Z.mulVecLin)
    (hYX : ∀ u : eX → ℂ,
      U_YX (T_X.mulVecLin.rangeRestrict u) =
        T_Y.mulVecLin.rangeRestrict (J_YX *ᵥ u))
    (hZY : ∀ u : eY → ℂ,
      U_ZY (T_Y.mulVecLin.rangeRestrict u) =
        T_Z.mulVecLin.rangeRestrict (J_ZY *ᵥ u))
    (hZX : ∀ u : eX → ℂ,
      U_ZX (T_X.mulVecLin.rangeRestrict u) =
        T_Z.mulVecLin.rangeRestrict ((J_ZY * J_YX) *ᵥ u)) :
    U_ZY.comp U_YX = U_ZX := by
  apply LinearMap.ext
  rintro ⟨_, ⟨u, rfl⟩⟩
  change U_ZY (U_YX (T_X.mulVecLin.rangeRestrict u)) =
    U_ZX (T_X.mulVecLin.rangeRestrict u)
  rw [hYX u, hZY (J_YX *ᵥ u), hZX u, Matrix.mulVec_mulVec]

/-- The block-diagonal coefficient arrow for two typed source families. -/
def jointSourceCoefficientCutoff {e1X e1Y e2X e2Y : ℕ}
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    Matrix (Fin e1Y ⊕ Fin e2Y) (Fin e1X ⊕ Fin e2X) ℂ :=
  Matrix.fromBlocks j₁ 0 0 j₂

/-- Block-diagonal coefficient cutoff acts family by family on the joint
source synthesis. -/
theorem jointSource_fromCols_mul_coefficientCutoff
    {h e1X e1Y e2X e2Y : ℕ}
    (S₁ : Matrix (Fin h) (Fin e1Y) ℂ)
    (S₂ : Matrix (Fin h) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    Matrix.fromCols S₁ S₂ * jointSourceCoefficientCutoff j₁ j₂ =
      Matrix.fromCols (S₁ * j₁) (S₂ * j₂) := by
  rw [jointSourceCoefficientCutoff, Matrix.fromCols_mul_fromBlocks]
  simp

/-- Compression of all four typed Gram blocks is exactly compression of the
complete joint Gram by the block-diagonal coefficient arrow. -/
theorem jointSource_fourBlockCompression_gram
    {hX hY e1X e1Y e2X e2Y : ℕ}
    (S1X : Matrix (Fin hX) (Fin e1X) ℂ)
    (S2X : Matrix (Fin hX) (Fin e2X) ℂ)
    (S1Y : Matrix (Fin hY) (Fin e1Y) ℂ)
    (S2Y : Matrix (Fin hY) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ)
    (h11 : S1Xᴴ * S1X = (S1Y * j₁)ᴴ * (S1Y * j₁))
    (h12 : S1Xᴴ * S2X = (S1Y * j₁)ᴴ * (S2Y * j₂))
    (h21 : S2Xᴴ * S1X = (S2Y * j₂)ᴴ * (S1Y * j₁))
    (h22 : S2Xᴴ * S2X = (S2Y * j₂)ᴴ * (S2Y * j₂)) :
    (Matrix.fromCols S1X S2X)ᴴ * Matrix.fromCols S1X S2X =
      (Matrix.fromCols S1Y S2Y * jointSourceCoefficientCutoff j₁ j₂)ᴴ *
        (Matrix.fromCols S1Y S2Y * jointSourceCoefficientCutoff j₁ j₂) := by
  rw [jointSource_fromCols_mul_coefficientCutoff]
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  rw [h11, h12, h21, h22]

/-- The four block-compression identities therefore produce the unique
minimal-carrier cutoff isometry. -/
theorem existsUnique_jointSourceCutoffIsometry_fromFourBlocks
    {hX hY e1X e1Y e2X e2Y : ℕ}
    (S1X : Matrix (Fin hX) (Fin e1X) ℂ)
    (S2X : Matrix (Fin hX) (Fin e2X) ℂ)
    (S1Y : Matrix (Fin hY) (Fin e1Y) ℂ)
    (S2Y : Matrix (Fin hY) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ)
    (h11 : S1Xᴴ * S1X = (S1Y * j₁)ᴴ * (S1Y * j₁))
    (h12 : S1Xᴴ * S2X = (S1Y * j₁)ᴴ * (S2Y * j₂))
    (h21 : S2Xᴴ * S1X = (S2Y * j₂)ᴴ * (S1Y * j₁))
    (h22 : S2Xᴴ * S2X = (S2Y * j₂)ᴴ * (S2Y * j₂)) :
    ∃! U : LinearMap.range (Matrix.fromCols S1X S2X).mulVecLin →ₗ[ℂ]
        LinearMap.range (Matrix.fromCols S1Y S2Y).mulVecLin,
      (∀ u : (Fin e1X ⊕ Fin e2X) → ℂ,
        U ((Matrix.fromCols S1X S2X).mulVecLin.rangeRestrict u) =
          (Matrix.fromCols S1Y S2Y).mulVecLin.rangeRestrict
            (jointSourceCoefficientCutoff j₁ j₂ *ᵥ u)) ∧
      (∀ x y : LinearMap.range (Matrix.fromCols S1X S2X).mulVecLin,
        star (x : Fin hX → ℂ) ⬝ᵥ (y : Fin hX → ℂ) =
          star (U x : Fin hY → ℂ) ⬝ᵥ (U y : Fin hY → ℂ)) :=
  existsUnique_jointSourceRangeCutoffIsometry
    (Matrix.fromCols S1X S2X) (Matrix.fromCols S1Y S2Y)
    (jointSourceCoefficientCutoff j₁ j₂)
    (jointSource_fourBlockCompression_gram
      S1X S2X S1Y S2Y j₁ j₂ h11 h12 h21 h22)

/-- The Moore--Penrose inverse square root depends only on the source Gram. -/
theorem sourceGramPseudoinverseSqrt_congr
    {hS hT e : ℕ}
    (S : Matrix (Fin hS) (Fin e) ℂ)
    (T : Matrix (Fin hT) (Fin e) ℂ)
    (hGram : Sᴴ * S = Tᴴ * T) :
    sourceGramPseudoinverseSqrt S = sourceGramPseudoinverseSqrt T := by
  unfold sourceGramPseudoinverseSqrt
  congr

/-- Consequently the normalized cross transport depends only on the two
marginal Grams and their mixed Gram block. -/
theorem normalizedSourceCrossTransport_congr_gram
    {hS hT e1 e2 : ℕ}
    (S₁ : Matrix (Fin hS) (Fin e1) ℂ)
    (S₂ : Matrix (Fin hS) (Fin e2) ℂ)
    (T₁ : Matrix (Fin hT) (Fin e1) ℂ)
    (T₂ : Matrix (Fin hT) (Fin e2) ℂ)
    (h1 : S₁ᴴ * S₁ = T₁ᴴ * T₁)
    (h2 : S₂ᴴ * S₂ = T₂ᴴ * T₂)
    (h21 : S₂ᴴ * S₁ = T₂ᴴ * T₁) :
    normalizedSourceCrossTransport S₁ S₂ =
      normalizedSourceCrossTransport T₁ T₂ := by
  unfold normalizedSourceCrossTransport
  rw [sourceGramPseudoinverseSqrt_congr S₁ T₁ h1,
    sourceGramPseudoinverseSqrt_congr S₂ T₂ h2, h21]

/-- The canonical arrow from the old whitened source support to the new one.
The old source is represented inside the new coefficient space by `j`. -/
noncomputable def sourceSupportCutoff {h eX eY : ℕ}
    (S : Matrix (Fin h) (Fin eY) ℂ)
    (j : Matrix (Fin eY) (Fin eX) ℂ) :
    Matrix (Fin eY) (Fin eX) ℂ :=
  (normalizedSourceEmbedding S)ᴴ * normalizedSourceEmbedding (S * j)

/-- The support cutoff intertwines the two normalized source embeddings. -/
theorem normalizedSourceEmbedding_sourceSupportCutoff {h eX eY : ℕ}
    (S : Matrix (Fin h) (Fin eY) ℂ)
    (j : Matrix (Fin eY) (Fin eX) ℂ) :
    normalizedSourceEmbedding S * sourceSupportCutoff S j =
      normalizedSourceEmbedding (S * j) := by
  let U := normalizedSourceEmbedding S
  let U₀ := normalizedSourceEmbedding (S * j)
  have hfix := normalizedSourceEmbedding_finalProjection_source S
  have hfix' : (U * Uᴴ) * U₀ = U₀ := by
    change (U * Uᴴ) * ((S * j) * sourceGramPseudoinverseSqrt (S * j)) = U₀
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]
    rfl
  change U * (Uᴴ * U₀) = U₀
  simpa only [Matrix.mul_assoc] using hfix'

/-- A source-support cutoff is a partial isometry, i.e. an isometry on the
old Moore--Penrose support. -/
theorem sourceSupportCutoff_partialIsometry {h eX eY : ℕ}
    (S : Matrix (Fin h) (Fin eY) ℂ)
    (j : Matrix (Fin eY) (Fin eX) ℂ) :
    sourceSupportCutoff S j *
        ((sourceSupportCutoff S j)ᴴ * sourceSupportCutoff S j) =
      sourceSupportCutoff S j := by
  let U := normalizedSourceEmbedding S
  let U₀ := normalizedSourceEmbedding (S * j)
  have hU := normalizedSourceEmbedding_sourceSupportCutoff S j
  have hU₀ := normalizedSourceEmbedding_partialIsometry (S * j)
  have hinitial :
      (sourceSupportCutoff S j)ᴴ * sourceSupportCutoff S j = U₀ᴴ * U₀ := by
    calc
      (sourceSupportCutoff S j)ᴴ * sourceSupportCutoff S j
          = U₀ᴴ * (U * sourceSupportCutoff S j) := by
            simp only [sourceSupportCutoff, U, U₀,
              Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = U₀ᴴ * U₀ := by rw [hU]
  rw [hinitial]
  change (Uᴴ * U₀) * (U₀ᴴ * U₀) = Uᴴ * U₀
  simp only [Matrix.mul_assoc]
  rw [hU₀]

/-- Compressed naturality of the normalized Moore--Penrose cross transport. -/
theorem normalizedSourceCrossTransport_compressedNaturality
    {h e1X e1Y e2X e2Y : ℕ}
    (S₁ : Matrix (Fin h) (Fin e1Y) ℂ)
    (S₂ : Matrix (Fin h) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    (sourceSupportCutoff S₂ j₂)ᴴ *
        normalizedSourceCrossTransport S₁ S₂ *
        sourceSupportCutoff S₁ j₁ =
      normalizedSourceCrossTransport (S₁ * j₁) (S₂ * j₂) := by
  rw [normalizedSourceCrossTransport_eq_embeddings,
    normalizedSourceCrossTransport_eq_embeddings]
  calc
    (sourceSupportCutoff S₂ j₂)ᴴ *
          ((normalizedSourceEmbedding S₂)ᴴ * normalizedSourceEmbedding S₁) *
          sourceSupportCutoff S₁ j₁ =
        (normalizedSourceEmbedding S₂ * sourceSupportCutoff S₂ j₂)ᴴ *
          (normalizedSourceEmbedding S₁ * sourceSupportCutoff S₁ j₁) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (normalizedSourceEmbedding (S₂ * j₂))ᴴ *
          normalizedSourceEmbedding (S₁ * j₁) := by
            rw [normalizedSourceEmbedding_sourceSupportCutoff,
              normalizedSourceEmbedding_sourceSupportCutoff]

/-- The new-support component of the transported old source. -/
noncomputable def sourceTransportNewDefect
    {h e1X e1Y e2X e2Y : ℕ}
    (S₁ : Matrix (Fin h) (Fin e1Y) ℂ)
    (S₂ : Matrix (Fin h) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (σ₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    Matrix (Fin e2Y) (Fin e1X) ℂ :=
  (1 - σ₂ * σ₂ᴴ) * normalizedSourceCrossTransport S₁ S₂ *
    sourceSupportCutoff S₁ j₁

/-- Vanishing of the orthogonal new-support component is exactly the stronger
transport intertwining relation. -/
theorem sourceTransportNewDefect_eq_zero_iff
    {h e1X e1Y e2X e2Y : ℕ}
    (S₁ : Matrix (Fin h) (Fin e1Y) ℂ)
    (S₂ : Matrix (Fin h) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    sourceTransportNewDefect S₁ S₂ j₁ (sourceSupportCutoff S₂ j₂) = 0 ↔
      normalizedSourceCrossTransport S₁ S₂ * sourceSupportCutoff S₁ j₁ =
        sourceSupportCutoff S₂ j₂ *
          normalizedSourceCrossTransport (S₁ * j₁) (S₂ * j₂) := by
  let σ₁ := sourceSupportCutoff S₁ j₁
  let σ₂ := sourceSupportCutoff S₂ j₂
  let K := normalizedSourceCrossTransport S₁ S₂
  let K₀ := normalizedSourceCrossTransport (S₁ * j₁) (S₂ * j₂)
  have hcomp : σ₂ᴴ * K * σ₁ = K₀ :=
    normalizedSourceCrossTransport_compressedNaturality S₁ S₂ j₁ j₂
  have hpartial := sourceSupportCutoff_partialIsometry S₂ j₂
  change (1 - σ₂ * σ₂ᴴ) * K * σ₁ = 0 ↔ K * σ₁ = σ₂ * K₀
  constructor
  · intro hzero
    have hzero' :
        (1 - σ₂ * σ₂ᴴ) * (K * σ₁) = 0 := by
      simpa only [Matrix.mul_assoc] using hzero
    rw [Matrix.sub_mul, Matrix.one_mul] at hzero'
    have hproj : K * σ₁ = (σ₂ * σ₂ᴴ) * (K * σ₁) := by
      exact sub_eq_zero.mp hzero'
    calc
      K * σ₁ = (σ₂ * σ₂ᴴ) * (K * σ₁) := hproj
      _ = σ₂ * (σ₂ᴴ * K * σ₁) := by simp only [Matrix.mul_assoc]
      _ = σ₂ * K₀ := by rw [hcomp]
  · intro hinter
    calc
      (1 - σ₂ * σ₂ᴴ) * K * σ₁
          = (1 - σ₂ * σ₂ᴴ) * (K * σ₁) := by
              simp only [Matrix.mul_assoc]
      _ = (1 - σ₂ * σ₂ᴴ) * (σ₂ * K₀) := by rw [hinter]
      _ = 0 := by
        rw [← Matrix.mul_assoc]
        have hproj : (1 - σ₂ * σ₂ᴴ) * σ₂ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul]
          exact sub_eq_zero.mpr (by
            simpa only [Matrix.mul_assoc] using hpartial.symm)
        rw [hproj, Matrix.zero_mul]

/-- The squared Hilbert--Schmidt defect vanishes exactly when the stronger
normalized transport intertwining relation holds. -/
theorem sourceTransportNewDefect_hilbertSchmidt_eq_zero_iff
    {h e1X e1Y e2X e2Y : ℕ}
    (S₁ : Matrix (Fin h) (Fin e1Y) ℂ)
    (S₂ : Matrix (Fin h) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ) :
    let D := sourceTransportNewDefect S₁ S₂ j₁
      (sourceSupportCutoff S₂ j₂)
    (Dᴴ * D).trace = 0 ↔
      normalizedSourceCrossTransport S₁ S₂ * sourceSupportCutoff S₁ j₁ =
        sourceSupportCutoff S₂ j₂ *
          normalizedSourceCrossTransport (S₁ * j₁) (S₂ * j₂) := by
  dsimp only
  rw [(joint_source_cutoff_functor
    (1 : Matrix (Fin e1X) (Fin e1X) ℂ)
    (1 : Matrix (Fin e1X) (Fin e1X) ℂ)
    (1 : Matrix (Fin e1X) (Fin e1X) ℂ)
    (1 : Matrix (Fin e1X) (Fin e1X) ℂ) (by simp) (by simp)).2.2.2]
  exact sourceTransportNewDefect_eq_zero_iff S₁ S₂ j₁ j₂

/-- The manuscript's compressed naturality identity, expressed with the old
and new cutoff realizations and the four Gram-compression hypotheses. -/
theorem normalizedSourceCrossTransport_cutoffNaturality
    {hX hY e1X e1Y e2X e2Y : ℕ}
    (S1X : Matrix (Fin hX) (Fin e1X) ℂ)
    (S2X : Matrix (Fin hX) (Fin e2X) ℂ)
    (S1Y : Matrix (Fin hY) (Fin e1Y) ℂ)
    (S2Y : Matrix (Fin hY) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ)
    (h11 : S1Xᴴ * S1X = (S1Y * j₁)ᴴ * (S1Y * j₁))
    (h21 : S2Xᴴ * S1X = (S2Y * j₂)ᴴ * (S1Y * j₁))
    (h22 : S2Xᴴ * S2X = (S2Y * j₂)ᴴ * (S2Y * j₂)) :
    (sourceSupportCutoff S2Y j₂)ᴴ *
        normalizedSourceCrossTransport S1Y S2Y *
        sourceSupportCutoff S1Y j₁ =
      normalizedSourceCrossTransport S1X S2X := by
  rw [normalizedSourceCrossTransport_compressedNaturality]
  exact (normalizedSourceCrossTransport_congr_gram
    S1X S2X (S1Y * j₁) (S2Y * j₂) h11 h22 h21).symm

/-- The Hilbert--Schmidt new-support defect vanishes exactly when the full
normalized transports intertwine, now written with the old cutoff transport. -/
theorem sourceTransportNewDefect_cutoffHilbertSchmidt_eq_zero_iff
    {hX hY e1X e1Y e2X e2Y : ℕ}
    (S1X : Matrix (Fin hX) (Fin e1X) ℂ)
    (S2X : Matrix (Fin hX) (Fin e2X) ℂ)
    (S1Y : Matrix (Fin hY) (Fin e1Y) ℂ)
    (S2Y : Matrix (Fin hY) (Fin e2Y) ℂ)
    (j₁ : Matrix (Fin e1Y) (Fin e1X) ℂ)
    (j₂ : Matrix (Fin e2Y) (Fin e2X) ℂ)
    (h11 : S1Xᴴ * S1X = (S1Y * j₁)ᴴ * (S1Y * j₁))
    (h21 : S2Xᴴ * S1X = (S2Y * j₂)ᴴ * (S1Y * j₁))
    (h22 : S2Xᴴ * S2X = (S2Y * j₂)ᴴ * (S2Y * j₂)) :
    let D := sourceTransportNewDefect S1Y S2Y j₁
      (sourceSupportCutoff S2Y j₂)
    (Dᴴ * D).trace = 0 ↔
      normalizedSourceCrossTransport S1Y S2Y * sourceSupportCutoff S1Y j₁ =
        sourceSupportCutoff S2Y j₂ *
          normalizedSourceCrossTransport S1X S2X := by
  dsimp only
  have hdefect :=
    sourceTransportNewDefect_hilbertSchmidt_eq_zero_iff S1Y S2Y j₁ j₂
  dsimp only at hdefect
  rw [← normalizedSourceCrossTransport_congr_gram
    S1X S2X (S1Y * j₁) (S2Y * j₂) h11 h22 h21] at hdefect
  exact hdefect

end NCG
