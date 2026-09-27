/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.GramDeterminedIsometry
import RenewalGeometry.Spectralization.OperatorTailMeasureNaimarkRealizationExact
/-!
# Uniqueness of the minimal operator-measure realization

This file closes `thm:supp-Naimark-realization` of `papers/predictive_spectral_geometry`
(`eq:supp-Naimark-unitary`): two minimal realizations of the same positive tail measure `μ` are
related by a unique unitary.

* `IsMinimalRealization μ P V`: `P` is a spectral measure supported in `(0,∞)` on a Hilbert space
  `K` (the spectral measure `E_C` of a nonnegative self-adjoint `C`), `V : H → K` is bounded with
  `⟨V ξ, P(E) V η⟩ = ⟨ξ, μ(E) η⟩` (i.e. `μ(E) = B E_C(E) B^*` with `B = V^*`), and `K` is the closed
  span of the source vectors `P(E) V ξ = E_C(E) B^* ξ`.
* `isMinimalRealization_canonical`: the canonical `(K_μ, P_μ, V_μ)` of `con:supp-Naimark-tail` is a
  minimal realization.
* `IsMinimalRealization.existsUnique_unitary`: **`eq:supp-Naimark-unitary`** — for two minimal
  realizations there is a unique unitary `U : K₁ ≃ K₂` with `U P₁(E) = P₂(E) U` for every Borel
  `E` (the spectral-measure form of `U C₁ = C₂ U`) and `U V₁ = V₂` (i.e. `U B₁^* = B₂^*`).
* `naimark_realization_unitary`: the packaged statement together with the unitary equivalence of
  every minimal realization with the canonical one.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **A minimal realization of `μ`** (`thm:supp-Naimark-realization`): a spectral measure `P`
supported in `(0,∞)` on `K`, a bounded `V : H → K` with `⟨V ξ, P(E) V η⟩ = ⟨ξ, μ(E) η⟩`
(`μ(E) = B P(E) B^*`, `B = V^*`), and `K = closure span {P(E) V ξ}`. -/
structure IsMinimalRealization (μ : PositiveTailMeasure H) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K)
    (V : EuclideanSpace ℂ H →L[ℂ] K) : Prop where
  isSpectralMeasure : IsSpectralMeasure P
  inner_eq : ∀ (s : Set ℝ) (hs : MeasurableSet s) (ξ η : EuclideanSpace ℂ H),
    ⟪V ξ, P s hs (V η)⟫_ℂ = ⟪ξ, Matrix.toEuclideanLin (Matrix.of (μ.toVectorMeasure s)) η⟫_ℂ
  minimal : (Submodule.span ℂ {y : K | ∃ (s : Set ℝ) (hs : MeasurableSet s)
    (ξ : EuclideanSpace ℂ H), y = P s hs (V ξ)}).topologicalClosure = ⊤

/-- The canonical dilation `(K_μ, P_μ, V_μ)` of `con:supp-Naimark-tail` is a minimal realization. -/
theorem PositiveTailMeasure.isMinimalRealization_canonical (μ : PositiveTailMeasure H) :
    IsMinimalRealization μ μ.spectralProj μ.embedV where
  isSpectralMeasure := μ.isSpectralMeasure_spectralProj
  inner_eq s hs ξ η := by
    rw [μ.toVectorMeasure_eq_compress s hs η, PositiveTailMeasure.compressB,
      ContinuousLinearMap.adjoint_inner_right]
  minimal := OperatorMeasureL2.L2.topologicalClosure_sourceSpan μ.toPosOperatorMeasure

namespace IsMinimalRealization

variable {μ : PositiveTailMeasure H} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K}
  {V : EuclideanSpace ℂ H →L[ℂ] K} (h : IsMinimalRealization μ P V)

include h

theorem adjoint_eq (s : Set ℝ) (hs : MeasurableSet s) : ContinuousLinearMap.adjoint (P s hs) = P s hs :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp (h.isSpectralMeasure.isSelfAdjoint s hs)

theorem inner_apply_left (s : Set ℝ) (hs : MeasurableSet s) (x y : K) :
    ⟪P s hs x, y⟫_ℂ = ⟪x, P s hs y⟫_ℂ := by
  conv_lhs => rw [← h.adjoint_eq s hs]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The Gram data of the source vectors: `⟨P(s) V ξ, P(t) V η⟩ = ⟨ξ, μ(s ∩ t) η⟩`. -/
theorem inner_source (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ξ η : EuclideanSpace ℂ H) :
    ⟪P s hs (V ξ), P t ht (V η)⟫_ℂ =
      ⟪ξ, Matrix.toEuclideanLin (Matrix.of (μ.toVectorMeasure (s ∩ t))) η⟫_ℂ := by
  rw [h.inner_apply_left, ← ContinuousLinearMap.comp_apply, ← h.isSpectralMeasure.inter,
    h.inner_eq]

/-- The index type of the generating family: measurable sets paired with head vectors. -/
abbrev SourceIndex (H : Type*) : Type _ := {s : Set ℝ // MeasurableSet s} × EuclideanSpace ℂ H

omit h in
/-- The generating family `(s, ξ) ↦ P(s) V ξ`. -/
noncomputable def sourceFamily (P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K) (V : EuclideanSpace ℂ H →L[ℂ] K) :
    SourceIndex H → K := fun p => P p.1.1 p.1.2 (V p.2)

omit h in
theorem range_sourceFamily :
    Set.range (sourceFamily P V) = {y : K | ∃ (s : Set ℝ) (hs : MeasurableSet s)
      (ξ : EuclideanSpace ℂ H), y = P s hs (V ξ)} := by
  ext y
  constructor
  · rintro ⟨⟨⟨s, hs⟩, ξ⟩, rfl⟩
    exact ⟨s, hs, ξ, rfl⟩
  · rintro ⟨s, hs, ξ, rfl⟩
    exact ⟨⟨⟨s, hs⟩, ξ⟩, rfl⟩

theorem closure_span_sourceFamily :
    (Submodule.span ℂ (Set.range (sourceFamily P V))).topologicalClosure = ⊤ := by
  rw [range_sourceFamily]; exact h.minimal

theorem sourceFamily_univ (ξ : EuclideanSpace ℂ H) :
    sourceFamily P V (⟨univ, MeasurableSet.univ⟩, ξ) = V ξ := by
  simp [sourceFamily, h.isSpectralMeasure.univ]

theorem apply_sourceFamily (s : Set ℝ) (hs : MeasurableSet s) (p : SourceIndex H) :
    P s hs (sourceFamily P V p) = sourceFamily P V (⟨s ∩ p.1.1, hs.inter p.1.2⟩, p.2) := by
  simp only [sourceFamily]
  rw [← ContinuousLinearMap.comp_apply, ← h.isSpectralMeasure.inter]

variable {K₂ : Type*} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {P₂ : ∀ s : Set ℝ, MeasurableSet s → K₂ →L[ℂ] K₂} {V₂ : EuclideanSpace ℂ H →L[ℂ] K₂}
  (h₂ : IsMinimalRealization μ P₂ V₂)

include h₂

/-- Two realizations of the same `μ` have the same Gram data on their source families. -/
theorem gram_eq (p q : SourceIndex H) :
    ⟪sourceFamily P V p, sourceFamily P V q⟫_ℂ = ⟪sourceFamily P₂ V₂ p, sourceFamily P₂ V₂ q⟫_ℂ := by
  simp only [sourceFamily]
  rw [h.inner_source, h₂.inner_source]

/-- **The intertwining unitary** between two minimal realizations. -/
noncomputable def unitary : K ≃ₗᵢ[ℂ] K₂ :=
  GramIsometry.toLinearIsometryEquiv (h.gram_eq h₂) h.closure_span_sourceFamily
    h₂.closure_span_sourceFamily

theorem unitary_sourceFamily (p : SourceIndex H) :
    h.unitary h₂ (sourceFamily P V p) = sourceFamily P₂ V₂ p :=
  GramIsometry.toLinearIsometryEquiv_gen _ _ _ p

/-- `U V₁ = V₂` (i.e. `U B₁^* = B₂^*`). -/
theorem unitary_source (ξ : EuclideanSpace ℂ H) : h.unitary h₂ (V ξ) = V₂ ξ := by
  rw [← h.sourceFamily_univ ξ, h.unitary_sourceFamily h₂, h₂.sourceFamily_univ]

/-- `U P₁(E) = P₂(E) U`: the spectral-measure form of `U C₁ = C₂ U`. -/
theorem unitary_intertwines (s : Set ℝ) (hs : MeasurableSet s) (x : K) :
    h.unitary h₂ (P s hs x) = P₂ s hs (h.unitary h₂ x) := by
  have hT : ((h.unitary h₂).toLinearIsometry.toContinuousLinearMap ∘L P s hs) =
      (P₂ s hs ∘L (h.unitary h₂).toLinearIsometry.toContinuousLinearMap) := by
    refine GramIsometry.clm_ext_of_forall_gen h.closure_span_sourceFamily fun p => ?_
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    rw [h.apply_sourceFamily s hs p, h.unitary_sourceFamily h₂, h.unitary_sourceFamily h₂,
      h₂.apply_sourceFamily s hs p]
  have := congrArg (fun T : K →L[ℂ] K₂ => T x) hT
  simpa using this

/-- Any unitary with the two intertwining properties is `unitary`. -/
theorem eq_unitary (U : K ≃ₗᵢ[ℂ] K₂)
    (hP : ∀ (s : Set ℝ) (hs : MeasurableSet s) (x : K), U (P s hs x) = P₂ s hs (U x))
    (hV : ∀ ξ : EuclideanSpace ℂ H, U (V ξ) = V₂ ξ) : U = h.unitary h₂ := by
  refine GramIsometry.linearIsometryEquiv_ext_of_forall_gen h.closure_span_sourceFamily fun p => ?_
  rw [h.unitary_sourceFamily h₂]
  simp only [sourceFamily]
  rw [hP, hV]

/-- **`eq:supp-Naimark-unitary`.**  Two minimal realizations of the same positive tail measure `μ`
are related by a unique unitary `U` with `U P₁(E) = P₂(E) U` for all Borel `E` and `U V₁ = V₂`
(`U B₁^* = B₂^*`). -/
theorem existsUnique_unitary :
    ∃! U : K ≃ₗᵢ[ℂ] K₂,
      (∀ (s : Set ℝ) (hs : MeasurableSet s) (x : K), U (P s hs x) = P₂ s hs (U x)) ∧
      ∀ ξ : EuclideanSpace ℂ H, U (V ξ) = V₂ ξ :=
  ⟨h.unitary h₂, ⟨h.unitary_intertwines h₂, h.unitary_source h₂⟩,
    fun U hU => h.eq_unitary h₂ U hU.1 hU.2⟩

end IsMinimalRealization

/-- **`thm:supp-Naimark-realization`, uniqueness clause, packaged.**  Every minimal realization
of `μ` is related to the canonical one `(K_μ, P_μ, V_μ)` — and any two minimal realizations to each
other — by a unique unitary intertwining the spectral measures and the source maps. -/
theorem naimark_realization_unitary (μ : PositiveTailMeasure H) :
    IsMinimalRealization μ μ.spectralProj μ.embedV ∧
    ∀ {K₁ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
      {P₁ : ∀ s : Set ℝ, MeasurableSet s → K₁ →L[ℂ] K₁} {V₁ : EuclideanSpace ℂ H →L[ℂ] K₁}
      {K₂ : Type*} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
      {P₂ : ∀ s : Set ℝ, MeasurableSet s → K₂ →L[ℂ] K₂} {V₂ : EuclideanSpace ℂ H →L[ℂ] K₂},
      IsMinimalRealization μ P₁ V₁ → IsMinimalRealization μ P₂ V₂ →
      ∃! U : K₁ ≃ₗᵢ[ℂ] K₂,
        (∀ (s : Set ℝ) (hs : MeasurableSet s) (x : K₁), U (P₁ s hs x) = P₂ s hs (U x)) ∧
        ∀ ξ : EuclideanSpace ℂ H, U (V₁ ξ) = V₂ ξ :=
  ⟨μ.isMinimalRealization_canonical, fun h₁ h₂ => h₁.existsUnique_unitary h₂⟩

end OperatorTailMeasure
end RenewalGeometry
