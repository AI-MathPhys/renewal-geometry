/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedRieszConvergenceFromAdjoints
import NCG.Grand.CompactCircleRieszProjection
import NCG.Grand.ContourResolventBounds

/-!
# Compressed Riesz consequences from adjoint convergence

This file completes the non-selfadjoint compact-screen pipeline after Riesz idempotence has been
established.  On a positive circle whose closed disc avoids zero, collective compactness makes
every sufficiently late idempotent Riesz operator compact and hence finite-rank.  Thus strong
convergence of an operator family and its adjoints gives, in one interface, compactness of the
limit, operator-norm convergence of the literal compressions, Riesz convergence, stability of
the Riesz-range dimension, and convergence of finite-source Gram matrices.

A second interface replaces the explicit idempotence hypotheses by dense spanning of the common-
carrier operators by their eigenspaces.  This isolates the only genuinely spectral input still
needed for compact normal operators beyond the current compact self-adjoint mathlib theorem.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Once the limiting and eventual Riesz operators are idempotent, collective compactness and
strong convergence of both operators and adjoints automatically give finite-rank stability and
all finite-source spectral consequences. -/
theorem compressedOperator_rieszConsequences_of_adjointStrong_of_idempotent
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hadjointStrong :
      J.StrongOperatorConverges J
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T))
    (hcompact : J.CollectivelyCompact Tn)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hidemSeq : ∀ᶠ n in atTop, IsIdempotentElem
      (circleRieszProjection
        (J.compressedOperator Tn n) center radius).toLinearMap)
    (hidem : IsIdempotentElem
      (circleRieszProjection T center radius).toLinearMap)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator Tn n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Tn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  obtain ⟨hTcompact, hop, hproj⟩ :=
    J.compressedOperator_circleRieszProjection_tendsto_of_adjointStrong
      Tn T hdense hstrong hadjointStrong hcompact center radius hR.le hcontour
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound T center radius hcontour
  obtain ⟨N, hN, hstage⟩ := eventually_circle_resolvent_bound_of_tendsto
    (J.compressedOperator Tn) T hop center radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (J.compressedOperator Tn n) :=
    hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hcompressedCompact := hcompact.compressedOperator J Tn
  have hstageCompact (n : ℕ) :
      IsCompactOperator ((J.compressedOperator Tn n : H →L[ℂ] H) : H → H) := by
    simpa [embeddedOperator, constantSystem] using
      CollectivelyCompact.isCompactOperator_embedded
        (constantSystem ℂ H) hcompressedCompact n
  have hfiniteSeq : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection
          (J.compressedOperator Tn n) center radius).toLinearMap) := by
    filter_upwards [hstageContour, hidemSeq] with n hnContour hnIdem
    exact finiteDimensional_range_of_compact_idempotent
      (circleRieszProjection (J.compressedOperator Tn n) center radius)
      (circleRieszProjection_isCompactOperator
        (J.compressedOperator Tn n) (hstageCompact n)
          center radius hR hzero hnContour)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp hnIdem)
  letI : Module.Finite ℂ
      (LinearMap.range (circleRieszProjection T center radius).toLinearMap) :=
    finiteDimensional_range_of_compact_idempotent
      (circleRieszProjection T center radius)
      (circleRieszProjection_isCompactOperator
        T hTcompact center radius hR hzero hcontour)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp hidem)
  have hrank := NCG.ProjectionStability.eventually_finrank_range_eq_of_tendsto
    (fun n ↦ circleRieszProjection
      (J.compressedOperator Tn n) center radius)
    (circleRieszProjection T center radius) hproj hidemSeq hidem hfiniteSeq
  exact ⟨hTcompact, hop, hproj, hrank,
    NCG.SpectralApproximation.sourceGram_tendsto hproj hsource⟩

/-- Dense spanning by eigenspaces discharges the only idempotence premises in the preceding
non-selfadjoint spectral-consequences theorem. -/
theorem compressedOperator_rieszConsequences_of_adjointStrong_of_dense_eigenspaces
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hadjointStrong :
      J.StrongOperatorConverges J
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T))
    (hcompact : J.CollectivelyCompact Tn)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hdenseSpectrumSeq : ∀ᶠ n in atTop, Dense
      ((((⨆ μ, Module.End.eigenspace
        (J.compressedOperator Tn n).toLinearMap μ) : Submodule ℂ H) : Set H)))
    (hdenseSpectrum : Dense
      ((((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ H) : Set H)))
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator Tn n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Tn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  obtain ⟨-, hop⟩ := J.compressedOperator_tendsto_operatorNorm_of_adjointStrong
    Tn T hdense hstrong hadjointStrong hcompact
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound T center radius hcontour
  obtain ⟨N, hN, hstage⟩ := eventually_circle_resolvent_bound_of_tendsto
    (J.compressedOperator Tn) T hop center radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (J.compressedOperator Tn n) :=
    hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hidemSeq : ∀ᶠ n in atTop, IsIdempotentElem
      (circleRieszProjection
        (J.compressedOperator Tn n) center radius).toLinearMap := by
    filter_upwards [hdenseSpectrumSeq, hstageContour] with n hnDense hnContour
    exact circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
      (J.compressedOperator Tn n) hnDense center radius hR hnContour
  have hidem : IsIdempotentElem
      (circleRieszProjection T center radius).toLinearMap :=
    circleRieszProjection_isIdempotentElem_of_dense_eigenspaces
      T hdenseSpectrum center radius hR hcontour
  exact J.compressedOperator_rieszConsequences_of_adjointStrong_of_idempotent
    Tn T hdense hstrong hadjointStrong hcompact center radius hR hzero hcontour
      hidemSeq hidem source sourceLim hsource

end NCG.VaryingHilbert.System
