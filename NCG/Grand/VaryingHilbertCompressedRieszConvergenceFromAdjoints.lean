/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AutomaticCircleRieszProjectionStability
import NCG.Grand.RieszProjectionStability
import NCG.Grand.CompressedOperatorNormConvergenceFromAdjoints
import NCG.Grand.FiniteSourceGramConvergence
import NCG.Grand.NearbyProjectionRankStability

/-!
# Riesz convergence for varying-Hilbert operators from adjoint convergence

The non-selfadjoint collectively compact upgrade is combined here with contour stability.
Varying-space strong convergence of an operator family and its adjoints yields norm convergence
of the literal common-carrier compressions, hence norm convergence of circle Riesz operators on
every limiting resolvent contour.  Projected finite-source Gram matrices then converge as well.
A separate theorem records stable range dimension under the minimal idempotence and finite-rank
hypotheses, without imposing symmetry.
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

/-- Strong convergence of a collectively compact family and its adjoints gives convergence of
the compressed Riesz operators on every limiting resolvent circle. -/
theorem compressedOperator_circleRieszProjection_tendsto_of_adjointStrong
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hadjointStrong :
      J.StrongOperatorConverges J
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T))
    (hcompact : J.CollectivelyCompact Tn)
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) := by
  obtain ⟨hTcompact, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_adjointStrong
      Tn T hdense hstrong hadjointStrong hcompact
  refine ⟨hTcompact, hop, ?_⟩
  exact circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
      (J.compressedOperator Tn) T hop center radius hradius hcontour

/-- In addition to compressed operator and Riesz convergence, every finite family of projected
source Gram matrices converges.  No selfadjointness is required. -/
theorem compressedOperator_rieszAndSourceGram_tendsto_of_adjointStrong
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
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Tn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  obtain ⟨hTcompact, hop, hproj⟩ :=
    J.compressedOperator_circleRieszProjection_tendsto_of_adjointStrong
      Tn T hdense hstrong hadjointStrong hcompact center radius hradius hcontour
  exact ⟨hTcompact, hop, hproj,
    NCG.SpectralApproximation.sourceGram_tendsto hproj hsource⟩

/-- Under the standard idempotence and finite-range hypotheses, the Riesz ranges in the previous
theorem have eventually stable dimension.  These assumptions are stated explicitly because this
result also applies to genuinely nonnormal families. -/
theorem compressedOperator_circleRieszProjection_finrank_eventuallyEq_of_adjointStrong
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hadjointStrong :
      J.StrongOperatorConverges J
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T))
    (hcompact : J.CollectivelyCompact Tn)
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hidemSeq : ∀ᶠ n in atTop, IsIdempotentElem
      (circleRieszProjection
        (J.compressedOperator Tn n) center radius).toLinearMap)
    (hidem : IsIdempotentElem
      (circleRieszProjection T center radius).toLinearMap)
    (hfiniteSeq : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection
          (J.compressedOperator Tn n) center radius).toLinearMap))
    [Module.Finite ℂ
      (LinearMap.range (circleRieszProjection T center radius).toLinearMap)] :
    ∀ᶠ n in atTop,
      Module.finrank ℂ
          (LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap) =
        Module.finrank ℂ
          (LinearMap.range
            (circleRieszProjection T center radius).toLinearMap) := by
  have hproj :=
    (J.compressedOperator_circleRieszProjection_tendsto_of_adjointStrong
      Tn T hdense hstrong hadjointStrong hcompact center radius hradius hcontour).2.2
  exact NCG.ProjectionStability.eventually_finrank_range_eq_of_tendsto
    (fun n ↦ circleRieszProjection
      (J.compressedOperator Tn n) center radius)
    (circleRieszProjection T center radius) hproj hidemSeq hidem hfiniteSeq

end NCG.VaryingHilbert.System
