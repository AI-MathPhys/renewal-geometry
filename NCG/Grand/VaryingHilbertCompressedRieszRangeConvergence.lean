/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences
import NCG.Grand.CircleRieszProjectionOrthogonality
import NCG.Grand.AutomaticCircleRieszProjectionStability
import NCG.Grand.ProjectionRangeConvergence

/-!
# Convergence of compressed Riesz spectral subspaces

For a collectively compact symmetric varying-Hilbert family, a limiting resolvent contour makes
the limiting and all sufficiently late circle Riesz operators orthogonal projections.  Their
operator-norm convergence then gives bilateral quantitative convergence of their unit ranges.
-/

open Complex Filter Topology
open NCG.ResolventStability
open NCG.ProjectionStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Compact symmetric varying-space convergence implies orthogonal Riesz-projection convergence
and bilateral convergence of the associated unit spectral subspaces. -/
theorem compressedOperator_circleRieszProjection_ranges_tendsto_of_contour
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      IsStarProjection (circleRieszProjection T center radius) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop, IsStarProjection
        (circleRieszProjection
          (J.compressedOperator Tn n) center radius)) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        (∀ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap →
          ‖x‖ ≤ 1 →
          ∃ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap ∧ ‖x - y‖ < ε) ∧
        (∀ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap →
          ‖y‖ ≤ 1 →
          ∃ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap ∧ ‖y - x‖ < ε) := by
  have hcompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator Tn n y) atTop (𝓝 (T y)) :=
    J.compressedOperator_tendsto Tn T hdense hstrong
  have hcompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator Tn) :=
    hcompact.compressedOperator J Tn
  have hlimitCompact : IsCompactOperator T :=
    hcompressedCompact.isCompactOperator_limit
      (J.compressedOperator Tn) T hcompressedStrong
  have hop : Tendsto (J.compressedOperator Tn) atTop (𝓝 T) :=
    J.compressedOperator_tendsto_operatorNorm
      Tn T hdense hstrong hcompact hsymm hlimSymm
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound T center radius hcontour
  obtain ⟨N, hN, hstage⟩ :=
    eventually_circle_resolvent_bound_of_tendsto
      (J.compressedOperator Tn) T hop center radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ n in atTop,
      ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (J.compressedOperator Tn n) :=
    hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hstageCompact : ∀ n,
      IsCompactOperator (J.compressedOperator Tn n : H → H) := by
    intro n
    simpa [NCG.VaryingHilbert.System.embeddedOperator,
      NCG.VaryingHilbert.constantSystem] using
        NCG.VaryingHilbert.System.CollectivelyCompact.isCompactOperator_embedded
          (NCG.VaryingHilbert.constantSystem ℂ H) hcompressedCompact n
  have hstarLim : IsStarProjection
      (circleRieszProjection T center radius) :=
    circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      T hlimitCompact hlimSymm center radius hR hcontour
  have hstarSeq : ∀ᶠ n in atTop, IsStarProjection
      (circleRieszProjection (J.compressedOperator Tn n) center radius) :=
    hstageContour.mono fun n hn ↦
      circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
        (J.compressedOperator Tn n) (hstageCompact n)
        (J.compressedOperator_isSymmetric Tn hsymm n)
        center radius hR hn
  have hproj : Tendsto
      (fun n ↦ circleRieszProjection
        (J.compressedOperator Tn n) center radius) atTop
      (𝓝 (circleRieszProjection T center radius)) :=
    circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
      (J.compressedOperator Tn) T hop center radius hR.le hcontour
  refine ⟨hlimitCompact, hop, hstarLim, hproj, hstarSeq, ?_⟩
  exact eventually_unit_ranges_mutually_approximated_of_starProjection_tendsto
      (fun n ↦ circleRieszProjection
        (J.compressedOperator Tn n) center radius)
      (circleRieszProjection T center radius) hproj hstarSeq hstarLim

/-- Around any nonzero center, compact symmetric spectral isolation automatically chooses a
Riesz circle, identifies the limiting projection range with the center eigenspace, and yields
orthogonal spectral-subspace convergence for the compressed varying-Hilbert family. -/
theorem compressedOperator_circleRieszProjection_ranges_tendsto_automaticCircle
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (hcenter : center ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      IsStarProjection (circleRieszProjection T center radius) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop, IsStarProjection
        (circleRieszProjection
          (J.compressedOperator Tn n) center radius)) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        (∀ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap →
          ‖x‖ ≤ 1 →
          ∃ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap ∧ ‖x - y‖ < ε) ∧
        (∀ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap →
          ‖y‖ ≤ 1 →
          ∃ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap ∧ ‖y - x‖ < ε) := by
  have hcompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator Tn n y) atTop (𝓝 (T y)) :=
    J.compressedOperator_tendsto Tn T hdense hstrong
  have hcompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator Tn) :=
    hcompact.compressedOperator J Tn
  have hlimitCompact : IsCompactOperator T :=
    hcompressedCompact.isCompactOperator_limit
      (J.compressedOperator Tn) T hcompressedStrong
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
      T hlimitCompact hlimSymm center hcenter
  have hfull :=
    J.compressedOperator_circleRieszProjection_ranges_tendsto_of_contour
      Tn T hdense hstrong hcompact hsymm hlimSymm center radius hR hcontour
  exact ⟨radius, hR, hzero, hcontour, hrange, hfull⟩

end NCG.VaryingHilbert.System

