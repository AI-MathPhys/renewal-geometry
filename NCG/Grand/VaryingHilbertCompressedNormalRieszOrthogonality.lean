/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedNormalSpectralConsequences
import NCG.Grand.CompactNormalCircleRieszProjectionOrthogonality
import NCG.Grand.ContourResolventBounds

/-!
# Orthogonality of compressed normal Riesz projections

For a collectively compact convergent normal varying-Hilbert family, the limiting circle Riesz
operator and every sufficiently late compressed circle Riesz operator are orthogonal projections.
Stage contour separation follows automatically from compressed operator-norm convergence.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- The limiting and eventual compressed circle Riesz operators of a collectively compact normal
family are orthogonal projections. -/
theorem compressedOperator_circleRieszProjection_isStarProjection_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsStarProjection (circleRieszProjection T center radius) ∧
      ∀ᶠ n in atTop, IsStarProjection
        (circleRieszProjection (J.compressedOperator Tn n) center radius) := by
  obtain ⟨hTcompact, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
  have hlimProjection :=
    circleRieszProjection_isStarProjection_of_compact_of_isStarNormal
      T hTcompact hlimNormal center radius hR hcontour
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound T center radius hcontour
  obtain ⟨N, hN, hstage⟩ := eventually_circle_resolvent_bound_of_tendsto
    (J.compressedOperator Tn) T hop center radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (J.compressedOperator Tn n) :=
    hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hcompressedCollective := hcompact.compressedOperator J Tn
  have hstageCompact (n : ℕ) :
      IsCompactOperator ((J.compressedOperator Tn n : H →L[ℂ] H) : H → H) := by
    simpa [embeddedOperator, constantSystem] using
      CollectivelyCompact.isCompactOperator_embedded
        (constantSystem ℂ H) hcompressedCollective n
  refine ⟨hlimProjection, ?_⟩
  filter_upwards [hstageContour] with n hnContour
  exact circleRieszProjection_isStarProjection_of_compact_of_isStarNormal
    (J.compressedOperator Tn n) (hstageCompact n)
      (J.compressedOperator_isStarNormal Tn hnormal n)
      center radius hR hnContour

end NCG.VaryingHilbert.System
