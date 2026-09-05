/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalCircleRieszSpectralSubspace
import NCG.Grand.VaryingHilbertCompressedNormalSpectralConsequences

/-!
# Exact spectral subspaces for compressed normal varying-Hilbert operators

Stable Riesz rank for compact normal families is stable total algebraic multiplicity: the limit
and all sufficiently late stage ranges are exactly the sums of the eigenspaces enclosed by the
fixed circle.
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

/-- On a positive zero-avoiding limiting resolvent circle, the limiting Riesz range and every
sufficiently late stage range are exactly the sums of the enclosed eigenspaces. Their total
algebraic multiplicities are eventually equal. -/
theorem compressedOperator_circleRieszProjection_spectralSubspaces_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
          Module.End.eigenspace T.toLinearMap μ ∧
      ∀ᶠ n in atTop,
        LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap =
            ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
              Module.End.eigenspace
                (J.compressedOperator Tn n).toLinearMap μ ∧
        Module.finrank ℂ
            ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
              Module.End.eigenspace
                (J.compressedOperator Tn n).toLinearMap μ) : Submodule ℂ H) =
          Module.finrank ℂ
            ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
              Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ H) := by
  obtain ⟨hTcompact, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
  have hlimitRange :=
    range_circleRieszProjection_eq_iSup_eigenspaces_mem_ball_of_compact_of_isStarNormal
      T hTcompact hlimNormal center radius hR hzero hcontour
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
  have hfull :=
    J.compressedOperator_fullRieszConsequences_of_isStarNormal
      (ι := Unit) Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR hzero hcontour
      (fun _ _ ↦ 0) (fun _ ↦ 0)
      (fun _ ↦ tendsto_const_nhds)
  have hfinrank : ∀ᶠ n in atTop,
      Module.finrank ℂ
          (LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap) =
        Module.finrank ℂ
          (LinearMap.range
            (circleRieszProjection T center radius).toLinearMap) :=
    hfull.2.2.2.1
  refine ⟨hlimitRange, ?_⟩
  filter_upwards [hstageContour, hfinrank] with n hnContour hnRank
  have hstageRange :=
    range_circleRieszProjection_eq_iSup_eigenspaces_mem_ball_of_compact_of_isStarNormal
      (J.compressedOperator Tn n) (hstageCompact n)
      (J.compressedOperator_isStarNormal Tn hnormal n)
      center radius hR hzero hnContour
  refine ⟨hstageRange, ?_⟩
  rw [← hstageRange, ← hlimitRange]
  exact hnRank

end NCG.VaryingHilbert.System
