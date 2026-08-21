/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactScreenSpectralConsequencesFromContour
import NCG.Grand.CompactSymmetricRieszEigenspace
import NCG.Grand.CompressedOperatorNormConvergence

/-!
# Spectral consequences for compressed varying-Hilbert operators

Collective compactness, symmetry, asymptotic density, and varying-space strong convergence are
converted here into the full common-carrier spectral package: compactness of the limit,
operator-norm convergence of the literal compressions, Riesz-projection convergence, stable
finite multiplicity, and convergence of projected source Gram matrices.
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

/-- A zero-avoiding limiting contour gives the complete spectral approximation package for a
collectively compact varying-Hilbert family and its literal common-carrier compressions. -/
theorem compressedOperator_spectralConsequences_of_collectivelyCompact_of_contour
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
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
  have hcompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator Tn n y) atTop (𝓝 (T y)) :=
    J.compressedOperator_tendsto Tn T hdense hstrong
  have hcompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator Tn) :=
    hcompact.compressedOperator J Tn
  have hspectral :=
    compactScreen_spectralConsequences_of_zero_avoiding_of_contour
      (J.compressedOperator Tn) T hcompressedCompact
      (J.compressedOperator_isSymmetric Tn hsymm) hlimSymm hcompressedStrong
      center radius hR hzero hcontour source sourceLim hsource
  have hop : Tendsto (J.compressedOperator Tn) atTop (𝓝 T) :=
    J.compressedOperator_tendsto_operatorNorm
      Tn T hdense hstrong hcompact hsymm hlimSymm
  exact ⟨hspectral.1, hop, hspectral.2⟩

/-- Around any nonzero center, compact symmetric spectral isolation automatically chooses a
zero-avoiding Riesz circle and yields the complete varying-Hilbert spectral approximation
package.  The limiting projection range is identified with the center eigenspace. -/
theorem compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (hcenter : center ≠ 0)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      IsCompactOperator T ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
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
  have hspectral :=
    J.compressedOperator_spectralConsequences_of_collectivelyCompact_of_contour
      Tn T hdense hstrong hcompact hsymm hlimSymm center radius hR hzero
        hcontour source sourceLim hsource
  exact ⟨radius, hR, hzero, hcontour, hspectral.1, hrange, hspectral.2⟩

end NCG.VaryingHilbert.System
