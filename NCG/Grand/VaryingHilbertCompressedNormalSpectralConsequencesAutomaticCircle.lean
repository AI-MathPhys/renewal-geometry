/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalRieszEigenspace
import NCG.Grand.VaryingHilbertCompressedNormalSpectralConsequences

/-!
# Automatic-circle spectral consequences for compressed normal operators

Compact-normal spectral isolation removes the contour premise from the complete normal
varying-Hilbert spectral approximation package around any nonzero center.
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

/-- Around every nonzero center, collective compactness and normality automatically choose a
zero-avoiding Riesz circle and yield compactness, norm convergence, exact limiting eigenspace
identification, stable multiplicity, and source-Gram convergence. -/
theorem compressedOperator_fullRieszConsequences_automaticCircle_of_isStarNormal
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
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
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
      T hTcompact hlimNormal center hcenter
  have hspectral :=
    J.compressedOperator_fullRieszConsequences_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal center radius hR hzero
        hcontour source sourceLim hsource
  exact ⟨radius, hR, hzero, hcontour, hspectral.1, hrange, hspectral.2⟩

end NCG.VaryingHilbert.System
