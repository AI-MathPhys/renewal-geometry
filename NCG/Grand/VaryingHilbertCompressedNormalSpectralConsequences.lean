/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedNormalRieszConsequences
import NCG.Grand.VaryingHilbertCompressedNormalRieszConvergence
import NCG.Grand.VaryingHilbertCompressedNormalOperators
import NCG.Grand.CompactNormalEigenspaces

/-!
# Full compressed spectral consequences for normal varying-Hilbert operators

Normality passes to every literal common-carrier compression.  Collective compactness makes those
compressed stages compact and makes the normal limit compact.  The compact-normal eigenspace
theorem therefore supplies Riesz idempotence at every stage and at the limit, removing the last
spectral premise from the normal varying-Hilbert compact-screen pipeline.
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

/-- A collectively compact strongly convergent normal family has all compressed compact-screen
spectral consequences on every positive zero-avoiding limiting resolvent circle. -/
theorem compressedOperator_fullRieszConsequences_of_isStarNormal
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
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
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  have hcompressedCollective := hcompact.compressedOperator J Tn
  have hstageCompact (n : ℕ) :
      IsCompactOperator ((J.compressedOperator Tn n : H →L[ℂ] H) : H → H) := by
    simpa [embeddedOperator, constantSystem] using
      CollectivelyCompact.isCompactOperator_embedded
        (constantSystem ℂ H) hcompressedCollective n
  have hdenseSpectrumSeq : ∀ᶠ n in atTop, Dense
      ((((⨆ μ, Module.End.eigenspace
        (J.compressedOperator Tn n).toLinearMap μ) : Submodule ℂ H) : Set H)) :=
    Filter.Eventually.of_forall fun n ↦
      NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
        (J.compressedOperator Tn n) (hstageCompact n)
          (J.compressedOperator_isStarNormal Tn hnormal n)
  have hdenseSpectrum : Dense
      ((((⨆ μ, Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ H) : Set H)) :=
    NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
      T hTcompact hlimNormal
  exact J.compressedOperator_rieszConsequences_of_isStarNormal_of_dense_eigenspaces
    Tn T hdense hstrong hcompact hnormal hlimNormal center radius hR hzero hcontour
      hdenseSpectrumSeq hdenseSpectrum source sourceLim hsource

end NCG.VaryingHilbert.System
