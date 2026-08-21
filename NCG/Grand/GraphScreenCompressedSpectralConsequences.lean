/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GraphScreenCompressedResolventNormConvergence
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences

/-!
# Full spectral consequences from compact graph screens

Compact screens for an auxiliary graph-output family transfer collective compactness through a
compatible physical-coordinate projection.  Symmetric strong convergence then yields the full
common-carrier package: compact limit, norm convergence, automatically selected Riesz circles,
eigenspace identification, stable multiplicity, and projected source-Gram convergence.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w v' w' x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace ℂ (Gn n)]

/-- Compact graph screens and symmetric varying-space strong convergence imply the complete
spectral approximation package for the projected physical operators. -/
theorem compressedOperator_fullSpectralConsequences_of_graphScreens_automaticCircle
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[ℂ] Gn n)
    (screen : ℕ → G →L[ℂ] G) (B : ℝ)
    (Pn : ∀ n, Gn n →L[ℂ] Hn n) (P : G →L[ℂ] H)
    (T : H →L[ℂ] H)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs graphTn,
      ‖y - screen R y‖ < ε)
    (hcommute : ∀ n y, J.embedding n (Pn n y) = P (L.embedding n y))
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J
      (fun n ↦ (Pn n).comp (graphTn n)) T)
    (hsymm : ∀ n,
      LinearMap.IsSymmetric ((Pn n).comp (graphTn n)).toLinearMap)
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
      Tendsto
        (J.compressedOperator (fun n ↦ (Pn n).comp (graphTn n)))
        atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator
            (fun n ↦ (Pn n).comp (graphTn n)) n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator
                  (fun n ↦ (Pn n).comp (graphTn n)) n)
                center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator
              (fun n ↦ (Pn n).comp (graphTn n)) n)
            center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  have hprojected :
      J.CollectivelyCompact (fun n ↦ (Pn n).comp (graphTn n)) :=
    L.collectivelyCompact_postcomp_of_compactOperator_screens J
      graphTn screen B Pn P hbounded hcompact htail hcommute
  exact J.compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
    (fun n ↦ (Pn n).comp (graphTn n)) T hdense hstrong hprojected
      hsymm hlimSymm center hcenter source sourceLim hsource

end NCG.VaryingHilbert.System
