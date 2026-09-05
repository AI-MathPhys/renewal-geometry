/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedRieszConsequencesFromAdjoints
import NCG.Grand.VaryingHilbertNormalAdjointConvergence

/-!
# Compressed Riesz consequences for normal varying-Hilbert operators

Normality makes adjoint strong convergence automatic.  These wrappers therefore expose the full
compact-screen spectral package directly from normal varying-space convergence, either assuming
Riesz idempotence or deriving it from dense spanning by eigenspaces.
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

/-- Normality removes the adjoint-convergence premise from the idempotent Riesz-consequences
compiler. -/
theorem compressedOperator_rieszConsequences_of_isStarNormal_of_idempotent
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
  have hadjointStrong :=
    hstrong.adjoint_of_isStarNormal J hdense hnormal hlimNormal
  exact J.compressedOperator_rieszConsequences_of_adjointStrong_of_idempotent
    Tn T hdense hstrong hadjointStrong hcompact center radius hR hzero hcontour
      hidemSeq hidem source sourceLim hsource

/-- For normal families, dense spanning by eigenspaces is enough to obtain compactness, norm and
Riesz convergence, stable isolated multiplicity, and finite-source Gram convergence. -/
theorem compressedOperator_rieszConsequences_of_isStarNormal_of_dense_eigenspaces
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
  have hadjointStrong :=
    hstrong.adjoint_of_isStarNormal J hdense hnormal hlimNormal
  exact J.compressedOperator_rieszConsequences_of_adjointStrong_of_dense_eigenspaces
    Tn T hdense hstrong hadjointStrong hcompact center radius hR hzero hcontour
      hdenseSpectrumSeq hdenseSpectrum source sourceLim hsource

end NCG.VaryingHilbert.System
