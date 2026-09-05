/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventGraphScreen
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences

/-!
# Full spectral consequences for weak graph resolvents from compact screens

For canonical weak-resolvent graph maps, the common graph-output bound is automatic.  A compact
screen tail therefore gives collective compactness of the physical resolvents, which combines
with symmetric strong convergence to yield compactness of the limit, literal norm-resolvent
convergence, and the complete automatic Riesz-projection package.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w z z' x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]

/-- Compact tails for canonical weak-resolvent graph outputs imply the complete spectral
approximation package for the physical resolvents and their common-carrier compressions. -/
theorem operatorGraphResolvent_fullSpectralConsequences_of_graphScreenTails_automaticCircle
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (Rn : ∀ n, Hn n →L[ℂ] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ cutoff, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)),
      ‖y - screen cutoff y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Rn T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Rn n).toLinearMap)
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
      Tendsto (J.compressedOperator Rn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Rn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator Rn n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Rn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  have hcollective : J.CollectivelyCompact Rn :=
    J.operatorGraphResolvent_collectivelyCompact_of_graphScreenTails
      L Dn An Rn lam hlam hEquation screen hcompact htail hfst
  exact J.compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
    Rn T hdense hstrong hcollective hsymm hlimSymm center hcenter
      source sourceLim hsource

end NCG.VaryingHilbert.System
