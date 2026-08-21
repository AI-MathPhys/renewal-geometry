/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactResolventShiftPropagation
import NCG.Grand.PositiveRealResolventShiftPropagation
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences

/-!
# Full one-shift resolvent spectral consequences with automatic circles

One collectively compact strongly convergent positive resolvent shift propagates to every
positive shift.  The generic compressed spectral compiler then returns compactness of the limit,
literal norm-resolvent convergence, an automatically selected Riesz circle, eigenspace
identification, stable multiplicity, and convergence of projected source Gram matrices.
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

/-- One compact strongly convergent resolvent shift gives the full compressed spectral package
at every selected positive shift and every nonzero spectral center. -/
theorem compressedResolvent_fullSpectralConsequences_of_oneShift_automaticCircle
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Rn : ℝ → ∀ n, Hn n →L[ℂ] Hn n) (R : ℝ → H →L[ℂ] H)
    (a : ℝ) (haPos : 0 < a)
    (hdense : J.IsAsymptoticallyDense)
    (haStrong : J.StrongOperatorConverges J (Rn a) (R a))
    (haCompact : J.CollectivelyCompact (Rn a))
    (hbound : ∀ b, 0 < b → ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ a b, 0 < a → 0 < b → ∀ n,
      Rn b n - Rn a n = ((a - b : ℝ) : ℂ) •
        ((Rn b n).comp (Rn a n)))
    (hstageReversed : ∀ b, 0 < b → ∀ n,
      Rn b n = Rn a n + ((a - b : ℝ) : ℂ) •
        ((Rn a n).comp (Rn b n)))
    (hlimit : ∀ a b, 0 < a → 0 < b →
      R a - R b = ((b - a : ℝ) : ℂ) • ((R a).comp (R b)))
    (hsymm : ∀ b, 0 < b → ∀ n,
      LinearMap.IsSymmetric (Rn b n).toLinearMap)
    (hlimSymm : ∀ b, 0 < b → LinearMap.IsSymmetric (R b).toLinearMap)
    (b : ℝ) (hbPos : 0 < b)
    (center : ℂ) (hcenter : center ≠ 0)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (circleRieszProjection (R b) center radius).toLinearMap =
        Module.End.eigenspace (R b).toLinearMap center ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (𝓝 (R b)) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator (Rn b) n) center radius) atTop
        (𝓝 (circleRieszProjection (R b) center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator (Rn b) n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection (R b) center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator (Rn b) n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection (R b) center radius) sourceLim)) := by
  have hallStrong : ∀ c, 0 < c →
      J.StrongOperatorConverges J (Rn c) (R c) :=
    haStrong.allPositiveRealResolventShifts J Rn R a haPos hdense
      hbound hstage hlimit
  have hallCompact : ∀ c, 0 < c → J.CollectivelyCompact (Rn c) :=
    haCompact.allPositiveRealResolventShifts J Rn a hbound hstageReversed
  exact J.compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
    (Rn b) (R b) hdense (hallStrong b hbPos) (hallCompact b hbPos)
      (hsymm b hbPos) (hlimSymm b hbPos) center hcenter
      source sourceLim hsource

end NCG.VaryingHilbert.System
