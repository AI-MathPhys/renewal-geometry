/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OneShiftResolventSpectralConsequences
import NCG.Grand.CompactScreenSpectralConsequencesFromContour
import NCG.Grand.SpectralGapCircleSelection

/-!
# One-shift spectral consequences from an isolation gap

This closes the contour-selection gap in the one-shift varying-Hilbert compiler.  Instead of
asking a model to choose a radius, prove zero avoidance, and check two endpoints, it asks only
for a positive spectral isolation gap around a nonzero limiting resolvent value.  The circle is
then selected automatically and all compact-screen consequences follow.
-/

open Complex Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- One collectively compact strongly convergent positive resolvent shift, together with a
positive isolation gap around a nonzero value of the limiting resolvent, automatically selects
an admissible Riesz circle and yields convergence, stable multiplicity, and source-Gram
convergence at every chosen positive shift. -/
theorem compressedResolvent_spectralConsequences_of_oneShift_of_spectralGap
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
    (center : ℂ) (gap : ℝ) (hgapPos : 0 < gap) (hcenter : center ≠ 0)
    (hgap : ∀ z ∈ spectrum ℂ (R b), z ≠ center → gap ≤ dist z center)
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) center radius) atTop
        (𝓝 (NCG.ResolventStability.circleRieszProjection
          (R b) center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (R b) center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n) center radius) (v n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) center radius) vlim)) := by
  obtain ⟨radius, hR, hzero, hlimitContour⟩ :=
    NCG.ResolventStability.exists_zeroAvoiding_resolvent_circle_of_spectral_gap
      (R b) center gap hgapPos hcenter hgap
  refine ⟨radius, hR, hzero, hlimitContour, ?_⟩
  have hallStrong : ∀ c, 0 < c →
      J.StrongOperatorConverges J (Rn c) (R c) :=
    haStrong.allPositiveRealResolventShifts J Rn R a haPos hdense
      hbound hstage hlimit
  have hallCompact : ∀ c, 0 < c → J.CollectivelyCompact (Rn c) :=
    haCompact.allPositiveRealResolventShifts J Rn a hbound hstageReversed
  have hbStrong := hallStrong b hbPos
  have hbCompact := hallCompact b hbPos
  have hcompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator (Rn b) n y) atTop (𝓝 (R b y)) :=
    J.compressedOperator_tendsto (Rn b) (R b) hdense hbStrong
  exact NCG.ResolventStability.compactScreen_spectralConsequences_of_zero_avoiding_of_contour
    (J.compressedOperator (Rn b)) (R b)
    (hbCompact.compressedOperator J (Rn b))
    (J.compressedOperator_isSymmetric (Rn b) (hsymm b hbPos))
    (hlimSymm b hbPos) hcompressedStrong center radius hR hzero
    hlimitContour v vlim hv

end NCG.VaryingHilbert.System
