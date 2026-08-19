/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OneShiftResolventSpectralConsequencesFromGap
import NCG.Grand.CompactSymmetricRieszEigenspace

/-!
# One-shift spectral consequences with automatic contour selection

For symmetric resolvent families, collective compactness at one shift makes the limiting
resolvent compact at every positive shift.  Compact symmetric spectral isolation then chooses
an admissible Riesz circle around any nonzero center automatically.  Thus concrete models no
longer need to supply a radius, endpoint checks, or even a separate spectral-gap certificate.
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

/-- One collectively compact strongly convergent positive resolvent shift automatically gives,
at every chosen positive shift and every nonzero complex center, an admissible Riesz circle,
compactness of the limit resolvent, projection convergence, stable finite multiplicity, and
source-Gram convergence. -/
theorem compressedResolvent_spectralConsequences_of_oneShift_automaticCircle
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
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) center radius).toLinearMap =
        Module.End.eigenspace (R b).toLinearMap center ∧
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
  have hcompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator (Rn b)) :=
    hbCompact.compressedOperator J (Rn b)
  have hlimitCompact : IsCompactOperator (R b) :=
    hcompressedCompact.isCompactOperator_limit
      (J.compressedOperator (Rn b)) (R b) hcompressedStrong
  obtain ⟨radius, hR, hzero, hlimitContour, hlimitRange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
      (R b) hlimitCompact (hlimSymm b hbPos) center hcenter
  have hspectral := compactScreen_spectralConsequences_of_zero_avoiding_of_contour
    (J.compressedOperator (Rn b)) (R b) hcompressedCompact
    (J.compressedOperator_isSymmetric (Rn b) (hsymm b hbPos))
    (hlimSymm b hbPos) hcompressedStrong center radius hR hzero
    hlimitContour v vlim hv
  exact ⟨radius, hR, hzero, hlimitContour, hlimitCompact, hlimitRange, hspectral.2⟩
end NCG.VaryingHilbert.System
