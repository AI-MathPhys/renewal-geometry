/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactResolventShiftUpgrade
import NCG.Grand.CompactScreenSpectralStability

/-!
# Spectral consequences from one collectively compact resolvent shift

Strong convergence and collective compactness at one positive shift propagate to every positive
shift.  At any chosen shift, compression to the common Hilbert space then feeds directly into
the compact-screen spectral theorem: the limit resolvent is compact, circle Riesz projections
converge, their finite ranks eventually agree, and all finite projected source Gram matrices
converge.
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

/-- One collectively compact, strongly convergent positive resolvent shift implies the full
compact spectral-screen conclusion at any positive shift and any real-centered circle avoiding
zero whose two endpoints lie in the limiting resolvent set. -/
theorem compressedResolvent_spectralConsequences_of_oneShift
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
    (center radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius)
    (hlimitLeft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ (R b))
    (hlimitRight : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ (R b))
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    IsCompactOperator (R b) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (center : ℂ) radius) atTop
        (𝓝 (NCG.ResolventStability.circleRieszProjection
          (R b) (center : ℂ) radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n) (center : ℂ) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (R b) (center : ℂ) radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n) (center : ℂ) radius) (v n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (center : ℂ) radius) vlim)) := by
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
  exact NCG.ResolventStability.compactScreen_spectralConsequences_of_zero_avoiding_of_endpoints
    (J.compressedOperator (Rn b)) (R b)
    (hbCompact.compressedOperator J (Rn b))
    (J.compressedOperator_isSymmetric (Rn b) (hsymm b hbPos))
    (hlimSymm b hbPos) hcompressedStrong center radius hR hzero
    hlimitLeft hlimitRight v vlim hv

end NCG.VaryingHilbert.System
