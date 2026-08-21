/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedNormalRieszOrthogonality
import NCG.Grand.ProjectionRangeConvergence

/-!
# Range convergence for compressed normal Riesz projections

For collectively compact normal varying-Hilbert families, operator-norm convergence of the Riesz
projections and their automatic orthogonality imply bilateral quantitative convergence of their
unit spectral subspaces.
-/

open Complex Filter Topology
open NCG.ResolventStability
open NCG.ProjectionStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Compact normal varying-space convergence gives orthogonal Riesz-projection convergence and
bilateral convergence of the associated unit spectral subspaces. -/
theorem compressedOperator_circleRieszProjection_ranges_tendsto_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      IsStarProjection (circleRieszProjection T center radius) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop, IsStarProjection
        (circleRieszProjection
          (J.compressedOperator Tn n) center radius)) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        (∀ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap →
          ‖x‖ ≤ 1 →
          ∃ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap ∧ ‖x - y‖ < ε) ∧
        (∀ y, y ∈ LinearMap.range
            (circleRieszProjection T center radius).toLinearMap →
          ‖y‖ ≤ 1 →
          ∃ x, x ∈ LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap ∧ ‖y - x‖ < ε) := by
  obtain ⟨hTcompact, hop, hproj⟩ :=
    J.compressedOperator_circleRieszProjection_tendsto_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
        center radius hR.le hcontour
  obtain ⟨hstarLim, hstarSeq⟩ :=
    J.compressedOperator_circleRieszProjection_isStarProjection_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
        center radius hR hcontour
  refine ⟨hTcompact, hop, hstarLim, hproj, hstarSeq, ?_⟩
  exact eventually_unit_ranges_mutually_approximated_of_starProjection_tendsto
    (fun n ↦ circleRieszProjection
      (J.compressedOperator Tn n) center radius)
    (circleRieszProjection T center radius) hproj hstarSeq hstarLim

end NCG.VaryingHilbert.System
