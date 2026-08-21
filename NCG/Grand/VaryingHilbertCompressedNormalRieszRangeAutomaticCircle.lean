/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalRieszEigenspace
import NCG.Grand.VaryingHilbertCompressedNormalRieszRangeConvergence

/-!
# Automatic-circle range convergence for compressed normal operators

For collectively compact normal varying-Hilbert families, compact-normal spectral isolation
automatically supplies a Riesz circle around any nonzero center. Its limiting range is the center
eigenspace, and the stage ranges converge bilaterally as orthogonal spectral subspaces.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Around every nonzero center, a collectively compact normal varying-space family admits an
automatic Riesz circle. The limiting Riesz range is the center eigenspace, and the unit stage and
limit spectral subspaces mutually approximate one another. -/
theorem compressedOperator_circleRieszProjection_ranges_tendsto_automaticCircle_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (hcenter : center ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
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
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
      T hTcompact hlimNormal center hcenter
  have hfull :=
    J.compressedOperator_circleRieszProjection_ranges_tendsto_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal center radius hR hcontour
  exact ⟨radius, hR, hzero, hcontour, hrange, hfull⟩

end NCG.VaryingHilbert.System
