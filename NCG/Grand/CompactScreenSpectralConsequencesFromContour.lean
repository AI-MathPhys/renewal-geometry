/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactScreenSpectralStability

/-!
# Compact-screen consequences from a limiting contour

This is the complex-centered contour form of the compact-screen compiler.  A limiting contour
in the resolvent set is enough: compactness upgrades strong convergence to operator-norm
convergence, and the quantitative Neumann argument then supplies eventual stage contours and
uniform resolvent bounds automatically.
-/

open Complex Filter Topology

noncomputable section

namespace NCG.ResolventStability

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A zero-avoiding limiting resolvent circle implies all compact-screen spectral consequences.
Unlike the endpoint wrapper, this form allows an arbitrary complex center. -/
theorem compactScreen_spectralConsequences_of_zero_avoiding_of_contour
    {ι : Type w}
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hcompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y)))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hlimitContour :
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ Tlim)
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    IsCompactOperator Tlim ∧
      Tendsto (fun n ↦ circleRieszProjection (T n) center radius) atTop
        (𝓝 (circleRieszProjection Tlim center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection (T n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection Tlim center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection (T n) center radius) (v n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection Tlim center radius) vlim)) := by
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound Tlim center radius hlimitContour
  have hop : Tendsto T atTop (𝓝 Tlim) :=
    NCG.VaryingHilbert.System.tendsto_operatorNorm_of_collectivelyCompact_of_symmetric'
      T Tlim hcompact hsymm hlimSymm hstrong
  obtain ⟨N, hN, hstage⟩ := eventually_circle_resolvent_bound_of_tendsto
    T Tlim hop center radius M hM hlimitContour hlimitBound
  have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (T n) := hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hstageBound : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      ‖resolvent (T n) z‖ ≤ N := hstage.mono fun n hn z hz ↦ (hn z hz).2
  exact compactScreen_spectralConsequences_of_zero_avoiding
    T Tlim hcompact hsymm hlimSymm hstrong center radius hR hzero M N hM
      hlimitContour hlimitBound hstageContour hstageBound v vlim hv

end NCG.ResolventStability
