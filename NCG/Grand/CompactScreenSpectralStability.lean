/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactLimit
import NCG.Grand.FiniteSourceGramConvergence
import NCG.Grand.NearbyProjectionRankStability
import NCG.Grand.CompactCircleRieszProjection

/-!
# Abstract spectral consequences of compact screens

This file assembles the reusable analytic output of a successful compact-screen argument.  Once
collective compactness and symmetric strong convergence have been established, the limiting
operator is compact, the circle Riesz projections converge in operator norm, isolated spectral
multiplicity is eventually stable, and every finite projected source Gram matrix converges.
-/

open Filter Topology Complex

noncomputable section

namespace NCG.ResolventStability

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact-screen Riesz convergence theorem with compactness of the limit derived, rather
than assumed, from collective compactness. -/
theorem circleRieszProjection_tendsto_of_collectivelyCompactStrong
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hcompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y)))
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit :
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ Tlim)
    (hlimit_bound :
      ∀ z ∈ Metric.sphere center radius, ‖resolvent Tlim z‖ ≤ M)
    (hstage_unit :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (T n))
    (hstage_bound :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        ‖resolvent (T n) z‖ ≤ N) :
    Tendsto (fun n ↦ circleRieszProjection (T n) center radius) atTop
      (𝓝 (circleRieszProjection Tlim center radius)) := by
  exact circleRieszProjection_tendsto_of_collectivelyCompact
    T Tlim hcompact (hcompact.isCompactOperator_limit T Tlim hstrong)
      hsymm hlim_symm hstrong center radius hradius M N hM
      hlimit_unit hlimit_bound hstage_unit hstage_bound

/-- All abstract spectral conclusions needed after a compact-screen estimate, bundled in one
theorem.  The remaining hypotheses concern contour separation/idempotence and finite rank, which
are deliberately left to the concrete model. -/
theorem compactScreen_spectralConsequences
    {ι : Type w}
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hcompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y)))
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit :
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ Tlim)
    (hlimit_bound :
      ∀ z ∈ Metric.sphere center radius, ‖resolvent Tlim z‖ ≤ M)
    (hstage_unit :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (T n))
    (hstage_bound :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        ‖resolvent (T n) z‖ ≤ N)
    (hidem_seq : ∀ᶠ n in atTop,
      IsIdempotentElem
        (circleRieszProjection (T n) center radius).toLinearMap)
    (hidem : IsIdempotentElem
      (circleRieszProjection Tlim center radius).toLinearMap)
    (hfinite_seq : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection (T n) center radius).toLinearMap))
    [Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection Tlim center radius).toLinearMap)]
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
  have hlim_compact := hcompact.isCompactOperator_limit T Tlim hstrong
  have hproj := circleRieszProjection_tendsto_of_collectivelyCompactStrong
    T Tlim hcompact hsymm hlim_symm hstrong center radius hradius M N hM
      hlimit_unit hlimit_bound hstage_unit hstage_bound
  refine ⟨hlim_compact, hproj, ?_, ?_⟩
  · exact NCG.ProjectionStability.eventually_finrank_range_eq_of_tendsto
      (fun n ↦ circleRieszProjection (T n) center radius)
      (circleRieszProjection Tlim center radius)
      hproj hidem_seq hidem hfinite_seq
  · exact NCG.SpectralApproximation.sourceGram_tendsto hproj hv

/-- For a positive contour whose closed disc avoids zero, collective compactness and symmetry
automatically discharge every Riesz idempotence and finite-rank premise in the abstract compact-
screen spectral theorem. -/
theorem compactScreen_spectralConsequences_of_zero_avoiding
    {ι : Type w}
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hcompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y)))
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit :
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ Tlim)
    (hlimit_bound :
      ∀ z ∈ Metric.sphere center radius, ‖resolvent Tlim z‖ ≤ M)
    (hstage_unit :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (T n))
    (hstage_bound :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        ‖resolvent (T n) z‖ ≤ N)
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
  have hstageCompact : ∀ n, IsCompactOperator (T n : H → H) := by
    intro n
    simpa [NCG.VaryingHilbert.System.embeddedOperator,
      NCG.VaryingHilbert.constantSystem] using
        NCG.VaryingHilbert.System.CollectivelyCompact.isCompactOperator_embedded
          (NCG.VaryingHilbert.constantSystem ℂ H) hcompact n
  have hlimCompact : IsCompactOperator (Tlim : H → H) :=
    hcompact.isCompactOperator_limit T Tlim hstrong
  have hidemSeq : ∀ᶠ n in atTop,
      IsIdempotentElem
        (circleRieszProjection (T n) center radius).toLinearMap :=
    hstage_unit.mono fun n hn ↦
      circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        (T n) (hstageCompact n) (hsymm n) center radius hR hn
  have hfiniteSeq : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection (T n) center radius).toLinearMap) :=
    hstage_unit.mono fun n hn ↦
      finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
        (T n) (hstageCompact n) (hsymm n) center radius hR hzero hn
  have hidemLim : IsIdempotentElem
      (circleRieszProjection Tlim center radius).toLinearMap :=
    circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
      Tlim hlimCompact hlim_symm center radius hR hlimit_unit
  letI : Module.Finite ℂ
      (LinearMap.range
        (circleRieszProjection Tlim center radius).toLinearMap) :=
    finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
      Tlim hlimCompact hlim_symm center radius hR hzero hlimit_unit
  exact compactScreen_spectralConsequences
    T Tlim hcompact hsymm hlim_symm hstrong center radius hR.le M N hM
      hlimit_unit hlimit_bound hstage_unit hstage_bound hidemSeq hidemLim
        hfiniteSeq v vlim hv

end NCG.ResolventStability
