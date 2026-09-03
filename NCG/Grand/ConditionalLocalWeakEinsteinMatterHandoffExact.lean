/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Conditional local weak Einstein--matter handoff

This module isolates the genuine limit-passage statement in
`thm:Einstein-handoff`.  The six loaded regulator packets in that theorem are
represented by convergence of each finite first-variation sector and by the
vanishing common-action and Ward defects along the selected cofinal
subsequence.  No limiting Euler equation is assumed: it is obtained by
uniqueness of limits.  Determining matter and metric test panels then upgrade
the weak identities to distributional scalar and Einstein equations.
-/

open Filter Topology

noncomputable section

namespace NCG.ConditionalLocalWeakEinsteinMatterHandoff

/-- Finite-regulator first variations on matter, metric, and Ward test panels. -/
structure FiniteVariations (MatterTest MetricTest WardTest : Type*) where
  matterKinetic : ℕ → MatterTest → ℝ
  matterGauge : ℕ → MatterTest → ℝ
  matterPotential : ℕ → MatterTest → ℝ
  matterCounterterm : ℕ → MatterTest → ℝ
  metricGravity : ℕ → MetricTest → ℝ
  metricRenormalizedStress : ℕ → MetricTest → ℝ
  ward : ℕ → WardTest → ℝ

/-- The corresponding local limiting first variations. -/
structure LimitVariations (MatterTest MetricTest WardTest : Type*) where
  matterKinetic : MatterTest → ℝ
  matterGauge : MatterTest → ℝ
  matterPotential : MatterTest → ℝ
  matterCounterterm : MatterTest → ℝ
  metricGravity : MetricTest → ℝ
  metricRenormalizedStress : MetricTest → ℝ
  ward : WardTest → ℝ

/-- Analytic output of the six regulator hypotheses (V1)--(V6): all sector
variations converge along one selected cofinal subsequence, while the complete
common-action and coherent-Ward residuals vanish. -/
structure RegulatorPacket (MatterTest MetricTest WardTest : Type*)
    (finite : FiniteVariations MatterTest MetricTest WardTest)
    (limit : LimitVariations MatterTest MetricTest WardTest) where
  selected : ℕ → ℕ
  selected_strictMono : StrictMono selected
  matterKinetic_tendsto : ∀ ψ, Tendsto
    (fun n => finite.matterKinetic (selected n) ψ) atTop
      (𝓝 (limit.matterKinetic ψ))
  matterGauge_tendsto : ∀ ψ, Tendsto
    (fun n => finite.matterGauge (selected n) ψ) atTop
      (𝓝 (limit.matterGauge ψ))
  matterPotential_tendsto : ∀ ψ, Tendsto
    (fun n => finite.matterPotential (selected n) ψ) atTop
      (𝓝 (limit.matterPotential ψ))
  matterCounterterm_tendsto : ∀ ψ, Tendsto
    (fun n => finite.matterCounterterm (selected n) ψ) atTop
      (𝓝 (limit.matterCounterterm ψ))
  metricGravity_tendsto : ∀ k, Tendsto
    (fun n => finite.metricGravity (selected n) k) atTop
      (𝓝 (limit.metricGravity k))
  metricRenormalizedStress_tendsto : ∀ k, Tendsto
    (fun n => finite.metricRenormalizedStress (selected n) k) atTop
      (𝓝 (limit.metricRenormalizedStress k))
  ward_tendsto : ∀ η, Tendsto
    (fun n => finite.ward (selected n) η) atTop (𝓝 (limit.ward η))
  matterDefect : ℕ → MatterTest → ℝ
  metricDefect : ℕ → MetricTest → ℝ
  wardDefect : ℕ → WardTest → ℝ
  finiteMatterVariation : ∀ n ψ,
    finite.matterKinetic (selected n) ψ +
        finite.matterGauge (selected n) ψ +
        finite.matterPotential (selected n) ψ +
        finite.matterCounterterm (selected n) ψ = matterDefect n ψ
  finiteMetricVariation : ∀ n k,
    finite.metricGravity (selected n) k +
        finite.metricRenormalizedStress (selected n) k = metricDefect n k
  finiteWardVariation : ∀ n η,
    finite.ward (selected n) η = wardDefect n η
  matterDefect_tendsto_zero : ∀ ψ,
    Tendsto (fun n => matterDefect n ψ) atTop (𝓝 0)
  metricDefect_tendsto_zero : ∀ k,
    Tendsto (fun n => metricDefect n k) atTop (𝓝 0)
  wardDefect_tendsto_zero : ∀ η,
    Tendsto (fun n => wardDefect n η) atTop (𝓝 0)

/-- The limiting common-action variation furnished by the regulator packet. -/
structure CommonActionVariation (MatterTest MetricTest WardTest : Type*) where
  matter : MatterTest → ℝ
  metric : MetricTest → ℝ
  ward : WardTest → ℝ
  matter_stationary : matter = 0
  metric_stationary : metric = 0
  ward_stationary : ward = 0

private theorem matter_limit_zero
    {MatterTest MetricTest WardTest : Type*}
    {finite : FiniteVariations MatterTest MetricTest WardTest}
    {limit : LimitVariations MatterTest MetricTest WardTest}
    (P : RegulatorPacket MatterTest MetricTest WardTest finite limit)
    (ψ : MatterTest) :
    limit.matterKinetic ψ + limit.matterGauge ψ +
        limit.matterPotential ψ + limit.matterCounterterm ψ = 0 := by
  have hlim := (((P.matterKinetic_tendsto ψ).add
    (P.matterGauge_tendsto ψ)).add
      (P.matterPotential_tendsto ψ)).add
        (P.matterCounterterm_tendsto ψ)
  have hdef : Tendsto
      (fun n => finite.matterKinetic (P.selected n) ψ +
        finite.matterGauge (P.selected n) ψ +
        finite.matterPotential (P.selected n) ψ +
        finite.matterCounterterm (P.selected n) ψ) atTop (𝓝 0) :=
    (P.matterDefect_tendsto_zero ψ).congr'
      (Filter.Eventually.of_forall fun n => (P.finiteMatterVariation n ψ).symm)
  exact tendsto_nhds_unique hlim hdef

private theorem metric_limit_zero
    {MatterTest MetricTest WardTest : Type*}
    {finite : FiniteVariations MatterTest MetricTest WardTest}
    {limit : LimitVariations MatterTest MetricTest WardTest}
    (P : RegulatorPacket MatterTest MetricTest WardTest finite limit)
    (k : MetricTest) :
    limit.metricGravity k + limit.metricRenormalizedStress k = 0 := by
  have hlim := (P.metricGravity_tendsto k).add
    (P.metricRenormalizedStress_tendsto k)
  have hdef : Tendsto
      (fun n => finite.metricGravity (P.selected n) k +
        finite.metricRenormalizedStress (P.selected n) k) atTop (𝓝 0) :=
    (P.metricDefect_tendsto_zero k).congr'
      (Filter.Eventually.of_forall fun n => (P.finiteMetricVariation n k).symm)
  exact tendsto_nhds_unique hlim hdef

private theorem ward_limit_zero
    {MatterTest MetricTest WardTest : Type*}
    {finite : FiniteVariations MatterTest MetricTest WardTest}
    {limit : LimitVariations MatterTest MetricTest WardTest}
    (P : RegulatorPacket MatterTest MetricTest WardTest finite limit)
    (η : WardTest) : limit.ward η = 0 := by
  have hdef : Tendsto (fun n => finite.ward (P.selected n) η) atTop (𝓝 0) :=
    (P.wardDefect_tendsto_zero η).congr'
      (Filter.Eventually.of_forall fun n => (P.finiteWardVariation n η).symm)
  exact tendsto_nhds_unique (P.ward_tendsto η) hdef

/-- **Conditional local weak Einstein--matter handoff.**  Vanishing finite
common-action and Ward defects pass to the local limit.  A determining metric
panel and the stress first-variation normalization upgrade the weak metric
identity to `2χ (G + Λg) = T`; a determining scalar panel upgrades the weak
matter identity to the scalar Euler equation; and the limiting Ward identity
gives distributional stress conservation. -/
theorem conditional_local_weak_Einstein_matter_handoff
    {MatterTest MetricTest WardTest ScalarDist TensorDist : Type*}
    [AddCommGroup ScalarDist] [Module ℝ ScalarDist]
    [AddCommGroup TensorDist] [Module ℝ TensorDist]
    (finite : FiniteVariations MatterTest MetricTest WardTest)
    (limit : LimitVariations MatterTest MetricTest WardTest)
    (P : RegulatorPacket MatterTest MetricTest WardTest finite limit)
    (χ : ℝ)
    (scalarPair : ScalarDist →ₗ[ℝ] (MatterTest → ℝ))
    (metricPair : TensorDist →ₗ[ℝ] (MetricTest → ℝ))
    (wardPair : TensorDist →ₗ[ℝ] (WardTest → ℝ))
    (hscalarDetermining : Function.Injective scalarPair)
    (hmetricDetermining : Function.Injective metricPair)
    (scalarEuler : ScalarDist)
    (einsteinPlusCosmological stress : TensorDist)
    (hmatterRepresentation : ∀ ψ,
      scalarPair scalarEuler ψ =
        limit.matterKinetic ψ + limit.matterGauge ψ +
          limit.matterPotential ψ + limit.matterCounterterm ψ)
    (hgravityRepresentation : ∀ k,
      limit.metricGravity k = χ * metricPair einsteinPlusCosmological k)
    (hstressRepresentation : ∀ k,
      limit.metricRenormalizedStress k =
        -(1 / 2 : ℝ) * metricPair stress k)
    (hwardRepresentation : limit.ward = wardPair stress) :
    Nonempty (CommonActionVariation MatterTest MetricTest WardTest) ∧
      scalarEuler = 0 ∧
      (2 * χ) • einsteinPlusCosmological = stress ∧
      wardPair stress = 0 := by
  have hmatter : (fun ψ =>
      limit.matterKinetic ψ + limit.matterGauge ψ +
        limit.matterPotential ψ + limit.matterCounterterm ψ) = 0 := by
    funext ψ
    exact matter_limit_zero P ψ
  have hmetric : (fun k =>
      limit.metricGravity k + limit.metricRenormalizedStress k) = 0 := by
    funext k
    exact metric_limit_zero P k
  have hward : limit.ward = 0 := by
    funext η
    exact ward_limit_zero P η
  let common : CommonActionVariation MatterTest MetricTest WardTest := {
    matter := fun ψ => limit.matterKinetic ψ + limit.matterGauge ψ +
      limit.matterPotential ψ + limit.matterCounterterm ψ
    metric := fun k => limit.metricGravity k + limit.metricRenormalizedStress k
    ward := limit.ward
    matter_stationary := hmatter
    metric_stationary := hmetric
    ward_stationary := hward }
  have hscalarPair : scalarPair scalarEuler = scalarPair 0 := by
    funext ψ
    rw [hmatterRepresentation ψ]
    simpa using congrFun hmatter ψ
  have hscalar : scalarEuler = 0 := hscalarDetermining hscalarPair
  have hEinsteinPair :
      metricPair ((2 * χ) • einsteinPlusCosmological) = metricPair stress := by
    funext k
    have hk := congrFun hmetric k
    rw [hgravityRepresentation k, hstressRepresentation k] at hk
    have hk' : χ * metricPair einsteinPlusCosmological k +
        -(1 / 2 : ℝ) * metricPair stress k = 0 := by
      simpa using hk
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    linarith
  have hEinstein : (2 * χ) • einsteinPlusCosmological = stress :=
    hmetricDetermining hEinsteinPair
  have hconservation : wardPair stress = 0 := by
    rw [← hwardRepresentation, hward]
  exact ⟨⟨common⟩, hscalar, hEinstein, hconservation⟩

end NCG.ConditionalLocalWeakEinsteinMatterHandoff
