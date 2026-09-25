/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Vacuum equation from certified accepted-action variations
  (`cor:supp-renewal-einstein`; emergent-spacetime manuscript, supplement;
  partial: the limit identification `eq:supp-einstein-insertion` of
  `thm:supp-renewal-palatini` is a disclosed hypothesis)

The corollary's own argument has three steps, all formalised here:

* **core vanishing**: along the selected cofinal subsequence the realized
  common-action first variations converge to the limiting first variation
  (`htendsto`) and vanish on the determining metric-test core (`hvanish`), so
  the limiting first variation vanishes on the core by uniqueness of limits
  (`limit_variation_vanishes_on_core`);
* **extension to the closure**: the limiting variation is represented as
  `χ ∫ √-g (G + Λ g) k` (`hrep`, the hypothesised `eq:supp-einstein-insertion`)
  with `χ ≠ 0`, and continuity in the declared test topology extends the
  vanishing from the core to its closure (`Set.EqOn.closure`); a dense core
  therefore gives vanishing on every test (`dense_core_extension`);
* **determining panel**: the injective (determining) pairing then gives the
  boxed distributional vacuum equation `G + Λ g = 0`
  (`vacuum_equation_from_certified_variations`).

`vacuum_equation_almost_surely` is the stochastic route: on the almost-sure
subsequence of `prop:supp-physical-test-stationarity` (supplied per path,
together with the pathwise compactness and identification budgets, as
`∀ᵐ ω, ∃ selected …`), the same deterministic argument applies pathwise and
gives `G + Λ g = 0` almost surely.

Not formalised (disclosed): the identification of the limit of each certified
first variation with `eq:supp-einstein-insertion` (the content of
`thm:supp-renewal-palatini`), which enters as the hypothesis `hrep`, and the
mean-square-to-almost-sure subsequence extraction of
`prop:supp-physical-test-stationarity`, which enters through the per-path
existence of the selected subsequence.
-/

open Filter Topology MeasureTheory

namespace RenewalGeometry

/-- Uniqueness of limits: if the realized first variations converge along the
selected subsequence to the limiting variation and vanish on the core, the
limiting variation vanishes on the core. -/
theorem limit_variation_vanishes_on_core {MetricTest : Type*}
    (finiteVar : ℕ → MetricTest → ℝ) (limitVar : MetricTest → ℝ) (selected : ℕ → ℕ)
    (htendsto : ∀ k, Tendsto (fun n => finiteVar (selected n) k) atTop (𝓝 (limitVar k)))
    (core : Set MetricTest)
    (hvanish : ∀ k ∈ core, Tendsto (fun n => finiteVar (selected n) k) atTop (𝓝 0)) :
    ∀ k ∈ core, limitVar k = 0 := fun k hk =>
  tendsto_nhds_unique (htendsto k) (hvanish k hk)

/-- Continuity in the declared test topology extends vanishing from a dense
determining core to every test. -/
theorem dense_core_extension {MetricTest : Type*} [TopologicalSpace MetricTest]
    (Φ : MetricTest → ℝ) (hcont : Continuous Φ) (core : Set MetricTest) (hcore : Dense core)
    (hzero : ∀ k ∈ core, Φ k = 0) : Φ = 0 := by
  have hEq : Set.EqOn Φ (fun _ => (0 : ℝ)) core := fun k hk => hzero k hk
  have hcl : Set.EqOn Φ (fun _ => (0 : ℝ)) (closure core) :=
    hEq.closure hcont continuous_const
  funext k
  exact hcl (hcore k)

/-- `cor:supp-renewal-einstein` (deterministic route, with the limit
identification `eq:supp-einstein-insertion` as hypothesis `hrep`): vanishing
realized common-action variations on a dense determining metric-test core,
along the selected cofinal subsequence on which the certified first
variations converge, imply the distributional vacuum equation
`G + Λ g = 0`, provided `χ ≠ 0`, the insertion is continuous in the declared
test topology, and the test panel is determining (injective pairing). -/
theorem vacuum_equation_from_certified_variations {MetricTest TensorDist : Type*}
    [TopologicalSpace MetricTest] [AddCommGroup TensorDist] [Module ℝ TensorDist]
    (finiteVar : ℕ → MetricTest → ℝ) (limitVar : MetricTest → ℝ) (selected : ℕ → ℕ)
    (htendsto : ∀ k, Tendsto (fun n => finiteVar (selected n) k) atTop (𝓝 (limitVar k)))
    (core : Set MetricTest) (hcore : Dense core)
    (hvanish : ∀ k ∈ core, Tendsto (fun n => finiteVar (selected n) k) atTop (𝓝 0))
    (χ : ℝ) (hχ : χ ≠ 0) (metricPair : TensorDist →ₗ[ℝ] (MetricTest → ℝ))
    (hdetermining : Function.Injective metricPair) (einsteinPlusCosmological : TensorDist)
    (hrep : ∀ k, limitVar k = χ * metricPair einsteinPlusCosmological k)
    (hcont : Continuous (metricPair einsteinPlusCosmological)) :
    einsteinPlusCosmological = 0 := by
  have hcore0 := limit_variation_vanishes_on_core finiteVar limitVar selected htendsto core hvanish
  have hzero : ∀ k ∈ core, metricPair einsteinPlusCosmological k = 0 := by
    intro k hk
    have h := hcore0 k hk
    rw [hrep k] at h
    exact (mul_eq_zero.mp h).resolve_left hχ
  have hall : metricPair einsteinPlusCosmological = 0 :=
    dense_core_extension _ hcont core hcore hzero
  apply hdetermining
  rw [hall, map_zero]

/-- Stochastic route of `cor:supp-renewal-einstein`: if for almost every path
the almost-sure subsequence of `prop:supp-physical-test-stationarity` (on
which the realized variations vanish on the countable core) also carries the
pathwise compactness and identification budgets (convergence of the
certified first variations to a limit represented by
`eq:supp-einstein-insertion`), then `G + Λ g = 0` almost surely. -/
theorem vacuum_equation_almost_surely {Ω MetricTest TensorDist : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [TopologicalSpace MetricTest] [AddCommGroup TensorDist]
    [Module ℝ TensorDist]
    (finiteVar : Ω → ℕ → MetricTest → ℝ) (limitVar : Ω → MetricTest → ℝ)
    (core : Set MetricTest) (hcore : Dense core)
    (χ : ℝ) (hχ : χ ≠ 0) (metricPair : TensorDist →ₗ[ℝ] (MetricTest → ℝ))
    (hdetermining : Function.Injective metricPair) (einsteinPlusCosmological : Ω → TensorDist)
    (hcont : ∀ ω, Continuous (metricPair (einsteinPlusCosmological ω)))
    (hrep : ∀ ω k, limitVar ω k = χ * metricPair (einsteinPlusCosmological ω) k)
    (hsub : ∀ᵐ ω ∂μ, ∃ selected : ℕ → ℕ,
      (∀ k, Tendsto (fun n => finiteVar ω (selected n) k) atTop (𝓝 (limitVar ω k))) ∧
      ∀ k ∈ core, Tendsto (fun n => finiteVar ω (selected n) k) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, einsteinPlusCosmological ω = 0 := by
  filter_upwards [hsub] with ω hω
  obtain ⟨selected, htendsto, hvanish⟩ := hω
  exact vacuum_equation_from_certified_variations (finiteVar ω) (limitVar ω) selected htendsto
    core hcore hvanish χ hχ metricPair hdetermining (einsteinPlusCosmological ω) (hrep ω)
    (hcont ω)

end RenewalGeometry
