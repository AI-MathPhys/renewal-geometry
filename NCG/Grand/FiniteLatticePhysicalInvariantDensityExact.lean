/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InvariantHolonomyVacuumOrbitExact
import NCG.Grand.PhysicalGaugeInvariantCyclicityExact

/-!
# Full physical density of averaged finite-lattice matrix polynomials

For an invariant reference measure and nonvanishing invariant vacuum, the
concrete matrix-entry bank is cyclic in the full measurable invariant space.
This does not identify a smaller primitive current/plaquette bank with that
matrix-entry bank or select additional topological sectors.
-/

open MeasureTheory

namespace NCG.FiniteLatticePhysicalInvariantDensity

open FiniteLatticeGaugeInvariantDensity PositiveVacuumWeightedL2 PositiveVacuumCyclicity
open CompactGaugeInvariantL2Density CompactGroupInvariantProjection

noncomputable section

variable {V E n : Type*} [Fintype V] [Fintype E] [Fintype n] [DecidableEq n]
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (target source : E → V)
variable (rho : G →* Matrix n n ℂ) (hcontinuous : Continuous rho)
variable (hfaithful : Function.Injective rho)
variable (ν : Measure (E → G)) (Omega : (E → G) → ℂ)
variable (hOmega : Measurable Omega) (hnonzero : ∀ᵐ U ∂ν, Omega U ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure ν Omega)] [(vacuumMeasure ν Omega).Regular]
variable (hpres : ∀ h, MeasurePreserving (gaugeAction G target source h) ν ν)
variable (hinvariant : ∀ h, (fun U => Omega (gaugeAction G target source h U)) =ᵐ[ν] Omega)

include hfaithful hinvariant in
/-- The right-hand side is the full independently defined physical fixed space. -/
theorem closure_holonomy_vacuumOrbit_eq_fixedSet :
    closure ((vacuumOrbit ν Omega hOmega hnonzero ∘ gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      fixedSet (pullback (gaugeAction G target source) ν hpres) := by
  rw [InvariantHolonomyVacuumOrbit.invariant_holonomy_vacuum_orbit
    G target source rho hcontinuous hfaithful ν Omega hOmega hnonzero]
  exact PhysicalGaugeInvariantCyclicity.closure_invariant_vacuumOrbit_eq_fixedSet
    (gaugeAction G target source) (continuous_gaugeAction G target source)
    ν Omega hOmega hnonzero hpres hinvariant (gaugeAction_mul G target source)
    (rightHaarProbability (V → G))

include hfaithful hinvariant in
/-- The concrete centered matrix-entry bank is cyclic in the full neutral
physical invariant space, with no closure-based definition of that space. -/
theorem closure_centered_holonomy_vacuumOrbit_eq_neutral :
    let vacuum := vacuumOrbit ν Omega hOmega hnonzero (1 : C(E → G, ℂ))
    let P := (Submodule.span ℂ {vacuum})ᗮ.starProjection
    closure ((P ∘ vacuumOrbit ν Omega hOmega hnonzero ∘ gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      fixedSet (pullback (gaugeAction G target source) ν hpres) ∩
        ((Submodule.span ℂ {vacuum})ᗮ : Set (Lp ℂ 2 ν)) := by
  dsimp only
  have h := InvariantVacuumOrthogonalCentering.closure_centered_fixed_eq_inter
    (pullback (gaugeAction G target source) ν hpres)
    (vacuumOrbit ν Omega hOmega hnonzero (1 : C(E → G, ℂ)))
    (PhysicalGaugeInvariantCyclicity.vacuum_mem_fixedSet
      (gaugeAction G target source) (continuous_gaugeAction G target source)
      ν Omega hOmega hnonzero hpres hinvariant (gaugeAction_mul G target source)
      (rightHaarProbability (V → G)))
    _ (closure_holonomy_vacuumOrbit_eq_fixedSet G target source rho hcontinuous
      hfaithful ν Omega hOmega hnonzero hpres hinvariant)
  simpa [Set.image_image, Function.comp_def, fixedSet,
    InvariantVacuumOrthogonalCentering.fixedSubmodule] using h

end

end NCG.FiniteLatticePhysicalInvariantDensity
