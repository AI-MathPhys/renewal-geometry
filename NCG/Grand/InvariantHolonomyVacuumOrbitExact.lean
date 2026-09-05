/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteLatticeGaugeInvariantDensityExact
import NCG.Grand.PositiveVacuumCyclicityExact

/-!
# Closed physical orbits of invariant holonomy polynomials

This assembles the actual lattice gauge action, normalized Haar averaging,
faithful holonomy matrix coefficients, and the constructed vacuum unitary.
The averaged matrix-entry polynomials and all continuous invariant functions
have the same closed physical vacuum orbit, also after orthogonal centering.

The theorem deliberately names the full matrix-entry polynomial bank. It does
not identify an unspecified or smaller primitive current/plaquette bank with
this bank, nor silently identify a selected closed orbit with a larger ambient
measurable invariant sector.
-/

open MeasureTheory

namespace NCG.InvariantHolonomyVacuumOrbit

open FiniteLatticeGaugeInvariantDensity PositiveVacuumWeightedL2 PositiveVacuumCyclicity

noncomputable section

variable {V E n : Type*} [Fintype V] [Fintype E] [Fintype n] [DecidableEq n]
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (target source : E → V)
variable (rho : G →* Matrix n n ℂ) (hcontinuous : Continuous rho)
variable (hfaithful : Function.Injective rho)
variable (μ : Measure (E → G)) (Omega : (E → G) → ℂ)
variable (hOmega : Measurable Omega) (hnonzero : ∀ᵐ U ∂μ, Omega U ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure μ Omega)]

include hfaithful

/-- The concrete averaged holonomy polynomials saturate the closed physical
orbit of the continuous gauge-invariant algebra. -/
theorem invariant_holonomy_vacuum_orbit :
    closure ((vacuumOrbit μ Omega hOmega hnonzero ∘ gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
    closure (vacuumOrbit μ Omega hOmega hnonzero ''
      {f : C(E → G, ℂ) | ∀ h U, f (gaugeAction G target source h U) = f U}) := by
  simpa only [Set.image_image, Function.comp_def] using
    (closure_vacuumOrbit_image_of_closure_eq μ Omega hOmega hnonzero _ _
      (closure_gaugeAverage_coordinateAlgebra G target source rho hcontinuous hfaithful))

/-- Orthogonal centering of the actual physical vacuum does not change the
equality of the two closed source orbits. -/
theorem centered_invariant_holonomy_vacuum_orbit :
    let vacuum := vacuumOrbit μ Omega hOmega hnonzero (1 : C(E → G, ℂ))
    let P := (Submodule.span ℂ {vacuum})ᗮ.orthogonalProjectionOnto
    closure ((P ∘ vacuumOrbit μ Omega hOmega hnonzero ∘ gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
    closure ((P ∘ vacuumOrbit μ Omega hOmega hnonzero) ''
      {f : C(E → G, ℂ) | ∀ h U, f (gaugeAction G target source h U) = f U}) := by
  dsimp only
  let P := (Submodule.span ℂ
    {vacuumOrbit μ Omega hOmega hnonzero (1 : C(E → G, ℂ))})ᗮ.orthogonalProjectionOnto
  have h := congrArg (fun s => closure (P '' s))
    (invariant_holonomy_vacuum_orbit G target source rho hcontinuous hfaithful
      μ Omega hOmega hnonzero)
  simpa only [closure_image_closure P.continuous, Set.image_image, Function.comp_def, P] using h

end

end NCG.InvariantHolonomyVacuumOrbit
