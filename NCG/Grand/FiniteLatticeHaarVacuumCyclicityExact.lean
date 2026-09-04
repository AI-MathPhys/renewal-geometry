/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteLatticePhysicalInvariantDensityExact
import NCG.Grand.FiniteLatticeHaarGaugeMeasureExact

/-!
# Physical invariant cyclicity with the canonical Haar reference measure

This final specialization constructs the invariant reference measure and
derives weighted regularity from compact metrizability. The only vacuum
inputs are measurability, nonvanishing, finite squared mass, and gauge
invariance. The writers remain the explicitly named full matrix-entry bank.
-/

open MeasureTheory

namespace NCG.FiniteLatticeHaarVacuumCyclicity

open FiniteLatticeGaugeInvariantDensity FiniteLatticeHaarGaugeMeasure
open PositiveVacuumWeightedL2 PositiveVacuumCyclicity
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
variable (Omega : (E → G) → ℂ) (hOmega : Measurable Omega)
variable (hnonzero : ∀ᵐ U ∂normalizedHaar (E → G), Omega U ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure (normalizedHaar (E → G)) Omega)]
variable (hinvariant : ∀ h,
  (fun U => Omega (gaugeAction G target source h U)) =ᵐ[normalizedHaar (E → G)] Omega)

include hfaithful hinvariant in
theorem closure_holonomy_vacuumOrbit_eq_fixedSet :
    closure ((vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero ∘
      gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      fixedSet (pullback (gaugeAction G target source) (normalizedHaar (E → G))
        (measurePreserving_gaugeAction G target source)) := by
  exact FiniteLatticePhysicalInvariantDensity.closure_holonomy_vacuumOrbit_eq_fixedSet
    G target source rho hcontinuous hfaithful (normalizedHaar (E → G)) Omega hOmega hnonzero
    (measurePreserving_gaugeAction G target source) hinvariant

include hfaithful hinvariant in
theorem closure_centered_holonomy_vacuumOrbit_eq_neutral :
    let vacuum := vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero
      (1 : C(E → G, ℂ))
    let P := (Submodule.span ℂ {vacuum})ᗮ.starProjection
    closure ((P ∘ vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero ∘
      gaugeAverage G target source) ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      fixedSet (pullback (gaugeAction G target source) (normalizedHaar (E → G))
        (measurePreserving_gaugeAction G target source)) ∩
      ((Submodule.span ℂ {vacuum})ᗮ : Set (Lp ℂ 2 (normalizedHaar (E → G)))) := by
  exact FiniteLatticePhysicalInvariantDensity.closure_centered_holonomy_vacuumOrbit_eq_neutral
    G target source rho hcontinuous hfaithful (normalizedHaar (E → G)) Omega hOmega hnonzero
    (measurePreserving_gaugeAction G target source) hinvariant

end

end NCG.FiniteLatticeHaarVacuumCyclicity
