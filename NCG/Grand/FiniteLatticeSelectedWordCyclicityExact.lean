/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HolonomyWordAlgebraExact
import NCG.Grand.SelectedInvariantSourceDensityExact
import NCG.Grand.FiniteLatticeHaarVacuumCyclicityExact

/-!
# Actual word-orbit cyclicity after retained measurable record selection

The reference law is the constructed edge-Haar law, the writers are literal
signed transport words, and the selected sector is given independently by
gauge invariance and vanishing outside the retained event. Density and
cyclicity are derived; neither is an input. Identification of a narrower
primitive current/plaquette bank with these words remains a separate task.
-/

open MeasureTheory

namespace NCG.FiniteLatticeSelectedWordCyclicity

open FiniteLatticeGaugeInvariantDensity FiniteLatticeHaarGaugeMeasure
open PositiveVacuumWeightedL2 PositiveVacuumCyclicity HolonomyWordAlgebra
open CompactGaugeInvariantL2Density CompactGroupInvariantProjection
open MeasurableRecordProjection SelectedInvariantSourceDensity

noncomputable section

variable {V E n : Type*} [Fintype V] [Fintype E] [Fintype n] [DecidableEq n]
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (target source : E → V)
variable (rho : G →* Matrix n n ℂ) (hcontinuous : Continuous rho)
variable (hfaithful : Function.Injective rho)
variable (hunitary : ∀ g, rho g⁻¹ = (rho g).conjTranspose)
variable (Omega : (E → G) → ℂ) (hOmega : Measurable Omega)
variable (hnonzero : ∀ᵐ U ∂normalizedHaar (E → G), Omega U ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure (normalizedHaar (E → G)) Omega)]
variable (hinvariant : ∀ h,
  (fun U => Omega (gaugeAction G target source h U)) =ᵐ[normalizedHaar (E → G)] Omega)

include hfaithful hunitary hinvariant

theorem closure_word_vacuumOrbit_eq_fixedSet :
    closure ((vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero ∘
      gaugeAverage G target source) ''
      (wordAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      fixedSet (pullback (gaugeAction G target source) (normalizedHaar (E → G))
        (measurePreserving_gaugeAction G target source)) := by
  rw [wordAlgebra_eq_matrixEntryAlgebra G rho hcontinuous hunitary]
  exact FiniteLatticeHaarVacuumCyclicity.closure_holonomy_vacuumOrbit_eq_fixedSet
    G target source rho hcontinuous hfaithful Omega hOmega hnonzero hinvariant

variable (S : Set (E → G)) (hS : MeasurableSet S)
variable (hrecord : ∀ h U, gaugeAction G target source h U ∈ S ↔ U ∈ S)

include hrecord

theorem closure_selected_word_vacuumOrbit_eq_sector :
    closure ((selection (normalizedHaar (E → G)) S hS ∘
      vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero ∘
      gaugeAverage G target source) ''
      (wordAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      (selectedSector (normalizedHaar (E → G)) S hS (gaugeAction G target source)
        (measurePreserving_gaugeAction G target source) : Set (Lp ℂ 2 (normalizedHaar (E → G)))) := by
  have hd := closure_word_vacuumOrbit_eq_fixedSet G target source rho hcontinuous
    hfaithful hunitary Omega hOmega hnonzero hinvariant
  have hs := closure_selected_writers_eq_sector (normalizedHaar (E → G)) S hS
    (gaugeAction G target source) (measurePreserving_gaugeAction G target source) hrecord _ hd
  simpa only [Set.image_image, Function.comp_def] using hs

theorem closure_centered_selected_word_vacuumOrbit_eq_neutral :
    let vacuum := select (normalizedHaar (E → G)) S hS
      (vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero (1 : C(E → G, ℂ)))
    let P := (Submodule.span ℂ {vacuum})ᗮ.starProjection
    closure ((P ∘ selection (normalizedHaar (E → G)) S hS ∘
      vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero ∘
      gaugeAverage G target source) ''
      (wordAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      (selectedSector (normalizedHaar (E → G)) S hS (gaugeAction G target source)
        (measurePreserving_gaugeAction G target source) : Set (Lp ℂ 2 (normalizedHaar (E → G)))) ∩
      ((Submodule.span ℂ {vacuum})ᗮ : Set (Lp ℂ 2 (normalizedHaar (E → G)))) := by
  have hd := closure_word_vacuumOrbit_eq_fixedSet G target source rho hcontinuous
    hfaithful hunitary Omega hOmega hnonzero hinvariant
  have hv := PhysicalGaugeInvariantCyclicity.vacuum_mem_fixedSet
    (gaugeAction G target source) (continuous_gaugeAction G target source)
    (normalizedHaar (E → G)) Omega hOmega hnonzero
    (measurePreserving_gaugeAction G target source) hinvariant (gaugeAction_mul G target source)
    (rightHaarProbability (V → G))
  have hs := closure_centered_selected_writers_eq_neutral (normalizedHaar (E → G)) S hS
    (gaugeAction G target source) (measurePreserving_gaugeAction G target source) hrecord
    (vacuumOrbit (normalizedHaar (E → G)) Omega hOmega hnonzero (1 : C(E → G, ℂ))) hv _ hd
  simpa only [Set.image_image, Function.comp_def] using hs

end

end NCG.FiniteLatticeSelectedWordCyclicity
