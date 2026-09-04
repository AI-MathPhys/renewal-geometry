/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactGaugeInvariantL2DensityExact
import NCG.Grand.InvariantVacuumPullbackExact
import NCG.Grand.PositiveVacuumCyclicityExact
import NCG.Grand.InvariantVacuumOrthogonalCenteringExact

/-!
# Physical cyclicity of continuous gauge invariants

The full physical invariant space is defined by measure-preserving pullbacks.
An invariant nonvanishing vacuum transports density from the weighted L²
fixed space to this independently defined physical space.
-/

open MeasureTheory

namespace NCG.PhysicalGaugeInvariantCyclicity

open PositiveVacuumWeightedL2 PositiveVacuumCyclicity
open CompactGaugeInvariantL2Density CompactGroupInvariantProjection

noncomputable section

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X] [FirstCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]
variable (act : G → X → X) (hact : Continuous (Function.uncurry act))
variable (ν : Measure X) (Omega : X → ℂ) (hOmega : Measurable Omega)
variable (hnonzero : ∀ᵐ x ∂ν, Omega x ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure ν Omega)] [(vacuumMeasure ν Omega).Regular]
variable (hpres : ∀ g, MeasurePreserving (act g) ν ν)
variable (hinvariant : ∀ g, (fun x => Omega (act g x)) =ᵐ[ν] Omega)
variable (hmul : ∀ g h x, act (g * h) x = act g (act h x))
variable (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]

include hact hinvariant hmul μ in
/-- Continuous invariant writers are cyclic in the full physical fixed space. -/
theorem closure_invariant_vacuumOrbit_eq_fixedSet :
    closure (vacuumOrbit ν Omega hOmega hnonzero ''
      CompactGaugeAveragingDensity.invariantSet act) =
      fixedSet (pullback act ν hpres) := by
  let U := vacuumUnitary ν Omega hOmega hnonzero
  let hw := fun g => InvariantVacuumPullback.measurePreserving_vacuumMeasure
    ν Omega hOmega (hpres g) (hinvariant g)
  have hd := closure_toLp_invariants_eq_fixedSet act hact
    (vacuumMeasure ν Omega) hw hmul μ
  have heq : U '' fixedSet (pullback act (vacuumMeasure ν Omega) hw) =
      fixedSet (pullback act ν hpres) := by
    ext v
    constructor
    · rintro ⟨w, hwfix, rfl⟩
      exact (InvariantVacuumPullback.vacuumUnitary_fixed_iff
        ν Omega hOmega hnonzero act hpres hinvariant w).mp hwfix
    · intro hv
      refine ⟨U.symm v, ?_, U.apply_symm_apply v⟩
      apply (InvariantVacuumPullback.vacuumUnitary_fixed_iff
        ν Omega hOmega hnonzero act hpres hinvariant (U.symm v)).mpr
      change ∀ i, pullback act ν hpres i (U (U.symm v)) = U (U.symm v)
      rw [U.apply_symm_apply]
      exact hv
  have htransport := U.toHomeomorph.image_closure
    (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure ν Omega) ℂ ''
      CompactGaugeAveragingDensity.invariantSet act)
  change U '' closure (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure ν Omega) ℂ ''
    CompactGaugeAveragingDensity.invariantSet act) =
    closure (U '' (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure ν Omega) ℂ ''
      CompactGaugeAveragingDensity.invariantSet act)) at htransport
  rw [hd, heq] at htransport
  have hfun : (vacuumOrbit ν Omega hOmega hnonzero : C(X, ℂ) → Lp ℂ 2 ν) =
      fun f => U (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure ν Omega) ℂ f) := by
    funext f
    rfl
  rw [hfun]
  simpa only [Set.image_image] using htransport.symm

include hact hinvariant hmul μ in
theorem vacuum_mem_fixedSet :
    vacuumOrbit ν Omega hOmega hnonzero (1 : C(X, ℂ)) ∈
      fixedSet (pullback act ν hpres) := by
  rw [← closure_invariant_vacuumOrbit_eq_fixedSet act hact ν Omega hOmega hnonzero
    hpres hinvariant hmul μ]
  apply subset_closure
  exact ⟨1, fun _ _ => rfl, rfl⟩

include hact hinvariant hmul μ in
/-- Centering is cyclic in the full neutral physical fixed space. -/
theorem closure_centered_invariant_vacuumOrbit_eq_neutral :
    let vacuum := vacuumOrbit ν Omega hOmega hnonzero (1 : C(X, ℂ))
    let P := (Submodule.span ℂ {vacuum})ᗮ.starProjection
    closure ((P ∘ vacuumOrbit ν Omega hOmega hnonzero) ''
      CompactGaugeAveragingDensity.invariantSet act) =
      fixedSet (pullback act ν hpres) ∩ ((Submodule.span ℂ {vacuum})ᗮ : Set (Lp ℂ 2 ν)) := by
  dsimp only
  have h := InvariantVacuumOrthogonalCentering.closure_centered_fixed_eq_inter
    (pullback act ν hpres) (vacuumOrbit ν Omega hOmega hnonzero (1 : C(X, ℂ)))
    (vacuum_mem_fixedSet act hact ν Omega hOmega hnonzero hpres hinvariant hmul μ)
    _ (closure_invariant_vacuumOrbit_eq_fixedSet act hact ν Omega hOmega hnonzero
      hpres hinvariant hmul μ)
  simpa [Set.image_image, Function.comp_def, fixedSet,
    InvariantVacuumOrthogonalCentering.fixedSubmodule] using h

end

end NCG.PhysicalGaugeInvariantCyclicity
