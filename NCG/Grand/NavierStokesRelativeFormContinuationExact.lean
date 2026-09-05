/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.NSRelative

/-!
# Exact relative-form Navier--Stokes continuation estimate

This module closes the missing implication in `thm:NS-relative-form`: the
actual `H^s` energy identity and the absolute relative-form estimate imply the
differential inequality used by the integrating-factor proof.
-/

noncomputable section

namespace NCG.NavierStokesRelativeForm

/-- The nonlinear relative-form hypothesis and the exact energy identity give
`Eₛ' + theta nu Dₛ ≤ k Eₛ`. -/
theorem differential_inequality_of_energy_and_relative_form
    (energyDerivative dissipation coefficient interaction energy : ℝ → ℝ)
    (nu theta : ℝ)
    (henergy : ∀ r, energyDerivative r + nu * dissipation r = -interaction r)
    (hrelative : ∀ r, |interaction r| ≤
      (1 - theta) * nu * dissipation r + coefficient r * energy r) :
    ∀ r, energyDerivative r ≤
      -(theta * nu) * dissipation r + coefficient r * energy r := by
  intro r
  have habs : -interaction r ≤ |interaction r| := neg_le_abs _
  have hrel := hrelative r
  have hE := henergy r
  linarith

/-- The complete boxed estimate of `thm:NS-relative-form`, with neither the
energy identity nor the nonlinear relative bound collapsed into the final
scalar differential inequality. -/
theorem weighted_energy_and_dissipation_estimate
    (energy energyDerivative dissipation coefficient primitive weightedDissipation
      interaction : ℝ → ℝ)
    (nu theta t : ℝ)
    (hnu : 0 ≤ nu) (htheta : 0 < theta) (_hthetaOne : theta ≤ 1)
    (henergyDeriv : ∀ r, HasDerivAt energy (energyDerivative r) r)
    (hprimitive : ∀ r, HasDerivAt primitive (coefficient r) r)
    (hprimitiveZero : primitive 0 = 0)
    (hweightedDissipation : ∀ r,
      HasDerivAt weightedDissipation
        (Real.exp (-primitive r) * dissipation r) r)
    (hweightedDissipationZero : weightedDissipation 0 = 0)
    (henergy : ∀ r,
      energyDerivative r + nu * dissipation r = -interaction r)
    (hrelative : ∀ r, |interaction r| ≤
      (1 - theta) * nu * dissipation r + coefficient r * energy r)
    (ht : 0 ≤ t) :
    Real.exp (-primitive t) * energy t +
        theta * nu * weightedDissipation t ≤ energy 0 := by
  apply NCG.ns_relative_energy energy energyDerivative dissipation coefficient
    primitive weightedDissipation nu theta t
  · exact mul_nonneg htheta.le hnu
  · exact henergyDeriv
  · exact hprimitive
  · exact hprimitiveZero
  · exact hweightedDissipation
  · exact hweightedDissipationZero
  · exact differential_inequality_of_energy_and_relative_form
      energyDerivative dissipation coefficient interaction energy nu theta
      henergy hrelative
  · exact ht

/-- A global continuation criterion consumes the exact estimate above.  The
criterion is kept as a typed PDE interface because its Sobolev local theory is
independent of the relative-form argument. -/
theorem global_smoothness_of_weighted_estimate
    (GlobalSmooth : Prop)
    (energy energyDerivative dissipation coefficient primitive weightedDissipation
      interaction : ℝ → ℝ)
    (nu theta : ℝ)
    (hnu : 0 ≤ nu) (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (henergyDeriv : ∀ r, HasDerivAt energy (energyDerivative r) r)
    (hprimitive : ∀ r, HasDerivAt primitive (coefficient r) r)
    (hprimitiveZero : primitive 0 = 0)
    (hweightedDissipation : ∀ r,
      HasDerivAt weightedDissipation
        (Real.exp (-primitive r) * dissipation r) r)
    (hweightedDissipationZero : weightedDissipation 0 = 0)
    (henergy : ∀ r,
      energyDerivative r + nu * dissipation r = -interaction r)
    (hrelative : ∀ r, |interaction r| ≤
      (1 - theta) * nu * dissipation r + coefficient r * energy r)
    (continuationCriterion :
      (∀ t, 0 ≤ t →
        Real.exp (-primitive t) * energy t +
          theta * nu * weightedDissipation t ≤ energy 0) → GlobalSmooth) :
    GlobalSmooth := by
  apply continuationCriterion
  intro t ht
  exact weighted_energy_and_dissipation_estimate
    energy energyDerivative dissipation coefficient primitive weightedDissipation
    interaction nu theta t hnu htheta hthetaOne henergyDeriv hprimitive
    hprimitiveZero hweightedDissipation hweightedDissipationZero henergy hrelative ht

end NCG.NavierStokesRelativeForm
