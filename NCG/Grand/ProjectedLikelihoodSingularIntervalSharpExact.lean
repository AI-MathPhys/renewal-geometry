/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TargetNativeReadLayerExact

/-!
# Sharp singular interval for finite projected likelihoods

This closes the attainment clause in `thm:GT-projected-likelihood-tower`.
Once the payoff outside the reference-null support is fixed, assigning the
constant lower or upper endpoint on that support attains the two endpoints of
the Lebesgue singular-mass interval exactly.
-/

open Finset

namespace NCG
namespace FiniteTargetProjectionAndQuotients

/-- Replace a payoff by a constant on the reference-null (singular) support. -/
noncomputable def payoffOnSingular {X : Type*}
    (nu f : X → ℝ) (c : ℝ) (x : X) : ℝ :=
  if nu x = 0 then c else f x

/-- Changing a payoff on the reference-null support does not change the
regular projected-likelihood contribution. -/
theorem regularIntegral_payoffOnSingular {X : Type*} [Fintype X]
    (rho nu f : X → ℝ) (c : ℝ) :
    realIntegral nu (fun x => regularDensity rho nu x *
      payoffOnSingular nu f c x) =
      realIntegral nu (fun x => regularDensity rho nu x * f x) := by
  unfold realIntegral
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : nu x = 0
  · simp [payoffOnSingular, hx]
  · simp [payoffOnSingular, hx]

/-- A constant payoff `c` on the singular support contributes exactly `c`
times the total singular mass. -/
theorem singularIntegral_payoffOnSingular {X : Type*} [Fintype X]
    (rho nu f : X → ℝ) (c : ℝ) :
    realIntegral (singularPart rho nu) (payoffOnSingular nu f c) =
      c * ∑ x, singularPart rho nu x := by
  unfold realIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : nu x = 0
  · simp [singularPart, payoffOnSingular, hx, mul_comm]
  · simp [singularPart, payoffOnSingular, hx]

/-- **Sharpness of the singular-mass interval.**  The lower and upper
endpoint payoffs agree with the prescribed payoff off the singular support,
obey the required bounds on that support, and attain the two advertised
endpoints exactly. -/
theorem singular_mass_interval_endpoints_attained
    {X : Type*} [Fintype X] (rho nu f : X → ℝ) (a b : ℝ)
    (hab : a ≤ b) :
    let regular := realIntegral nu (fun x => regularDensity rho nu x * f x)
    let mass := ∑ x, singularPart rho nu x
    let fLow := payoffOnSingular nu f a
    let fHigh := payoffOnSingular nu f b
    (∀ x, nu x ≠ 0 → fLow x = f x) ∧
      (∀ x, nu x ≠ 0 → fHigh x = f x) ∧
      (∀ x, nu x = 0 → a ≤ fLow x ∧ fLow x ≤ b) ∧
      (∀ x, nu x = 0 → a ≤ fHigh x ∧ fHigh x ≤ b) ∧
      realIntegral rho fLow = regular + a * mass ∧
      realIntegral rho fHigh = regular + b * mass := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [payoffOnSingular, hx]
  · intro x hx
    simp [payoffOnSingular, hx]
  · intro x hx
    simp [payoffOnSingular, hx, hab]
  · intro x hx
    simp [payoffOnSingular, hx, hab]
  · rw [finite_singular_integral_formula]
    rw [regularIntegral_payoffOnSingular, singularIntegral_payoffOnSingular]
  · rw [finite_singular_integral_formula]
    rw [regularIntegral_payoffOnSingular, singularIntegral_payoffOnSingular]

end FiniteTargetProjectionAndQuotients
end NCG
