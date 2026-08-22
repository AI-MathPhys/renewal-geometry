/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedActionInformationPythagoras

/-!
# Finite target projections and real/complex quotient towers

This file is the finite target-native probability layer.  It proves change of
variables, projected Radon--Nikodym formulas, the nested quotient tower, the
zero-safe singular decomposition, and the canonical phase-quenched law.
-/

open Finset

namespace NCG
namespace FiniteTargetProjectionAndQuotients

open AcceptedActionInformationPythagoras

/-- Pushforward of a finite complex measure. -/
noncomputable def complexPushforward {Omega X : Type*}
    [Fintype Omega] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) (x : X) : Complex :=
  Finset.univ.filter (fun omega => T omega = x) |>.sum zeta

/-- Integral of a scalar record against a finite real measure. -/
noncomputable def realIntegral {Omega : Type*} [Fintype Omega]
    (rho f : Omega -> Real) : Real :=
  Finset.univ.sum (fun omega => rho omega * f omega)

/-- Integral of a complex payoff against a finite complex measure. -/
noncomputable def complexIntegral {Omega : Type*} [Fintype Omega]
    (zeta f : Omega -> Complex) : Complex :=
  Finset.univ.sum (fun omega => zeta omega * f omega)

theorem real_pushforward_change_variables
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq X]
    (T : Omega -> X) (rho : Omega -> Real) (f : X -> Real) :
    realIntegral rho (fun omega => f (T omega)) =
      realIntegral (pushforwardRow T rho) f := by
  unfold realIntegral pushforwardRow
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := T)
    (fun _ _ => Finset.mem_univ _) (fun omega => rho omega * f (T omega))]
  apply sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro omega homega
  rw [(Finset.mem_filter.mp homega).2]

theorem complex_pushforward_change_variables
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) (f : X -> Complex) :
    complexIntegral zeta (fun omega => f (T omega)) =
      complexIntegral (complexPushforward T zeta) f := by
  unfold complexIntegral complexPushforward
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := T)
    (fun _ _ => Finset.mem_univ _) (fun omega => zeta omega * f (T omega))]
  apply sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro omega homega
  rw [(Finset.mem_filter.mp homega).2]

theorem real_pushforward_comp
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Omega -> X) (s : X -> Y) (rho : Omega -> Real) :
    pushforwardRow (fun omega => s (T omega)) rho =
      pushforwardRow s (pushforwardRow T rho) := by
  funext y
  have h := real_pushforward_change_variables T rho
    (fun x => if s x = y then 1 else 0)
  simpa [realIntegral, pushforwardRow, mul_ite] using h

theorem complex_pushforward_comp
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Omega -> X) (s : X -> Y) (zeta : Omega -> Complex) :
    complexPushforward (fun omega => s (T omega)) zeta =
      complexPushforward s (complexPushforward T zeta) := by
  funext y
  have h := complex_pushforward_change_variables T zeta
    (fun x => if s x = y then 1 else 0)
  simpa [complexIntegral, complexPushforward, mul_ite] using h
/-- Projected likelihood ratio on a finite target record. -/
noncomputable def projectedLikelihood
    {Omega X : Type*} [Fintype Omega] [DecidableEq X]
    (T : Omega -> X) (rho nu : Omega -> Real) (x : X) : Real :=
  pushforwardRow T rho x / pushforwardRow T nu x

theorem projectedLikelihood_factor
    {Omega X : Type*} [Fintype Omega] [DecidableEq X]
    (T : Omega -> X) (rho nu : Omega -> Real)
    (hT : Function.Surjective T) (hnu : forall omega, 0 < nu omega) (x : X) :
    pushforwardRow T nu x * projectedLikelihood T rho nu x =
      pushforwardRow T rho x := by
  unfold projectedLikelihood
  field_simp [ne_of_gt (pushforwardRow_pos T nu hT hnu x)]

/-- `thm:GT-projected-likelihood-tower`, dominated finite branch: every
target-measurable payoff is reconstructed from the projected likelihood. -/
theorem projected_likelihood_representation
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq X]
    (T : Omega -> X) (rho nu : Omega -> Real) (f : X -> Real)
    (hT : Function.Surjective T) (hnu : forall omega, 0 < nu omega) :
    realIntegral rho (fun omega => f (T omega)) =
      realIntegral (pushforwardRow T nu)
        (fun x => projectedLikelihood T rho nu x * f x) := by
  rw [real_pushforward_change_variables]
  unfold realIntegral
  apply sum_congr rfl
  intro x _
  rw [← mul_assoc, projectedLikelihood_factor T rho nu hT hnu]

/-- Nested finite likelihood tower. -/
theorem projected_likelihood_tower
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Omega -> X) (s : X -> Y) (rho nu : Omega -> Real)
    (hT : Function.Surjective T) (hs : Function.Surjective s)
    (hnu : forall omega, 0 < nu omega) (y : Y) :
    projectedLikelihood (fun omega => s (T omega)) rho nu y =
      (Finset.univ.filter (fun x => s x = y)).sum (fun x =>
        pushforwardRow T nu x * projectedLikelihood T rho nu x) /
        pushforwardRow s (pushforwardRow T nu) y := by
  rw [projectedLikelihood, real_pushforward_comp T s rho,
    real_pushforward_comp T s nu]
  unfold pushforwardRow
  congr 1
  apply sum_congr rfl
  intro x _
  rw [← projectedLikelihood_factor T rho nu hT hnu]

/-- Zero-safe finite Lebesgue density. -/
noncomputable def regularDensity {X : Type*}
    (rho nu : X -> Real) (x : X) : Real :=
  if nu x = 0 then 0 else rho x / nu x

/-- Singular mass retained on the zero set of the reference law. -/
noncomputable def singularPart {X : Type*}
    (rho nu : X -> Real) (x : X) : Real :=
  if nu x = 0 then rho x else 0

theorem finite_lebesgue_decomposition {X : Type*}
    (rho nu : X -> Real) (x : X) :
    rho x = regularDensity rho nu x * nu x + singularPart rho nu x := by
  by_cases h : nu x = 0
  · simp [regularDensity, singularPart, h]
  · simp [regularDensity, singularPart, h]
    field_simp

theorem finite_singular_integral_formula
    {X : Type*} [Fintype X] (rho nu f : X -> Real) :
    realIntegral rho f =
      realIntegral nu (fun x => regularDensity rho nu x * f x) +
      realIntegral (singularPart rho nu) f := by
  unfold realIntegral
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  rw [finite_lebesgue_decomposition rho nu x]
  ring

/-- Sharp interval from knowing only the singular mass and pointwise payoff
bounds on the singular support. -/
theorem singular_mass_sharp_interval
    {X : Type*} [Fintype X] (rho nu f : X -> Real) (a b : Real)
    (hrho : forall x, 0 <= rho x) (hab : a <= b)
    (hf : forall x, nu x = 0 -> a <= f x /\ f x <= b) :
    let regular := realIntegral nu (fun x => regularDensity rho nu x * f x)
    let mass := Finset.univ.sum (fun x => singularPart rho nu x)
    regular + a * mass <= realIntegral rho f /\
      realIntegral rho f <= regular + b * mass := by
  dsimp only
  rw [finite_singular_integral_formula]
  constructor
  · apply add_le_add_left
    unfold realIntegral
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x _
    by_cases h : nu x = 0
    · simp only [singularPart, h, if_true]
      exact mul_le_mul_of_nonneg_left (hf x h).1 (hrho x)
    · simp [singularPart, h]
  · apply add_le_add_left
    unfold realIntegral
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x _
    by_cases h : nu x = 0
    · simp only [singularPart, h, if_true]
      exact mul_le_mul_of_nonneg_left (hf x h).2 (hrho x)
    · simp [singularPart, h]
/-- Projected complex density with respect to a positive reference row. -/
noncomputable def projectedComplexWeight
    {Omega X : Type*} [Fintype Omega] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) (nu : Omega -> Real)
    (x : X) : Complex :=
  complexPushforward T zeta x / (pushforwardRow T nu x : Complex)

theorem projectedComplexWeight_factor
    {Omega X : Type*} [Fintype Omega] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) (nu : Omega -> Real)
    (hT : Function.Surjective T) (hnu : forall omega, 0 < nu omega) (x : X) :
    (pushforwardRow T nu x : Complex) * projectedComplexWeight T zeta nu x =
      complexPushforward T zeta x := by
  unfold projectedComplexWeight
  field_simp [ne_of_gt (pushforwardRow_pos T nu hT hnu x)]

/-- `thm:GT-complex-quotient-tower`, payoff reconstruction branch. -/
theorem projected_complex_representation
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) (nu : Omega -> Real)
    (f : X -> Complex) (hT : Function.Surjective T)
    (hnu : forall omega, 0 < nu omega) :
    complexIntegral zeta (fun omega => f (T omega)) =
      complexIntegral (fun x => (pushforwardRow T nu x : Complex))
        (fun x => projectedComplexWeight T zeta nu x * f x) := by
  rw [complex_pushforward_change_variables]
  unfold complexIntegral
  apply sum_congr rfl
  intro x _
  rw [← mul_assoc, projectedComplexWeight_factor T zeta nu hT hnu]

theorem projected_complex_tower
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Omega -> X) (s : X -> Y) (zeta : Omega -> Complex)
    (nu : Omega -> Real) (hT : Function.Surjective T)
    (hnu : forall omega, 0 < nu omega) (y : Y) :
    projectedComplexWeight (fun omega => s (T omega)) zeta nu y =
      (Finset.univ.filter (fun x => s x = y)).sum (fun x =>
        (pushforwardRow T nu x : Complex) * projectedComplexWeight T zeta nu x) /
        (pushforwardRow s (pushforwardRow T nu) y : Complex) := by
  rw [projectedComplexWeight, complex_pushforward_comp T s zeta,
    real_pushforward_comp T s nu]
  unfold complexPushforward
  congr 1
  apply sum_congr rfl
  intro x _
  rw [projectedComplexWeight_factor T zeta nu hT hnu]

/-- Total complex amplitude is invariant under projection. -/
theorem complex_amplitude_projection_invariant
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq X]
    (T : Omega -> X) (zeta : Omega -> Complex) :
    Finset.univ.sum (complexPushforward T zeta) = Finset.univ.sum zeta := by
  simpa [complexIntegral] using
    (complex_pushforward_change_variables T zeta (fun _ => (1 : Complex))).symm

/-- Total variation of a finite complex measure. -/
noncomputable def complexVariation {X : Type*} [Fintype X]
    (zeta : X -> Complex) : Real :=
  Finset.univ.sum (fun x => norm (zeta x))

/-- Phase-quenched probability mass. -/
noncomputable def phaseQuenchedLaw {X : Type*} [Fintype X]
    (zeta : X -> Complex) (x : X) : Real :=
  norm (zeta x) / complexVariation zeta

/-- Zero-safe polar phase. -/
noncomputable def polarPhase {X : Type*} (zeta : X -> Complex) (x : X) : Complex :=
  if zeta x = 0 then 1 else zeta x / norm (zeta x)

/-- `cor:GT-phase-quenched-quotient`: canonical positive law, unit phase on
its support, polar reconstruction, and the total-amplitude identity. -/
theorem phase_quenched_quotient
    {X : Type*} [Fintype X] (zeta : X -> Complex)
    (hvariation : complexVariation zeta ≠ 0) :
    (forall x, 0 <= phaseQuenchedLaw zeta x) /\
    Finset.univ.sum (phaseQuenchedLaw zeta) = 1 /\
    (forall x, phaseQuenchedLaw zeta x ≠ 0 -> norm (polarPhase zeta x) = 1) /\
    (forall x, zeta x =
      (complexVariation zeta : Complex) *
        (phaseQuenchedLaw zeta x : Complex) * polarPhase zeta x) /\
    Finset.univ.sum zeta =
      (complexVariation zeta : Complex) *
        Finset.univ.sum (fun x =>
          (phaseQuenchedLaw zeta x : Complex) * polarPhase zeta x) := by
  have hvarNonneg : 0 <= complexVariation zeta :=
    sum_nonneg (fun x _ => norm_nonneg _)
  have hvarPos : 0 < complexVariation zeta :=
    lt_of_le_of_ne hvarNonneg (Ne.symm hvariation)
  have hvarC : (complexVariation zeta : Complex) ≠ 0 := by
    exact_mod_cast hvariation
  have hpolar : forall x, zeta x =
      (complexVariation zeta : Complex) *
        (phaseQuenchedLaw zeta x : Complex) * polarPhase zeta x := by
    intro x
    by_cases hz : zeta x = 0
    · simp [phaseQuenchedLaw, polarPhase, hz]
    · have hnorm : norm (zeta x) ≠ 0 := norm_ne_zero_iff.mpr hz
      have hnormC : (norm (zeta x) : Complex) ≠ 0 := by
        exact_mod_cast hnorm
      unfold phaseQuenchedLaw polarPhase
      rw [if_neg hz]
      push_cast
      field_simp [hvarC, hnormC]
  refine ⟨?_, ?_, ?_, hpolar, ?_⟩
  · intro x
    exact div_nonneg (norm_nonneg _) hvarPos.le
  · unfold phaseQuenchedLaw complexVariation
    rw [← Finset.sum_div]
    exact div_self hvariation
  · intro x hx
    have hz : zeta x ≠ 0 := by
      intro hz
      apply hx
      simp [phaseQuenchedLaw, hz]
    rw [polarPhase, if_neg hz, norm_div]
    simp [norm_ne_zero_iff.mpr hz]
  · rw [Finset.mul_sum]
    apply sum_congr rfl
    intro x _
    simpa [mul_assoc] using (hpolar x).symm
end FiniteTargetProjectionAndQuotients
end NCG
