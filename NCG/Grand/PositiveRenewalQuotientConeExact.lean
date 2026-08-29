/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveRenewalQuotientDynamics
import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Exact minimality and proper-cone certificate for the renewal quotient

This removes the dimension-identification hypothesis from the earlier
minimality result.  A realization of the leading target Hankel panel already
contains two linearly independent predictive states.  Since the explicit
positive realization has two states, a minimal realization has dimension
exactly two.  We also exhibit the standard positive orthant as a proper
generating cone and its coordinate sum as a strictly positive mass
functional.
-/

open Matrix

namespace NCG
namespace PositiveRenewalQuotientConeExact

/-- The leading target Hankel panel, over an arbitrary characteristic-zero
ordered field used below. -/
def targetHankelRat : Matrix (Fin 2) (Fin 2) ℚ :=
  !![8 / 15, 64 / 225; 64 / 225, 392 / 3375]

/-- A realization of the target Hankel panel contains two linearly
independent predictive columns. -/
theorem targetHankel_predictiveStates_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : Fin 2 → V) (ell : Fin 2 → V →ₗ[ℚ] ℚ)
    (hrealize : ∀ i j, ell i (x j) = targetHankelRat i j) :
    LinearIndependent ℚ x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have heval : ∀ k : Fin 2, ∑ i, g i * targetHankelRat k i = 0 := by
    intro k
    have h := congrArg (ell k) hg
    simpa [map_sum, hrealize, smul_eq_mul] using h
  have h0 := heval 0
  have h1 := heval 1
  simp [targetHankelRat, Fin.sum_univ_two] at h0 h1
  have hg0 : g 0 = 0 := by
    linear_combination
      (-3375 / 64 : ℚ) * (392 / 3375 : ℚ) * h0 +
      (3375 / 64 : ℚ) * (64 / 225 : ℚ) * h1
  have hg1 : g 1 = 0 := by
    linear_combination
      (3375 / 64 : ℚ) * (64 / 225 : ℚ) * h0 -
      (3375 / 64 : ℚ) * (8 / 15 : ℚ) * h1
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

/-- The target Hankel rank forces dimension at least two in every finite
linear realization; no prior identification of dimension with Hankel rank is
assumed. -/
theorem targetHankel_finrank_atLeast_two
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (x : Fin 2 → V) (ell : Fin 2 → V →ₗ[ℚ] ℚ)
    (hrealize : ∀ i j, ell i (x j) = targetHankelRat i j) :
    2 ≤ Module.finrank ℚ V := by
  have hli := targetHankel_predictiveStates_linearIndependent x ell hrealize
  simpa using hli.fintype_card_le_finrank

/-- Minimality against the explicit two-state realization therefore forces
dimension exactly two. -/
theorem minimal_targetRenewal_finrank_two
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (x : Fin 2 → V) (ell : Fin 2 → V →ₗ[ℚ] ℚ)
    (hrealize : ∀ i j, ell i (x j) = targetHankelRat i j)
    (hminimal : Module.finrank ℚ V ≤ 2) :
    Module.finrank ℚ V = 2 := by
  exact Nat.le_antisymm hminimal
    (targetHankel_finrank_atLeast_two x ell hrealize)

/-- The normalized mass functional on the two-state positive quotient. -/
def coordinateMass : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x 0 + x 1
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- The standard positive orthant is a genuine proper cone. -/
def renewalProperCone : ProperCone ℝ (Fin 2 → ℝ) :=
  ProperCone.positive ℝ (Fin 2 → ℝ)

/-- The positive orthant generates the entire two-dimensional predictive
space. -/
theorem renewalProperCone_generating :
    Submodule.span ℝ (renewalProperCone : Set (Fin 2 → ℝ)) = ⊤ := by
  apply top_unique
  intro x _
  let xp : Fin 2 → ℝ := fun i => max (x i) 0
  let xn : Fin 2 → ℝ := fun i => max (-x i) 0
  have hxp : xp ∈ renewalProperCone := by
    intro i
    exact le_max_right _ _
  have hxn : xn ∈ renewalProperCone := by
    intro i
    exact le_max_right _ _
  have hdecomp : x = xp - xn := by
    funext i
    dsimp only [xp, xn]
    exact (max_zero_sub_max_neg_zero_eq_self (x i)).symm
  rw [hdecomp]
  exact Submodule.sub_mem _ (Submodule.subset_span hxp)
    (Submodule.subset_span hxn)

/-- Coordinate mass is nonnegative on the cone and strictly positive on every
nonzero positive predictive state. -/
theorem coordinateMass_positive :
    (∀ x ∈ renewalProperCone, 0 ≤ coordinateMass x)
      ∧ (∀ x ∈ renewalProperCone, x ≠ 0 → 0 < coordinateMass x) := by
  constructor
  · intro x hx
    exact add_nonneg (hx 0) (hx 1)
  · intro x hx hne
    have hsome : 0 < x 0 ∨ 0 < x 1 := by
      by_contra h
      push_neg at h
      have h0 : x 0 = 0 := le_antisymm h.1 (hx 0)
      have h1 : x 1 = 0 := le_antisymm h.2 (hx 1)
      apply hne
      funext i
      fin_cases i <;> assumption
    rcases hsome with h0 | h1
    · exact add_pos_of_pos_of_nonneg h0 (hx 1)
    · exact add_pos_of_nonneg_of_pos (hx 0) h1

/-- Exact general-clause certificate.  Any finite minimal predictive
realization of the target panel is two-dimensional; consequently it admits
two-state coordinates.  The proper-generating-cone and positive-mass
hypotheses are recorded literally, while the dimension conclusion follows
from the target law itself. -/
theorem properCone_minimalPredictiveQuotient_twoDimensional
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (C : ProperCone ℝ (Fin 2 → ℝ))
    (hgen : Submodule.span ℝ (C : Set (Fin 2 → ℝ)) = ⊤)
    (mass : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hmass : ∀ y ∈ C, y ≠ 0 → 0 < mass y)
    (x : Fin 2 → V) (ell : Fin 2 → V →ₗ[ℚ] ℚ)
    (hrealize : ∀ i j, ell i (x j) = targetHankelRat i j)
    (hminimal : Module.finrank ℚ V ≤ 2) :
    Module.finrank ℚ V = 2 ∧ Nonempty (V ≃ₗ[ℚ] (Fin 2 → ℚ)) := by
  have hdim := minimal_targetRenewal_finrank_two x ell hrealize hminimal
  refine ⟨hdim, ?_⟩
  exact ⟨LinearEquiv.ofFinrankEq V (Fin 2 → ℚ) (by simpa [hdim])⟩

/-- Bundled concrete proper-cone witness used by the general clause. -/
theorem explicit_twoState_properGenerating_positiveMass :
    Submodule.span ℝ (renewalProperCone : Set (Fin 2 → ℝ)) = ⊤
      ∧ (∀ x ∈ renewalProperCone, 0 ≤ coordinateMass x)
      ∧ (∀ x ∈ renewalProperCone, x ≠ 0 → 0 < coordinateMass x) := by
  exact ⟨renewalProperCone_generating, coordinateMass_positive⟩

end PositiveRenewalQuotientConeExact
end NCG
