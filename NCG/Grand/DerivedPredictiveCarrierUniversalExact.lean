/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derived predictive carriers and their universal property

This file constructs the quotient by complete finite-future laws, proves the right-congruence and
chain-factorization clauses, and proves the coarsest-realization universal property.  Zero-probability
branches are assigned the identity update only to totalize the quotient map; on every occurring
branch the quotient update is exactly `[h] ↦ [ha]`.
-/

namespace NCG.DerivedPredictiveCarrierUniversal

/-- A complete finite-future predictive law with deterministic history extension. -/
structure PredictiveSystem (History Letter : Type*) where
  probability : History → List Letter → ℝ
  step : History → Letter → History
  branch : History → Letter → ℝ
  probability_nil : ∀ h, probability h [] = 1
  probability_cons : ∀ h a w,
    probability h (a :: w) = branch h a * probability (step h a) w

namespace PredictiveSystem

variable {History Letter : Type*} (P : PredictiveSystem History Letter)

/-- Histories are future equivalent when every declared finite-future probability agrees. -/
def FutureEquivalent (h h' : History) : Prop :=
  ∀ w, P.probability h w = P.probability h' w

theorem futureEquivalent_equivalence : Equivalence P.FutureEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · intro h w
    rfl
  · intro h h' hh w
    exact (hh w).symm
  · intro h₁ h₂ h₃ h₁₂ h₂₃ w
    exact (h₁₂ w).trans (h₂₃ w)

def futureSetoid : Setoid History where
  r := P.FutureEquivalent
  iseqv := P.futureEquivalent_equivalence

abbrev MinimalCarrier := Quotient P.futureSetoid

theorem branch_eq_of_futureEquivalent {h h' : History}
    (hh : P.FutureEquivalent h h') (a : Letter) :
    P.branch h a = P.branch h' a := by
  have hw := hh [a]
  simpa [P.probability_cons, P.probability_nil] using hw

/-- Right congruence on an occurring branch, derived by cancellation in the chain rule. -/
theorem step_futureEquivalent {h h' : History}
    (hh : P.FutureEquivalent h h') (a : Letter) (ha : P.branch h a ≠ 0) :
    P.FutureEquivalent (P.step h a) (P.step h' a) := by
  intro w
  have hw := hh (a :: w)
  rw [P.probability_cons, P.probability_cons,
    ← P.branch_eq_of_futureEquivalent hh a] at hw
  exact mul_left_cancel₀ ha hw

/-- A total representative update: nonoccurring branches stay in their present class. -/
noncomputable def effectiveStep (h : History) (a : Letter) : History :=
  if P.branch h a = 0 then h else P.step h a

theorem effectiveStep_respects (a : Letter) {h h' : History}
    (hh : P.FutureEquivalent h h') :
    P.FutureEquivalent (P.effectiveStep h a) (P.effectiveStep h' a) := by
  have hb := P.branch_eq_of_futureEquivalent hh a
  by_cases hz : P.branch h a = 0
  · have hz' : P.branch h' a = 0 := by rw [← hb]; exact hz
    simpa [effectiveStep, hz, hz'] using hh
  · have hz' : P.branch h' a ≠ 0 := by rw [← hb]; exact hz
    simpa [effectiveStep, hz, hz'] using P.step_futureEquivalent hh a hz

/-- The branch probability descends to the minimal predictive carrier. -/
def minimalBranch (a : Letter) : P.MinimalCarrier → ℝ :=
  Quotient.lift (fun h => P.branch h a)
    (fun _ _ hh => P.branch_eq_of_futureEquivalent hh a)

@[simp] theorem minimalBranch_mk (h : History) (a : Letter) :
    P.minimalBranch a (Quotient.mk P.futureSetoid h) = P.branch h a := rfl

/-- The totalized deterministic update on the quotient. -/
noncomputable def minimalUpdate (a : Letter) : P.MinimalCarrier → P.MinimalCarrier :=
  Quotient.map (fun h => effectiveStep P h a)
    (fun _ _ hh => P.effectiveStep_respects a hh)

/-- On every occurring branch the quotient update is exactly `[h] ↦ [ha]`. -/
theorem minimalUpdate_mk_of_occurs (h : History) (a : Letter)
    (ha : P.branch h a ≠ 0) :
    P.minimalUpdate a (Quotient.mk P.futureSetoid h) =
      Quotient.mk P.futureSetoid (P.step h a) := by
  simp [minimalUpdate, effectiveStep, ha]

/-- Recursive product of branch probabilities along a word. -/
def pathWeight (h : History) : List Letter → ℝ
  | [] => 1
  | a :: w => P.branch h a * pathWeight (P.step h a) w

/-- The complete future law factors as the product of successive branch laws. -/
theorem probability_eq_pathWeight (h : History) (w : List Letter) :
    P.probability h w = pathWeight (P := P) h w := by
  induction w generalizing h with
  | nil => exact P.probability_nil h
  | cons a w ih =>
      rw [P.probability_cons, pathWeight, ih]

/-- A reachable deterministic realization of the same complete future law. -/
structure Realization (State : Type*) where
  stateOf : History → State
  update : State → Letter → State
  rate : State → Letter → ℝ
  futureLaw : State → List Letter → ℝ
  reachable : Function.Surjective stateOf
  state_step : ∀ h a, stateOf (P.step h a) = update (stateOf h) a
  branch_factor : ∀ h a, P.branch h a = rate (stateOf h) a
  future_factor : ∀ h w, P.probability h w = futureLaw (stateOf h) w

namespace Realization

variable {State : Type*} (R : P.Realization State)

noncomputable def representative (s : State) : History :=
  Classical.choose (R.reachable s)

theorem stateOf_representative (s : State) :
    R.stateOf (representative P R s) = s :=
  Classical.choose_spec (R.reachable s)

/-- Histories represented by the same realization state have identical complete futures. -/
theorem futureEquivalent_of_stateOf_eq {h h' : History}
    (hs : R.stateOf h = R.stateOf h') : P.FutureEquivalent h h' := by
  intro w
  rw [R.future_factor, R.future_factor, hs]

/-- The canonical map from any reachable deterministic realization to the future quotient. -/
noncomputable def toMinimal (s : State) : P.MinimalCarrier :=
  Quotient.mk P.futureSetoid (representative P R s)

theorem toMinimal_stateOf (h : History) :
    toMinimal P R (R.stateOf h) = Quotient.mk P.futureSetoid h := by
  apply Quotient.sound
  exact futureEquivalent_of_stateOf_eq P R (stateOf_representative P R _)

theorem toMinimal_surjective : Function.Surjective (toMinimal P R) := by
  intro z
  refine Quotient.inductionOn z ?_
  intro h
  exact ⟨R.stateOf h, toMinimal_stateOf P R h⟩

theorem toMinimal_branch (s : State) (a : Letter) :
    P.minimalBranch a (toMinimal P R s) = R.rate s a := by
  rw [toMinimal, P.minimalBranch_mk, R.branch_factor,
    stateOf_representative P R]

/-- The canonical map intertwines every occurring update. -/
theorem toMinimal_update_of_occurs (s : State) (a : Letter)
    (ha : R.rate s a ≠ 0) :
    toMinimal P R (R.update s a) = P.minimalUpdate a (toMinimal P R s) := by
  let h := representative P R s
  have hs : R.stateOf h = s := stateOf_representative P R s
  have hbranch : P.branch h a ≠ 0 := by
    rw [R.branch_factor, hs]
    exact ha
  unfold toMinimal
  rw [P.minimalUpdate_mk_of_occurs h a hbranch]
  apply Quotient.sound
  apply futureEquivalent_of_stateOf_eq P R
  rw [stateOf_representative P R, R.state_step, hs]

/-- Uniqueness of the quotient map from its values on represented histories. -/
theorem toMinimal_unique (f : State → P.MinimalCarrier)
    (hf : ∀ h, f (R.stateOf h) = Quotient.mk P.futureSetoid h) :
    f = toMinimal P R := by
  funext s
  rw [← stateOf_representative P R s, hf, toMinimal_stateOf P R]

/-- Two supplied realization states are erased to the same minimal state exactly when all of their
declared finite-future laws agree. -/
theorem toMinimal_eq_iff_futureLaw_eq (s t : State) :
    toMinimal P R s = toMinimal P R t ↔
      ∀ w, R.futureLaw s w = R.futureLaw t w := by
  constructor
  · intro hst w
    have hfuture : P.FutureEquivalent (representative P R s) (representative P R t) :=
      Quotient.exact hst
    have hw := hfuture w
    rw [R.future_factor, R.future_factor,
      stateOf_representative P R, stateOf_representative P R] at hw
    exact hw
  · intro hfuture
    apply Quotient.sound
    intro w
    rw [R.future_factor, R.future_factor,
      stateOf_representative P R, stateOf_representative P R]
    exact hfuture w

/-- Every state coordinate surviving the quotient is separated by an actual finite future word. -/
theorem exists_finite_future_of_toMinimal_ne {s t : State}
    (hst : toMinimal P R s ≠ toMinimal P R t) :
    ∃ w : List Letter, R.futureLaw s w ≠ R.futureLaw t w := by
  by_contra h
  push_neg at h
  exact hst ((toMinimal_eq_iff_futureLaw_eq P R s t).2 h)

/-- `cor:GT-ledger-not-foundational`: a generated reachable ledger is a compiled presentation of
the future quotient.  The canonical map is surjective and unique; its fibres are exactly complete
future-law fibres, and every pair of states outside one fibre has a finite distinguishing future. -/
theorem generated_ledger_is_compiled_presentation :
    Function.Surjective (toMinimal P R) ∧
    (∀ f : State → P.MinimalCarrier,
      (∀ h, f (R.stateOf h) = Quotient.mk P.futureSetoid h) →
        f = toMinimal P R) ∧
    (∀ s t, toMinimal P R s = toMinimal P R t ↔
      ∀ w, R.futureLaw s w = R.futureLaw t w) ∧
    (∀ s t, toMinimal P R s ≠ toMinimal P R t →
      ∃ w : List Letter, R.futureLaw s w ≠ R.futureLaw t w) := by
  exact ⟨toMinimal_surjective P R, toMinimal_unique P R,
    toMinimal_eq_iff_futureLaw_eq P R, fun _ _ => exists_finite_future_of_toMinimal_ne P R⟩

end Realization

/-- Complete theorem packet for `thm:GT-derived-predictive-carrier`: future equivalence is a right
congruence on occurring branches, finite-word laws factor through quotient branch probabilities,
and every reachable deterministic realization has a unique surjection to the minimal carrier that
intertwines branch laws and all occurring updates. -/
theorem derived_predictive_relation_carrier
    {State : Type*} (R : P.Realization State) :
    Equivalence P.FutureEquivalent ∧
    (∀ {h h'} (hh : P.FutureEquivalent h h') a,
      P.branch h a ≠ 0 → P.FutureEquivalent (P.step h a) (P.step h' a)) ∧
    (∀ h w, P.probability h w = pathWeight (P := P) h w) ∧
    Function.Surjective (Realization.toMinimal P R) ∧
    (∀ s a, P.minimalBranch a (Realization.toMinimal P R s) = R.rate s a) ∧
    (∀ s a, R.rate s a ≠ 0 →
      Realization.toMinimal P R (R.update s a) =
        P.minimalUpdate a (Realization.toMinimal P R s)) ∧
    (∀ f : State → P.MinimalCarrier,
      (∀ h, f (R.stateOf h) = Quotient.mk P.futureSetoid h) →
        f = Realization.toMinimal P R) := by
  exact ⟨P.futureEquivalent_equivalence,
    fun hh a ha => P.step_futureEquivalent hh a ha,
    P.probability_eq_pathWeight,
    Realization.toMinimal_surjective P R,
    Realization.toMinimal_branch P R,
    Realization.toMinimal_update_of_occurs P R,
    Realization.toMinimal_unique P R⟩

end PredictiveSystem

end NCG.DerivedPredictiveCarrierUniversal
