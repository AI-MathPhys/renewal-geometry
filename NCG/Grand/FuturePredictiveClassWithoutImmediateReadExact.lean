/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Future sufficiency does not create an immediate Read

This is the explicit two-class persistent process from
`cth:GT-future-no-immediate-read`.  Its one-letter future laws distinguish the two predictive
classes, while the declared same-cut Read is constant.
-/

open scoped BigOperators

namespace NCG.FuturePredictiveClassWithoutImmediateRead

abbrev State := Fin 2
abbrev Letter := Fin 2

/-- State `0` emits `a` with probability `3/4`; state `1` reverses the two probabilities. -/
def branchProbability (s : State) (a : Letter) : ℚ :=
  if s = a then 3 / 4 else 1 / 4

/-- Every letter preserves the predictive class. -/
def persistentUpdate (s : State) (_a : Letter) : State := s

/-- The only declared same-cut physical Read. -/
def sameCutRead (_s : State) : Unit := ()

theorem branchProbability_nonnegative (s : State) (a : Letter) :
    0 ≤ branchProbability s a := by
  simp only [branchProbability]
  split <;> norm_num

theorem branchProbability_normalized (s : State) :
    ∑ a, branchProbability s a = 1 := by
  fin_cases s <;> norm_num [branchProbability, Fin.sum_univ_two]

/-- Equality of all declared one-letter futures.  For this persistent process it already equals
complete future equivalence. -/
def FutureEquivalent (s t : State) : Prop :=
  ∀ a, branchProbability s a = branchProbability t a

theorem futureEquivalent_equivalence : Equivalence FutureEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · intro s a
    rfl
  · intro s t h a
    exact (h a).symm
  · intro s t u hst htu a
    exact (hst a).trans (htu a)

def futureSetoid : Setoid State where
  r := FutureEquivalent
  iseqv := futureEquivalent_equivalence

abbrev MinimalPredictiveCarrier := Quotient futureSetoid

theorem zero_one_not_futureEquivalent : ¬FutureEquivalent 0 1 := by
  intro h
  have ha := h 0
  norm_num [branchProbability] at ha

theorem predictiveClasses_distinct :
    (Quotient.mk futureSetoid 0 : MinimalPredictiveCarrier) ≠
      Quotient.mk futureSetoid 1 := by
  intro h
  exact zero_one_not_futureEquivalent (Quotient.exact h)

theorem sameCutRead_constant (s t : State) : sameCutRead s = sameCutRead t := rfl

/-- Exact finite counterexample: the normalized persistent process has two distinct classes in its
minimal future quotient, separated by the future event `a`, but no declared same-cut Read separates
them. -/
theorem future_sufficiency_does_not_create_same_cut_read :
    (∀ s, (∀ a, 0 ≤ branchProbability s a) ∧
      ∑ a, branchProbability s a = 1) ∧
    (∀ s a, persistentUpdate s a = s) ∧
    branchProbability 0 0 = 3 / 4 ∧
    branchProbability 1 0 = 1 / 4 ∧
    (Quotient.mk futureSetoid 0 : MinimalPredictiveCarrier) ≠
      Quotient.mk futureSetoid 1 ∧
    sameCutRead 0 = sameCutRead 1 := by
  refine ⟨?_, ?_, by norm_num [branchProbability], by norm_num [branchProbability],
    predictiveClasses_distinct, rfl⟩
  · intro s
    exact ⟨branchProbability_nonnegative s, branchProbability_normalized s⟩
  · intro s a
    rfl

end NCG.FuturePredictiveClassWithoutImmediateRead
