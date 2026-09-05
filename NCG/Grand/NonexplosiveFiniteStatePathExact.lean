/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCJumpSequenceLawExact

/-!
# Nonexplosive finite-state step paths

Mathlib currently has no dedicated Skorokhod path-space carrier.  This file
builds the deterministic finite-state carrier needed here: a positive,
nonexplosive holding-time clock, its first-crossing jump index, and the
associated right-continuous step path.  Every compact time interval sees only
finitely many jumps.
-/

open Filter Finset Set
open scoped Topology BigOperators

noncomputable section

namespace NCG.NonexplosiveFiniteStatePath

/-- Concrete càdlàg certificate for a path on nonnegative real time with
finite discrete state: local constancy from the right and existence of a
locally constant left value at every positive time. -/
structure CadlagStepPath (S : Type*) where
  toFun : ℝ → S
  rightLocallyConstant : ∀ t,
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s, t ≤ s → s < t + delta → toFun s = toFun t
  leftLocallyConstant : ∀ t, 0 < t →
    ∃ leftState : S, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, 0 ≤ s → t - delta < s → s < t → toFun s = leftState

/-- Time of the `n`th jump for a sequence of holding times. -/
def cumulativeHold (hold : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, hold i

@[simp] theorem cumulativeHold_zero (hold : ℕ → ℝ) :
    cumulativeHold hold 0 = 0 := by
  simp [cumulativeHold]

theorem cumulativeHold_succ (hold : ℕ → ℝ) (n : ℕ) :
    cumulativeHold hold (n + 1) = cumulativeHold hold n + hold n := by
  simp [cumulativeHold, Finset.sum_range_succ]

/-- A positive holding-time clock with no finite accumulation of jumps. -/
structure Clock where
  hold : ℕ → ℝ
  hold_pos : ∀ n, 0 < hold n
  eventually_after : ∀ T : ℝ, ∃ n : ℕ, T < cumulativeHold hold (n + 1)

/-- Cumulative jump times of a positive clock are strictly increasing. -/
theorem Clock.cumulativeHold_strictMono (clock : Clock) :
    StrictMono (cumulativeHold clock.hold) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [cumulativeHold_succ]
  exact lt_add_of_pos_right _ (clock.hold_pos n)

/-- Index of the state occupied at time `t`: the first holding interval whose
right endpoint lies strictly after `t`. -/
def jumpIndex (clock : Clock) (t : ℝ) : ℕ :=
  Nat.find (clock.eventually_after t)

/-- The selected holding interval ends after the observation time. -/
theorem jumpIndex_lt_nextJump (clock : Clock) (t : ℝ) :
    t < cumulativeHold clock.hold (jumpIndex clock t + 1) :=
  Nat.find_spec (clock.eventually_after t)

/-- No earlier holding interval ends after the observation time. -/
theorem earlierJump_le_time (clock : Clock) (t : ℝ)
    {m : ℕ} (hm : m < jumpIndex clock t) :
    cumulativeHold clock.hold (m + 1) ≤ t := by
  exact le_of_not_gt
    (((Nat.find_eq_iff (clock.eventually_after t)).mp rfl).2 m hm)

/-- The jump index is monotone in time. -/
theorem jumpIndex_mono (clock : Clock) : Monotone (jumpIndex clock) := by
  intro s t hst
  apply Nat.find_min'
  exact hst.trans_lt (jumpIndex_lt_nextJump clock t)

/-- The first-crossing index stays fixed in a nontrivial right neighborhood. -/
theorem jumpIndex_eq_on_right_window (clock : Clock) (t s : ℝ)
    (hts : t ≤ s)
    (hs : s < cumulativeHold clock.hold (jumpIndex clock t + 1)) :
    jumpIndex clock s = jumpIndex clock t := by
  apply (Nat.find_eq_iff (clock.eventually_after s)).2
  constructor
  · exact hs
  · intro m hm
    have hmle := earlierJump_le_time clock t hm
    exact not_lt_of_ge (hmle.trans hts)

/-- A time lying between two consecutive cumulative jump times has the
corresponding jump index. -/
theorem jumpIndex_eq_of_between (clock : Clock) (m : ℕ) (s : ℝ)
    (hlower : cumulativeHold clock.hold m ≤ s)
    (hupper : s < cumulativeHold clock.hold (m + 1)) :
    jumpIndex clock s = m := by
  apply (Nat.find_eq_iff (clock.eventually_after s)).2
  constructor
  · exact hupper
  · intro j hj
    have hjm : j + 1 ≤ m := Nat.succ_le_iff.mpr hj
    have hcum : cumulativeHold clock.hold (j + 1) ≤
        cumulativeHold clock.hold m :=
      (clock.cumulativeHold_strictMono.monotone hjm)
    exact not_lt_of_ge (hcum.trans hlower)

/-- At every positive time the jump index is constant on a nontrivial left
neighborhood, possibly with the preceding index at an exact jump time. -/
theorem jumpIndex_leftLocallyConstant (clock : Clock) (t : ℝ) (ht : 0 < t) :
    ∃ m : ℕ, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, 0 ≤ s → t - delta < s → s < t → jumpIndex clock s = m := by
  generalize hn : jumpIndex clock t = n
  cases n with
  | zero =>
      refine ⟨0, t, ht, ?_⟩
      intro s hs0 _hst hs
      apply jumpIndex_eq_of_between clock 0 s
      · simpa using hs0
      · exact hs.trans (by simpa [hn] using jumpIndex_lt_nextJump clock t)
  | succ m =>
      have hm_lt : m < jumpIndex clock t := by simp [hn]
      have hcum_le : cumulativeHold clock.hold (m + 1) ≤ t :=
        earlierJump_le_time clock t hm_lt
      by_cases hstrict : cumulativeHold clock.hold (m + 1) < t
      · let delta := t - cumulativeHold clock.hold (m + 1)
        have hdelta : 0 < delta := sub_pos.mpr hstrict
        refine ⟨m + 1, delta, hdelta, ?_⟩
        intro s _hs0 hleft hright
        apply jumpIndex_eq_of_between clock (m + 1) s
        · dsimp only [delta] at hleft
          linarith
        · exact hright.trans (by
            simpa [hn] using jumpIndex_lt_nextJump clock t)
      · have heq : cumulativeHold clock.hold (m + 1) = t :=
          le_antisymm hcum_le (le_of_not_gt hstrict)
        refine ⟨m, clock.hold m, clock.hold_pos m, ?_⟩
        intro s _hs0 hleft hright
        apply jumpIndex_eq_of_between clock m s
        · rw [← heq, cumulativeHold_succ] at hleft
          linarith
        · simpa [heq] using hright

/-- State-valued step path realized by a nonexplosive clock and a sequence of
successive states. -/
def realizedState {S : Type*} (clock : Clock) (state : ℕ → S) (t : ℝ) : S :=
  state (jumpIndex clock t)

/-- The realized path is constant on an explicit right neighborhood of every
time.  This is the right-continuity clause for a finite discrete state space. -/
theorem realizedState_rightLocallyConstant
    {S : Type*} (clock : Clock) (state : ℕ → S) (t : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s, t ≤ s → s < t + delta →
        realizedState clock state s = realizedState clock state t := by
  let delta := cumulativeHold clock.hold (jumpIndex clock t + 1) - t
  have hdelta : 0 < delta := sub_pos.mpr (jumpIndex_lt_nextJump clock t)
  refine ⟨delta, hdelta, ?_⟩
  intro s hts hs
  unfold realizedState
  apply congrArg state
  apply jumpIndex_eq_on_right_window clock t s hts
  dsimp only [delta] at hs
  linarith

/-- The realized finite-state path has an explicit left limit at every
positive time. -/
theorem realizedState_leftLocallyConstant
    {S : Type*} (clock : Clock) (state : ℕ → S) (t : ℝ) (ht : 0 < t) :
    ∃ leftState : S, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, 0 ≤ s → t - delta < s → s < t →
        realizedState clock state s = leftState := by
  obtain ⟨m, delta, hdelta, hindex⟩ :=
    jumpIndex_leftLocallyConstant clock t ht
  refine ⟨state m, delta, hdelta, ?_⟩
  intro s hs0 hleft hright
  unfold realizedState
  rw [hindex s hs0 hleft hright]

/-- Every positive nonexplosive clock and state sequence canonically defines
a finite-state càdlàg step path. -/
def realizedCadlagStepPath
    {S : Type*} (clock : Clock) (state : ℕ → S) : CadlagStepPath S where
  toFun := realizedState clock state
  rightLocallyConstant := realizedState_rightLocallyConstant clock state
  leftLocallyConstant := realizedState_leftLocallyConstant clock state

@[simp] theorem realizedCadlagStepPath_apply
    {S : Type*} (clock : Clock) (state : ℕ → S) (t : ℝ) :
    (realizedCadlagStepPath clock state).toFun t =
      realizedState clock state t := rfl

/-- On the entire compact horizon `[0,T]`, the occupied-state index is bounded
by the single finite number `jumpIndex T`. -/
theorem realizedState_finiteHorizon_index_bound
    (clock : Clock) {t T : ℝ} (htT : t ≤ T) :
    jumpIndex clock t ≤ jumpIndex clock T :=
  jumpIndex_mono clock htT

/-- A jump sequence stores holding time in the first coordinate and state in
the second; dropping the initial dummy entry produces the physical clock. -/
def clockOfJumpSequence (z : ℕ → ℝ × S)
    (hpos : ∀ n, 0 < (z (n + 1)).1)
    (hnonexplosive : ∀ T, ∃ n,
      T < cumulativeHold (fun m => (z (m + 1)).1) (n + 1)) : Clock where
  hold n := (z (n + 1)).1
  hold_pos := hpos
  eventually_after := hnonexplosive

/-- Realized state path of a certified nonexplosive jump sequence. -/
def realizedJumpSequenceState (z : ℕ → ℝ × S)
    (hpos : ∀ n, 0 < (z (n + 1)).1)
    (hnonexplosive : ∀ T, ∃ n,
      T < cumulativeHold (fun m => (z (m + 1)).1) (n + 1))
    (t : ℝ) : S :=
  realizedState (clockOfJumpSequence z hpos hnonexplosive)
    (fun n => (z n).2) t

/-- Càdlàg step-path certificate extracted from a nonexplosive jump
sequence. -/
def cadlagStepPathOfJumpSequence (z : ℕ → ℝ × S)
    (hpos : ∀ n, 0 < (z (n + 1)).1)
    (hnonexplosive : ∀ T, ∃ n,
      T < cumulativeHold (fun m => (z (m + 1)).1) (n + 1)) :
    CadlagStepPath S :=
  realizedCadlagStepPath (clockOfJumpSequence z hpos hnonexplosive)
    (fun n => (z n).2)

/-- Certified jump-sequence paths inherit explicit right-local constancy. -/
theorem realizedJumpSequenceState_rightLocallyConstant
    (z : ℕ → ℝ × S)
    (hpos : ∀ n, 0 < (z (n + 1)).1)
    (hnonexplosive : ∀ T, ∃ n,
      T < cumulativeHold (fun m => (z (m + 1)).1) (n + 1))
    (t : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s, t ≤ s → s < t + delta →
        realizedJumpSequenceState z hpos hnonexplosive s =
          realizedJumpSequenceState z hpos hnonexplosive t :=
  realizedState_rightLocallyConstant
    (clockOfJumpSequence z hpos hnonexplosive) (fun n => (z n).2) t

/-- Certified jump-sequence paths also inherit an explicit left limit at
every positive time. -/
theorem realizedJumpSequenceState_leftLocallyConstant
    (z : ℕ → ℝ × S)
    (hpos : ∀ n, 0 < (z (n + 1)).1)
    (hnonexplosive : ∀ T, ∃ n,
      T < cumulativeHold (fun m => (z (m + 1)).1) (n + 1))
    (t : ℝ) (ht : 0 < t) :
    ∃ leftState : S, ∃ delta : ℝ, 0 < delta ∧
      ∀ s, 0 ≤ s → t - delta < s → s < t →
        realizedJumpSequenceState z hpos hnonexplosive s = leftState :=
  realizedState_leftLocallyConstant
    (clockOfJumpSequence z hpos hnonexplosive) (fun n => (z n).2) t ht

end NCG.NonexplosiveFiniteStatePath
