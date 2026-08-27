/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTPeriodicization
import NCG.Grand.GTSourceVariance

/-!
# Exhaustion of feasible currents on the artificially closed path

The periodicization counterexample previously computed the energy of the
one-parameter backflow family.  This file proves that conservation forces every
feasible current on the one-cycle graph to belong to that family, so the scalar
minimum is the minimum over the full feasible-current space.
-/

open Finset

namespace NCG

/-- A conserved current for the unit source from the left to the right endpoint
after adding one closing edge.  Interior conservation makes all path-edge
currents equal; endpoint conservation gives `path - closing = 1`. -/
structure UnitSourceCycleCurrent (N : ℕ) [NeZero N] where
  path : Fin N → ℝ
  closing : ℝ
  path_constant : ∀ i j, path i = path j
  source_balance : path 0 - closing = 1

/-- The current with backflow parameter `t`: `1-t` on every physical path edge
and `-t` on the artificial closing edge. -/
def cycleCurrentOfBackflow (N : ℕ) [NeZero N] (t : ℝ) :
    UnitSourceCycleCurrent N where
  path := fun _ => 1 - t
  closing := -t
  path_constant := fun _ _ => rfl
  source_balance := by ring

/-- Unit-resistance energy of a feasible closed-cycle current. -/
def unitSourceCycleEnergy {N : ℕ} [NeZero N]
    (j : UnitSourceCycleCurrent N) : ℝ :=
  ∑ i, (j.path i) ^ 2 + j.closing ^ 2

/-- Conservation exhausts the full feasible current space by a unique backflow
parameter. -/
theorem unitSourceCycleCurrent_unique_backflow {N : ℕ} [NeZero N]
    (j : UnitSourceCycleCurrent N) :
    ∃! t : ℝ,
      (∀ i, j.path i = 1 - t) ∧ j.closing = -t := by
  refine ⟨-j.closing, ?_, ?_⟩
  · constructor
    · intro i
      calc
        j.path i = j.path 0 := j.path_constant i 0
        _ = 1 + j.closing := by linarith [j.source_balance]
        _ = 1 - -j.closing := by ring
    · ring
  · intro t ht
    linarith [ht.2]

/-- The energy of every feasible current is the scalar quadratic from the
backflow calculation. -/
theorem unitSourceCycleEnergy_eq_quadratic {N : ℕ} [NeZero N]
    (j : UnitSourceCycleCurrent N) (t : ℝ)
    (hpath : ∀ i, j.path i = 1 - t) (hclosing : j.closing = -t) :
    unitSourceCycleEnergy j = N * (1 - t) ^ 2 + t ^ 2 := by
  simp_rw [unitSourceCycleEnergy, hpath, hclosing]
  simp

/-- The minimum over all conserved cycle currents is exactly `N/(N+1)`, and
is attained by the unique optimal backflow current. -/
theorem unitSourceCycleEnergy_isLeast (N : ℕ) (hN : 1 ≤ N) :
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    IsLeast (Set.range (unitSourceCycleEnergy (N := N)))
      ((N : ℝ) / (N + 1)) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨_, hlower, hattain, _⟩ := gt_periodicization N hN
  constructor
  · refine ⟨cycleCurrentOfBackflow N ((N : ℝ) / (N + 1)), ?_⟩
    rw [unitSourceCycleEnergy_eq_quadratic _ ((N : ℝ) / (N + 1))
      (fun _ => rfl) rfl]
    exact hattain
  · intro e he
    obtain ⟨j, rfl⟩ := he
    obtain ⟨t, ht, -⟩ := unitSourceCycleCurrent_unique_backflow j
    rw [unitSourceCycleEnergy_eq_quadratic j t ht.1 ht.2]
    exact hlower t

/-- The physical open current costs `N`, whereas the least current after
artificial closure costs `N/(N+1)`; the exact erasure factor is `N+1`. -/
theorem periodicClosure_full_feasible_counterexample (N : ℕ) (hN : 1 ≤ N) :
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    (∑ _e ∈ range N, ((1 : ℝ)) ^ 2) = N
    ∧ IsLeast (Set.range (unitSourceCycleEnergy (N := N)))
        ((N : ℝ) / (N + 1))
    ∧ (N : ℝ) / ((N : ℝ) / (N + 1)) = N + 1 := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨hopen, _, _, hfactor⟩ := gt_periodicization N hN
  exact ⟨hopen, unitSourceCycleEnergy_isLeast N hN, hfactor⟩

/-- The exact erasure factors are unbounded. -/
theorem periodicClosure_erasure_factors_unbounded (c : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ c < (N : ℝ) + 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt c
  refine ⟨max 1 n, Nat.le_max_left _ _, ?_⟩
  have hnmax : (n : ℝ) ≤ (max 1 n : ℕ) := by exact_mod_cast Nat.le_max_right 1 n
  linarith

end NCG
