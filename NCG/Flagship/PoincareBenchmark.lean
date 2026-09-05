/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Perelman benchmark interface
  (`prop:Poincare-benchmark`, flagship manuscript)

The formal core of the scale-flow benchmark interface:

* `benchmark_surgery_budget`: a scale-flow module with monotone
  entropy between surgeries and a summable entropy/coercivity
  budget keeps the total entropy controlled —
  `S(n) ≥ S(0) - Σ_{k<n} b(k)` — the shape of the
  monotone-entropy/controlled-surgery certificate the interface
  demands;
* `benchmark_monotone`: with an empty budget the entropy is
  monotone along the flow (the surgery-free clause).

Rendering disclosed: per the manuscript, Perelman's Ricci-flow
solution is used ONLY as an external benchmark for a valid
scale-flow module (monotone entropy, canonical-neighbourhood
control, no collapsing, controlled surgery with summable
budget); nothing here reproves Poincaré or exports Perelman's
geometric estimates to arithmetic, gauge, fluid, or complexity
sectors — the interface is the displayed certificate shape, and
its formal core is the budget arithmetic proved here.
-/

namespace NCG

/-- The controlled-surgery budget: entropy drops at most `b k`
per surgery, so `S n ≥ S 0 - Σ_{k<n} b k`. -/
theorem benchmark_surgery_budget (S b : ℕ → ℝ)
    (hstep : ∀ k, S k - b k ≤ S (k + 1)) :
    ∀ n, S 0 - ∑ k ∈ Finset.range n, b k ≤ S n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := hstep n
    linarith

/-- Surgery-free clause: an empty budget gives monotone entropy
along the flow. -/
theorem benchmark_monotone (S : ℕ → ℝ)
    (hstep : ∀ k, S k - 0 ≤ S (k + 1)) : Monotone S := by
  refine monotone_nat_of_le_succ fun k => ?_
  have := hstep k
  linarith

end NCG
