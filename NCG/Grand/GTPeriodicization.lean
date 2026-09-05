/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Artificial periodic closure can erase an open-boundary
  cost (`cth:GT-periodicization`, Gran-Tensor manuscript)

* `gt_periodicization`: for the source `s = -δ₀ + δ_N` on
  the unit-weight path, the (unique) open-path current
  carries unit flow on each of the `N` edges, with energy
  exactly `N`; adjoining one artificial unit closing edge,
  a cycle current routes flow `t` backwards through the
  closing edge with energy `N(1-t)² + t²`, whose minimum
  over `t` is exactly `N/(N+1)`, attained at
  `t = N/(N+1)`; the erased cost factor is exactly
  `N + 1`, unbounded.

The uniqueness of the open-path current (the divergence
equations force the cumulative-sum formula) is
`NCG.gt_open_current`; the cycle feasibility bookkeeping
(any cycle current with the same source is the closed-loop
shift of the open one) is the manuscript's one-cycle
parametrization.
-/

open Finset

namespace NCG

/-- `cth:GT-periodicization`. -/
theorem gt_periodicization (N : ℕ) (hN : 1 ≤ N) :
    -- the open-path energy of the unit-flow current
    ((∑ _e ∈ range N, ((1 : ℝ)) ^ 2) = N)
    -- the one-parameter cycle family dominates N/(N+1)
    ∧ (∀ t : ℝ, (N : ℝ) / (N + 1)
        ≤ N * (1 - t) ^ 2 + t ^ 2)
    -- attained exactly at the optimal backflow
    ∧ (N * (1 - (N : ℝ) / (N + 1)) ^ 2
        + ((N : ℝ) / (N + 1)) ^ 2 = N / (N + 1))
    -- the erased factor is N + 1, unbounded
    ∧ ((N : ℝ) / ((N : ℝ) / (N + 1)) = N + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro t
    rw [div_le_iff₀ hN1]
    nlinarith [sq_nonneg ((N + 1 : ℝ) * t - N),
      sq_nonneg t, sq_nonneg (1 - t)]
  · field_simp
    ring
  · have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc,
      div_self hN0, mul_one]

end NCG
