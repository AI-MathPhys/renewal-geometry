/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Nonsummable defects need not obstruct a unique limit
  (`cth:nonsummable-defects-convergent`,
  Gran-Tensor manuscript)

* `nonsummable_defects_convergent`: the Bernoulli states with
  parameter `p_n = 1/2 + (-1)ⁿ/(n+2)`:
  (i) converge to the unique fair limit `1/2`;
  (ii) have non-summable one-step defects
      (`|p_{n+1} - p_n| = 1/(n+2) + 1/(n+3)` dominates the
      harmonic tail).

Hence summability is a sharp sufficient condition for a
quantitative correction, not a necessary condition for
convergence.
-/

namespace NCG

/-- `cth:nonsummable-defects-convergent`. -/
theorem nonsummable_defects_convergent :
    -- (i) the states converge to the fair limit
    Filter.Tendsto
      (fun n : ℕ => (1/2 : ℝ) + (-1)^n / (n + 2))
      Filter.atTop (nhds (1/2))
    -- (ii) the one-step defects are not summable
    ∧ ¬ Summable (fun n : ℕ =>
        |((1/2 : ℝ) + (-1)^(n+1) / (n + 3))
          - ((1/2 : ℝ) + (-1)^n / (n + 2))|) := by
  constructor
  · have h0 : Filter.Tendsto
        (fun n : ℕ => ((-1 : ℝ))^n / (n + 2))
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
      rw [show ‖((n : ℝ) + 2)‖ = (n : ℝ) + 2 from by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]]
      exact one_div_le_one_div_of_le (by positivity)
        (by linarith)
    have := Filter.Tendsto.const_add (1/2 : ℝ) h0
    simpa using this
  · intro hsum
    -- the defect dominates the harmonic tail `1/(n+2)`
    have hd : ∀ n : ℕ,
        ((1 : ℝ) / (n + 2))
          ≤ |((1/2 : ℝ) + (-1)^(n+1) / (n + 3))
            - ((1/2 : ℝ) + (-1)^n / (n + 2))| := by
      intro n
      have h1 : ((1/2 : ℝ) + (-1)^(n+1) / (n + 3))
          - ((1/2 : ℝ) + (-1)^n / (n + 2))
          = (-1)^(n+1) * (1 / (n + 3) + 1 / (n + 2)) := by
        rw [pow_succ]
        ring
      rw [h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, abs_of_pos (by positivity)]
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 3) := by positivity
      linarith
    have hharm : Summable (fun n : ℕ =>
        (1 : ℝ) / ((n : ℝ) + 2)) :=
      Summable.of_nonneg_of_le
        (fun n => by positivity) hd hsum
    have hshift : Summable (fun n : ℕ =>
        (fun m : ℕ => (1 : ℝ) / (m : ℝ)) (n + 2)) := by
      have heq : (fun n : ℕ =>
          (fun m : ℕ => (1 : ℝ) / (m : ℝ)) (n + 2))
          = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) := by
        funext n
        push_cast
        ring
      rw [heq]
      exact hharm
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff 2).mp hshift)

end NCG
