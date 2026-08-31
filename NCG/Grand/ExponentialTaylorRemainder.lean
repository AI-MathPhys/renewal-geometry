/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Explicit exponential Taylor remainders

Uniform scalar estimates used by the finite holonomy, regulator, and
cofinal-mesh arguments in the Gran--Tensor development.
-/

open Finset

namespace NCG.ExponentialTaylorRemainder

/-- The exponential remainder after its linear Taylor polynomial is bounded
globally by `|x|² exp |x|`. -/
theorem abs_exp_sub_linear_le (x : ℝ) :
    |Real.exp x - (1 + x)| ≤ |x| ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num [Finset.sum_range_succ] at h
  have hr : ‖Real.exp x - (1 + x)‖ ≤ x ^ 2 * Real.exp |x| := by
    exact_mod_cast h
  simpa [Real.norm_eq_abs, sq_abs] using hr

/-- Uniform quadratic remainder on `|x| ≤ M`. -/
theorem abs_exp_sub_linear_le_on {x M : ℝ} (hM : |x| ≤ M) :
    |Real.exp x - (1 + x)| ≤ Real.exp M * |x| ^ 2 := by
  calc
    |Real.exp x - (1 + x)| ≤ |x| ^ 2 * Real.exp |x| :=
      abs_exp_sub_linear_le x
    _ ≤ |x| ^ 2 * Real.exp M := by gcongr
    _ = Real.exp M * |x| ^ 2 := by ring

/-- The exponential remainder after its quadratic Taylor polynomial is at
most `|x|³ exp |x|`.  The deliberately simple constant is convenient for
uniform compact-slab estimates. -/
theorem abs_exp_sub_quadratic_le (x : ℝ) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤
      |x| ^ 3 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 3
  norm_num [Finset.sum_range_succ] at h
  exact_mod_cast h

/-- On `|x| ≤ M`, the same remainder has the uniform cubic bound
`exp M · |x|³`. -/
theorem abs_exp_sub_quadratic_le_on {x M : ℝ} (hM : |x| ≤ M) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤
      Real.exp M * |x| ^ 3 := by
  calc
    |Real.exp x - (1 + x + x ^ 2 / 2)|
        ≤ |x| ^ 3 * Real.exp |x| := abs_exp_sub_quadratic_le x
    _ ≤ |x| ^ 3 * Real.exp M := by
      gcongr
    _ = Real.exp M * |x| ^ 3 := by ring

/-- Substitution `x = a h` produces the standard `O(h³)` estimate used for
one mesh cell. -/
theorem abs_exp_mul_sub_quadratic_le
    (a h M : ℝ) (hM : |a * h| ≤ M) :
    |Real.exp (a * h) - (1 + a * h + (a * h) ^ 2 / 2)| ≤
      Real.exp M * |a| ^ 3 * |h| ^ 3 := by
  calc
    |Real.exp (a * h) - (1 + a * h + (a * h) ^ 2 / 2)|
        ≤ Real.exp M * |a * h| ^ 3 := abs_exp_sub_quadratic_le_on hM
    _ = Real.exp M * |a| ^ 3 * |h| ^ 3 := by
      rw [abs_mul, mul_pow]
      ring

end NCG.ExponentialTaylorRemainder
