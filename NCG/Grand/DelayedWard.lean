/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One delayed binary Read evaluates the minimal Ward current
  (`thm:delayed-binary-Ward`, Gran-Tensor manuscript)

* `delayed_binary_ward`: for `n` writing atoms joined to one
  nonwriting atom at the common rate `r`:
  (i) the boxed closed form
      `h_n(t) = 1/(n+1) + (a - 1/(n+1))e^{-(n+1)rt}`
      solves the boxed relaxation equation
      `h_n'(t) = r(1 - (n+1)h_n(t))` at every time;
  (ii) it satisfies the initial condition `h_n(0) = a`;
  (iii) the boxed outward cross-fibre current
      `𝒥 = -h_n'(0) = r((n+1)a - 1)`;
  (iv) the boxed identification `𝒥 = r·n·J_n` with the
      one-scalar Ward coordinate `J_n = a - (1-a)/n`.

The reduction of arbitrary writing-to-writing dynamics to
the two-state nonwriting probability (orbit preservation
plus the common exchange rate) is the manuscript's
symmetry step producing this scalar equation.
-/

namespace NCG

/-- `thm:delayed-binary-Ward`. -/
theorem delayed_binary_ward (n : ℕ) (r a t : ℝ)
    (hn : 1 ≤ n) :
    -- (i) the boxed closed form solves the relaxation
    -- equation
    (HasDerivAt
      (fun τ : ℝ => 1 / ((n : ℝ) + 1)
        + (a - 1 / ((n : ℝ) + 1))
          * Real.exp (-((n : ℝ) + 1) * r * τ))
      (r * (1 - ((n : ℝ) + 1)
        * (1 / ((n : ℝ) + 1) + (a - 1 / ((n : ℝ) + 1))
          * Real.exp (-((n : ℝ) + 1) * r * t)))) t)
    -- (ii) the initial condition
    ∧ (1 / ((n : ℝ) + 1) + (a - 1 / ((n : ℝ) + 1))
        * Real.exp (-((n : ℝ) + 1) * r * 0) = a)
    -- (iii) the boxed outward current
    ∧ (-((a - 1 / ((n : ℝ) + 1)) * (-((n : ℝ) + 1) * r))
        = r * (((n : ℝ) + 1) * a - 1))
    -- (iv) the boxed identification with `r n J_n`
    ∧ (r * (((n : ℝ) + 1) * a - 1)
        = r * n * (a - (1 - a) / n)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hlin : HasDerivAt
        (fun τ : ℝ => -((n : ℝ) + 1) * r * τ)
        (-((n : ℝ) + 1) * r) t := by
      simpa using (hasDerivAt_id t).const_mul
        (-((n : ℝ) + 1) * r)
    have hexp := (Real.hasDerivAt_exp
      (-((n : ℝ) + 1) * r * t)).comp t hlin
    have hmul := (hexp.const_mul
      (a - 1 / ((n : ℝ) + 1))).const_add
      (1 / ((n : ℝ) + 1))
    have hm := hmul
    simp only [Function.comp] at hm
    have hval : r * (1 - ((n : ℝ) + 1)
          * (1 / ((n : ℝ) + 1) + (a - 1 / ((n : ℝ) + 1))
            * Real.exp (-((n : ℝ) + 1) * r * t)))
        = (a - 1 / ((n : ℝ) + 1))
          * (Real.exp (-((n : ℝ) + 1) * r * t)
            * (-((n : ℝ) + 1) * r)) := by
      have hcan0 : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))
          = 1 := by
        rw [mul_one_div, div_self hn1]
      linear_combination (-r) * hcan0
    rw [hval]
    exact hm
  · rw [mul_zero, Real.exp_zero, mul_one]
    ring
  · have hcan : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
      rw [mul_one_div, div_self hn1]
    linear_combination (-r) * hcan
  · field_simp
    ring

end NCG
