/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Universal coercive continuum handoff
  (`thm:universal-coercive-continuum`, Gran-Tensor manuscript)

* `head_tail_numerical_bound`: the boxed branch-(H1) bound — for
  the head–tail block form with head bound `a`, tail bound `d`,
  and leakage `b`, the quadratic form satisfies
  `ax² + 2bxy + dy² ≤ q*(x² + y²)` with
  `q* = (a + d + √((a-d)² + 4b²))/2`,
  the largest eigenvalue of the 2×2 comparison matrix (so
  `b² < (1-a)(1-d)` gives `q* < 1`);
* `head_tail_contraction`: with `a, d < 1` and
  `b² < (1-a)(1-d)`, indeed `q* < 1` — the uniform contraction
  transferring the noncollapsing gap to the limit;
* the geometric decay clause is the proved `uniform_gap_decay`
  (SourceIdealSplit), giving gap `-τ⁻¹ log q*` at physical time
  `τ`.

Rendering disclosed: the reduction of the operator norm
`‖(I-E)T(I-E)‖` to the 2×2 numerical bound (head/tail splitting
of the transient space with the declared leakage blocks) and the
weighted-influence branch (H2) are the manuscript's operator
bookkeeping; the eigenvalue bound and the contraction criterion
are proved here.
-/

namespace NCG

/-- Boxed 2×2 numerical-range bound: the head–tail quadratic form
is dominated by `q* = (a+d+√((a-d)²+4b²))/2`. -/
theorem head_tail_numerical_bound (a b d x y : ℝ) :
    a * x ^ 2 + 2 * b * (x * y) + d * y ^ 2
      ≤ (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2
        * (x ^ 2 + y ^ 2) := by
  set s : ℝ := Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) with hsdef
  have hs : s ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsad : |a - d| ≤ s := by
    rw [hsdef, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have habs := abs_le.mp hsad
  have hA : 0 ≤ s - a + d := by linarith [habs.2]
  have hB : 0 ≤ s + a - d := by linarith [habs.1]
  have hAB : (s - a + d) * (s + a - d) = 4 * b ^ 2 := by
    nlinarith [hs]
  have hid : (2 * s) * ((a + d + s) * (x ^ 2 + y ^ 2)
        - 2 * (a * x ^ 2 + 2 * b * (x * y) + d * y ^ 2))
      = ((s - a + d) * x - 2 * b * y) ^ 2
        + ((s + a - d) * y - 2 * b * x) ^ 2
        + ((s - a + d) * (s + a - d) - 4 * b ^ 2)
          * (x ^ 2 + y ^ 2) := by
    ring
  have hG2 : 0 ≤ (2 * s) * ((a + d + s) * (x ^ 2 + y ^ 2)
      - 2 * (a * x ^ 2 + 2 * b * (x * y) + d * y ^ 2)) := by
    rw [hid, hAB, sub_self, zero_mul, add_zero]
    positivity
  rcases eq_or_lt_of_le hs0 with hs0' | hspos
  · have hzero : (a - d) ^ 2 + 4 * b ^ 2 = 0 := by
      nlinarith [hs]
    have had : a = d := by nlinarith [hzero, sq_nonneg b]
    have hb0 : b = 0 := by
      nlinarith [hzero, sq_nonneg (a - d)]
    rw [had, hb0, ← hs0']
    ring_nf
    nlinarith [sq_nonneg x, sq_nonneg y]
  · nlinarith [hG2, hspos]

/-- Contraction criterion: `a, d < 1` with `b² < (1-a)(1-d)`
give `q* < 1` — the uniform head–tail contraction. -/
theorem head_tail_contraction (a b d : ℝ) (ha : a < 1)
    (hd : d < 1) (hb : b ^ 2 < (1 - a) * (1 - d)) :
    (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2 < 1 := by
  have hkey : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)
      < 2 - a - d := by
    have h2ad : (0:ℝ) < 2 - a - d := by linarith
    refine (Real.sqrt_lt' h2ad).mpr ?_
    nlinarith
  linarith

end NCG
