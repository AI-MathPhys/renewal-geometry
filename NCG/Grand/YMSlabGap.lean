/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Volume-uniform strong-electric `SU(3)` slab gap
  (`thm:YM-strong-electric-gap`, Gran-Tensor manuscript)

The boxed root bound in full:

* `slab_root_lt_one`: under the boxed smallness condition
  `2ε + 12·tanh η < 1` (with `b := 1 - 12·tanh η`), the boxed
  root `r = (b - √(b² - 4ε²))/(2ε)` satisfies `0 ≤ r < 1` — the
  discriminant is positive and `r < 1` is exactly the smallness
  condition;
* `slab_root_rationalized`: the stable form
  `r = 2ε/(b + √(b² - 4ε²))`, which also interprets `ε = 0` by
  continuity;
* `quadratic_gap_dichotomy`: the Schur-iteration mechanism — any
  self-consistent bound `εx² - bx + ε ≥ 0` with `x` below the
  large root forces `x` at or below the boxed small root
  (the two roots have product `1`);
* `numeric_slab_bound`: the boxed numeric instance — with
  `12·tanh η ≤ 2/3` and `0 < ε ≤ 3/26`, the root is at most
  `6ε ≤ 9/13`.

Rendering disclosed: the `SU(3)` heat-kernel/Wilson transfer
operator, the reduction of `‖T|_{Ω^⊥}‖` to the self-consistent
Schur bound `x ≤ εx² + 12·tanh η·x + ε` on the neutral sector,
and the heat-kernel estimate `ε_κ ≤ 3/26` for `κ ≥ 4` (with
`12·tanh(1/18) ≤ 2/3`) are the manuscript's model layer; the
root algebra, the dichotomy, and the numeric bound are proved
here.
-/

namespace NCG

/-- Discriminant positivity and the boxed root window: under
`2ε + (1-b) < 1`, i.e. `2ε < b`, the boxed small root satisfies
`0 ≤ r < 1`. -/
theorem slab_root_lt_one (ε b : ℝ) (hε : 0 < ε)
    (hsmall : 2 * ε < b) :
    0 ≤ (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε)
      ∧ (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε) < 1 := by
  have hb : 0 < b := lt_trans (by positivity) hsmall
  have hdisc : 0 < b ^ 2 - 4 * ε ^ 2 := by nlinarith
  have hs := Real.sqrt_nonneg (b ^ 2 - 4 * ε ^ 2)
  have hslt : Real.sqrt (b ^ 2 - 4 * ε ^ 2) ≤ b := by
    calc Real.sqrt (b ^ 2 - 4 * ε ^ 2)
        ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = b := Real.sqrt_sq hb.le
  constructor
  · apply div_nonneg _ (by positivity)
    linarith
  · rw [div_lt_one (by positivity)]
    have hkey : b - 2 * ε < Real.sqrt (b ^ 2 - 4 * ε ^ 2) := by
      have hb2ε : 0 ≤ b - 2 * ε := by linarith
      have hlt : (b - 2 * ε) ^ 2 < b ^ 2 - 4 * ε ^ 2 := by
        nlinarith
      calc b - 2 * ε = Real.sqrt ((b - 2 * ε) ^ 2) :=
            (Real.sqrt_sq hb2ε).symm
        _ < Real.sqrt (b ^ 2 - 4 * ε ^ 2) :=
            Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    linarith

/-- Rationalized stable form of the boxed root:
`(b - √(b²-4ε²))/(2ε) = 2ε/(b + √(b²-4ε²))`. -/
theorem slab_root_rationalized (ε b : ℝ) (hε : 0 < ε)
    (hsmall : 2 * ε < b) :
    (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε)
      = 2 * ε / (b + Real.sqrt (b ^ 2 - 4 * ε ^ 2)) := by
  have hb : 0 < b := lt_trans (by positivity) hsmall
  have hdisc : 0 ≤ b ^ 2 - 4 * ε ^ 2 := by nlinarith
  have hs2 : Real.sqrt (b ^ 2 - 4 * ε ^ 2) ^ 2
      = b ^ 2 - 4 * ε ^ 2 := Real.sq_sqrt hdisc
  have hden : 0 < b + Real.sqrt (b ^ 2 - 4 * ε ^ 2) := by
    have := Real.sqrt_nonneg (b ^ 2 - 4 * ε ^ 2)
    linarith
  field_simp
  nlinarith [hs2]

/-- Schur-iteration dichotomy: a self-consistent bound
`εx² - bx + ε ≥ 0` with `x` strictly below the large root
`r₊ = (b + √(b²-4ε²))/(2ε)` forces `x` at or below the boxed
small root. -/
theorem quadratic_gap_dichotomy (ε b x : ℝ) (hε : 0 < ε)
    (hsmall : 2 * ε < b)
    (hself : 0 ≤ ε * x ^ 2 - b * x + ε)
    (hbelow : x < (b + Real.sqrt (b ^ 2 - 4 * ε ^ 2))
      / (2 * ε)) :
    x ≤ (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε) := by
  have hb : 0 < b := lt_trans (by positivity) hsmall
  have hdisc : 0 ≤ b ^ 2 - 4 * ε ^ 2 := by nlinarith
  have hs2 : Real.sqrt (b ^ 2 - 4 * ε ^ 2) ^ 2
      = b ^ 2 - 4 * ε ^ 2 := Real.sq_sqrt hdisc
  set s := Real.sqrt (b ^ 2 - 4 * ε ^ 2) with hsdef
  -- factorization: ε x² - b x + ε = ε (x - r₋)(x - r₊)
  have hfact : ε * x ^ 2 - b * x + ε
      = ε * (x - (b - s) / (2 * ε))
        * (x - (b + s) / (2 * ε)) := by
    field_simp
    nlinarith [hs2]
  by_contra hgt
  have hgt' := not_le.mp hgt
  have h1 : 0 < x - (b - s) / (2 * ε) := by linarith
  have h2 : x - (b + s) / (2 * ε) < 0 := by linarith
  nlinarith [hfact, mul_pos (mul_pos hε h1) (neg_pos.mpr h2)]

/-- Boxed numeric instance: `12·tanh η ≤ 2/3` and
`0 < ε ≤ 3/26` give root `≤ 6ε ≤ 9/13`. -/
theorem numeric_slab_bound (ε t : ℝ) (hε : 0 < ε)
    (hεb : ε ≤ 3 / 26) (ht : t ≤ 2 / 3) (_ht0 : 0 ≤ t) :
    ((1 - t) - Real.sqrt ((1 - t) ^ 2 - 4 * ε ^ 2))
      / (2 * ε) ≤ 9 / 13 := by
  have hsmall : 2 * ε < 1 - t := by nlinarith
  have hb : 0 < 1 - t := lt_trans (by positivity) hsmall
  rw [slab_root_rationalized ε (1 - t) hε hsmall]
  have hs := Real.sqrt_nonneg ((1 - t) ^ 2 - 4 * ε ^ 2)
  have hden : 1 / 3 ≤ (1 - t)
      + Real.sqrt ((1 - t) ^ 2 - 4 * ε ^ 2) := by
    nlinarith
  have hdenpos : 0 < (1 - t)
      + Real.sqrt ((1 - t) ^ 2 - 4 * ε ^ 2) := by
    linarith
  rw [div_le_iff₀ hdenpos]
  nlinarith

end NCG
