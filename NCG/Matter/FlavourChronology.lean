/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Flavour chronology: mirror amplitudes and the pair selector
(SM_emergence, Phase 2)

* `mirror_relative_rotation` — `thm:mirror-amplitudes-main` (boxed
  rotation): for the coherent mirror amplitudes
  `A(c_u) = (a, b)`, `A(c_d) = (a, -b)` with
  `a = √2·x⁴/D`, `b = √6·x²(x-1)/(2D)`, the relative light-plane
  rotation is the `D`-independent closed form
  `ℓ_FR(x) = 2a(-b)/(a² + b²) = 4√3·x²(1-x)/(4x⁴ + 3(1-x)²)`;
* `pair_selector_dominance`, `pair_selector_suppression` —
  `thm:pair-selector-main`: in the alternating pair-orbit matrix
  `Ξ_x` the mirror pair carries the strictly maximal area
  (`x < 1 + 3x + x²` for `0 < x < 1`, with `C(x) > 0`), and pairs
  through `r₂₃` are suppressed by exactly
  `ε_pair(x) = x/(1 + 3x + x²)`.
-/

namespace NCG

open Real

/-- `√2·√6 = 2√3`. -/
theorem sqrt_two_mul_sqrt_six :
    Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (2:ℝ) * 6 = 2 ^ 2 * 3 by norm_num]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- `thm:mirror-amplitudes-main` (relative light-plane rotation): the
mirror pair `(a, ±b)` has the `D`-independent relative rotation
`2a(-b)/(a²+b²) = 4√3 x²(1-x)/(4x⁴+3(1-x)²)`. -/
theorem mirror_relative_rotation (x D : ℝ) (hx : x ≠ 0) (hD : D ≠ 0) :
    2 * (Real.sqrt 2 * x ^ 4 / D)
        * (-(Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D)))
      / ((Real.sqrt 2 * x ^ 4 / D) ^ 2
        + (Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D)) ^ 2)
    = 4 * Real.sqrt 3 * x ^ 2 * (1 - x)
      / (4 * x ^ 4 + 3 * (1 - x) ^ 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hx4 : (0:ℝ) < x ^ 4 := by positivity
  have hden : (0:ℝ) < 4 * x ^ 4 + 3 * (1 - x) ^ 2 := by
    nlinarith [sq_nonneg (1 - x)]
  have ha2 : (Real.sqrt 2 * x ^ 4 / D) ^ 2 = 2 * x ^ 8 / D ^ 2 := by
    rw [div_pow, mul_pow, h2]
    ring_nf
  have hb2 : (Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D)) ^ 2
      = 3 * x ^ 4 * (x - 1) ^ 2 / (2 * D ^ 2) := by
    rw [div_pow, mul_pow, mul_pow, h6]
    rw [show ((2:ℝ) * D) ^ 2 = 2 * (2 * D ^ 2) by ring]
    rw [show (6:ℝ) * (x ^ 2) ^ 2 * (x - 1) ^ 2
        = 2 * (3 * x ^ 4 * (x - 1) ^ 2) by ring]
    rw [mul_div_mul_left _ _ (two_ne_zero)]
  have hab : (Real.sqrt 2 * x ^ 4 / D)
      * (Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D))
      = Real.sqrt 3 * x ^ 6 * (x - 1) / D ^ 2 := by
    rw [div_mul_div_comm]
    rw [show Real.sqrt 2 * x ^ 4 * (Real.sqrt 6 * x ^ 2 * (x - 1))
        = (Real.sqrt 2 * Real.sqrt 6) * (x ^ 6 * (x - 1)) by ring,
      sqrt_two_mul_sqrt_six]
    rw [show D * (2 * D) = 2 * D ^ 2 by ring]
    rw [show (2:ℝ) * Real.sqrt 3 * (x ^ 6 * (x - 1))
        = 2 * (Real.sqrt 3 * x ^ 6 * (x - 1)) by ring]
    rw [mul_div_mul_left _ _ (two_ne_zero)]
  have hmain : 2 * (Real.sqrt 2 * x ^ 4 / D)
      * (-(Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D)))
      = -(2 * ((Real.sqrt 2 * x ^ 4 / D)
        * (Real.sqrt 6 * x ^ 2 * (x - 1) / (2 * D)))) := by
    ring
  rw [hmain, hab, ha2, hb2]
  have hD2pos : (0:ℝ) < D ^ 2 :=
    lt_of_le_of_ne (sq_nonneg D) (Ne.symm hD2)
  have hsum_pos : (0:ℝ) < 2 * x ^ 8 / D ^ 2
      + 3 * x ^ 4 * (x - 1) ^ 2 / (2 * D ^ 2) := by
    have hx8 : (0:ℝ) < x ^ 8 := by positivity
    have h1 : (0:ℝ) < 2 * x ^ 8 / D ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 3 * x ^ 4 * (x - 1) ^ 2 / (2 * D ^ 2) := by
      positivity
    linarith
  rw [div_eq_div_iff (ne_of_gt hsum_pos) (ne_of_gt hden)]
  field_simp
  ring

/-- `thm:pair-selector-main` (dominance): for `0 < x < 1` and
`C(x) > 0`, the mirror-pair entry `C(1+3x+x²)` strictly dominates
the `r₂₃`-pair entries `Cx` — the mirror pair has strictly maximal
area. -/
theorem pair_selector_dominance (x C : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hC : 0 < C) :
    C * x < C * (1 + 3 * x + x ^ 2) := by
  apply mul_lt_mul_of_pos_left _ hC
  nlinarith

/-- `thm:pair-selector-main` (suppression ratio): pairs involving
`r₂₃` are suppressed by exactly `ε_pair(x) = x/(1+3x+x²)`, which is
strictly less than one on `0 < x < 1`. -/
theorem pair_selector_suppression (x C : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hC : 0 < C) :
    C * x / (C * (1 + 3 * x + x ^ 2)) = x / (1 + 3 * x + x ^ 2) ∧
    x / (1 + 3 * x + x ^ 2) < 1 := by
  have hpos : (0:ℝ) < 1 + 3 * x + x ^ 2 := by nlinarith
  constructor
  · rw [mul_div_mul_left _ _ (ne_of_gt hC)]
  · rw [div_lt_one hpos]
    nlinarith

end NCG
