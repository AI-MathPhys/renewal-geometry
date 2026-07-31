/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bridge boundary-layer displacement
  (`prop:bridge-displacement`, GR_emergence)

The calibrated bridge coordinate `q = e^{-χ*}` with Perron rapidity
`sinh χ* = Bε` has the exact closed form

  `1 - q = 1 - e^{-arsinh(Bε)} = 1 + Bε - √(1 + (Bε)²)`,

so the displacement error is exactly `√(1+x²) - 1 ∈ [0, x²/2]` — a
sharp version of the manuscript's `1 - q = Bε + O((Bε)²)`:

* `exp_neg_arsinh` — `e^{-arsinh x} = √(1+x²) - x`;
* `bridge_displacement` — `|1 - e^{-arsinh x} - x| ≤ x²/2`;
* `bridge_displacement_hubble` — the `B = dH` substitution
  `|1 - q - dHε| ≤ d²(Hε)²/2`;
* `krein_expansion_arrow` — the sign equivalences
  `0 < B ↔ 0 < χ* ↔ 0 < 1 - e^{-2χ*}`.
-/

namespace NCG

open Real

/-- The exact reciprocal form of the bridge coordinate. -/
theorem exp_neg_arsinh (x : ℝ) :
    Real.exp (-(Real.arsinh x)) = Real.sqrt (1 + x ^ 2) - x := by
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have habs : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    linarith
  have hpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    rcases abs_le.mp habs with ⟨h1, _⟩
    have hlt : |x| < Real.sqrt (1 + x ^ 2) := by
      rcases lt_or_eq_of_le habs with h | h
      · exact h
      · exfalso
        have := congrArg (fun y => y ^ 2) h
        simp only [sq_abs] at this
        rw [hsq] at this
        linarith
    rcases abs_lt.mp hlt with ⟨h2, _⟩
    linarith
  have hprod : (x + Real.sqrt (1 + x ^ 2))
      * (Real.sqrt (1 + x ^ 2) - x) = 1 := by
    nlinarith [hsq]
  rw [Real.exp_neg, Real.exp_arsinh]
  rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv, eq_comm]
  field_simp
  linarith [hprod]

/-- `prop:bridge-displacement` (sharp form): the bridge displacement
agrees with the rapidity to second order, with explicit constant. -/
theorem bridge_displacement (x : ℝ) :
    |1 - Real.exp (-(Real.arsinh x)) - x| ≤ x ^ 2 / 2 := by
  rw [exp_neg_arsinh]
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hlow : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [hsq, Real.sqrt_nonneg (1 + x ^ 2)]
  have hup : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 / 2 := by
    nlinarith [hsq, Real.sqrt_nonneg (1 + x ^ 2)]
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- `prop:bridge-displacement` (Hubble substitution): with `B = dH`,
`1 - q = dHε + O((Hε)²)` with explicit constant `d²/2`. -/
theorem bridge_displacement_hubble {B H eps : ℝ} (d : ℝ)
    (hB : B = d * H) :
    |1 - Real.exp (-(Real.arsinh (B * eps))) - d * H * eps|
      ≤ d ^ 2 * (H * eps) ^ 2 / 2 := by
  rw [hB]
  calc |1 - Real.exp (-(Real.arsinh (d * H * eps))) - d * H * eps|
      ≤ (d * H * eps) ^ 2 / 2 := bridge_displacement (d * H * eps)
  _ = d ^ 2 * (H * eps) ^ 2 / 2 := by ring

/-- `cor:krein-positive-expansion-arrow` (sign equivalences): with
`sinh χ* = Bε` and `ε > 0`, the expansion signs agree:
`0 < B ↔ 0 < χ* ↔ 0 < 1 - e^{-2χ*}`. -/
theorem krein_expansion_arrow {B eps chi : ℝ} (heps : 0 < eps)
    (hsinh : Real.sinh chi = B * eps) :
    (0 < B ↔ 0 < chi) ∧ (0 < chi ↔ 0 < 1 - Real.exp (-(2 * chi))) := by
  have hchi : chi = Real.arsinh (B * eps) := by
    rw [← hsinh, Real.arsinh_sinh]
  constructor
  · rw [hchi, Real.arsinh_pos_iff]
    constructor
    · intro h
      positivity
    · intro h
      by_contra hB
      rw [not_lt] at hB
      nlinarith
  · constructor
    · intro h
      have : Real.exp (-(2 * chi)) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      linarith
    · intro h
      have : Real.exp (-(2 * chi)) < 1 := by linarith
      rw [Real.exp_lt_one_iff] at this
      linarith

end NCG
