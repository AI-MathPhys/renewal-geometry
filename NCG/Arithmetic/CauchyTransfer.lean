/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive-mass transfer through the finite bank
  (`thm:v003-cauchy-transfer`, `corollary:dyadic-bank`,
  arithmetic monograph)

* `positive_mass_transfer` — multiplying the pointwise minorant
  sandwich `0 ≤ 𝔓(n) − 𝔠(n) ≤ K·𝔈(n)` by nonnegative weights `b_n`
  and summing gives `Q − K·U ≤ C ≤ Q`: any lower bound on the
  weighted prime–semiprime mass survives in the finite
  phase-complete tensor whenever the aliased tail `K·U` is small
  (`thm:v003-cauchy-transfer`; the pointwise sandwich is the
  hypothesis, supplied by the Cauchy-minorant theorem);
* `dyadic_bank` / `dyadic_bank_constants` — the dyadic
  specialization `r = 1/4`, `s = 1/2`: the aliasing constant is
  `ϑC_s = 6·2⁻ᵐ` and the total coefficient variation
  `r⁻¹ + r⁻² + ϑC_s ≤ 26` (`corollary:dyadic-bank`).
-/

namespace NCG.CauchyTransfer

/-- `thm:v003-cauchy-transfer`: the weighted sums inherit the
pointwise sandwich: `Q − K·U ≤ C ≤ Q`. -/
theorem positive_mass_transfer {ι : Type*} (S : Finset ι)
    (b P c E : ι → ℝ) (K : ℝ)
    (hb : ∀ n ∈ S, 0 ≤ b n)
    (hlow : ∀ n ∈ S, 0 ≤ P n - c n)
    (hhigh : ∀ n ∈ S, P n - c n ≤ K * E n) :
    (∑ n ∈ S, b n * P n) - K * (∑ n ∈ S, b n * E n)
        ≤ ∑ n ∈ S, b n * c n
      ∧ (∑ n ∈ S, b n * c n) ≤ ∑ n ∈ S, b n * P n := by
  constructor
  · have hsum : (∑ n ∈ S, b n * P n) - (∑ n ∈ S, b n * c n)
        ≤ K * ∑ n ∈ S, b n * E n := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have h1 := hhigh n hn
      have h2 := hb n hn
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    linarith
  · refine Finset.sum_le_sum fun n hn => ?_
    have h1 := hlow n hn
    have h2 := hb n hn
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- `corollary:dyadic-bank` (constants): at `r = 1/4`, `s = 1/2` the
aliasing constant is `ϑC_s = 6·2⁻ᵐ` and the total coefficient
variation `r⁻¹ + r⁻² + ϑC_s` is at most `26`. -/
theorem dyadic_bank_constants (m : ℕ) :
    ((1 / 4 : ℝ) / (1 / 2)) ^ m * ((1 / 2 : ℝ)⁻¹ + ((1 / 2 : ℝ)⁻¹) ^ 2)
        = 6 * (2 : ℝ)⁻¹ ^ m
      ∧ (1 / 4 : ℝ)⁻¹ + (((1 / 4 : ℝ))⁻¹) ^ 2 + 6 * (2 : ℝ)⁻¹ ^ m
        ≤ 26 := by
  constructor
  · norm_num
    ring
  · have hpow : (2 : ℝ)⁻¹ ^ m ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [hpow]

/-- `corollary:dyadic-bank` (transfer): the dyadic bank inherits the
mass-transfer sandwich with aliasing constant `6·2⁻ᵐ`. -/
theorem dyadic_bank {ι : Type*} (S : Finset ι) (b P c E : ι → ℝ)
    (m : ℕ) (hb : ∀ n ∈ S, 0 ≤ b n)
    (hlow : ∀ n ∈ S, 0 ≤ P n - c n)
    (hhigh : ∀ n ∈ S, P n - c n ≤ 6 * (2 : ℝ)⁻¹ ^ m * E n) :
    (∑ n ∈ S, b n * P n)
        - 6 * (2 : ℝ)⁻¹ ^ m * (∑ n ∈ S, b n * E n)
        ≤ ∑ n ∈ S, b n * c n
      ∧ (∑ n ∈ S, b n * c n) ≤ ∑ n ∈ S, b n * P n :=
  positive_mass_transfer S b P c E (6 * (2 : ℝ)⁻¹ ^ m) hb hlow hhigh

end NCG.CauchyTransfer
