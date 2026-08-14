/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Local renewal and tetrahedral cells do not force a
  global atlas (`cth:local-renewal-no-global-atlas`,
  Gran-Tensor manuscript)

* `local_renewal_no_global_atlas`: the negative-extension
  collapse — for the path extension on `N³` vertices with
  masses `N⁻³` and capacities `N⁻²`, the half-path cut has
  exactly one boundary edge and mass `⌊N³/2⌋/N³ ≥ 1/4`, so
  the isoperimetric ratio obeys the boxed
  `I_N⁻ ≤ N⁻²/(⌊N³/2⌋/N³)^{2/3} ≤ 4/N² → 0`;
  both the bound and the limit are proved.

The positive extension (the cubic box `[N]³` with
nearest-neighbour capacities `N⁻²`, whose every cut obeys
the Cartesian cut bound `I_N⁺ ≥ 1/16`) and the tensor
construction showing that both extensions restrict to the
same complete local renewal and internal-cell cylinder law
(discarding the independent endpoint ledger) are the
manuscript's construction layers; together with the
proved collapse they give the boxed pair
`inf I⁺ > 0`, `I⁻ → 0`.
-/

open Filter

namespace NCG

/-- `cth:local-renewal-no-global-atlas` (the
negative-extension collapse). -/
theorem local_renewal_no_global_atlas :
    -- the half-path mass is at least a quarter
    (∀ N : ℕ, 2 ≤ N →
      (1 : ℝ) / 4 ≤ ((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
    -- the boxed cut-ratio bound
    ∧ (∀ N : ℕ, 2 ≤ N →
      ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2)
    -- the boxed collapse I⁻ → 0
    ∧ Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2)
        / (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3)) atTop (nhds 0) := by
  have hmass : ∀ N : ℕ, 2 ≤ N →
      (1 : ℝ) / 4 ≤ ((N ^ 3 / 2 : ℕ) : ℝ)
        / (N : ℝ) ^ 3 := by
    intro N hN
    have hN3 : 8 ≤ N ^ 3 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    have hdiv : N ^ 3 ≤ 4 * (N ^ 3 / 2) := by
      have := Nat.div_add_mod (N ^ 3) 2
      have hmod : N ^ 3 % 2 < 2 := Nat.mod_lt _ (by
        norm_num)
      omega
    have hpos : (0 : ℝ) < (N : ℝ) ^ 3 := by
      have : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le (by norm_num)
          hN
      positivity
    rw [div_le_div_iff₀ (by norm_num) hpos]
    have : ((N : ℝ) ^ 3) ≤ 4 * ((N ^ 3 / 2 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    linarith
  have hbound : ∀ N : ℕ, 2 ≤ N →
      ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2 := by
    intro N hN
    have hm := hmass N hN
    have hden : ((1 : ℝ) / 4) ^ ((2 : ℝ) / 3)
        ≤ (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by norm_num) hm (by norm_num)
    have hq : (1 : ℝ) / 4 ≤ ((1 : ℝ) / 4)
        ^ ((2 : ℝ) / 3) := by
      calc (1 : ℝ) / 4 = ((1 : ℝ) / 4) ^ ((1 : ℝ)) := by
            rw [Real.rpow_one]
        _ ≤ ((1 : ℝ) / 4) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_ge
              (by norm_num) (by norm_num) (by norm_num)
    have hden4 : (1 : ℝ) / 4
        ≤ (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3) := le_trans hq hden
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hN
    calc ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ ((N : ℝ)⁻¹ ^ 2) / ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_left (by positivity)
            (by norm_num) hden4
      _ = 4 / (N : ℝ) ^ 2 := by
          rw [div_div_eq_mul_div, div_one, inv_pow,
            inv_mul_eq_div]
  refine ⟨hmass, hbound, ?_⟩
  apply squeeze_zero' ?_ ?_
    (tendsto_const_div_atTop_nhds_zero_nat 4)
  · filter_upwards [Filter.eventually_ge_atTop 2]
      with N _
    have hden : (0 : ℝ) ≤ (((N ^ 3 / 2 : ℕ) : ℝ)
        / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 2]
      with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hN
    have hcast : (2 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      nlinarith
    calc ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2 := hbound N hN
      _ ≤ 4 / (N : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num)
            hNpos hNN

end NCG
