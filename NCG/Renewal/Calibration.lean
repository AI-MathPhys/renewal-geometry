/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Renewal calibration: the pressure-zero equation

**Proposition `prop:renewal-calibration`**: in the conformal contracting
regime with calibrated generator lengths `ℓ_σ > 0`, the Bowen pressure-zero
condition

`Φ(s) = Σ_σ e^{−s ℓ_σ} = 1`

has a **unique** solution `s`, which is the metric predictive dimension
(the Moran–Falconer exponent of Theorem `thm:fractal` after the
substitution `r_σ = e^{−ℓ_σ}`).  This file proves existence and uniqueness
of the calibration point: the pressure function is continuous and strictly
decreasing, exceeds `1` at `s = 0` whenever there are at least two reset
symbols, and tends to `0` at infinity.

## Main results

* `NCG.pressure_strictAnti`, `NCG.pressure_continuous`,
  `NCG.pressure_tendsto_zero` — analytic behaviour of the pressure;
* `NCG.pressure_eq_one_existsUnique` —
  **Proposition `prop:renewal-calibration`**: the pressure-zero equation
  has exactly one root. -/

namespace NCG

open Finset Filter

variable {E : Type*} [Fintype E] [Nonempty E]

/-- The **pressure function** of a calibrated renewal alphabet:
`Φ(s) = Σ_σ e^{−s ℓ_σ}` (Proposition `prop:renewal-calibration`). -/
noncomputable def pressure (ℓ : E → ℝ) (s : ℝ) : ℝ :=
  ∑ σ, Real.exp (-s * ℓ σ)

/-- The pressure is strictly decreasing for positive calibrated lengths. -/
theorem pressure_strictAnti (ℓ : E → ℝ) (hℓ : ∀ σ, 0 < ℓ σ) :
    StrictAnti (pressure ℓ) := by
  intro a b hab
  apply Finset.sum_lt_sum_of_nonempty univ_nonempty
  intro σ _
  apply Real.exp_lt_exp.mpr
  have := hℓ σ
  nlinarith

/-- The pressure is continuous. -/
theorem pressure_continuous (ℓ : E → ℝ) : Continuous (pressure ℓ) := by
  apply continuous_finset_sum
  intro σ _
  exact Real.continuous_exp.comp ((continuous_id.neg).mul continuous_const)

/-- The pressure tends to `0` at infinity. -/
theorem pressure_tendsto_zero (ℓ : E → ℝ) (hℓ : ∀ σ, 0 < ℓ σ) :
    Tendsto (pressure ℓ) atTop (nhds 0) := by
  rw [show (0 : ℝ) = ∑ _σ : E, 0 by simp]
  apply tendsto_finset_sum
  intro σ _
  apply Real.tendsto_exp_atBot.comp
  exact Tendsto.atBot_mul_const (hℓ σ) tendsto_neg_atTop_atBot

/-- At `s = 0` the pressure is the number of reset symbols. -/
theorem pressure_zero (ℓ : E → ℝ) :
    pressure ℓ 0 = Fintype.card E := by
  simp [pressure]

/-- **Proposition `prop:renewal-calibration`** (renewal calibration): for a
renewal alphabet with at least two symbols and positive calibrated lengths,
the Bowen pressure-zero equation `Σ_σ e^{−s ℓ_σ} = 1` has exactly one
solution — the metric predictive dimension of the contracting reset
system (Theorem `thm:fractal` via `r_σ = e^{−ℓ_σ}`). -/
theorem pressure_eq_one_existsUnique (ℓ : E → ℝ) (hℓ : ∀ σ, 0 < ℓ σ)
    (hE : 2 ≤ Fintype.card E) :
    ∃! s : ℝ, pressure ℓ s = 1 := by
  -- the pressure eventually drops below `1`
  obtain ⟨M, hM⟩ : ∃ M, pressure ℓ M < 1 :=
    ((pressure_tendsto_zero ℓ hℓ).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)).exists
  -- and starts above `1`
  have h0 : 1 < pressure ℓ 0 := by
    rw [pressure_zero]
    have h2 : (2 : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast hE
    linarith
  have hM0 : 0 < M := by
    by_contra hle
    push_neg at hle
    have := (pressure_strictAnti ℓ hℓ).antitone hle
    linarith
  -- intermediate value between `0` and `M`
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc' hM0.le
    (pressure_continuous ℓ).continuousOn ⟨hM.le, h0.le⟩
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact (pressure_strictAnti ℓ hℓ).injective (by rw [hs, ht])

end NCG
