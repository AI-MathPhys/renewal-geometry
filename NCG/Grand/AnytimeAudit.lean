/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Selection-safe adaptive coordinate audit
  (`thm:anytime-audit`, Gran-Tensor manuscript)

* `confidence_radius_calibration`: the boxed radius is exactly
  Hoeffding-calibrated — with
  `ε = √((2k)⁻¹·log X)` one has `exp(-2k·ε²) = X⁻¹`, so the
  per-(coordinate, count) failure weight at
  `X = π²k²/(3αw_j)` is `3αw_j/(π²k²)`;
* `basel_budget`: the count ledger closes —
  `∑ₖ 1/k² = π²/6` (Basel), so each coordinate spends exactly
  `αw_j·(6/π²)·(π²/6) = αw_j`;
* `weight_budget`: the coordinate ledger closes —
  `∑ⱼ w_j ≤ 1` gives `∑ⱼ αw_j ≤ α`;
* `union_bound_budget`: the simultaneous confidence region —
  a countable family of failure events with budgeted measures
  has total measure at most `α` (`measure_iUnion_le`).

Rendering disclosed: the time-uniform Hoeffding inequality for
predictably sampled bounded coordinates (the martingale/optional
-stopping input `P(|p̂ - p| > ε at N_j(t) = k) ≤ 2exp(-2kε²)`)
is the manuscript's probabilistic layer; the exact calibration
of the boxed radius, both ledgers, and the union bound are
proved here.
-/

open MeasureTheory

namespace NCG

/-- Boxed radius calibration: `ε = √((2k)⁻¹·log X)` gives
`exp(-2k·ε²) = X⁻¹` — the Hoeffding exponent spends exactly the
assigned failure weight. -/
theorem confidence_radius_calibration (k X : ℝ) (hk : 0 < k)
    (hX : 1 ≤ X) :
    Real.exp (-(2 * k)
      * Real.sqrt ((2 * k)⁻¹ * Real.log X) ^ 2) = X⁻¹ := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have harg : 0 ≤ (2 * k)⁻¹ * Real.log X := by positivity
  have hcoll : -(2 * k) * ((2 * k)⁻¹ * Real.log X)
      = -Real.log X := by
    field_simp
  rw [Real.sq_sqrt harg, hcoll, Real.exp_neg,
    Real.exp_log (lt_of_lt_of_le zero_lt_one hX)]

/-- Basel ledger: `∑ₖ 1/k² = π²/6`. -/
theorem basel_budget :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

/-- Coordinate ledger: `∑ⱼ wⱼ ≤ 1` spends at most `α`. -/
theorem weight_budget {J : Type*} [Fintype J] (w : J → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hw : ∑ j, w j ≤ 1) :
    ∑ j, α * w j ≤ α := by
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right hα hw

/-- Simultaneous confidence region: budgeted failure events have
total measure at most `α`. -/
theorem union_bound_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (f : ℕ → ENNReal)
    (hf : ∀ n, μ (A n) ≤ f n) (α : ENNReal)
    (hsum : ∑' n, f n ≤ α) : μ (⋃ n, A n) ≤ α :=
  le_trans (measure_iUnion_le A)
    (le_trans (ENNReal.tsum_le_tsum hf) hsum)

end NCG
