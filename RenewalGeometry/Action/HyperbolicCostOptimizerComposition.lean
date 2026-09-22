/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Optimizer composition characterizes action--law matching
(`prop:main-optimizer-composition`, emergent-spacetime manuscript)

The measured quadratic interval cost in hyperbolic form
(`eq:main-hyperbolic-cost`) is
`E_{μ,θ,C}(x,y) = μ coth θ (x² + y²) − 2 μ csch θ x y + C (y² − x²)`.
With `ρ = C/μ` and `Δ_rel = 1 − ρ²` (`eq:main-relative-rank-defect`) we prove:

* `hyperbolicCost_sub_optimizer`: `E(x,y) − E(x, m_θ x) = (μ coth θ + C)(y − m_θ x)²`,
  hence (`optimizerMap_isMin`, `optimizerMap_unique`) `y ↦ E(x,y)` has the unique
  minimizer `m_θ(x) = r_θ x`, `r_θ = (cosh θ + ρ sinh θ)⁻¹`, and `m_θ x > 0` for
  `x > 0` (`eq:main-optimizer-map`);
* `optimizerRatio_inv_add_sub`: the composition defect identity
  `r_{θ+φ}⁻¹ − (r_θ r_φ)⁻¹ = Δ_rel sinh θ sinh φ` (`eq:main-optimizer-defect`);
* `optimizerMap_comp_iff`: for one positive pair `θ, φ` and one `x > 0`,
  `m_{θ+φ}(x) = m_φ(m_θ(x))` holds iff `Δ_rel = 0`; consequently
  (`relativeDefect_eq_zero_iff_comp`) matching is equivalent to composition for
  every positive pair, and already to composition for one pair at one `x > 0`;
* `relativeDefect_eq_zero_iff_mul_eq_sq`: `Δ_rel = 0 ↔ A B = C²` for `μ = √(AB)`;
* `optimizerRatio_of_relativeDefect_eq_zero`: on the matched branch
  `r_θ = e^{−ρθ}` with `ρ = ±1`.

Only the standing hypothesis `|ρ| ≤ 1` (i.e. `|C| ≤ μ`, the positivity of the
measured cost) and `θ > 0` are used.
-/

namespace RenewalGeometry.HyperbolicCostOptimizer

open Real

/-- The hyperbolic interval cost `E_{μ,θ,C}(x,y)` of `eq:main-hyperbolic-cost`
(with `coth θ = cosh θ / sinh θ` and `csch θ = 1 / sinh θ`). -/
noncomputable def hyperbolicCost (μ θ C x y : ℝ) : ℝ :=
  μ * (cosh θ / sinh θ) * (x ^ 2 + y ^ 2) - 2 * μ * (1 / sinh θ) * x * y
    + C * (y ^ 2 - x ^ 2)

/-- The optimizer denominator `d_θ = cosh θ + ρ sinh θ`
(proof of `prop:main-optimizer-composition`). -/
noncomputable def optimizerDenominator (ρ θ : ℝ) : ℝ := cosh θ + ρ * sinh θ

/-- The optimizer ratio `r_θ = (cosh θ + ρ sinh θ)⁻¹` of `eq:main-optimizer-map`. -/
noncomputable def optimizerRatio (ρ θ : ℝ) : ℝ := (optimizerDenominator ρ θ)⁻¹

/-- The optimizer map `m_θ(x) = r_θ x` of `eq:main-optimizer-map`. -/
noncomputable def optimizerMap (ρ θ x : ℝ) : ℝ := optimizerRatio ρ θ * x

/-- The scale-free mismatch `Δ_rel = 1 − ρ²` of `eq:main-relative-rank-defect`. -/
def relativeDefect (ρ : ℝ) : ℝ := 1 - ρ ^ 2

/-- `|sinh θ| < cosh θ`. -/
lemma abs_sinh_lt_cosh (θ : ℝ) : |sinh θ| < cosh θ := by
  have h1 : sinh θ ^ 2 < cosh θ ^ 2 := by rw [cosh_sq]; linarith
  have h2 : |sinh θ| < |cosh θ| := sq_lt_sq.mp h1
  rwa [abs_of_pos (cosh_pos θ)] at h2

/-- The optimizer denominator is positive whenever `|ρ| ≤ 1`. -/
theorem optimizerDenominator_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) (θ : ℝ) :
    0 < optimizerDenominator ρ θ := by
  unfold optimizerDenominator
  have h1 := abs_sinh_lt_cosh θ
  have h2 : |ρ * sinh θ| ≤ |sinh θ| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hρ
  have h3 := neg_abs_le (ρ * sinh θ)
  linarith

/-- The optimizer ratio is positive whenever `|ρ| ≤ 1`. -/
theorem optimizerRatio_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) (θ : ℝ) :
    0 < optimizerRatio ρ θ :=
  inv_pos.mpr (optimizerDenominator_pos hρ θ)

/-- Positivity of the minimizer: `m_θ(x) > 0` for `x > 0`
(`eq:main-optimizer-map`). -/
theorem optimizerMap_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) (θ : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < optimizerMap ρ θ x :=
  mul_pos (optimizerRatio_pos hρ θ) hx

/-- The `y²`-coefficient `μ coth θ + C` of the cost is positive for `μ > 0`,
`|C| ≤ μ`, `θ > 0` (proof of `prop:main-optimizer-composition`). -/
theorem leading_coefficient_pos {μ θ C : ℝ} (hμ : 0 < μ) (hC : |C| ≤ μ) (hθ : 0 < θ) :
    0 < μ * (cosh θ / sinh θ) + C := by
  have hs : 0 < sinh θ := sinh_pos_iff.mpr hθ
  have hρ : |C / μ| ≤ 1 := by
    rw [abs_div, abs_of_pos hμ, div_le_one hμ]
    exact hC
  have hd := optimizerDenominator_pos hρ θ
  unfold optimizerDenominator at hd
  have : μ * (cosh θ / sinh θ) + C = μ * (cosh θ + C / μ * sinh θ) / sinh θ := by
    field_simp
  rw [this]
  positivity

/-- Completing the square: the cost exceeds its value at the optimizer map by
`(μ coth θ + C) (y − m_θ x)²`, where `ρ = C/μ`. -/
theorem hyperbolicCost_sub_optimizer {μ θ C : ℝ} (hμ : 0 < μ) (hC : |C| ≤ μ) (hθ : 0 < θ)
    (x y : ℝ) :
    hyperbolicCost μ θ C x y - hyperbolicCost μ θ C x (optimizerMap (C / μ) θ x)
      = (μ * (cosh θ / sinh θ) + C) * (y - optimizerMap (C / μ) θ x) ^ 2 := by
  have hs : sinh θ ≠ 0 := (sinh_pos_iff.mpr hθ).ne'
  have hρ : |C / μ| ≤ 1 := by
    rw [abs_div, abs_of_pos hμ, div_le_one hμ]
    exact hC
  have hd : cosh θ + C / μ * sinh θ ≠ 0 := (optimizerDenominator_pos hρ θ).ne'
  have hd' : μ * cosh θ + C * sinh θ ≠ 0 := by
    have : μ * cosh θ + C * sinh θ = μ * (cosh θ + C / μ * sinh θ) := by
      field_simp
    rw [this]
    exact mul_ne_zero hμ.ne' hd
  have hm : optimizerMap (C / μ) θ x = μ * x / (μ * cosh θ + C * sinh θ) := by
    unfold optimizerMap optimizerRatio optimizerDenominator
    field_simp
  obtain ⟨d, hd_eq⟩ : ∃ d, d = μ * cosh θ + C * sinh θ := ⟨_, rfl⟩
  rw [← hd_eq] at hm hd'
  rw [hm]
  unfold hyperbolicCost
  field_simp
  rw [hd_eq]
  ring

/-- `m_θ(x)` minimizes `y ↦ E_{μ,θ,C}(x,y)` (`eq:main-optimizer-map`). -/
theorem optimizerMap_isMin {μ θ C : ℝ} (hμ : 0 < μ) (hC : |C| ≤ μ) (hθ : 0 < θ)
    (x y : ℝ) :
    hyperbolicCost μ θ C x (optimizerMap (C / μ) θ x) ≤ hyperbolicCost μ θ C x y := by
  have h := hyperbolicCost_sub_optimizer hμ hC hθ x y
  have hpos := leading_coefficient_pos hμ hC hθ
  have : 0 ≤ (μ * (cosh θ / sinh θ) + C) * (y - optimizerMap (C / μ) θ x) ^ 2 :=
    mul_nonneg hpos.le (sq_nonneg _)
  linarith

/-- The minimizer of `y ↦ E_{μ,θ,C}(x,y)` is unique: any `y` attaining the minimum
equals `m_θ(x)`. -/
theorem optimizerMap_unique {μ θ C : ℝ} (hμ : 0 < μ) (hC : |C| ≤ μ) (hθ : 0 < θ)
    (x y : ℝ)
    (hy : hyperbolicCost μ θ C x y ≤ hyperbolicCost μ θ C x (optimizerMap (C / μ) θ x)) :
    y = optimizerMap (C / μ) θ x := by
  have h := hyperbolicCost_sub_optimizer hμ hC hθ x y
  have hpos := leading_coefficient_pos hμ hC hθ
  have hsq : (μ * (cosh θ / sinh θ) + C) * (y - optimizerMap (C / μ) θ x) ^ 2 ≤ 0 := by
    linarith
  have hsq' : (y - optimizerMap (C / μ) θ x) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hsq hpos
  have : y - optimizerMap (C / μ) θ x = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsq' (sq_nonneg _))
  linarith

/-- Hyperbolic addition for the optimizer denominator:
`d_{θ+φ} − d_θ d_φ = Δ_rel sinh θ sinh φ`. -/
theorem optimizerDenominator_add_sub (ρ θ φ : ℝ) :
    optimizerDenominator ρ (θ + φ) - optimizerDenominator ρ θ * optimizerDenominator ρ φ
      = relativeDefect ρ * (sinh θ * sinh φ) := by
  unfold optimizerDenominator relativeDefect
  rw [cosh_add, sinh_add]
  ring

/-- The composition defect identity `eq:main-optimizer-defect`:
`r_{θ+φ}⁻¹ − (r_θ r_φ)⁻¹ = Δ_rel sinh θ sinh φ`. -/
theorem optimizerRatio_inv_add_sub (ρ θ φ : ℝ) :
    (optimizerRatio ρ (θ + φ))⁻¹ - (optimizerRatio ρ θ * optimizerRatio ρ φ)⁻¹
      = relativeDefect ρ * sinh θ * sinh φ := by
  unfold optimizerRatio
  rw [mul_inv, inv_inv, inv_inv, inv_inv, optimizerDenominator_add_sub]
  ring

/-- For one positive pair `θ, φ` and one `x > 0`, `m_{θ+φ}(x) = m_φ(m_θ(x))` holds
iff `Δ_rel = 0` (`prop:main-optimizer-composition`, "already for one positive pair
at one `x > 0`"). -/
theorem optimizerMap_comp_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {θ φ x : ℝ}
    (hθ : 0 < θ) (hφ : 0 < φ) (hx : 0 < x) :
    optimizerMap ρ (θ + φ) x = optimizerMap ρ φ (optimizerMap ρ θ x) ↔
      relativeDefect ρ = 0 := by
  have hsθ : 0 < sinh θ := sinh_pos_iff.mpr hθ
  have hsφ : 0 < sinh φ := sinh_pos_iff.mpr hφ
  have hdθ := optimizerDenominator_pos hρ θ
  have hdφ := optimizerDenominator_pos hρ φ
  have hdθφ := optimizerDenominator_pos hρ (θ + φ)
  have key := optimizerDenominator_add_sub ρ θ φ
  unfold optimizerMap optimizerRatio
  constructor
  · intro h
    have h1 : (optimizerDenominator ρ (θ + φ))⁻¹
        = (optimizerDenominator ρ φ)⁻¹ * (optimizerDenominator ρ θ)⁻¹ := by
      have := h
      rw [← mul_assoc] at this
      exact mul_right_cancel₀ hx.ne' this
    rw [← mul_inv, inv_inj] at h1
    have h2 : relativeDefect ρ * (sinh θ * sinh φ) = 0 := by
      rw [← key, h1]; ring
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact h2
    · exact absurd h2 (mul_pos hsθ hsφ).ne'
  · intro h
    rw [h, zero_mul, sub_eq_zero] at key
    rw [key, mul_inv]
    ring

/-- `prop:main-optimizer-composition`: the matched surface `Δ_rel = 0` is
equivalent to `m_{θ+φ} = m_φ ∘ m_θ` on `x > 0` for every positive pair, and
already to that equality for one positive pair at one `x > 0`. -/
theorem relativeDefect_eq_zero_iff_comp {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (relativeDefect ρ = 0 ↔
      ∀ θ > 0, ∀ φ > 0, ∀ x > 0,
        optimizerMap ρ (θ + φ) x = optimizerMap ρ φ (optimizerMap ρ θ x)) ∧
    (relativeDefect ρ = 0 ↔
      ∃ θ > 0, ∃ φ > 0, ∃ x > 0,
        optimizerMap ρ (θ + φ) x = optimizerMap ρ φ (optimizerMap ρ θ x)) := by
  constructor
  · constructor
    · intro h θ hθ φ hφ x hx
      exact (optimizerMap_comp_iff hρ hθ hφ hx).mpr h
    · intro h
      exact (optimizerMap_comp_iff hρ one_pos one_pos one_pos).mp (h 1 one_pos 1 one_pos 1 one_pos)
  · constructor
    · intro h
      exact ⟨1, one_pos, 1, one_pos, 1, one_pos,
        (optimizerMap_comp_iff hρ one_pos one_pos one_pos).mpr h⟩
    · rintro ⟨θ, hθ, φ, hφ, x, hx, h⟩
      exact (optimizerMap_comp_iff hρ hθ hφ hx).mp h

/-- With `μ = √(AB)` and `ρ = C/μ` (`eq:main-relative-rank-defect`), `Δ_rel = 0`
is exactly the rank-one condition `AB = C²`. -/
theorem relativeDefect_eq_zero_iff_mul_eq_sq {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) :
    relativeDefect (C / Real.sqrt (A * B)) = 0 ↔ A * B = C ^ 2 := by
  have hAB : 0 < A * B := mul_pos hA hB
  have hs : 0 < Real.sqrt (A * B) := Real.sqrt_pos.mpr hAB
  unfold relativeDefect
  rw [div_pow, Real.sq_sqrt hAB.le, sub_eq_zero, eq_comm, div_eq_one_iff_eq hAB.ne', eq_comm]

/-- On the matched branch `Δ_rel = 0` one has `ρ = ±1` and `r_θ = e^{−ρθ}`
(`prop:main-optimizer-composition`, last clause). -/
theorem optimizerRatio_of_relativeDefect_eq_zero {ρ : ℝ} (h : relativeDefect ρ = 0)
    (θ : ℝ) :
    (ρ = 1 ∨ ρ = -1) ∧ optimizerRatio ρ θ = Real.exp (-ρ * θ) := by
  have hsq : (ρ - 1) * (ρ + 1) = 0 := by
    unfold relativeDefect at h
    ring_nf
    linarith
  have hρ : ρ = 1 ∨ ρ = -1 := by
    rcases mul_eq_zero.mp hsq with h1 | h1
    · left; linarith
    · right; linarith
  refine ⟨hρ, ?_⟩
  unfold optimizerRatio optimizerDenominator
  rcases hρ with rfl | rfl
  · rw [one_mul, cosh_add_sinh, ← Real.exp_neg]
    ring_nf
  · rw [neg_one_mul, ← sub_eq_add_neg, cosh_sub_sinh, ← Real.exp_neg]
    ring_nf

end RenewalGeometry.HyperbolicCostOptimizer
