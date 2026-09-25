/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Alternative finite-prefix stationarity criterion
  (`thm:prefix-stationarity`, `cor:prefix-table`,
  Einstein–Standard-Model action-closure manuscript)

The same-action descent calculation of `app:prefix-stationarity`,
formalised on an abstract real inner-product space `E` whose norm plays
the role of the mass norm `‖·‖_{0,h}` of `eq:prefix-mass`.

* `taylor_gap_on`, `descent_lower_on`: the chart-restricted Taylor
  identity and the lower descent inequality `eq:prefix-descent1`
  (the local action `𝒜` is only assumed differentiable on a convex
  chart `Θ`, with the Hessian scale `eq:prefix-Hessian` rendered as the
  Lipschitz bound `‖∇𝒜 x - ∇𝒜 y‖ ≤ K₀ h⁻² ‖x - y‖` on `Θ`);
* `step_bound`: the one-step inequality
  `‖E(θ_j)‖² ≤ (4ℓ_h²/a_h) (𝒜 θ_j - 𝒜 θ_{j+1}) + (2 + 2ℓ_h²/a_h²) ‖b_j‖²`
  obtained from `eq:prefix-descent2` and Young's inequality;
* `prefix_average`: the telescoped prefix average `eq:prefix-average`
  with the explicit constants `C₀ = 4ℓ₀²/a₀`, `D₁ = 2 + 2ℓ₀²/a₀²`,
  `a₀ = g_*/υ₀ - K₀/2`, `ℓ₀ = g^*/υ₀ + K₀`;
* `prefix_selected`: the selected-slope conclusion `eq:prefix-selected`
  (an observed index realising the minimum of the finite list);
* `prefix_table_probability`: `cor:prefix-table` — on a probability
  space, the failure probability of the best safe record is bounded by
  `p_exit + C₀ D₀/(J h^{2+2α}) + D₁ h^{-2α} 𝒬^{bal}` (Markov's inequality
  applied to the safe-indicated pathwise average);
* `eventually_certified_of_summable`: the dyadic Borel–Cantelli clause.

The operational potential `Ψ_h` enters only through its gradient `p`,
with `eq:prefix-Fisher` rendered as strong monotonicity `g_*` and the
Lipschitz bound `g^*` of `p` on the chart.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace RenewalGeometry
namespace PrefixStationarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ### Chart-restricted Taylor layer -/

/-- Chain rule along an affine segment, at a point where `f` has
gradient `g`. -/
theorem hasDerivAt_line_of_hasGradientAt (f : E → ℝ) (g : E → E)
    (a v : E) (t : ℝ) (hg : HasGradientAt f (g (a + t • v)) (a + t • v)) :
    HasDerivAt (fun s : ℝ => f (a + s • v)) ⟪g (a + t • v), v⟫ t := by
  have hpath : HasDerivAt (fun s : ℝ => a + s • v) v t := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) t :=
      (hasDerivAt_id t).smul_const v
    rw [one_smul] at h1
    exact h1.const_add a
  have h := hg.hasFDerivAt.comp_hasDerivAt t hpath
  have hval : (InnerProductSpace.toDual ℝ E (g (a + t • v))) v
      = ⟪g (a + t • v), v⟫ := InnerProductSpace.toDual_apply_apply
  rw [hval] at h
  exact h

omit [CompleteSpace E] in
/-- Points of the connecting segment stay in a convex chart. -/
theorem segment_mem_of_convex {Θ : Set E} (hΘ : Convex ℝ Θ) {a v : E}
    (ha : a ∈ Θ) (hav : a + v ∈ Θ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    a + t • v ∈ Θ :=
  hΘ.add_smul_mem ha hav ht

/-- Fundamental theorem of calculus for the first-order Taylor gap on a
convex chart. -/
theorem taylor_gap_on (f : E → ℝ) (g : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hg : ∀ x ∈ Θ, HasGradientAt f (g x) x)
    (hgc : ContinuousOn g Θ) {a v : E} (ha : a ∈ Θ) (hav : a + v ∈ Θ) :
    f (a + v) - f a - ⟪g a, v⟫
      = ∫ t in (0:ℝ)..1, (⟪g (a + t • v), v⟫ - ⟪g a, v⟫) := by
  have hcont : ContinuousOn (fun t : ℝ =>
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.inner ?_ continuousOn_const
    refine hgc.comp (by fun_prop : Continuous fun t : ℝ => a + t • v).continuousOn ?_
    intro t ht
    exact segment_mem_of_convex hΘ ha hav ht
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => f (a + s • v) - s * ⟪g a, v⟫)
        (⟪g (a + t • v), v⟫ - ⟪g a, v⟫) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 := hasDerivAt_line_of_hasGradientAt f g a v t
      (hg _ (segment_mem_of_convex hΘ ha hav ht))
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪g a, v⟫) ⟪g a, v⟫ t := by
      have h3 := (hasDerivAt_id t).mul_const ⟪g a, v⟫
      rwa [one_mul] at h3
    exact h1.sub h2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  rw [h]
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_mul, sub_zero]
  ring

/-- **The lower descent inequality `eq:prefix-descent1`**: an `L`-Lipschitz
gradient on a convex chart gives
`f(a+v) ≥ f(a) + ⟪∇f(a),v⟫ - (L/2)‖v‖²` whenever `a, a+v ∈ Θ`. -/
theorem descent_lower_on (f : E → ℝ) (g : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hg : ∀ x ∈ Θ, HasGradientAt f (g x) x)
    (hgc : ContinuousOn g Θ) (L : ℝ)
    (hlip : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {a v : E} (ha : a ∈ Θ) (hav : a + v ∈ Θ) :
    f a + ⟪g a, v⟫ - L / 2 * ‖v‖ ^ 2 ≤ f (a + v) := by
  have hgap := taylor_gap_on f g hΘ hg hgc ha hav
  have hlow : ∀ t ∈ Set.Icc (0:ℝ) 1,
      -(L * t * ‖v‖ ^ 2) ≤ ⟪g (a + t • v), v⟫ - ⟪g a, v⟫ := by
    intro t ht
    have hmem := segment_mem_of_convex hΘ ha hav ht
    have hl := hlip _ hmem _ ha
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1] at hl
    rw [← inner_sub_left]
    have hcs := abs_real_inner_le_norm (g (a + t • v) - g a) v
    have h1 : ‖g (a + t • v) - g a‖ * ‖v‖ ≤ L * t * ‖v‖ ^ 2 := by
      calc ‖g (a + t • v) - g a‖ * ‖v‖ ≤ (L * (t * ‖v‖)) * ‖v‖ :=
            mul_le_mul_of_nonneg_right hl (norm_nonneg _)
        _ = L * t * ‖v‖ ^ 2 := by ring
    have h2 := neg_abs_le ⟪g (a + t • v) - g a, v⟫
    linarith
  have hint1 : Continuous (fun t : ℝ => -(L * t * ‖v‖ ^ 2)) := by fun_prop
  have hint2 : ContinuousOn (fun t : ℝ =>
      ⟪g (a + t • v), v⟫ - ⟪g a, v⟫) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.inner ?_ continuousOn_const
    refine hgc.comp (by fun_prop : Continuous fun t : ℝ => a + t • v).continuousOn ?_
    intro t ht
    exact segment_mem_of_convex hΘ ha hav ht
  have hmono2 := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) zero_le_one
    (hint1.intervalIntegrable 0 1) hint2.intervalIntegrable hlow
  have hval : (∫ t in (0:ℝ)..1, -(L * t * ‖v‖ ^ 2)) = -(L / 2 * ‖v‖ ^ 2) := by
    have h1 : (fun t : ℝ => -(L * t * ‖v‖ ^ 2))
        = fun t : ℝ => (-(L * ‖v‖ ^ 2)) * t := by
      funext t
      ring
    rw [h1, intervalIntegral.integral_const_mul, integral_id]
    ring_nf
  rw [hval, ← hgap] at hmono2
  linarith

/-! ### The prefix balance and the one-step inequality -/

/-- The balance residual `b_j` of `eq:prefix-balance`:
`b_j = E(θ_{j+1}) + υ⁻¹ (p(θ_{j+1}) - p(θ_j))`. -/
noncomputable def prefixBalance (Egrad p : E → E) (υ : ℝ) (θ : ℕ → E) (j : ℕ) : E :=
  Egrad (θ (j + 1)) + υ⁻¹ • (p (θ (j + 1)) - p (θ j))

/-- The cutoff-free coefficient `a₀ = g_*/υ₀ - K₀/2` of
`a_h = a₀ h⁻²`. -/
noncomputable def prefixA0 (gs K0 υ0 : ℝ) : ℝ := gs / υ0 - K0 / 2

/-- The cutoff-free coefficient `ℓ₀ = g^*/υ₀ + K₀` of `ℓ_h = ℓ₀ h⁻²`. -/
noncomputable def prefixL0 (gu K0 υ0 : ℝ) : ℝ := gu / υ0 + K0

/-- The constant `C₀ = 4ℓ₀²/a₀` of `eq:prefix-average`. -/
noncomputable def prefixC0 (gs gu K0 υ0 : ℝ) : ℝ :=
  4 * prefixL0 gu K0 υ0 ^ 2 / prefixA0 gs K0 υ0

/-- The constant `D₁ = 2 + 2ℓ₀²/a₀²` of `eq:prefix-average`. -/
noncomputable def prefixD1 (gs gu K0 υ0 : ℝ) : ℝ :=
  2 + 2 * prefixL0 gu K0 υ0 ^ 2 / prefixA0 gs K0 υ0 ^ 2

theorem prefixA0_pos {gs K0 υ0 : ℝ} (hgs : 0 < gs) (hυ0 : 0 < υ0)
    (hK0 : 0 ≤ K0) (hsmall : υ0 * K0 < gs / 2) : 0 < prefixA0 gs K0 υ0 := by
  unfold prefixA0
  have h1 : K0 / 2 < gs / υ0 := by
    rw [lt_div_iff₀ hυ0]
    nlinarith
  linarith

theorem prefixL0_nonneg {gu K0 υ0 : ℝ} (hgu : 0 ≤ gu) (hυ0 : 0 < υ0)
    (hK0 : 0 ≤ K0) : 0 ≤ prefixL0 gu K0 υ0 := by
  unfold prefixL0
  exact add_nonneg (div_nonneg hgu hυ0.le) hK0

/-- Pure real algebra of the one-step estimate: from
`Δ ≥ (α/2)D² - B²/(2α)` and `X ≤ B + ℓ D` one gets
`X² ≤ (4ℓ²/α) Δ + (2 + 2ℓ²/α²) B²`. -/
theorem step_algebra {α ℓ B D X Δ : ℝ} (hα : 0 < α) (hℓ : 0 ≤ ℓ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hX : 0 ≤ X)
    (hΔ : α / 2 * D ^ 2 - B ^ 2 / (2 * α) ≤ Δ) (hXle : X ≤ B + ℓ * D) :
    X ^ 2 ≤ 4 * ℓ ^ 2 / α * Δ + (2 + 2 * ℓ ^ 2 / α ^ 2) * B ^ 2 := by
  have hD2 : α ^ 2 * D ^ 2 ≤ 2 * α * Δ + B ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hΔ (by positivity : (0:ℝ) ≤ 2 * α)
    have h2 : 2 * α * (α / 2 * D ^ 2 - B ^ 2 / (2 * α)) = α ^ 2 * D ^ 2 - B ^ 2 := by
      field_simp
      try ring
    linarith
  have hX2 : X ^ 2 ≤ 2 * B ^ 2 + 2 * ℓ ^ 2 * D ^ 2 := by
    have h1 : X ^ 2 ≤ (B + ℓ * D) ^ 2 := by
      have := mul_le_mul hXle hXle hX (by positivity)
      nlinarith
    nlinarith [sq_nonneg (B - ℓ * D)]
  have hkey : α ^ 2 * X ^ 2 ≤ 4 * ℓ ^ 2 * α * Δ + 2 * α ^ 2 * B ^ 2 + 2 * ℓ ^ 2 * B ^ 2 := by
    have h1 : α ^ 2 * X ^ 2 ≤ α ^ 2 * (2 * B ^ 2 + 2 * ℓ ^ 2 * D ^ 2) :=
      mul_le_mul_of_nonneg_left hX2 (by positivity)
    have h2 : 2 * ℓ ^ 2 * (α ^ 2 * D ^ 2) ≤ 2 * ℓ ^ 2 * (2 * α * Δ + B ^ 2) :=
      mul_le_mul_of_nonneg_left hD2 (by positivity)
    nlinarith
  have hα2 : 0 < α ^ 2 := by positivity
  rw [show 4 * ℓ ^ 2 / α * Δ + (2 + 2 * ℓ ^ 2 / α ^ 2) * B ^ 2
      = (4 * ℓ ^ 2 * α * Δ + 2 * α ^ 2 * B ^ 2 + 2 * ℓ ^ 2 * B ^ 2) / α ^ 2 by
    field_simp
    try ring]
  rw [le_div_iff₀ hα2]
  linarith

/-- **One-step inequality** (`eq:prefix-descent2` and the residual
decomposition of `app:prefix-stationarity`): for consecutive chart points
`x, y` with `d = y - x` and balance `b = E(y) + υ⁻¹ (p y - p x)`,
`‖E x‖² ≤ (4ℓ_h²/a_h) (𝒜 x - 𝒜 y) + (2 + 2ℓ_h²/a_h²) ‖b‖²`, where
`a_h = g_*/υ - K_h/2` and `ℓ_h = g^*/υ + K_h` with `K_h = K₀ h⁻²`. -/
theorem step_bound (𝒜 : E → ℝ) (Egrad p : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hgrad : ∀ x ∈ Θ, HasGradientAt 𝒜 (Egrad x) x)
    (hcont : ContinuousOn Egrad Θ) (Kh gs gu υ : ℝ)
    (hKh : 0 ≤ Kh) (hgu : 0 ≤ gu) (hυ : 0 < υ)
    (hah : 0 < gs / υ - Kh / 2)
    (hHess : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖Egrad x - Egrad y‖ ≤ Kh * ‖x - y‖)
    (hFisherLow : ∀ x ∈ Θ, ∀ y ∈ Θ, gs * ‖y - x‖ ^ 2 ≤ ⟪p y - p x, y - x⟫)
    (hFisherUp : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖p y - p x‖ ≤ gu * ‖y - x‖)
    {x y : E} (hx : x ∈ Θ) (hy : y ∈ Θ) :
    ‖Egrad x‖ ^ 2
      ≤ 4 * (gu / υ + Kh) ^ 2 / (gs / υ - Kh / 2) * (𝒜 x - 𝒜 y)
        + (2 + 2 * (gu / υ + Kh) ^ 2 / (gs / υ - Kh / 2) ^ 2)
          * ‖Egrad y + υ⁻¹ • (p y - p x)‖ ^ 2 := by
  set d := y - x with hd
  set b := Egrad y + υ⁻¹ • (p y - p x) with hb
  set α := gs / υ - Kh / 2 with hα
  set ℓ := gu / υ + Kh with hℓ
  -- descent from y back to x
  have hdesc := descent_lower_on 𝒜 Egrad hΘ hgrad hcont Kh hHess hy
    (v := -d) (by rw [hd]; simpa using hx)
  have hxy : y + -d = x := by rw [hd]; abel
  rw [hxy, norm_neg] at hdesc
  -- ⟪E y, -d⟫ = -⟪b, d⟫ + υ⁻¹ ⟪p y - p x, d⟫
  have hEy : Egrad y = b - υ⁻¹ • (p y - p x) := by rw [hb]; abel
  have hinner : ⟪Egrad y, -d⟫ = -⟪b, d⟫ + υ⁻¹ * ⟪p y - p x, d⟫ := by
    rw [hEy, inner_neg_right, inner_sub_left, real_inner_smul_left]
    ring
  have hFL := hFisherLow x hx y hy
  rw [← hd] at hFL
  -- Young's inequality
  have hyoung : ⟪b, d⟫ ≤ ‖b‖ ^ 2 / (2 * α) + α / 2 * ‖d‖ ^ 2 := by
    have hcs := real_inner_le_norm b d
    have h1 : ‖b‖ * ‖d‖ ≤ ‖b‖ ^ 2 / (2 * α) + α / 2 * ‖d‖ ^ 2 := by
      rw [show ‖b‖ ^ 2 / (2 * α) + α / 2 * ‖d‖ ^ 2
          = (‖b‖ ^ 2 + α ^ 2 * ‖d‖ ^ 2) / (2 * α) by field_simp; try ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖b‖ - α * ‖d‖)]
    linarith
  have hΔ : α / 2 * ‖d‖ ^ 2 - ‖b‖ ^ 2 / (2 * α) ≤ 𝒜 x - 𝒜 y := by
    have h1 : 𝒜 y + ⟪Egrad y, -d⟫ - Kh / 2 * ‖d‖ ^ 2 ≤ 𝒜 x := hdesc
    rw [hinner] at h1
    have h2 : υ⁻¹ * (gs * ‖d‖ ^ 2) ≤ υ⁻¹ * ⟪p y - p x, d⟫ :=
      mul_le_mul_of_nonneg_left hFL (by positivity)
    have h3 : υ⁻¹ * (gs * ‖d‖ ^ 2) - Kh / 2 * ‖d‖ ^ 2 = α * ‖d‖ ^ 2 := by
      rw [hα]; field_simp; try ring
    linarith
  -- the residual decomposition
  have hEx : Egrad x = b - υ⁻¹ • (p y - p x) + (Egrad x - Egrad y) := by
    rw [hb]; abel
  have hXle : ‖Egrad x‖ ≤ ‖b‖ + ℓ * ‖d‖ := by
    have hH := hHess x hx y hy
    rw [norm_sub_rev x y, ← hd] at hH
    have hFU := hFisherUp x hx y hy
    rw [← hd] at hFU
    calc ‖Egrad x‖ = ‖b - υ⁻¹ • (p y - p x) + (Egrad x - Egrad y)‖ := by rw [← hEx]
      _ ≤ ‖b - υ⁻¹ • (p y - p x)‖ + ‖Egrad x - Egrad y‖ := norm_add_le _ _
      _ ≤ ‖b‖ + ‖υ⁻¹ • (p y - p x)‖ + ‖Egrad x - Egrad y‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ ‖b‖ + υ⁻¹ * (gu * ‖d‖) + Kh * ‖d‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hυ)]
          gcongr
      _ = ‖b‖ + ℓ * ‖d‖ := by rw [hℓ]; ring
  have hℓnn : 0 ≤ ℓ := by rw [hℓ]; positivity
  exact step_algebra hah hℓnn (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hΔ hXle

/-! ### The prefix average and the selected slope -/

/-- **`thm:prefix-stationarity`, `eq:prefix-average`.**  On a convex chart
`Θ` where the local action `𝒜` has gradient `E = ∇𝒜` with Hessian scale
`‖E x - E y‖ ≤ K₀ h⁻² ‖x - y‖` and oscillation `≤ D₀`, and where the
operational potential has gradient `p` with `g_* ‖y-x‖² ≤ ⟪p y - p x, y - x⟫`
and `‖p y - p x‖ ≤ g^* ‖y - x‖`, with `υ_h = υ₀ h²` and `υ₀ K₀ < g_*/2`,
every accepted finite sequence `θ_0, …, θ_J ∈ Θ` satisfies
`(1/J) Σ_{j<J} ‖E(θ_j)‖² ≤ C₀ h⁻² D₀/J + D₁ (1/J) Σ_{j<J} ‖b_j‖²`. -/
theorem prefix_average (𝒜 : E → ℝ) (Egrad p : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hgrad : ∀ x ∈ Θ, HasGradientAt 𝒜 (Egrad x) x)
    (hcont : ContinuousOn Egrad Θ) (h K0 D0 gs gu υ0 : ℝ)
    (hh : 0 < h) (hK0 : 0 ≤ K0) (hgs : 0 < gs) (hgsu : gs ≤ gu)
    (hυ0 : 0 < υ0) (hsmall : υ0 * K0 < gs / 2)
    (hHess : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖Egrad x - Egrad y‖ ≤ K0 * h⁻¹ ^ 2 * ‖x - y‖)
    (hosc : ∀ x ∈ Θ, ∀ y ∈ Θ, 𝒜 x - 𝒜 y ≤ D0)
    (hFisherLow : ∀ x ∈ Θ, ∀ y ∈ Θ, gs * ‖y - x‖ ^ 2 ≤ ⟪p y - p x, y - x⟫)
    (hFisherUp : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖p y - p x‖ ≤ gu * ‖y - x‖)
    (J : ℕ) (hJ : 0 < J) (θ : ℕ → E) (hθ : ∀ j ≤ J, θ j ∈ Θ) :
    (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ‖Egrad (θ j)‖ ^ 2
      ≤ prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J)
        + prefixD1 gs gu K0 υ0
          * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
              ‖prefixBalance Egrad p (υ0 * h ^ 2) θ j‖ ^ 2) := by
  set Kh := K0 * h⁻¹ ^ 2 with hKh
  set υ := υ0 * h ^ 2 with hυ
  have hυpos : 0 < υ := by positivity
  have hKhnn : 0 ≤ Kh := by positivity
  have ha0 := prefixA0_pos hgs hυ0 hK0 hsmall
  have hgu : 0 ≤ gu := by linarith
  -- the h-scaled coefficients
  have hαh : gs / υ - Kh / 2 = prefixA0 gs K0 υ0 * h⁻¹ ^ 2 := by
    rw [hυ, hKh, prefixA0]
    field_simp
    try ring
  have hℓh : gu / υ + Kh = prefixL0 gu K0 υ0 * h⁻¹ ^ 2 := by
    rw [hυ, hKh, prefixL0]
    field_simp
    try ring
  have hah : 0 < gs / υ - Kh / 2 := by rw [hαh]; positivity
  -- one-step bounds
  have hstep : ∀ j ∈ Finset.range J,
      ‖Egrad (θ j)‖ ^ 2
        ≤ prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (𝒜 (θ j) - 𝒜 (θ (j + 1)))
          + prefixD1 gs gu K0 υ0 * ‖prefixBalance Egrad p υ θ j‖ ^ 2 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hs := step_bound 𝒜 Egrad p hΘ hgrad hcont Kh gs gu υ hKhnn hgu hυpos hah
      hHess hFisherLow hFisherUp (hθ j hj.le) (hθ (j + 1) hj)
    have hC : 4 * (gu / υ + Kh) ^ 2 / (gs / υ - Kh / 2)
        = prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 := by
      rw [hαh, hℓh, prefixC0]
      field_simp
      try ring
    have hD : 2 + 2 * (gu / υ + Kh) ^ 2 / (gs / υ - Kh / 2) ^ 2
        = prefixD1 gs gu K0 υ0 := by
      rw [hαh, hℓh, prefixD1]
      field_simp
      try ring
    rw [hC, hD] at hs
    exact hs
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub' (fun j => 𝒜 (θ j))] at hsum
  have hD0 : 𝒜 (θ 0) - 𝒜 (θ J) ≤ D0 := hosc _ (hθ 0 (Nat.zero_le _)) _ (hθ J le_rfl)
  have hC0nn : 0 ≤ prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 := by
    unfold prefixC0
    have := prefixL0_nonneg hgu hυ0 hK0
    positivity
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  have h1 : (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ‖Egrad (θ j)‖ ^ 2
      ≤ (1 / (J:ℝ)) * (prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * D0
          + prefixD1 gs gu K0 υ0 * ∑ j ∈ Finset.range J,
              ‖prefixBalance Egrad p υ θ j‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hD0 hC0nn
    linarith
  calc (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ‖Egrad (θ j)‖ ^ 2
      ≤ _ := h1
    _ = _ := by ring

/-- **`eq:prefix-selected`**: the smallest observed full native slope
satisfies
`‖E(θ_{j*})‖ ≤ √C₀ h⁻¹ √(D₀/J) + √D₁ (J⁻¹ Σ_{j<J} ‖b_j‖²)^{1/2}`;
in particular the paper's form with `C = max(√C₀, √D₁)`. -/
theorem prefix_selected (𝒜 : E → ℝ) (Egrad p : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hgrad : ∀ x ∈ Θ, HasGradientAt 𝒜 (Egrad x) x)
    (hcont : ContinuousOn Egrad Θ) (h K0 D0 gs gu υ0 : ℝ)
    (hh : 0 < h) (hK0 : 0 ≤ K0) (hgs : 0 < gs) (hgsu : gs ≤ gu)
    (hυ0 : 0 < υ0) (hsmall : υ0 * K0 < gs / 2)
    (hHess : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖Egrad x - Egrad y‖ ≤ K0 * h⁻¹ ^ 2 * ‖x - y‖)
    (hosc : ∀ x ∈ Θ, ∀ y ∈ Θ, 𝒜 x - 𝒜 y ≤ D0)
    (hFisherLow : ∀ x ∈ Θ, ∀ y ∈ Θ, gs * ‖y - x‖ ^ 2 ≤ ⟪p y - p x, y - x⟫)
    (hFisherUp : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖p y - p x‖ ≤ gu * ‖y - x‖)
    (J : ℕ) (hJ : 0 < J) (θ : ℕ → E) (hθ : ∀ j ≤ J, θ j ∈ Θ) :
    ∃ jstar < J, (∀ j < J, ‖Egrad (θ jstar)‖ ≤ ‖Egrad (θ j)‖) ∧
      ‖Egrad (θ jstar)‖
        ≤ Real.sqrt (prefixC0 gs gu K0 υ0) * h⁻¹ * Real.sqrt (D0 / J)
          + Real.sqrt (prefixD1 gs gu K0 υ0)
            * Real.sqrt ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
                ‖prefixBalance Egrad p (υ0 * h ^ 2) θ j‖ ^ 2) := by
  have havg := prefix_average 𝒜 Egrad p hΘ hgrad hcont h K0 D0 gs gu υ0 hh hK0 hgs
    hgsu hυ0 hsmall hHess hosc hFisherLow hFisherUp J hJ θ hθ
  obtain ⟨jstar, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range J)
    (fun j => ‖Egrad (θ j)‖) ⟨0, Finset.mem_range.mpr hJ⟩
  rw [Finset.mem_range] at hjmem
  refine ⟨jstar, hjmem, fun j hj => hjmin j (Finset.mem_range.mpr hj), ?_⟩
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  -- min² ≤ average
  have hmin2 : ‖Egrad (θ jstar)‖ ^ 2
      ≤ (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ‖Egrad (θ j)‖ ^ 2 := by
    have hle : ∀ j ∈ Finset.range J, ‖Egrad (θ jstar)‖ ^ 2 ≤ ‖Egrad (θ j)‖ ^ 2 := by
      intro j hj
      have := hjmin j hj
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hs := Finset.sum_le_sum hle
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hJpos]
    linarith
  have hD0 : 0 ≤ D0 := by
    have := hosc _ (hθ 0 (Nat.zero_le _)) _ (hθ 0 (Nat.zero_le _))
    linarith
  have hgu : 0 ≤ gu := by linarith
  have ha0 := prefixA0_pos hgs hυ0 hK0 hsmall
  have hℓ0 := prefixL0_nonneg hgu hυ0 hK0
  have hC0 : 0 ≤ prefixC0 gs gu K0 υ0 := by unfold prefixC0; positivity
  have hD1 : 0 ≤ prefixD1 gs gu K0 υ0 := by unfold prefixD1; positivity
  set B := (1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
    ‖prefixBalance Egrad p (υ0 * h ^ 2) θ j‖ ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set X := prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J) with hX
  set Y := prefixD1 gs gu K0 υ0 * B with hY
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hYnn : 0 ≤ Y := by rw [hY]; positivity
  have hsq : ‖Egrad (θ jstar)‖ ^ 2 ≤ X + Y := hmin2.trans havg
  have hsqrt : ‖Egrad (θ jstar)‖ ≤ Real.sqrt (X + Y) := by
    rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact hsq
  have hsplit : Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 := Real.sq_sqrt hXnn
    have h2 := Real.sq_sqrt hYnn
    nlinarith [Real.sqrt_nonneg X, Real.sqrt_nonneg Y]
  have hXs : Real.sqrt X = Real.sqrt (prefixC0 gs gu K0 υ0) * h⁻¹ * Real.sqrt (D0 / J) := by
    rw [hX, Real.sqrt_mul (by positivity), Real.sqrt_mul hC0, Real.sqrt_sq (by positivity)]
  have hYs : Real.sqrt Y = Real.sqrt (prefixD1 gs gu K0 υ0) * Real.sqrt B := by
    rw [hY, Real.sqrt_mul hD1]
  rw [← hXs, ← hYs]
  exact hsqrt.trans hsplit

/-! ### Finite-table certification (`cor:prefix-table`) -/

/-- **`cor:prefix-table`, `eq:prefix-table-probability`** (Markov step).
Let `(Ω, P)` be a probability space carrying the accepted record
`θ_j : Ω → E`, let `G` be the measurable safe event on which the
accepted prefix stays inside the chart, `p_exit = P(Gᶜ)`, and
`𝒬^{bal} = (1/J) Σ_{j<J} E[1_G ‖b_j‖²]`.  Then for `0 < α ≤ 1` (any
`α > 0` in fact) the probability that the best safe observed record has
full native slope `> h^α` is at most
`p_exit + C₀ D₀/(J h^{2+2α}) + D₁ h^{-2α} 𝒬^{bal}`.
Integrability of the safe-indicated squared slopes and balances is
assumed (finite tables). -/
theorem prefix_table_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒜 : E → ℝ) (Egrad p : E → E) {Θ : Set E}
    (hΘ : Convex ℝ Θ) (hgrad : ∀ x ∈ Θ, HasGradientAt 𝒜 (Egrad x) x)
    (hcont : ContinuousOn Egrad Θ) (h K0 D0 gs gu υ0 : ℝ)
    (hh : 0 < h) (hK0 : 0 ≤ K0) (hgs : 0 < gs) (hgsu : gs ≤ gu)
    (hυ0 : 0 < υ0) (hsmall : υ0 * K0 < gs / 2)
    (hHess : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖Egrad x - Egrad y‖ ≤ K0 * h⁻¹ ^ 2 * ‖x - y‖)
    (hosc : ∀ x ∈ Θ, ∀ y ∈ Θ, 𝒜 x - 𝒜 y ≤ D0) (hD0 : 0 ≤ D0)
    (hFisherLow : ∀ x ∈ Θ, ∀ y ∈ Θ, gs * ‖y - x‖ ^ 2 ≤ ⟪p y - p x, y - x⟫)
    (hFisherUp : ∀ x ∈ Θ, ∀ y ∈ Θ, ‖p y - p x‖ ≤ gu * ‖y - x‖)
    (J : ℕ) (hJ : 0 < J) (θ : ℕ → Ω → E) (G : Set Ω) (hG : MeasurableSet G)
    (hsafe : ∀ ω ∈ G, ∀ j ≤ J, θ j ω ∈ Θ)
    (hintE : ∀ j, Integrable (G.indicator fun ω => ‖Egrad (θ j ω)‖ ^ 2) P)
    (hintb : ∀ j, Integrable (G.indicator fun ω =>
      ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) P)
    (α : ℝ) :
    P.real {ω | ω ∉ G ∨ ∀ j < J, h ^ α < ‖Egrad (θ j ω)‖}
      ≤ P.real Gᶜ
        + prefixC0 gs gu K0 υ0 * D0 / (J * h ^ (2 + 2 * α))
        + prefixD1 gs gu K0 υ0 * h ^ (-(2 * α))
          * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
              ∫ ω, G.indicator (fun ω =>
                ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) ω ∂P) := by
  -- the safe-indicated pathwise mean square
  set F : Ω → ℝ := fun ω => G.indicator (fun ω =>
    (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ‖Egrad (θ j ω)‖ ^ 2) ω with hF
  have hFeq : F = fun ω => (1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
      G.indicator (fun ω => ‖Egrad (θ j ω)‖ ^ 2) ω := by
    funext ω
    rw [hF]
    by_cases hω : ω ∈ G
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hFint : Integrable F P := by
    rw [hFeq]
    exact (integrable_finsetSum _ (fun j _ => hintE j)).const_mul _
  have hFnn : 0 ≤ᵐ[P] F := by
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [hF]
    apply Set.indicator_nonneg
    intro ω _
    positivity
  -- pathwise bound on G
  have hpath : ∀ ω ∈ G, F ω
      ≤ prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J)
        + prefixD1 gs gu K0 υ0 * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
            ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) := by
    intro ω hω
    simp only [hF, Set.indicator_of_mem hω]
    exact prefix_average 𝒜 Egrad p hΘ hgrad hcont h K0 D0 gs gu υ0 hh hK0 hgs hgsu hυ0
      hsmall hHess hosc hFisherLow hFisherUp J hJ (fun i => θ i ω) (hsafe ω hω)
  -- the failure event is contained in Gᶜ ∪ {h^{2α} ≤ F}
  have hε : 0 < h ^ (2 * α) := Real.rpow_pos_of_pos hh _
  have hsub : {ω | ω ∉ G ∨ ∀ j < J, h ^ α < ‖Egrad (θ j ω)‖}
      ⊆ Gᶜ ∪ {ω | h ^ (2 * α) ≤ F ω} := by
    intro ω hω
    rcases hω with hω | hω
    · exact Or.inl hω
    · by_cases hωG : ω ∈ G
      · right
        show h ^ (2 * α) ≤ F ω
        simp only [hF, Set.indicator_of_mem hωG]
        have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
        have hterm : ∀ j ∈ Finset.range J, h ^ (2 * α) ≤ ‖Egrad (θ j ω)‖ ^ 2 := by
          intro j hj
          have h1 := hω j (Finset.mem_range.mp hj)
          have h2 : h ^ (2 * α) = (h ^ α) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
            norm_num
            ring_nf
          rw [h2]
          exact pow_le_pow_left₀ (Real.rpow_nonneg hh.le _) h1.le 2
        have hs := Finset.sum_le_sum hterm
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hJpos]
        linarith
      · exact Or.inl hωG
  -- Markov's inequality
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hFnn hFint (h ^ (2 * α))
  -- the integral of F is bounded by the safe balance sum
  have hint_le : ∫ ω, F ω ∂P
      ≤ prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J)
        + prefixD1 gs gu K0 υ0 * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
            ∫ ω, G.indicator (fun ω =>
              ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) ω ∂P) := by
    -- pointwise: F ≤ 1_G·const + D₁ (1/J) Σ 1_G ‖b_j‖²
    have hgu : 0 ≤ gu := by linarith
    have ha0 := prefixA0_pos hgs hυ0 hK0 hsmall
    have hℓ0 := prefixL0_nonneg hgu hυ0 hK0
    have hC0 : 0 ≤ prefixC0 gs gu K0 υ0 := by unfold prefixC0; positivity
    have hD1 : 0 ≤ prefixD1 gs gu K0 υ0 := by unfold prefixD1; positivity
    set cst := prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J) with hcst
    have hcstnn : 0 ≤ cst := by rw [hcst]; positivity
    have hpt : ∀ ω, F ω ≤ G.indicator (fun _ => cst) ω
        + prefixD1 gs gu K0 υ0 * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
            G.indicator (fun ω =>
              ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) ω) := by
      intro ω
      by_cases hω : ω ∈ G
      · simp only [Set.indicator_of_mem hω]
        exact hpath ω hω
      · simp [hF, Set.indicator_of_notMem hω]
    have hint2 : Integrable (fun ω => G.indicator (fun _ => cst) ω
        + prefixD1 gs gu K0 υ0 * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
            G.indicator (fun ω =>
              ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) ω)) P := by
      refine Integrable.add ?_ ?_
      · exact (integrable_const cst).indicator hG
      · exact ((integrable_finsetSum _ (fun j _ => hintb j)).const_mul _).const_mul _
    have hle := integral_mono hFint hint2 hpt
    rw [integral_add ((integrable_const cst).indicator hG)
      (((integrable_finsetSum _ (fun j _ => hintb j)).const_mul _).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ (fun j _ => hintb j),
      integral_indicator_const _ hG] at hle
    have hGle : (P.real G) • cst ≤ cst := by
      rw [smul_eq_mul]
      have : P.real G ≤ 1 := by
        rw [measureReal_def]
        have := prob_le_one (μ := P) (s := G)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      nlinarith
    linarith
  -- assemble
  have hunion : P.real {ω | ω ∉ G ∨ ∀ j < J, h ^ α < ‖Egrad (θ j ω)‖}
      ≤ P.real Gᶜ + P.real {ω | h ^ (2 * α) ≤ F ω} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hmark2 : P.real {ω | h ^ (2 * α) ≤ F ω} ≤ (h ^ (2 * α))⁻¹ * ∫ ω, F ω ∂P := by
    rw [← div_eq_inv_mul, le_div_iff₀ hε]
    linarith [hmarkov]
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  have hpow1 : (h ^ (2 * α))⁻¹ * (prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J))
      = prefixC0 gs gu K0 υ0 * D0 / (J * h ^ (2 + 2 * α)) := by
    rw [Real.rpow_add hh, Real.rpow_two]
    field_simp
  have hpow2 : (h ^ (2 * α))⁻¹ = h ^ (-(2 * α)) := by
    rw [Real.rpow_neg hh.le]
  calc P.real {ω | ω ∉ G ∨ ∀ j < J, h ^ α < ‖Egrad (θ j ω)‖}
      ≤ P.real Gᶜ + P.real {ω | h ^ (2 * α) ≤ F ω} := hunion
    _ ≤ P.real Gᶜ + (h ^ (2 * α))⁻¹ * ∫ ω, F ω ∂P := by linarith
    _ ≤ P.real Gᶜ + (h ^ (2 * α))⁻¹ * (prefixC0 gs gu K0 υ0 * h⁻¹ ^ 2 * (D0 / J)
        + prefixD1 gs gu K0 υ0 * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
            ∫ ω, G.indicator (fun ω =>
              ‖prefixBalance Egrad p (υ0 * h ^ 2) (fun i => θ i ω) j‖ ^ 2) ω ∂P)) := by
        gcongr
    _ = _ := by
        rw [mul_add, hpow1, ← mul_assoc, ← mul_assoc, mul_comm (h ^ (2 * α))⁻¹, hpow2]
        ring

/-- **Dyadic Borel–Cantelli clause of `cor:prefix-table`**: if the
failure events `A_n` of a cutoff family on a common probability space
have summable probability bounds, then almost surely only finitely many
cutoffs fail — eventual certification without independence. -/
theorem eventually_certified_of_summable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω) (bound : ℕ → ℝ)
    (hA : ∀ n, P.real (A n) ≤ bound n) (hsum : Summable bound) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ω ∉ A n := by
  have hbnn : ∀ n, 0 ≤ bound n := fun n => (measureReal_nonneg).trans (hA n)
  have hfin : ∑' n, P (A n) ≠ ⊤ := by
    have h1 : ∀ n, P (A n) ≤ ENNReal.ofReal (bound n) := by
      intro n
      have := hA n
      rw [measureReal_def] at this
      have hfin' : P (A n) ≠ ⊤ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal hfin']
      exact ENNReal.ofReal_le_ofReal this
    have h2 : ∑' n, P (A n) ≤ ∑' n, ENNReal.ofReal (bound n) := ENNReal.tsum_le_tsum h1
    have h3 : ∑' n, ENNReal.ofReal (bound n) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hbnn hsum]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h3 h2
  have hlim := measure_limsup_atTop_eq_zero hfin
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hlim
  intro ω hω
  simp only [Set.mem_ofPred_eq, Filter.not_eventually, not_not] at hω
  rw [Filter.mem_limsup_iff_frequently_mem]
  exact hω

end PrefixStationarity
end RenewalGeometry
