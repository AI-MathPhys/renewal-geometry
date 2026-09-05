/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mittag-Leffler kernel for the fractional dark-energy cluster
  (GR_emergence, §deficiency relaxation)

The minimal Caputo/Mittag-Leffler foundation used by
`prop:deficiency-subordination`, `thm:source-free-no-crossing`,
`thm:irreversible-crossing-threshold` and
`cor:exchange-driven-crossing`:

* `Gamma_add_rpow_le` — the Gautschi-type ratio bound
  `(x-1)^α Γ(x) ≤ Γ(x+α)` from the log-convexity of `Γ`
  (Bohr–Mollerup slope monotonicity);
* `mlSummable`, `mittagLeffler` — the two-parameter Mittag-Leffler
  series `E_{α,β}(x) = Σ xⁿ/Γ(αn+β)` converges for every real `x`
  (`α > 0`, `β ≥ 1`), by the ratio test against the Gautschi bound;
* `mittagLeffler_zero`, `mlRelax`, `mlRelax_zero` — the fractional
  relaxation profile `y(t) = y₀ E_α(-λ tᵅ)` and its initial value;
* `crossing_threshold_iff`, `early_slope_sign` — the boxed
  irreversibility threshold `σ₀ > Γm²Δ₀`: the early-time slope
  coefficient `(s₀ - λΔ₀)/Γ(α)` of the driven Caputo equation is
  positive exactly above threshold;
* `later_turning_point` — the turning-point mechanism of
  `cor:exchange-driven-crossing`: a differentiable trajectory that
  starts at `y₀`, rises strictly above it, and converges to a limit
  below its risen value has a strictly positive interior local
  maximum where its derivative vanishes (the `w = -1` crossing
  instant, transverse when the second derivative is nonzero).
-/

namespace NCG

open Real Filter

/-- Gautschi-type lower ratio bound from log-convexity: for `x ≥ 2`
and `0 < α ≤ 1`, `(x-1)^α Γ(x) ≤ Γ(x+α)`. -/
theorem Gamma_add_rpow_le {x α : ℝ} (hx : 2 ≤ x) (hα : 0 < α) :
    (x - 1) ^ α * Real.Gamma x ≤ Real.Gamma (x + α) := by
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hxα : (0 : ℝ) < x + α := by linarith
  have hslope := Real.convexOn_log_Gamma.slope_mono_adjacent
    (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr hxα)
    (show x - 1 < x by linarith) (show x < x + α by linarith)
  have hrec : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
    have h := Real.Gamma_add_one (s := x - 1) h1.ne'
    have he : x - 1 + 1 = x := by ring
    rw [he] at h
    exact h
  have hG1 : (0 : ℝ) < Real.Gamma (x - 1) := Real.Gamma_pos_of_pos h1
  have hGx : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  have hGxα : (0 : ℝ) < Real.Gamma (x + α) := Real.Gamma_pos_of_pos hxα
  have hlogdiff : Real.log (Real.Gamma x) - Real.log (Real.Gamma (x - 1))
      = Real.log (x - 1) := by
    rw [hrec, Real.log_mul h1.ne' hG1.ne']
    ring
  simp only [Function.comp_apply] at hslope
  have hkey : α * Real.log (x - 1) + Real.log (Real.Gamma x)
      ≤ Real.log (Real.Gamma (x + α)) := by
    have hden1 : x - (x - 1) = 1 := by ring
    have hden2 : x + α - x = α := by ring
    rw [hden1, hden2, div_one] at hslope
    rw [hlogdiff] at hslope
    have h2 : Real.log (x - 1) * α ≤
        Real.log (Real.Gamma (x + α)) - Real.log (Real.Gamma x) := by
      have := (le_div_iff₀ hα).mp hslope
      linarith
    linarith
  calc (x - 1) ^ α * Real.Gamma x
      = Real.exp (α * Real.log (x - 1) + Real.log (Real.Gamma x)) := by
        rw [Real.exp_add, Real.exp_log hGx,
          Real.rpow_def_of_pos h1, mul_comm (Real.log (x - 1)) α]
  _ ≤ Real.exp (Real.log (Real.Gamma (x + α))) := Real.exp_le_exp.mpr hkey
  _ = Real.Gamma (x + α) := Real.exp_log hGxα

/-- The two-parameter Mittag-Leffler series converges for all real
arguments (`0 < α ≤ 1 ≤ β`). -/
theorem mlSummable {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    Summable (fun n : ℕ => x ^ n / Real.Gamma (α * n + β)) := by
  set M : ℝ := max 1 ((2 * |x| + 1) ^ (1 / α)) with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMα : 2 * |x| ≤ M ^ α := by
    have h2x : (0 : ℝ) ≤ 2 * |x| + 1 := by positivity
    have h1 : (2 * |x| + 1) ^ (1 / α) ≤ M := le_max_right _ _
    have h2 : ((2 * |x| + 1) ^ (1 / α)) ^ α ≤ M ^ α :=
      Real.rpow_le_rpow (Real.rpow_nonneg h2x _) h1 hα.le
    rw [← Real.rpow_mul h2x, one_div, inv_mul_cancel₀ hα.ne',
      Real.rpow_one] at h2
    linarith
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2)
    (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop
    ⌈(2 + M) / α⌉₊] with n hn
  have hna : 2 + M ≤ α * n := by
    have h1 : (2 + M) / α ≤ (⌈(2 + M) / α⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(2 + M) / α⌉₊ : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
    calc 2 + M = ((2 + M) / α) * α := by field_simp
    _ ≤ (n : ℝ) * α := by
        apply mul_le_mul_of_nonneg_right _ hα.le
        linarith
    _ = α * n := by ring
  have hz2 : (2 : ℝ) ≤ α * n + β := by
    have : (0 : ℝ) ≤ M := by linarith
    linarith
  have hz1 : M ≤ α * n + β - 1 := by linarith
  have hG : (0 : ℝ) < Real.Gamma (α * n + β) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hG' : (0 : ℝ) < Real.Gamma (α * n + β + α) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgautschi := Gamma_add_rpow_le hz2 hα
  have hMpow : M ^ α ≤ (α * n + β - 1) ^ α :=
    Real.rpow_le_rpow (by linarith) hz1 hα.le
  have hratio : 2 * |x| * Real.Gamma (α * n + β) ≤
      Real.Gamma (α * n + β + α) := by
    calc 2 * |x| * Real.Gamma (α * n + β)
        ≤ (α * n + β - 1) ^ α * Real.Gamma (α * n + β) := by
          apply mul_le_mul_of_nonneg_right _ hG.le
          linarith
    _ ≤ Real.Gamma (α * n + β + α) := hgautschi
  have hexp : α * (n + 1 : ℕ) + β = α * n + β + α := by
    push_cast
    ring
  rw [hexp]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, abs_pow,
    abs_pow, abs_of_pos hG, abs_of_pos hG']
  have hhalf : (1 : ℝ) / 2 * (|x| ^ n / Real.Gamma (α * n + β))
      = |x| ^ n / (2 * Real.Gamma (α * n + β)) := by
    ring
  rw [hhalf, div_le_div_iff₀ hG' (by positivity), pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hratio
    (pow_nonneg (abs_nonneg x) n)]

/-- The two-parameter Mittag-Leffler function `E_{α,β}`. -/
noncomputable def mittagLeffler (α β x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ n / Real.Gamma (α * n + β)

/-- `E_{α,β}(0) = 1/Γ(β)`. -/
theorem mittagLeffler_zero (α β : ℝ) : mittagLeffler α β 0 = 1 / Real.Gamma β := by
  unfold mittagLeffler
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [zero_pow hn]
    simp

/-- The fractional relaxation profile `y(t) = y₀ E_α(-λ tᵅ)` of
`prop:deficiency-subordination`. -/
noncomputable def mlRelax (α lam y0 t : ℝ) : ℝ :=
  y0 * mittagLeffler α 1 (-(lam * t ^ α))

/-- The relaxation profile starts at `y₀`. -/
theorem mlRelax_zero {α : ℝ} (hα : 0 < α) (lam y0 : ℝ) :
    mlRelax α lam y0 0 = y0 := by
  unfold mlRelax
  rw [Real.zero_rpow hα.ne']
  simp [mittagLeffler_zero, Real.Gamma_one]

/-- `thm:irreversible-crossing-threshold` (boxed criterion): with
`λ = Γm²/C` and `s₀ = σ₀/C`, the early-time slope coefficient
`s₀ - λΔ₀` is positive iff `σ₀ > Γm²Δ₀`. -/
theorem crossing_threshold_iff {C Gm2 sigma0 Delta0 : ℝ}
    (hC : 0 < C) :
    0 < sigma0 / C - Gm2 / C * Delta0 ↔ Gm2 * Delta0 < sigma0 := by
  have h : sigma0 / C - Gm2 / C * Delta0
      = (sigma0 - Gm2 * Delta0) / C := by
    field_simp
  rw [h]
  constructor
  · intro hpos
    have hmul := mul_pos hpos hC
    rw [div_mul_cancel₀ _ hC.ne'] at hmul
    linarith
  · intro hlt
    exact div_pos (by linarith) hC

/-- The early-time Caputo slope `(s₀ - λΔ₀)/Γ(α) · t^{α-1}` has the
sign of the threshold criterion (`Γ(α) > 0`). -/
theorem early_slope_sign {α C Gm2 sigma0 Delta0 : ℝ} (hα : 0 < α)
    (hC : 0 < C) (habove : Gm2 * Delta0 < sigma0) :
    0 < (sigma0 / C - Gm2 / C * Delta0) / Real.Gamma α :=
  div_pos ((crossing_threshold_iff hC).mpr habove)
    (Real.Gamma_pos_of_pos hα)

/-- `cor:exchange-driven-crossing` (turning-point mechanism): a
differentiable trajectory starting at `y₀`, rising strictly above it
at some `t₁ > 0`, and converging at late times to a limit strictly
below its risen value, has a strictly positive local maximum where
its derivative vanishes — the crossing instant `t_c`, transverse when
the second derivative is nonzero there. -/
theorem later_turning_point {f : ℝ → ℝ} {y0 L t1 : ℝ}
    (hdiff : Differentiable ℝ f) (h0 : f 0 = y0) (ht1 : 0 < t1)
    (hrise : y0 < f t1) (hlim : Tendsto f atTop (nhds L))
    (hL : L < f t1) :
    ∃ tc, 0 < tc ∧ IsLocalMax f tc ∧ deriv f tc = 0 := by
  have hev : ∀ᶠ t in atTop, f t < f t1 :=
    hlim.eventually_lt_const hL
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  set R : ℝ := max T t1 + 1 with hR
  have ht1R : t1 ≤ R := by
    have := le_max_right T t1
    linarith [hR]
  have hne : (Set.Icc (0 : ℝ) R).Nonempty :=
    ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, by linarith⟩⟩
  obtain ⟨tc, htc_mem, htc_max⟩ :=
    isCompact_Icc.exists_isMaxOn hne (hdiff.continuous.continuousOn)
  have ht1mem : t1 ∈ Set.Icc (0 : ℝ) R := ⟨ht1.le, ht1R⟩
  have hfc : f t1 ≤ f tc := htc_max ht1mem
  have htc0 : 0 < tc := by
    rcases (htc_mem.1).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, h0] at hfc
      linarith
  have htcT : tc < T := by
    by_contra hcon
    rw [not_lt] at hcon
    have := hT tc hcon
    linarith
  have htcR : tc < R := by
    have := le_max_left T t1
    linarith [hR]
  have hnhds : Set.Icc (0 : ℝ) R ∈ nhds tc := Icc_mem_nhds htc0 htcR
  have hlmax : IsLocalMax f tc := htc_max.isLocalMax hnhds
  exact ⟨tc, htc0, hlmax, hlmax.deriv_eq_zero⟩

end NCG
