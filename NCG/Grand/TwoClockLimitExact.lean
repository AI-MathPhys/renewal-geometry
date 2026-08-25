/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ProjectionPersistenceTradeoff

/-!
# The singular two-clock limit

Machinery for `thm:renewal-interchange-two-clock`, addressing the
fidelity-audit gap (the previous Lean was only the scalar limit
`σλ/κ → 0`): the record's analytic content — the mode-multiplier limits of
the exact Fourier spectrum of the proved anchor
`thm:projection-persistence-tradeoff` — is formalized exactly.

* `exp_apply_eigenvector`: the semigroup bridge — the exponential of a
  bounded operator acts on an eigenvector by the scalar exponential of its
  eigenvalue, so the anchor's exact diagonal generator action
  `𝓛 Φ(e_k) = −Λ_{k,N} Φ(e_k)` exponentiates to the mode multiplier
  `e^{−tΛ_{k,N}}`;
* `tendsto_sq_mul_sin_sq`: the lattice eigenvalue asymptotics
  `N² sin²(πa/N) → π²a²`;
* `decayRate_fixed_mode`: the anchor's boxed decay rate at a fixed integer
  mode, in explicit form;
* `fast_clock_multiplier` (boxed (i)): on the fast clock `t = σ/κ_N`, with
  `λ_N/κ_N → 0`, the mode multiplier converges to the continuum heat
  multiplier `e^{−σ·4π²|k|²}`;
* `slow_clock_nonzero_multiplier` (boxed (ii), nonzero modes): on the slow
  renewal clock `t = s/λ_N`, with `κ_N/λ_N → ∞`, every nonzero spatial mode
  multiplier vanishes;
* `slow_clock_zero_mode` (boxed (ii), zero mode): the zero mode retains the
  exact scalar count relaxation `e^{−22s/15}` at every finite `N`.
-/

open Filter Real NormedSpace Nat
open scoped Topology

namespace NCG
namespace TwoClock

/-! ### The semigroup bridge: eigenvector exponentials -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem pow_apply_eigenvector (A : E →L[ℂ] E) {v : E} {μ : ℂ}
    (hv : A v = μ • v) (n : ℕ) : (A ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (A ^ (n + 1)) v = A ((A ^ n) v) := by
      rw [_root_.pow_succ']
      rfl
    rw [hstep, ih, map_smul, hv, smul_smul, ← _root_.pow_succ]

/-- **The semigroup bridge**: the exponential of a bounded operator acts on an
eigenvector by the scalar exponential of its eigenvalue. -/
theorem exp_apply_eigenvector (A : E →L[ℂ] E) {v : E} {μ : ℂ}
    (hv : A v = μ • v) : exp A v = exp μ • v := by
  have hsA : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • A ^ n) (exp A) := by
    rw [exp_eq_tsum (𝕂 := ℂ)]
    exact (expSeries_summable' (𝕂 := ℂ) A).hasSum
  have hsv := (ContinuousLinearMap.apply ℂ E v).hasSum hsA
  have hsμ : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • μ ^ n) (exp μ) := by
    rw [exp_eq_tsum (𝕂 := ℂ)]
    exact (expSeries_summable' (𝕂 := ℂ) μ).hasSum
  have hsv' := (ContinuousLinearMap.toSpanSingleton ℂ v).hasSum hsμ
  have hfun : (fun n : ℕ =>
      (ContinuousLinearMap.apply ℂ E v) ((n !⁻¹ : ℂ) • A ^ n))
      = fun n : ℕ =>
        (ContinuousLinearMap.toSpanSingleton ℂ v) ((n !⁻¹ : ℂ) • μ ^ n) := by
    funext n
    simp only [ContinuousLinearMap.apply_apply, smul_apply,
      ContinuousLinearMap.toSpanSingleton_apply, pow_apply_eigenvector A hv n,
      smul_smul, smul_eq_mul]
  rw [hfun] at hsv
  have h := hsv.unique hsv'
  simpa [ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using h

/-! ### Lattice eigenvalue asymptotics -/

theorem tendsto_natCast_mul_sin (a : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sin (π * a / N)) atTop (𝓝 (π * a)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [mul_zero, zero_div, Real.sin_zero]
    exact tendsto_const_nhds
  · have hu : Tendsto (fun N : ℕ => π * a / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (π * a)
    have hu' : Tendsto (fun N : ℕ => π * a / N) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ha) hN'
    have hslope : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
      have h2 := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sin 0)
      simpa [slope_fun_def, Real.sin_zero, Real.cos_zero, sub_zero,
        div_eq_inv_mul] using h2
    have hcomp := hslope.comp hu'
    have hlim := hcomp.const_mul (π * a)
    have heq : ∀ᶠ N : ℕ in atTop,
        (π * a) * (Real.sin (π * a / N) / (π * a / N))
          = (N : ℝ) * Real.sin (π * a / N) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hπa : π * a ≠ 0 := mul_ne_zero Real.pi_ne_zero ha
      field_simp
    refine Tendsto.congr' heq ?_
    simpa [Function.comp_def, mul_one] using hlim

theorem tendsto_sq_mul_sin_sq (a : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Real.sin (π * a / N) ^ 2) atTop
      (𝓝 (π ^ 2 * a ^ 2)) := by
  have h2 := (tendsto_natCast_mul_sin a).mul (tendsto_natCast_mul_sin a)
  have heq : (fun N : ℕ => ((N : ℝ) * Real.sin (π * a / N))
      * ((N : ℝ) * Real.sin (π * a / N)))
      = fun N : ℕ => (N : ℝ) ^ 2 * Real.sin (π * a / N) ^ 2 := by
    funext N
    ring
  rw [heq] at h2
  have hval : (π * a) * (π * a) = π ^ 2 * a ^ 2 := by ring
  rwa [hval] at h2

/-- The anchor's boxed decay rate `Λ_{k,N}` at a fixed integer mode, in
explicit form. -/
theorem decayRate_fixed_mode {N : ℕ} [NeZero N] (lam kappa : ℝ)
    (a : Fin 3 → ℕ) (hA : ∀ j, a j < N) :
    NCG.FlipInterchange.decayRate (N := N) lam kappa
        (fun j => (a j : ZMod N))
      = 22 * lam / 15 + 4 * kappa * (N : ℝ) ^ 2
          * ∑ j : Fin 3, Real.sin (π * (a j : ℝ) / N) ^ 2 := by
  unfold NCG.FlipInterchange.decayRate
  have hsum : ∑ j : Fin 3,
      Real.sin (π * (((fun j => (a j : ZMod N)) j).val : ℝ) / N) ^ 2
      = ∑ j : Fin 3, Real.sin (π * (a j : ℝ) / N) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.val_natCast_of_lt (hA j)]
  rw [hsum]

/-! ### The two clocks -/

/-- **Boxed (i), the fast clock**: at `t = σ/κ_N` with `λ_N/κ_N → 0`, the
mode multiplier converges to the continuum heat multiplier
`e^{−σ·4π²|k|²}`. -/
theorem fast_clock_multiplier (lam kappa : ℕ → ℝ) (a : Fin 3 → ℝ) (σ : ℝ)
    (hκpos : ∀ N, 0 < kappa N)
    (hratio : Tendsto (fun N => lam N / kappa N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.exp (-(σ / kappa N)
        * (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2
            * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2)))
      atTop (𝓝 (Real.exp (-σ * (4 * π ^ 2 * ∑ j : Fin 3, (a j) ^ 2)))) := by
  have hsum : Tendsto
      (fun N : ℕ => ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)
      atTop (𝓝 (∑ j : Fin 3, π ^ 2 * (a j) ^ 2)) :=
    tendsto_finsetSum _ fun j _ => tendsto_sq_mul_sin_sq (a j)
  have hterm1 : Tendsto (fun N : ℕ => -σ * (22 / 15) * (lam N / kappa N))
      atTop (𝓝 0) := by
    simpa using hratio.const_mul (-σ * (22 / 15))
  have hterm2 : Tendsto (fun N : ℕ => -(4 * σ)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)
      atTop (𝓝 (-(4 * σ) * ∑ j : Fin 3, π ^ 2 * (a j) ^ 2)) :=
    hsum.const_mul _
  have hcomb := hterm1.add hterm2
  have hpt : ∀ N : ℕ, -σ * (22 / 15) * (lam N / kappa N)
      + -(4 * σ) * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2
      = -(σ / kappa N) * (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2
          * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2) := by
    intro N
    have hκ : kappa N ≠ 0 := (hκpos N).ne'
    rw [show ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2
        = (N : ℝ) ^ 2 * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2 from
      (Finset.mul_sum _ _ _).symm]
    field_simp
    ring
  have hexp := hcomb.congr hpt
  have hval : (0 : ℝ) + -(4 * σ) * ∑ j : Fin 3, π ^ 2 * (a j) ^ 2
      = -σ * (4 * π ^ 2 * ∑ j : Fin 3, (a j) ^ 2) := by
    rw [show ∑ j : Fin 3, π ^ 2 * (a j) ^ 2
        = π ^ 2 * ∑ j : Fin 3, (a j) ^ 2 from (Finset.mul_sum _ _ _).symm]
    ring
  rw [hval] at hexp
  exact (Real.continuous_exp.tendsto _).comp hexp

/-- **Boxed (ii), nonzero modes on the slow clock**: at `t = s/λ_N` with
`κ_N/λ_N → ∞`, every nonzero spatial mode multiplier vanishes. -/
theorem slow_clock_nonzero_multiplier (lam kappa : ℕ → ℝ) (a : Fin 3 → ℝ)
    (s : ℝ) (hs : 0 < s) (hlampos : ∀ N, 0 < lam N)
    (hratio : Tendsto (fun N => kappa N / lam N) atTop atTop)
    (ha : 0 < ∑ j : Fin 3, (a j) ^ 2) :
    Tendsto (fun N : ℕ => Real.exp (-(s / lam N)
        * (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2
            * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2)))
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun N : ℕ => ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)
      atTop (𝓝 (∑ j : Fin 3, π ^ 2 * (a j) ^ 2)) :=
    tendsto_finsetSum _ fun j _ => tendsto_sq_mul_sin_sq (a j)
  have hposlim : 0 < ∑ j : Fin 3, π ^ 2 * (a j) ^ 2 := by
    rw [show ∑ j : Fin 3, π ^ 2 * (a j) ^ 2
        = π ^ 2 * ∑ j : Fin 3, (a j) ^ 2 from (Finset.mul_sum _ _ _).symm]
    exact mul_pos (by positivity) ha
  have hprod : Tendsto (fun N : ℕ => (kappa N / lam N)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)
      atTop atTop := hratio.atTop_mul_pos hposlim hsum
  have hprod4 : Tendsto (fun N : ℕ => (4 * s) * ((kappa N / lam N)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2))
      atTop atTop := hprod.const_mul_atTop (by positivity)
  have hneg0 : Tendsto (fun N : ℕ => -((4 * s) * ((kappa N / lam N)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)))
      atTop atBot := tendsto_neg_atBot_iff.mpr hprod4
  have hneg : Tendsto (fun N : ℕ => -22 * s / 15 + -((4 * s) * ((kappa N / lam N)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2)))
      atTop atBot :=
    tendsto_atBot_add_const_left atTop (-22 * s / 15) hneg0
  have hpt : ∀ N : ℕ, -22 * s / 15 + -((4 * s) * ((kappa N / lam N)
      * ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2))
      = -(s / lam N) * (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2
          * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2) := by
    intro N
    have hlam : lam N ≠ 0 := (hlampos N).ne'
    rw [show ∑ j : Fin 3, (N : ℝ) ^ 2 * Real.sin (π * a j / N) ^ 2
        = (N : ℝ) ^ 2 * ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2 from
      (Finset.mul_sum _ _ _).symm]
    field_simp
    ring
  have hexp := hneg.congr hpt
  exact Real.tendsto_exp_atBot.comp hexp

/-- **Boxed (ii), the zero mode**: on the slow clock the zero mode retains the
exact scalar count relaxation `e^{−22s/15}` at every finite `N`. -/
theorem slow_clock_zero_mode (lam : ℕ → ℝ) (s : ℝ) (N : ℕ)
    (hlam : lam N ≠ 0) :
    Real.exp (-(s / lam N) * (22 * lam N / 15))
      = Real.exp (-22 * s / 15) := by
  congr 1
  field_simp

end TwoClock
end NCG
