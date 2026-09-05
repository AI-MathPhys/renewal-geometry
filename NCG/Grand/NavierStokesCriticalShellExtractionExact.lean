/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Critical-shell extraction for Navier--Stokes continuation criteria

This file formalizes the reusable logical and quantitative end of NS.10--NS.11.
Once failure of a terminal high-frequency smallness criterion supplies a shell
beyond every time/frequency cutoff, dependent choice produces times converging
to the maximal endpoint and frequencies tending to infinity.  The standard
Bernstein and frequency-localization inequalities then force the energy and
vorticity lower bounds.
-/

open Filter Topology

noncomputable section

namespace NCG.NavierStokesCriticalShellExtraction

/-- Failure of terminal shell smallness at every scale produces a critical
sequence with `t_j → T` and `q_j → ∞`. -/
theorem exists_critical_shell_sequence
    (amplitude : ℝ → ℕ → ℝ) (T threshold : ℝ)
    (hexit : ∀ j : ℕ, ∃ t : ℝ, ∃ q : ℕ,
      T - 1 / ((j : ℝ) + 1) < t ∧ t < T ∧ j < q ∧
        threshold ≤ amplitude t q) :
    ∃ t : ℕ → ℝ, ∃ q : ℕ → ℕ,
      Tendsto t atTop (𝓝 T) ∧ Tendsto q atTop atTop ∧
      (∀ j, t j < T) ∧ (∀ j, threshold ≤ amplitude (t j) (q j)) := by
  choose t q hlower hupper hq hamp using hexit
  refine ⟨t, q, ?_, ?_, hupper, hamp⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun j ↦ norm_nonneg (t j - T)) ?_
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro j
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (le_of_lt (hupper j)))]
    linarith [hlower j]
  · exact tendsto_atTop_mono (fun j ↦ Nat.le_of_lt (hq j)) tendsto_id

/-- Bernstein converts a critical amplitude lower bound into the scale-sharp
energy lower bound, in denominator-free form. -/
theorem shell_energy_lower_from_bernstein
    (critical C lambda velocityL2 : ℝ)
    (hcritical : 0 ≤ critical) (hC : 0 ≤ C) (hlambda : 0 ≤ lambda)
    (hvelocity : 0 ≤ velocityL2)
    (hbernstein : critical ≤ C * Real.sqrt lambda * velocityL2) :
    critical ^ 2 ≤ C ^ 2 * lambda * velocityL2 ^ 2 := by
  have hright : 0 ≤ C * Real.sqrt lambda * velocityL2 := by positivity
  have hsq := (sq_le_sq₀ hcritical hright).2 hbernstein
  rw [mul_pow, mul_pow, Real.sq_sqrt hlambda] at hsq
  nlinarith

/-- Adding frequency localization gives the scale-sharp vorticity lower bound.
The denominator-free inequality is equivalent to
`vorticityL2² ≥ (curlConstant²/C²) critical² lambda` when `C>0`. -/
theorem shell_vorticity_lower_from_bernstein
    (critical C curlConstant lambda velocityL2 vorticityL2 : ℝ)
    (hcritical : 0 ≤ critical) (hC : 0 ≤ C) (hcurl : 0 ≤ curlConstant)
    (hlambda : 0 ≤ lambda) (hvelocity : 0 ≤ velocityL2)
    (hvorticity : 0 ≤ vorticityL2)
    (hbernstein : critical ≤ C * Real.sqrt lambda * velocityL2)
    (hfrequency : curlConstant * lambda * velocityL2 ≤ vorticityL2) :
    curlConstant ^ 2 * critical ^ 2 * lambda ≤ C ^ 2 * vorticityL2 ^ 2 := by
  have henergy := shell_energy_lower_from_bernstein critical C lambda velocityL2
    hcritical hC hlambda hvelocity hbernstein
  have hleft : 0 ≤ curlConstant * lambda * velocityL2 := by positivity
  have hfreqSq := (sq_le_sq₀ hleft hvorticity).2 hfrequency
  have henergyScaled := mul_le_mul_of_nonneg_left henergy
    (mul_nonneg (sq_nonneg curlConstant) hlambda)
  have hfreqScaled := mul_le_mul_of_nonneg_left hfreqSq (sq_nonneg C)
  calc
    curlConstant ^ 2 * critical ^ 2 * lambda =
        (curlConstant ^ 2 * lambda) * critical ^ 2 := by ring
    _ ≤ (curlConstant ^ 2 * lambda) *
        (C ^ 2 * lambda * velocityL2 ^ 2) := henergyScaled
    _ = C ^ 2 * (curlConstant * lambda * velocityL2) ^ 2 := by ring
    _ ≤ C ^ 2 * vorticityL2 ^ 2 := hfreqScaled

/-- Bernstein plus the Fourier Gevrey weight gives NS.21.  `normalizedShell`
is `lambda⁻¹ ‖u_q‖∞`, and `shellL2` is `‖u_q‖₂`. -/
theorem gevrey_shell_bound
    (normalizedShell shellL2 C c sigma lambda gevreyStock : ℝ)
    (hC : 0 ≤ C) (hlambda : 0 ≤ lambda) (hstock : 0 ≤ gevreyStock)
    (hbernstein : normalizedShell ≤ C * Real.sqrt lambda * shellL2)
    (hweight : Real.exp (c * sigma * lambda) * shellL2 ≤ gevreyStock) :
    normalizedShell ≤
      C * Real.sqrt lambda * Real.exp (-(c * sigma * lambda)) * gevreyStock := by
  have hscaled := mul_le_mul_of_nonneg_left hweight
    (Real.exp_nonneg (-(c * sigma * lambda)))
  have hshell : shellL2 ≤ Real.exp (-(c * sigma * lambda)) * gevreyStock := by
    calc
      shellL2 = Real.exp (-(c * sigma * lambda)) *
          (Real.exp (c * sigma * lambda) * shellL2) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp (-(c * sigma * lambda)) * gevreyStock := hscaled
  calc
    normalizedShell ≤ C * Real.sqrt lambda * shellL2 := hbernstein
    _ ≤ C * Real.sqrt lambda *
        (Real.exp (-(c * sigma * lambda)) * gevreyStock) := by
      exact mul_le_mul_of_nonneg_left hshell (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = C * Real.sqrt lambda * Real.exp (-(c * sigma * lambda)) *
        gevreyStock := by ring

/-- The logarithmic analytic-radius collapse NS.22, expressed from the exact
rearranged Gevrey shell inequality. -/
theorem critical_shell_radius_bound
    (c sigma lambda C gevreyStock c0 nu : ℝ)
    (hc : 0 < c) (hlambda : 0 < lambda) (hC : 0 < C)
    (hstock : 0 < gevreyStock) (hc0 : 0 < c0) (hnu : 0 < nu)
    (hgevrey : Real.exp (c * sigma * lambda) ≤
      C * gevreyStock * Real.sqrt lambda / (c0 * nu)) :
    sigma ≤ 1 / (c * lambda) *
      (Real.log (C * gevreyStock / (c0 * nu)) + (1 / 2) * Real.log lambda) := by
  have hsqrt : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hright : 0 < C * gevreyStock * Real.sqrt lambda / (c0 * nu) := by positivity
  have hlog := Real.log_le_log (Real.exp_pos _) hgevrey
  rw [Real.log_exp] at hlog
  have hdecomp :
      Real.log (C * gevreyStock * Real.sqrt lambda / (c0 * nu)) =
        Real.log (C * gevreyStock / (c0 * nu)) + (1 / 2) * Real.log lambda := by
    rw [Real.log_div (mul_ne_zero (mul_ne_zero hC.ne' hstock.ne') hsqrt.ne')
        (mul_ne_zero hc0.ne' hnu.ne'),
      Real.log_mul (mul_ne_zero hC.ne' hstock.ne') hsqrt.ne',
      Real.log_div (mul_ne_zero hC.ne' hstock.ne') (mul_ne_zero hc0.ne' hnu.ne'),
      Real.log_sqrt hlambda.le]
    ring
  rw [hdecomp] at hlog
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ (mul_pos hc hlambda)).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hlog)

end NCG.NavierStokesCriticalShellExtraction
