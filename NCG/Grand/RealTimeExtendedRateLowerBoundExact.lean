/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealTimeTiltedLowerBoundExact
import NCG.Grand.LegendreDerivativeApproximationExact

/-!
# Real-time open-set lower bounds at every finite-rate point

Quadratic regularization extends the derivative-slope bound to all finite
Legendre-rate points, including derivative-range endpoints. The only
analytic inputs are the actual moment limits and differentiability of
the limiting pressure; no exposed-point density assumption is supplied.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.RealTimeExtendedRateLowerBound

open RealTimeExponentialUpperBound ExponentialTiltLocalLowerBound

noncomputable section

/-- Complete open-set lower estimate at any point with a finite rate bound. -/
theorem eventually_mass_open_ge_of_rate_le
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (G : Set ℝ) (a r epsilon : ℝ)
    (hd : Differentiable ℝ psi) (hG : IsOpen G) (ha : a ∈ G)
    (hr : ExtendedLegendreRate.rate psi a ≤ (r : EReal)) (hepsilon : 0 < epsilon)
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u))) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-t * (r + epsilon)) ≤ originalMass (mu t) G := by
  obtain ⟨k, hk, hcost⟩ :=
    LegendreDerivativeApproximation.exists_derivative_mem_open_with_cost_le psi hd G a r hG ha hr
  have hlocal := RealTimeTiltedLowerBound.eventually_mass_open_lower_bound_at_derivative
    mu psi G k (deriv psi k) epsilon hG hk (hd k).hasDerivAt hepsilon hint hone hpos hlim
  filter_upwards [hlocal, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  apply le_trans _ ht
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (show k * deriv psi k - psi k + epsilon ≤ r + epsilon by linarith)
    (neg_nonpos.mpr ht0))

/-- If any point in an open set has rate strictly below `A`, its probability
is eventually at least `exp(-t*A)` over all real horizons. -/
theorem eventually_mass_open_ge_of_rate_lt
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (G : Set ℝ) (a A : ℝ)
    (hd : Differentiable ℝ psi) (hG : IsOpen G) (ha : a ∈ G)
    (hA : ExtendedLegendreRate.rate psi a < (A : EReal))
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u))) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-t * A) ≤ originalMass (mu t) G := by
  obtain ⟨r, hr, hrA⟩ := EReal.exists_between_coe_real hA
  have hlt : r < A := EReal.coe_lt_coe_iff.mp hrA
  have hbound := eventually_mass_open_ge_of_rate_le mu psi G a r (A - r) hd hG ha hr.le
    (sub_pos.mpr hlt) hint hone hpos hlim
  simpa only [add_sub_cancel] using hbound

end

end NCG.RealTimeExtendedRateLowerBound
