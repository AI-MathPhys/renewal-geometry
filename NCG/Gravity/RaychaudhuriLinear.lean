/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The linearized Raychaudhuri area variation
  (`lem:raychaudhuri`, GR_emergence)

At equilibrium (expansion and shear zero to first order) the
Raychaudhuri equation linearizes to `θ' = -R_{kk}` with `θ(0) = 0`
at the bifurcation surface.  The area variation is the integrated
expansion, and integration by parts produces the affine-weighted
flux:

* `linearized_expansion` — `θ(η) = -∫₀^η R_{kk}`;
* `raychaudhuri_area_variation` — the exact weighted form
  `∫₀^Λ θ = -∫₀^Λ (Λ-η)·R_{kk}(η) dη`;
* `raychaudhuri_frozen_weight` — for the locally frozen diamond
  (`R_{kk}` constant across the small diamond) this is exactly the
  boxed affine-parameter weight
  `δS_area = -(1/4G)·∫₀^Λ R_{kk}·η dη` per unit transverse area.

The geometric inputs (renewal characteristics are null generators,
transverse area obeys Raychaudhuri's equation, `S_area = A/4G`) are
the declared layers, as in the manuscript's citation-based proof.
-/

namespace NCG

open intervalIntegral

/-- Linearized Raychaudhuri: `θ' = -R` with `θ(0) = 0` integrates to
`θ(η) = -∫₀^η R`. -/
theorem linearized_expansion {R theta : ℝ → ℝ} (hR : Continuous R)
    (htheta0 : theta 0 = 0)
    (hderiv : ∀ x, HasDerivAt theta (-(R x)) x) (eta : ℝ) :
    theta eta = -∫ s in (0 : ℝ)..eta, R s := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := theta) (f' := fun x => -(R x))
    (fun x _ => hderiv x) ((hR.neg).intervalIntegrable 0 eta)
  rw [htheta0, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_neg]

/-- `lem:raychaudhuri` (exact weighted form): the integrated
expansion carries the affine weight,
`∫₀^Λ θ = -∫₀^Λ (Λ-η)·R(η) dη`. -/
theorem raychaudhuri_area_variation {R theta : ℝ → ℝ}
    (hR : Continuous R) (htheta0 : theta 0 = 0)
    (hderiv : ∀ x, HasDerivAt theta (-(R x)) x) (Lam : ℝ) :
    (∫ eta in (0 : ℝ)..Lam, theta eta)
      = -∫ eta in (0 : ℝ)..Lam, (Lam - eta) * R eta := by
  set F : ℝ → ℝ := fun eta => ∫ s in (0 : ℝ)..eta, R s with hF
  have hFderiv : ∀ x : ℝ, HasDerivAt F (R x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hR.intervalIntegrable 0 x)
      (hR.stronglyMeasurable.stronglyMeasurableAtFilter)
      hR.continuousAt
  have hthetaF : ∀ eta, theta eta = -(F eta) := fun eta =>
    linearized_expansion hR htheta0 hderiv eta
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (u' := R) (v := fun x : ℝ => x) (v' := fun _ => (1 : ℝ))
    (fun x _ => hFderiv x) (fun x _ => hasDerivAt_id x)
    (hR.intervalIntegrable 0 Lam)
    (continuous_const.intervalIntegrable 0 Lam)
  simp only [mul_one] at hparts
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  rw [hF0, zero_mul, sub_zero] at hparts
  calc (∫ eta in (0 : ℝ)..Lam, theta eta)
      = ∫ eta in (0 : ℝ)..Lam, -(F eta) :=
        intervalIntegral.integral_congr fun x _ => hthetaF x
  _ = -∫ eta in (0 : ℝ)..Lam, F eta := intervalIntegral.integral_neg
  _ = -(F Lam * Lam - ∫ x in (0 : ℝ)..Lam, R x * x) := by
        rw [hparts]
  _ = -∫ eta in (0 : ℝ)..Lam, (Lam - eta) * R eta := by
        have hsplit : (∫ eta in (0 : ℝ)..Lam, (Lam - eta) * R eta)
            = Lam * (∫ eta in (0 : ℝ)..Lam, R eta)
              - ∫ eta in (0 : ℝ)..Lam, eta * R eta := by
          rw [show (fun eta => (Lam - eta) * R eta)
            = fun eta => Lam * R eta - eta * R eta from by
              funext eta
              ring]
          have hi1 : IntervalIntegrable (fun eta : ℝ => Lam * R eta)
              MeasureTheory.volume 0 Lam :=
            (hR.intervalIntegrable 0 Lam).const_mul Lam
          have hi2 : IntervalIntegrable (fun eta : ℝ => eta * R eta)
              MeasureTheory.volume 0 Lam :=
            Continuous.intervalIntegrable
              (by exact continuous_id.mul hR) 0 Lam
          rw [intervalIntegral.integral_sub hi1 hi2,
            intervalIntegral.integral_const_mul]
        have hcomm : (∫ x in (0 : ℝ)..Lam, R x * x)
            = ∫ eta in (0 : ℝ)..Lam, eta * R eta :=
          intervalIntegral.integral_congr fun x _ => by ring
        rw [hsplit, ← hcomm]
        simp only [hF]
        ring

/-- `lem:raychaudhuri` (frozen diamond): for locally constant
`R_{kk}` the weighted form is exactly the boxed affine-parameter
display `∫₀^Λ θ = -∫₀^Λ R_{kk}·η dη`. -/
theorem raychaudhuri_frozen_weight {R0 Lam : ℝ} {theta : ℝ → ℝ}
    (htheta0 : theta 0 = 0)
    (hderiv : ∀ x, HasDerivAt theta (-R0) x) :
    (∫ eta in (0 : ℝ)..Lam, theta eta)
      = -∫ eta in (0 : ℝ)..Lam, R0 * eta := by
  have h := raychaudhuri_area_variation (R := fun _ => R0)
    continuous_const htheta0 hderiv Lam
  rw [h]
  congr 1
  rw [show (fun eta => (Lam - eta) * R0)
    = fun eta => Lam * R0 - eta * R0 from by
      funext eta
      ring]
  have hi1 : IntervalIntegrable (fun _ : ℝ => Lam * R0)
      MeasureTheory.volume 0 Lam :=
    continuous_const.intervalIntegrable 0 Lam
  have hi2 : IntervalIntegrable (fun eta : ℝ => eta * R0)
      MeasureTheory.volume 0 Lam :=
    Continuous.intervalIntegrable
      (by exact continuous_id.mul continuous_const) 0 Lam
  rw [intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  have hid : (∫ x in (0 : ℝ)..Lam, x) = Lam ^ 2 / 2 := by
    have h1 := integral_pow (a := (0 : ℝ)) (b := Lam) (n := 1)
    simp only [pow_one] at h1
    rw [h1]
    norm_num
  rw [hid]
  simp only [smul_eq_mul, sub_zero]
  ring

end NCG
