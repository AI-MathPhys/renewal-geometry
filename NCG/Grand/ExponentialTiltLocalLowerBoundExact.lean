/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialTiltWindowConcentrationExact

/-!
# Concrete local large-deviation lower bounds

This file proves the change-of-measure inequality for actual real measures and
combines it with tilted-window concentration.  At an exposed value
`a = psi'(k)`, every open window around `a` receives the sharp exponential
lower bound, with the expected `|k| delta` window error.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.ExponentialTiltLocalLowerBound

open NCG.ExponentialTiltMeasure
open NCG.ExponentialTiltLowerBound
open NCG.ExponentialTiltWindowConcentration
open NCG.SCGFExponentialTiltConcentration
open NCG.DifferentiableLegendreDual

/-- The original mass of a set, represented as a real set integral.  For a
finite measure this equals `mu.real s`. -/
def originalMass (mu : Measure ℝ) (s : Set ℝ) : ℝ :=
  ∫ _ in s, (1 : ℝ) ∂mu

/-- A pointwise exponential bound on a measurable set gives the exact
change-of-measure inequality between original and tilted mass. -/
theorem exponentialMoment_mul_tiltedMass_le_originalMass
    (mu : Measure ℝ) (n : ℕ) (k cost : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hbound : ∀ x ∈ s, k * x ≤ cost)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    Real.exp (-(n : ℝ) * cost) * exponentialMoment mu n k *
        tiltedMass mu n k s ≤ originalMass mu s := by
  let f : ℝ → ℝ := fun x => Real.exp ((n : ℝ) * k * x)
  let c : ℝ := Real.exp ((n : ℝ) * cost)
  have hcint : IntegrableOn (fun _ : ℝ => c) s mu := by
    have h := (hone.const_mul c).integrableOn (s := s)
    simpa only [mul_one] using h
  have hpoint : ∀ x ∈ s, f x ≤ c := by
    intro x hx
    apply Real.exp_le_exp.mpr
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound x hx) (Nat.cast_nonneg n)
  have hintBound :
      (∫ x in s, f x ∂mu) ≤ c * originalMass mu s := by
    calc
      (∫ x in s, f x ∂mu) ≤ ∫ _ in s, c ∂mu :=
        MeasureTheory.setIntegral_mono_on hk.integrableOn hcint hs hpoint
      _ = c * originalMass mu s := by
        unfold originalMass
        rw [← MeasureTheory.integral_const_mul]
        simp only [mul_one]
  have hcancel : exponentialMoment mu n k * tiltedMass mu n k s =
      ∫ x in s, f x ∂mu := by
    unfold tiltedMass
    rw [mul_div_cancel₀ _ hpos.ne']
  calc
    Real.exp (-(n : ℝ) * cost) * exponentialMoment mu n k *
          tiltedMass mu n k s =
        Real.exp (-(n : ℝ) * cost) * (∫ x in s, f x ∂mu) := by
      rw [mul_assoc, hcancel]
    _ ≤ Real.exp (-(n : ℝ) * cost) * (c * originalMass mu s) :=
      mul_le_mul_of_nonneg_left hintBound (Real.exp_nonneg _)
    _ = originalMass mu s := by
      dsimp only [c]
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp

/-- On the open window `(a-delta,a+delta)`, the tilt exponent is bounded by
`k*a + |k|*delta`. -/
theorem tilt_on_Ioo_le_center_add_abs_error
    (k a delta x : ℝ) (hx : x ∈ Set.Ioo (a - delta) (a + delta)) :
    k * x ≤ k * a + |k| * delta := by
  by_cases hk : 0 ≤ k
  · rw [abs_of_nonneg hk]
    have hmul := mul_le_mul_of_nonneg_left hx.2.le hk
    nlinarith
  · have hkneg : k < 0 := lt_of_not_ge hk
    rw [abs_of_neg hkneg]
    have hmul := mul_le_mul_of_nonpos_left hx.1.le hkneg.le
    nlinarith

/-- The exact concrete change-of-measure inequality on an open window. -/
theorem tiltedWindow_changeOfMeasure
    (mu : Measure ℝ) (n : ℕ) (k a delta : ℝ)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    Real.exp (-(n : ℝ) * (k * a + |k| * delta)) *
        exponentialMoment mu n k *
        tiltedMass mu n k (Set.Ioo (a - delta) (a + delta)) ≤
      originalMass mu (Set.Ioo (a - delta) (a + delta)) := by
  exact exponentialMoment_mul_tiltedMass_le_originalMass
    mu n k (k * a + |k| * delta) _ measurableSet_Ioo
    (tilt_on_Ioo_le_center_add_abs_error k a delta) hk hone hpos

/-- Concrete local Gartner--Ellis lower bound at an exposed point. -/
theorem eventually_originalMass_Ioo_lower_bound
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (k a delta epsilon : ℝ)
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) *
        (k * a + |k| * delta - psi k + epsilon)) ≤
      originalMass (mu n) (Set.Ioo (a - delta) (a + delta)) := by
  let Z : ℕ → ℝ → ℝ := fun n q => exponentialMoment (mu n) n q
  let P : ℕ → ℝ := fun n =>
    originalMass (mu n) (Set.Ioo (a - delta) (a + delta))
  let Q : ℕ → ℝ := fun n =>
    tiltedMass (mu n) n k (Set.Ioo (a - delta) (a + delta))
  have hQ : Tendsto Q atTop (𝓝 1) := by
    exact exposed_tiltedWindow_tendsto_one mu psi k a delta
      hderiv hdelta hint hpos hlim
  apply eventually_originalMass_lower_bound Z P Q psi k
    (k * a + |k| * delta) epsilon
  · exact hpos
  · exact hlim k
  · exact hQ
  · intro n
    exact tiltedWindow_changeOfMeasure (mu n) n k a delta
      (hint n k) (hone n) (hpos n k)
  · exact hepsilon

/-- Rate-function form of the concrete local lower bound.  Convex duality
identifies the exposed-point cost exactly, leaving only the finite window
error `|k| * delta` and the arbitrary asymptotic error `epsilon`. -/
theorem eventually_originalMass_Ioo_lower_bound_rateFunction
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (k a delta epsilon : ℝ)
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) *
        (NCG.rateFunction psi a + |k| * delta + epsilon)) ≤
      originalMass (mu n) (Set.Ioo (a - delta) (a + delta)) := by
  have hrate := rateFunction_at_derivative hconv hderiv
  simpa [hrate, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    eventually_originalMass_Ioo_lower_bound mu psi k a delta epsilon
      hderiv hdelta hepsilon hint hone hpos hlim

end NCG.ExponentialTiltLocalLowerBound
