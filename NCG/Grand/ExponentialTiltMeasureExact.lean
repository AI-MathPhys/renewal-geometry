/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialTiltLowerBoundExact

/-!
# Concrete exponential tilting of real probability laws

This file realizes the scalar tilted-law quantities used by the abstract
Gartner--Ellis machinery as ordinary Lebesgue integrals.  It proves the exact
normalization and the two Chernoff tail bounds directly from the exponential
moments of a real random variable.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.ExponentialTiltMeasure

/-- Exponential moment at speed `n`. -/
def exponentialMoment (mu : Measure ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp ((n : ℝ) * k * x) ∂mu

/-- Mass of a set under the exponentially tilted law, represented as a ratio
of real integrals. -/
def tiltedMass (mu : Measure ℝ) (n : ℕ) (k : ℝ) (s : Set ℝ) : ℝ :=
  (∫ x : ℝ in s, Real.exp ((n : ℝ) * k * x) ∂mu) /
    exponentialMoment mu n k

/-- The tilted mass of the whole line is one. -/
theorem tiltedMass_univ
    (mu : Measure ℝ) (n : ℕ) (k : ℝ)
    (hpos : 0 < exponentialMoment mu n k) :
    tiltedMass mu n k Set.univ = 1 := by
  unfold tiltedMass exponentialMoment
  rw [MeasureTheory.setIntegral_univ]
  apply div_self
  unfold exponentialMoment at hpos
  exact hpos.ne'

/-- Tilted masses are nonnegative. -/
theorem tiltedMass_nonnegative
    (mu : Measure ℝ) (n : ℕ) (k : ℝ) (s : Set ℝ)
    (hpos : 0 < exponentialMoment mu n k) :
    0 ≤ tiltedMass mu n k s := by
  unfold tiltedMass
  exact div_nonneg
    (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)) hpos.le

/-- Generic one-sided Chernoff estimate under exponential tilting.  The set
hypothesis says that `q * (x-b)` is nonnegative throughout the tail. -/
theorem tiltedMass_set_le_moment_ratio
    (mu : Measure ℝ) (n : ℕ) (k q b : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hset : ∀ x ∈ s, 0 ≤ q * (x - b))
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * (k + q) * x)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    tiltedMass mu n k s ≤
      Real.exp (-(n : ℝ) * q * b) *
        exponentialMoment mu n (k + q) / exponentialMoment mu n k := by
  have hpoint : ∀ x ∈ s,
      Real.exp ((n : ℝ) * k * x) ≤
        Real.exp (-(n : ℝ) * q * b) *
          Real.exp ((n : ℝ) * (k + q) * x) := by
    intro x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hqx := hset x hx
    nlinarith
  have hright : IntegrableOn
      (fun x : ℝ => Real.exp (-(n : ℝ) * q * b) *
        Real.exp ((n : ℝ) * (k + q) * x)) s mu :=
    (hkq.const_mul _).integrableOn
  have hsetIntegral :
      (∫ x : ℝ in s, Real.exp ((n : ℝ) * k * x) ∂mu) ≤
        Real.exp (-(n : ℝ) * q * b) *
          (∫ x : ℝ in s,
            Real.exp ((n : ℝ) * (k + q) * x) ∂mu) := by
    calc
      (∫ x : ℝ in s, Real.exp ((n : ℝ) * k * x) ∂mu) ≤
          ∫ x : ℝ in s, Real.exp (-(n : ℝ) * q * b) *
            Real.exp ((n : ℝ) * (k + q) * x) ∂mu :=
        MeasureTheory.setIntegral_mono_on hk.integrableOn hright hs hpoint
      _ = Real.exp (-(n : ℝ) * q * b) *
          (∫ x : ℝ in s,
            Real.exp ((n : ℝ) * (k + q) * x) ∂mu) := by
        exact MeasureTheory.integral_const_mul _ _
  have hrestrict :
      (∫ x : ℝ in s, Real.exp ((n : ℝ) * (k + q) * x) ∂mu) ≤
        exponentialMoment mu n (k + q) := by
    unfold exponentialMoment
    exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) hkq
  unfold tiltedMass
  apply (div_le_div_iff_of_pos_right hpos).2
  calc
    (∫ x : ℝ in s, Real.exp ((n : ℝ) * k * x) ∂mu) ≤
        Real.exp (-(n : ℝ) * q * b) *
          (∫ x : ℝ in s,
            Real.exp ((n : ℝ) * (k + q) * x) ∂mu) := hsetIntegral
    _ ≤ Real.exp (-(n : ℝ) * q * b) *
        exponentialMoment mu n (k + q) :=
      mul_le_mul_of_nonneg_left hrestrict (Real.exp_nonneg _)

/-- Upper-tail Chernoff estimate under the tilted law. -/
theorem tiltedMass_Ici_le
    (mu : Measure ℝ) (n : ℕ) (k q b : ℝ) (hq : 0 ≤ q)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * (k + q) * x)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    tiltedMass mu n k (Set.Ici b) ≤
      Real.exp (-(n : ℝ) * q * b) *
        exponentialMoment mu n (k + q) / exponentialMoment mu n k := by
  apply tiltedMass_set_le_moment_ratio mu n k q b (Set.Ici b)
    measurableSet_Ici _ hk hkq hpos
  intro x hx
  exact mul_nonneg hq (sub_nonneg.mpr hx)

/-- Lower-tail Chernoff estimate under the tilted law, using a negative
increment `q`. -/
theorem tiltedMass_Iic_le
    (mu : Measure ℝ) (n : ℕ) (k q b : ℝ) (hq : q ≤ 0)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * (k + q) * x)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    tiltedMass mu n k (Set.Iic b) ≤
      Real.exp (-(n : ℝ) * q * b) *
        exponentialMoment mu n (k + q) / exponentialMoment mu n k := by
  apply tiltedMass_set_le_moment_ratio mu n k q b (Set.Iic b)
    measurableSet_Iic _ hk hkq hpos
  intro x hx
  exact mul_nonneg_of_nonpos_of_nonpos hq (sub_nonpos.mpr hx)

end NCG.ExponentialTiltMeasure
