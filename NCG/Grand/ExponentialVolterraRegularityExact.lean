/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Nonnegative-time regularity of exponential Volterra equations

Integrable convolution sources first give a variation-of-constants formula
and continuity. Once the source is continuous, the same identity gives the
backward derivative, including the right derivative at the origin.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace NCG.ExponentialVolterraRegularity

noncomputable section

theorem exp_sub_mul_factor (a T u : ℝ) :
    Real.exp (a*(T-u)) = Real.exp (a*T) * Real.exp (-a*u) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Reflection converts the exponential convolution to a fixed primitive. -/
theorem integral_exp_convolution_eq (a T : ℝ) (J : ℝ → ℝ) (hT : 0 ≤ T) :
    (∫ t in Icc 0 T, Real.exp (a*t) * J (T-t)) =
      Real.exp (a*T) * ∫ u in 0..T, Real.exp (-a*u) * J u := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have hreflect := intervalIntegral.integral_comp_sub_left
    (fun u => Real.exp (a*(T-u)) * J u) T (a := 0) (b := T)
  simp only [sub_sub_cancel, sub_self, sub_zero] at hreflect
  rw [hreflect]
  simp_rw [exp_sub_mul_factor, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

/-- Reflection also transports integrability of the actual convolution source. -/
theorem intervalIntegrable_weightedSource
    (a T : ℝ) (J : ℝ → ℝ) (hT : 0 ≤ T)
    (hi : IntegrableOn (fun t => Real.exp (a*t) * J (T-t)) (Icc 0 T)) :
    IntervalIntegrable (fun u => Real.exp (-a*u) * J u) volume 0 T := by
  have hii := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hi
  have hr := (hii.comp_sub_left T).symm
  simp only [sub_zero, sub_self, sub_sub_cancel] at hr
  have hm := hr.const_mul (Real.exp (-(a*T)))
  have heq : (fun u => Real.exp (-(a*T)) * (Real.exp (a*(T-u)) * J u)) =
      fun u => Real.exp (-a*u) * J u := by
    funext u
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [heq] at hm

/-- Primitives of functions integrable on every positive-time interval are
continuous on the entire physical half-line. -/
theorem continuousOn_primitive_nonnegative (J : ℝ → ℝ)
    (hi : ∀ T, 0 ≤ T → IntervalIntegrable J volume 0 T) :
    ContinuousOn (fun t => ∫ u in 0..t, J u) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hb : 0 ≤ t+1 := by linarith
  have hc : ContinuousWithinAt (fun t => ∫ u in 0..t, J u) (Icc 0 (t+1)) t := by
    apply intervalIntegral.continuousWithinAt_primitive (measure_singleton t)
    simpa only [min_self, max_eq_right hb] using hi (t+1) hb
  apply hc.mono_of_mem_nhdsWithin
  have hnear : Iic (t+1) ∈ 𝓝[Ici (0 : ℝ)] t :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : t < t+1))
  simpa only [Ici_inter_Iic] using inter_mem self_mem_nhdsWithin hnear

/-- A continuous half-line source has the expected primitive derivative,
without any requirement at negative times. -/
theorem hasDerivWithinAt_primitive_nonnegative (J : ℝ → ℝ)
    (hi : ∀ T, 0 ≤ T → IntervalIntegrable J volume 0 T)
    (hc : ContinuousOn J (Ici 0)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun T => ∫ u in 0..T, J u) (J t) (Ici 0) t := by
  letI : Fact (t ∈ Icc (0 : ℝ) (t+1)) := ⟨⟨ht, by linarith⟩⟩
  have hcc : ContinuousOn J (Icc 0 (t+1)) := hc.mono fun _ h => h.1
  have hd : HasDerivWithinAt (fun T => ∫ u in 0..T, J u) (J t) (Icc 0 (t+1)) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (hi t ht)
      (hcc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hcc t ⟨ht, by linarith⟩)
  apply hd.mono_of_mem_nhdsWithin
  have hnear : Iic (t+1) ∈ 𝓝[Ici (0 : ℝ)] t :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : t < t+1))
  simpa only [Ici_inter_Iic] using inter_mem self_mem_nhdsWithin hnear

/-- Variation of constants, derived directly from the Volterra equation. -/
theorem eq_variationOfConstants_of_volterra
    (a f : ℝ) (F J : ℝ → ℝ)
    (heq : ∀ T, 0 ≤ T → F T = Real.exp (a*T) * f +
      ∫ t in Icc 0 T, Real.exp (a*t) * J (T-t)) (T : ℝ) (hT : 0 ≤ T) :
    F T = Real.exp (a*T) * (f + ∫ u in 0..T, Real.exp (-a*u) * J u) := by
  rw [heq T hT, integral_exp_convolution_eq a T J hT, mul_add]

/-- Volterra solutions are continuous before any continuity of the source
is assumed, provided the convolution is integrable on each finite interval. -/
theorem continuousOn_of_volterra
    (a f : ℝ) (F J : ℝ → ℝ)
    (hi : ∀ T, 0 ≤ T → IntegrableOn (fun t => Real.exp (a*t) * J (T-t)) (Icc 0 T))
    (heq : ∀ T, 0 ≤ T → F T = Real.exp (a*T) * f +
      ∫ t in Icc 0 T, Real.exp (a*t) * J (T-t)) :
    ContinuousOn F (Ici 0) := by
  have hprim := continuousOn_primitive_nonnegative (fun u => Real.exp (-a*u) * J u)
    (fun T hT => intervalIntegrable_weightedSource a T J hT (hi T hT))
  have hE : ContinuousOn (fun T : ℝ => Real.exp (a*T)) (Ici 0) := by fun_prop
  apply (hE.mul (continuousOn_const.add hprim)).congr
  intro T hT
  exact eq_variationOfConstants_of_volterra a f F J heq T hT

/-- Differentiating a genuine Volterra solution on nonnegative time yields
its backward equation once the source is continuous. -/
theorem hasDerivWithinAt_of_volterra
    (a f : ℝ) (F J : ℝ → ℝ)
    (hi : ∀ T, 0 ≤ T → IntegrableOn (fun t => Real.exp (a*t) * J (T-t)) (Icc 0 T))
    (heq : ∀ T, 0 ≤ T → F T = Real.exp (a*T) * f +
      ∫ t in Icc 0 T, Real.exp (a*t) * J (T-t))
    (hc : ContinuousOn J (Ici 0)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt F (a * F t + J t) (Ici 0) t := by
  have hweighted : ContinuousOn (fun u => Real.exp (-a*u) * J u) (Ici 0) :=
    (by fun_prop : ContinuousOn (fun u : ℝ => Real.exp (-a*u)) (Ici 0)).mul hc
  have hprim := hasDerivWithinAt_primitive_nonnegative (fun u => Real.exp (-a*u) * J u)
    (fun T hT => intervalIntegrable_weightedSource a T J hT (hi T hT)) hweighted t ht
  have hE : HasDerivWithinAt (fun u : ℝ => Real.exp (a*u)) (Real.exp (a*t)*a) (Ici 0) t := by
    simpa only [id_eq, mul_one] using! (((hasDerivAt_id t).const_mul a).exp).hasDerivWithinAt
  have hd := hE.mul (hprim.const_add f)
  have hcancel : Real.exp (a*t) * Real.exp (-a*t) = 1 := by
    rw [← Real.exp_add, show a*t + -a*t = 0 by ring, Real.exp_zero]
  have hderiv : Real.exp (a*t)*a * (f + ∫ u in 0..t, Real.exp (-a*u) * J u) +
      Real.exp (a*t) * (Real.exp (-a*t) * J t) = a * F t + J t := by
    rw [eq_variationOfConstants_of_volterra a f F J heq t ht]
    have hcancelJ := congrArg (fun r => r * J t) hcancel
    nlinarith
  exact (hd.congr_deriv hderiv).congr
    (fun u hu => eq_variationOfConstants_of_volterra a f F J heq u hu)
    (eq_variationOfConstants_of_volterra a f F J heq t ht)

end

end NCG.ExponentialVolterraRegularity
