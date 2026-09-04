/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFirstJumpIntegrationExact
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace transform of genuine CTMC holding times

The one-step law has transform `rate / (rate + s)`. Its uniform finite-state
bound supplies a contraction for proving exponential tails of the jump count.
Clipping nonphysical negative holding inputs makes the discount globally
bounded without changing it almost surely under the actual holding law.
-/

open MeasureTheory ProbabilityTheory Set

namespace NCG.FiniteCTMCHoldingLaplace

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCHoldingPositivity FiniteCTMCFirstJumpIntegration

noncomputable section

/-- The negative exponential of an exponential holding time is integrable. -/
theorem integrable_exp_neg_holding (rate s : ℝ) (hr : 0 < rate) (hs : 0 ≤ s) :
    Integrable (fun t => Real.exp (-(s * t))) (expMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  have hpos : ∀ᵐ t ∂expMeasure rate, t ∈ Ioi 0 := by
    apply (ae_mem_iff_measure_eq measurableSet_Ioi.nullMeasurableSet).2
    simpa using expMeasure_Ioi_zero_eq_one hr
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs ht.le))

/-- Exact Laplace transform, derived from the exponential density. -/
theorem integral_exp_neg_holding (rate s : ℝ) (hr : 0 < rate) (hs : 0 ≤ s) :
    (∫ t, Real.exp (-(s * t)) ∂expMeasure rate) = rate / (rate + s) := by
  rw [integral_expMeasure_eq_setIntegral_density rate hr]
  have heq : (fun t : ℝ => rate * Real.exp (-(rate * t)) * Real.exp (-(s * t))) =
      fun t => rate * Real.exp ((-(rate + s)) * t) := by
    funext t
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos (add_pos_of_pos_of_nonneg hr hs))]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, div_neg, neg_neg]
  ring

/-- Bounded discount on all raw holding coordinates, physical or otherwise. -/
def holdingDiscount (s t : ℝ) : ℝ := Real.exp (-(s * max t 0))

theorem measurable_holdingDiscount (s : ℝ) : Measurable (holdingDiscount s) := by
  unfold holdingDiscount
  fun_prop

theorem holdingDiscount_pos (s t : ℝ) : 0 < holdingDiscount s t := Real.exp_pos _

theorem holdingDiscount_le_one (s t : ℝ) (hs : 0 ≤ s) : holdingDiscount s t ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs (le_max_right t 0)))

theorem integrable_holdingDiscount (rate s : ℝ) (hr : 0 < rate) (hs : 0 ≤ s) :
    Integrable (holdingDiscount s) (expMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  apply (integrable_const (1 : ℝ)).mono' (measurable_holdingDiscount s).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (holdingDiscount_pos s t)]
    exact holdingDiscount_le_one s t hs

theorem integral_holdingDiscount (rate s : ℝ) (hr : 0 < rate) (hs : 0 ≤ s) :
    (∫ t, holdingDiscount s t ∂expMeasure rate) = rate / (rate + s) := by
  letI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  have hpos : ∀ᵐ t ∂expMeasure rate, t ∈ Ioi 0 := by
    apply (ae_mem_iff_measure_eq measurableSet_Ioi.nullMeasurableSet).2
    simpa using expMeasure_Ioi_zero_eq_one hr
  rw [← integral_exp_neg_holding rate s hr hs]
  apply integral_congr_ae
  filter_upwards [hpos] with t ht
  change 0 < t at ht
  simp only [holdingDiscount, max_eq_left ht.le]

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The actual holding/destination kernel integrates the bounded discount
to the exponential Laplace transform, independently of the destination. -/
theorem integral_holdingDestination_discount
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) (s : ℝ) (hs : 0 ≤ s) :
    (∫ q, holdingDiscount s q.1 ∂holdingDestinationMeasure L x) =
      escapeRate L x / (escapeRate L x + s) := by
  letI : IsProbabilityMeasure (expMeasure (escapeRate L x)) :=
    isProbabilityMeasure_expMeasure (hescape x)
  letI : IsProbabilityMeasure (destinationMeasure L x) :=
    destinationMeasure_isProbabilityMeasure L hL hescape x
  have hi := (integrable_holdingDiscount (escapeRate L x) s (hescape x) hs).comp_fst
    (destinationMeasure L x)
  unfold holdingDestinationMeasure
  rw [integral_prod _ hi]
  simp only [integral_const, probReal_univ, one_smul]
  exact integral_holdingDiscount (escapeRate L x) s (hescape x) hs

/-- Uniform upper escape rate gives a common one-step Laplace bound. -/
theorem integral_holdingDestination_discount_le
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) (s R : ℝ)
    (hs : 0 ≤ s) (hR : escapeRate L x ≤ R) :
    (∫ q, holdingDiscount s q.1 ∂holdingDestinationMeasure L x) ≤ R / (R + s) := by
  rw [integral_holdingDestination_discount L hL hescape x s hs]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (hescape x) hs)
    (add_pos_of_pos_of_nonneg (lt_of_lt_of_le (hescape x) hR) hs)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hR hs]

end

end NCG.FiniteCTMCHoldingLaplace
