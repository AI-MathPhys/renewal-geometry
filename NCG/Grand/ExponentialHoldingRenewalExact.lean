/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFirstJumpIntegrationExact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Density and interval form of exponential first-jump renewal equations

These lemmas preserve integrability when passing from the exponential
holding measure to Lebesgue measure. They also separate the no-jump tail
from the jump contribution, retaining the jump-at-horizon boundary.
-/

open MeasureTheory ProbabilityTheory Set

namespace NCG.ExponentialHoldingRenewal

open FiniteCTMCFirstJumpIntegration

noncomputable section

/-- Integrability under the exponential law is exactly integrability of
the density-weighted function on the nonnegative half-line. -/
theorem integrable_expMeasure_iff_density
    (rate : ℝ) (hr : 0 < rate) (f : ℝ → ℝ) :
    Integrable f (expMeasure rate) ↔
      IntegrableOn (fun t => rate * Real.exp (-(rate*t)) * f t) (Ici 0) := by
  rw [expMeasure, gammaMeasure]
  change Integrable f (volume.withDensity (fun t => ENNReal.ofReal (gammaPDFReal 1 rate t))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gammaPDFReal 1 rate).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _), smul_eq_mul]
  have heq : (fun t => gammaPDFReal 1 rate t * f t) =
      (Ici 0).indicator (fun t => rate * Real.exp (-(rate*t)) * f t) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [gammaPDFReal]
      norm_num
      simp [Set.indicator, ht]
    · simp [gammaPDFReal, ht, Set.indicator]
  rw [heq, integrable_indicator_iff measurableSet_Ici]

/-- Restricting an exponential integral to holding times up to `T` yields
the density integral over the closed physical interval. -/
theorem integral_expMeasure_Iic_eq_density_Icc
    (rate T : ℝ) (hr : 0 < rate) (f : ℝ → ℝ) :
    (∫ t in Iic T, f t ∂expMeasure rate) =
      ∫ t in Icc 0 T, rate * Real.exp (-(rate*t)) * f t := by
  rw [← integral_indicator measurableSet_Iic,
    integral_expMeasure_eq_setIntegral_density rate hr]
  have heq : (fun t => rate * Real.exp (-(rate*t)) * (Iic T).indicator f t) =
      (Iic T).indicator (fun t => rate * Real.exp (-(rate*t)) * f t) := by
    funext t
    by_cases ht : t ≤ T <;> simp [Set.indicator, ht]
  rw [heq, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rw [show Iic T ∩ Ici (0 : ℝ) = Icc 0 T by ext t; simp [and_comm]]

/-- The jump contribution is integrable on the entire finite interval if
the piecewise renewal integrand is integrable under the holding law. -/
theorem integrableOn_renewal_jump_density
    (rate T A : ℝ) (hr : 0 < rate) (B : ℝ → ℝ)
    (hi : Integrable (fun t => if T < t then A else B t) (expMeasure rate)) :
    IntegrableOn (fun t => rate * Real.exp (-(rate*t)) * B t) (Icc 0 T) := by
  have hd := (integrable_expMeasure_iff_density rate hr _).mp hi
  have hrestrict := hd.mono_set (show Icc 0 T ⊆ Ici 0 from fun _ h => h.1)
  apply hrestrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [if_neg (not_lt_of_ge ht.2)]

/-- Exact scalar renewal equation: no-jump survival plus the physical jump
integral, without assuming continuity of the unknown renewal function. -/
theorem integral_renewal_eq_survival_add_jump
    (rate T A : ℝ) (hr : 0 < rate) (hT : 0 ≤ T) (B : ℝ → ℝ)
    (hi : Integrable (fun t => if T < t then A else B t) (expMeasure rate)) :
    (∫ t, (if T < t then A else B t) ∂expMeasure rate) =
      Real.exp (-(rate*T)) * A +
        ∫ t in Icc 0 T, rate * Real.exp (-(rate*t)) * B t := by
  rw [← integral_add_compl measurableSet_Ioi hi, Set.compl_Ioi]
  have htail : (∫ t in Ioi T, (if T < t then A else B t) ∂expMeasure rate) =
      Real.exp (-(rate*T)) * A := by
    calc
      _ = ∫ _ in Ioi T, A ∂expMeasure rate := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact if_pos ht
      _ = _ := by
        rw [setIntegral_const, expMeasure_real_Ioi rate T hr hT, smul_eq_mul]
  rw [htail, integral_expMeasure_Iic_eq_density_Icc rate T hr]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [if_neg (not_lt_of_ge ht.2)]

end

end NCG.ExponentialHoldingRenewal
