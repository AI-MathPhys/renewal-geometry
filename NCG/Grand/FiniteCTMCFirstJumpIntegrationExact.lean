/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCAdmissiblePathLawExact
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact integration over the first jump of a finite CTMC

This file supplies the measure-theoretic identities used when conditioning
the additive functional on the first holding time and destination.  The
finite destination integral becomes a weighted sum, the exponential law is
replaced by its Lebesgue density, and its survival probability is evaluated
at an arbitrary nonnegative horizon.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal BigOperators

noncomputable section

namespace NCG.FiniteCTMCFirstJumpIntegration

open NCG.DrivenProcess.FinitePath
open NCG.DrivenProcess
open NCG.FiniteCTMCJumpSequenceLaw
open NCG.QuantumCylinderInverseLimit

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.haveILetI false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- A real-valued integral against a finite discrete law is its weighted
finite sum. -/
theorem integral_discrete
    (v : S → ℝ) (hv : ∀ y, 0 ≤ v y) (f : S → ℝ) :
    ∫ y, f y ∂(discrete v) = ∑ y, v y * f y := by
  unfold discrete
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (hv y), smul_eq_mul]
  · intro y hy
    exact (Integrable.of_finite (μ := Measure.dirac y)).smul_measure
      ENNReal.ofReal_ne_top

/-- Fubini plus the preceding atomic formula gives the exact conditional
first-jump integral. -/
theorem integral_holdingDestinationMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S)
    (F : ℝ × S → ℝ)
    (hF : Integrable F (holdingDestinationMeasure L x)) :
    ∫ z, F z ∂(holdingDestinationMeasure L x) =
      ∫ t, ∑ y, destinationProbability L x y * F (t, y)
        ∂(ProbabilityTheory.expMeasure (escapeRate L x)) := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (escapeRate L x)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (hescape x)
  letI : IsProbabilityMeasure (destinationMeasure L x) :=
    destinationMeasure_isProbabilityMeasure L hL hescape x
  unfold holdingDestinationMeasure
  rw [integral_prod F hF]
  congr 1
  funext t
  exact integral_discrete (destinationProbability L x)
    (destinationProbability_nonnegative L hL hescape x) (fun y => F (t, y))

/-- The exponential distribution has its defining real density on the
nonnegative half-line. -/
theorem integral_expMeasure_eq_setIntegral_density
    (rate : ℝ) (hRate : 0 < rate) (f : ℝ → ℝ) :
    ∫ t, f t ∂(ProbabilityTheory.expMeasure rate) =
      ∫ t in Set.Ici 0, rate * Real.exp (-(rate * t)) * f t := by
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  change (∫ t : ℝ, f t
      ∂volume.withDensity (fun t => ENNReal.ofReal
        (ProbabilityTheory.gammaPDFReal 1 rate t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (ProbabilityTheory.measurable_gammaPDFReal 1 rate).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (ProbabilityTheory.gammaPDFReal_nonneg zero_lt_one hRate _), smul_eq_mul]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 ≤ t
  · rw [ProbabilityTheory.gammaPDFReal]
    norm_num
    simp [Set.indicator, ht]
  · simp [ProbabilityTheory.gammaPDFReal, ht, Set.indicator]

/-- Exact exponential survival probability at an arbitrary nonnegative
horizon. -/
theorem expMeasure_real_Ioi
    (rate T : ℝ) (hRate : 0 < rate) (hT : 0 ≤ T) :
    (ProbabilityTheory.expMeasure rate).real (Set.Ioi T) =
      Real.exp (-(rate * T)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hRate
  have hic : (ProbabilityTheory.expMeasure rate).real (Set.Iic T) =
      1 - Real.exp (-(rate * T)) := by
    rw [← ProbabilityTheory.cdf_eq_real,
      ProbabilityTheory.cdf_expMeasure_eq hRate]
    simp [hT]
  rw [← compl_Iic, measureReal_compl measurableSet_Iic,
    probReal_univ, hic]
  ring

/-- The contribution of paths whose first holding time exceeds the horizon
is the familiar killed diagonal exponential. -/
theorem integral_noJumpTerm
    (rate k vx T fx : ℝ) (hRate : 0 < rate) (hT : 0 ≤ T) :
    ∫ _t in Set.Ioi T, Real.exp (k * T * vx) * fx
        ∂(ProbabilityTheory.expMeasure rate) =
      Real.exp ((-rate + k * vx) * T) * fx := by
  rw [setIntegral_const, expMeasure_real_Ioi rate T hRate hT,
    smul_eq_mul, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end NCG.FiniteCTMCFirstJumpIntegration
