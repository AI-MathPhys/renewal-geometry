/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LogExponentialMomentConvexityExact
import NCG.Grand.IrreducibleFiniteCTMCSCGFExact
import NCG.Grand.ExtendedLegendreRateExact

/-!
# Convexity of the genuine finite-CTMC SCGF and its good rate

Finite-time convexity follows from the integrable actual path observable.
The proved real-time stochastic limit gives convexity of the spectral
abscissa. Its extended Legendre rate is nonnegative, has a zero, has a
convex epigraph, and has compact finite sublevels. No LDP is asserted here.
-/

open MeasureTheory Filter Set Topology
open scoped BigOperators

namespace NCG.FiniteCTMCSCGFConvexity

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCInitialMixture FiniteCTMCAdmissiblePathLaw
open FiniteCTMCAdditiveRewardMeasurability IrreducibleGeneratorEscape
open MetzlerExponentialPositivity MetzlerSpectralAbscissa
open LogExponentialMomentConvexity

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The terminal-one integrand is exactly the exponential of the additive reward. -/
theorem feynmanKacIntegrand_one (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) :
    FiniteCTMCFeynmanKacPathMoment.feynmanKacIntegrand v g k T (fun _ => 1) =
      (fun z => Real.exp (k * finiteHorizonAdditiveReward v g T z)) := by
  funext z
  exact mul_one _

/-- Positivity of the actual exponential path moment, from proved
integrability and the genuine probability law. -/
theorem pathMoment_pos
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hescape : ∀ x, 0 < escapeRate L x)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    0 < pathMoment x₀ p L hL hescape v g k T (fun _ => 1) := by
  letI := admissiblePathLaw_isProbabilityMeasure x₀ p hp hsum L hL hescape
  have hi := integrable_feynmanKacIntegrand_initialLaw L hL hescape x₀ p
    v g k T (fun _ => 1) hT
  rw [feynmanKacIntegrand_one] at hi
  simpa only [pathMoment, feynmanKacIntegrand_one]
    using integral_exp_pos hi

/-- Convexity of the finite-time log of the genuine path expectation. -/
theorem convexOn_log_pathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hescape : ∀ x, 0 < escapeRate L x)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ConvexOn ℝ univ
      (fun k => Real.log (pathMoment x₀ p L hL hescape v g k T (fun _ => 1))) := by
  letI := admissiblePathLaw_isProbabilityMeasure x₀ p hp hsum L hL hescape
  have hc := convexOn_log_integral_exp (admissiblePathLaw x₀ p L hL hescape)
    (finiteHorizonAdditiveReward v g T) (fun q => by
      simpa only [feynmanKacIntegrand_one] using
        integrable_feynmanKacIntegrand_initialLaw L hL hescape x₀ p
          v g q T (fun _ => 1) hT)
  simpa only [pathMoment, feynmanKacIntegrand_one] using hc

/-- Nonnegative time normalization preserves log-moment convexity. -/
theorem convexOn_scaled_log_pathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hescape : ∀ x, 0 < escapeRate L x)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ConvexOn ℝ univ
      (fun k => Real.log (pathMoment x₀ p L hL hescape v g k T (fun _ => 1)) / T) := by
  have hc := ConvexOn.smul (inv_nonneg.mpr hT)
    (convexOn_log_pathMoment L hL hescape x₀ p hp hsum v g T hT)
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hc

/-- Convexity of the actual spectral SCGF, from genuine path expectations
and their continuous-time limit, not an assumed pressure property. -/
theorem convexOn_spectralAbscissa [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) :
    ConvexOn ℝ univ (fun q => spectralAbscissa (tilt L v g q)) := by
  let x₀ : S := Classical.choice inferInstance
  apply convexOn_of_pointwise_tendsto atTop
    (fun T k => Real.log (pathMoment x₀ (pointMass x₀) L hL
      (escapeRate_pos L hL hirr) v g k T (fun _ => 1)) / T)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact convexOn_scaled_log_pathMoment L hL (escapeRate_pos L hL hirr)
      x₀ (pointMass x₀) (pointMass_nonnegative x₀) (sum_pointMass x₀) v g T hT
  · intro q
    exact IrreducibleFiniteCTMCSCGF.tendsto_scaled_log_pathMoment_spectralAbscissa
      L hL hirr x₀ (pointMass x₀) (pointMass_nonnegative x₀) (sum_pointMass x₀) v g q

/-- The full extended-valued Legendre rate of the actual spectral SCGF. -/
def spectralRate (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (a : ℝ) : EReal :=
  ExtendedLegendreRate.rate (fun q => spectralAbscissa (tilt L v g q)) a

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The concrete spectral rate is nonnegative, including infinite costs. -/
theorem spectralRate_nonneg [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) (a : ℝ) : 0 ≤ spectralRate L v g a := by
  apply ExtendedLegendreRate.rate_nonneg _ _ a
  rw [spectralAbscissa_eq_exponent _ (tilt_isIrreducibleMetzler L hL hirr v g 0)]
  exact IrreducibleFiniteCTMCSCGF.scgf_zero L hL hirr v g

/-- The actual spectral rate attains zero at the derivative of the SCGF
at zero, so its compact-sublevel certificate is not vacuous. -/
theorem exists_spectralRate_zero [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) : ∃ a : ℝ, spectralRate L v g a = 0 := by
  let psi : ℝ → ℝ := fun q => spectralAbscissa (tilt L v g q)
  have hd := (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa
    L hL hirr v g 0).differentiableAt.hasDerivAt
  refine ⟨deriv psi 0, ?_⟩
  change ExtendedLegendreRate.rate psi (deriv psi 0) = 0
  rw [ExtendedLegendreRate.rate_at_derivative (convexOn_spectralAbscissa L hL hirr v g) hd]
  have hzero : spectralAbscissa (tilt L v g 0) = 0 := by
    rw [spectralAbscissa_eq_exponent _ (tilt_isIrreducibleMetzler L hL hirr v g 0)]
    exact IrreducibleFiniteCTMCSCGF.scgf_zero L hL hirr v g
  simp [hzero]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Compact finite sublevels of the concrete extended spectral rate. -/
theorem isCompact_spectralRate_sublevel
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (r : ℝ) :
    IsCompact {a : ℝ | spectralRate L v g a ≤ (r : EReal)} :=
  ExtendedLegendreRate.isCompact_sublevel _ r

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Convex epigraph of the concrete extended spectral rate. -/
theorem convex_spectralRate_epigraph
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) :
    Convex ℝ {p : ℝ × ℝ | spectralRate L v g p.1 ≤ (p.2 : EReal)} :=
  ExtendedLegendreRate.convex_epigraph _

end

end NCG.FiniteCTMCSCGFConvexity
