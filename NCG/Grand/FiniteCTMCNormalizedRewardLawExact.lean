/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCSCGFConvexityExact
import NCG.Grand.ExponentialTiltMeasureExact

/-!
# The actual law of the normalized finite-CTMC reward

The distribution is the measurable pushforward of the genuine admissible
path law under `Y_T / T`. Probability, exponential integrability, positivity,
and both real-time and natural-time moment limits are derived from that
construction. The harmless zero-time convention is included explicitly.
-/

open MeasureTheory Filter Set Topology
open scoped BigOperators

namespace NCG.FiniteCTMCNormalizedRewardLaw

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCPathCarrierMeasurability FiniteCTMCAdditiveRewardMeasurability
open FiniteCTMCAdmissiblePathLaw FiniteCTMCInitialMixture FiniteCTMCSCGFConvexity
open IrreducibleGeneratorEscape MetzlerExponentialPositivity MetzlerSpectralAbscissa
open ExponentialTiltMeasure SCGFExponentialTiltConcentration

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The normalized physical occupation-plus-jump reward; at zero time it is zero. -/
def normalizedReward (v : S → ℝ) (g : S → S → ℝ) (T : ℝ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ := finiteHorizonAdditiveReward v g T z / T

theorem measurable_normalizedReward (v : S → ℝ) (g : S → S → ℝ)
    (T : ℝ) (hT : 0 ≤ T) : Measurable (normalizedReward v g T) :=
  (measurable_finiteHorizonAdditiveReward v g T hT).div_const T

/-- Scaling the normalized reward recovers the original exponential
integrand, including zero time where the additive reward itself vanishes. -/
theorem exp_scaled_normalizedReward_eq (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) :
    (fun z => Real.exp (T * k * normalizedReward v g T z)) =
      (fun z => Real.exp (k * finiteHorizonAdditiveReward v g T z)) := by
  funext z
  by_cases hzero : T = 0
  · subst T
    simp [finiteHorizonAdditiveReward_zero]
  · congr 1
    dsimp only [normalizedReward]
    field_simp

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- The actual pushforward probability law of the empirical reward. -/
def normalizedRewardLaw (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) : Measure ℝ :=
  (admissiblePathLaw x₀ p L hL hescape).map (normalizedReward v g T)

/-- The normalized reward law is a probability law at every nonnegative horizon. -/
theorem normalizedRewardLaw_isProbabilityMeasure
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    IsProbabilityMeasure (normalizedRewardLaw L hL hescape x₀ p v g T) := by
  letI := admissiblePathLaw_isProbabilityMeasure x₀ p hp hsum L hL hescape
  exact Measure.isProbabilityMeasure_map (measurable_normalizedReward v g T hT).aemeasurable

/-- Every exponential moment of the actual normalized reward law is integrable. -/
theorem integrable_exp_normalizedRewardLaw
    (x₀ : S) (p : S → ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun a : ℝ => Real.exp (T * k * a))
      (normalizedRewardLaw L hL hescape x₀ p v g T) := by
  unfold normalizedRewardLaw
  apply (integrable_map_measure
    ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)
    (measurable_normalizedReward v g T hT).aemeasurable).mpr
  change Integrable (fun z => Real.exp (T * k * normalizedReward v g T z)) _
  rw [exp_scaled_normalizedReward_eq]
  simpa only [feynmanKacIntegrand_one] using
    integrable_feynmanKacIntegrand_initialLaw L hL hescape x₀ p v g k T (fun _ => 1) hT

/-- Exact moment identification for the pushforward law, derived by change of variables. -/
theorem integral_exp_normalizedRewardLaw_eq_pathMoment
    (x₀ : S) (p : S → ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k T : ℝ) (hT : 0 ≤ T) :
    (∫ a : ℝ, Real.exp (T * k * a) ∂normalizedRewardLaw L hL hescape x₀ p v g T) =
      pathMoment x₀ p L hL hescape v g k T (fun _ => 1) := by
  unfold normalizedRewardLaw
  have hexp : Measurable (fun a : ℝ => Real.exp (T * k * a)) :=
    (measurable_id.const_mul (T * k)).exp
  rw [integral_map (measurable_normalizedReward v g T hT).aemeasurable
    hexp.aestronglyMeasurable]
  rw [exp_scaled_normalizedReward_eq]
  simp only [pathMoment, feynmanKacIntegrand_one]

/-- Positivity of the actual empirical-law exponential moments. -/
theorem integral_exp_normalizedRewardLaw_pos
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    0 < ∫ a : ℝ, Real.exp (T * k * a) ∂normalizedRewardLaw L hL hescape x₀ p v g T := by
  rw [integral_exp_normalizedRewardLaw_eq_pathMoment L hL hescape x₀ p v g k T hT]
  exact pathMoment_pos L hL hescape x₀ p hp hsum v g k T hT

omit hescape in
/-- The continuous-time log-moment limit for the actual empirical reward laws. -/
theorem tendsto_scaled_log_integral_exp [Nontrivial S]
    (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto (fun T : ℝ =>
      Real.log (∫ a : ℝ, Real.exp (T * k * a)
        ∂normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g T) / T)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
  apply (IrreducibleFiniteCTMCSCGF.tendsto_scaled_log_pathMoment_spectralAbscissa
    L hL hirr x₀ p hp hsum v g k).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [integral_exp_normalizedRewardLaw_eq_pathMoment L hL
    (escapeRate_pos L hL hirr) x₀ p v g k T hT]

omit hescape in
/-- The actual-law limit in the existing natural-time Gartner--Ellis interface. -/
theorem tendsto_normalizedLogMoment [Nontrivial S]
    (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto (fun n : ℕ => normalizedLogMoment
      (fun m q => exponentialMoment
        (normalizedRewardLaw L hL (escapeRate_pos L hL hirr) x₀ p v g m) m q) n k)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
  exact (tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g k).comp
    tendsto_natCast_atTop_atTop

end

end NCG.FiniteCTMCNormalizedRewardLaw
