/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCGeneralPathLawExact
import NCG.Grand.FiniteCTMCNormalizedRewardLawExact
import NCG.Grand.RealTimeGartnerEllisExact

/-!
# Actual empirical reward laws for the general-generator path construction

The physical normalized reward law agrees with that of the positive-escape
lift. Probability, exponential integrability, and strict moment positivity
hold for every finite generator. In the nontrivial irreducible case, the
existing spectral limit yields the full LDP for this same physical law.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.FiniteCTMCGeneralRewardLaw

open DrivenProcess FiniteGeneratorPositiveEscapeLift FiniteCTMCClockProjection
open FiniteCTMCGeneralPathLaw FiniteCTMCNormalizedRewardLaw
open FiniteCTMCPathCarrierMeasurability FiniteCTMCFeynmanKacPathMoment
open MetzlerExponentialPositivity MetzlerSpectralAbscissa IrreducibleGeneratorEscape

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Pushforward of the actual physical path law by `Y_T/T`, for every generator. -/
def physicalRewardLaw (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) : Measure ℝ :=
  (physicalPathLaw L hL x₀ p).map (normalizedReward v (visibleJumpReward g) T)

/-- Exact equality with the lifted reward law; no limiting interpolation is used. -/
theorem physicalRewardLaw_eq_liftedRewardLaw
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    physicalRewardLaw L hL x₀ p v g T =
      normalizedRewardLaw (clockLift L) (clockLift_isGenerator L hL)
        (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p)
        (liftFunction v) (liftJumpReward g) T := by
  unfold physicalRewardLaw physicalPathLaw
  rw [Measure.map_map (measurable_normalizedReward v (visibleJumpReward g) T hT)
    measurable_forgetClockPath]
  rfl

theorem physicalRewardLaw_isProbabilityMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    IsProbabilityMeasure (physicalRewardLaw L hL x₀ p v g T) := by
  rw [physicalRewardLaw_eq_liftedRewardLaw L hL x₀ p v g T hT]
  exact normalizedRewardLaw_isProbabilityMeasure (clockLift L) (clockLift_isGenerator L hL)
    (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p) (initialLift_nonneg p hp)
    (by simpa only [sum_initialLift] using hsum) (liftFunction v) (liftJumpReward g) T hT

theorem integrable_exp_physicalRewardLaw
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun a : ℝ => Real.exp (T * k * a)) (physicalRewardLaw L hL x₀ p v g T) := by
  rw [physicalRewardLaw_eq_liftedRewardLaw L hL x₀ p v g T hT]
  exact integrable_exp_normalizedRewardLaw (clockLift L) (clockLift_isGenerator L hL)
    (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p)
    (liftFunction v) (liftJumpReward g) k T hT

theorem integral_exp_physicalRewardLaw_eq_pathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    (∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T) =
      physicalPathMoment L hL x₀ p v g k T (fun _ => 1) := by
  rw [physicalRewardLaw_eq_liftedRewardLaw L hL x₀ p v g T hT,
    integral_exp_normalizedRewardLaw_eq_pathMoment (hT := hT)]
  exact (physicalPathMoment_eq_liftedPathMoment L hL x₀ p v g k T (fun _ => 1) hT).symm

theorem integral_exp_physicalRewardLaw_pos
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (hT : 0 ≤ T) :
    0 < ∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T := by
  rw [physicalRewardLaw_eq_liftedRewardLaw L hL x₀ p v g T hT]
  exact integral_exp_normalizedRewardLaw_pos (clockLift L) (clockLift_isGenerator L hL)
    (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p) (initialLift_nonneg p hp)
    (by simpa only [sum_initialLift] using hsum) (liftFunction v) (liftJumpReward g) k T hT

/-- The general physical construction has the same actual spectral SCGF
limit on the nontrivial irreducible branch. -/
theorem tendsto_scaled_log_integral_exp [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto (fun T : ℝ => Real.log
      (∫ a : ℝ, Real.exp (T * k * a) ∂physicalRewardLaw L hL x₀ p v g T) / T)
      atTop (𝓝 (spectralAbscissa (tilt L v g k))) := by
  apply (IrreducibleFiniteCTMCSCGF.tendsto_scaled_log_pathMoment_spectralAbscissa
    L hL hirr x₀ p hp hsum v g k).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [integral_exp_physicalRewardLaw_eq_pathMoment L hL x₀ p v g k T hT,
    physicalPathMoment_eq_exponentialEntry_pairing L hL x₀ p hp v g k T (fun _ => 1) hT,
    IrreducibleFiniteCTMCSCGF.pathMoment_eq_tiltedSemigroup L hL hirr x₀ p hp
      v g k T (fun _ => 1) hT]

/-- Full real-time LDP for the general physical construction on the
nontrivial irreducible branch. -/
theorem hasLargeDeviationPrinciple [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) :
    RealTimeLargeDeviations.HasLargeDeviationPrinciple
      (fun T => physicalRewardLaw L hL x₀ p v g T) (FiniteCTMCSCGFConvexity.spectralRate L v g) := by
  apply RealTimeLargeDeviations.hasLargeDeviationPrinciple_of_differentiable_logMoment
    _ (fun q => spectralAbscissa (tilt L v g q))
  · exact fun T hT => physicalRewardLaw_isProbabilityMeasure L hL x₀ p hp hsum v g T hT
  · exact fun q => (IrreducibleFiniteCTMCSCGF.analyticAt_spectralAbscissa L hL hirr v g q).differentiableAt
  · exact fun T hT q => integrable_exp_physicalRewardLaw L hL x₀ p v g q T hT
  · exact fun T hT q => integral_exp_physicalRewardLaw_pos L hL x₀ p hp hsum v g q T hT
  · exact fun q => tendsto_scaled_log_integral_exp L hL hirr x₀ p hp hsum v g q

end

end NCG.FiniteCTMCGeneralRewardLaw
