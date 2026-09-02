/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IndependentExponentialCompletionTime

/-!
# Exact continuous renewal completion time

This file closes the probability-space realization in
`thm:renewal-continuous-completion`.  For every positive opportunity rate
`lambda`, the canonical product of exponential measures carries two
independent holding times with rates `4 * lambda / 5` and
`2 * lambda / 3`.  Their sum is the completion time.  The certificate
records its law, Laplace transform, mean, reciprocal physical intensity, and
the infinitesimal survival-rate characterization of both stages.
-/

open MeasureTheory ProbabilityTheory Real

namespace NCG
namespace ContinuousRenewalCompletion

noncomputable section

/-- The canonical two-stage probability space is a genuine probability
measure, without a supplied freshness or independence hypothesis. -/
theorem canonicalStageMeasure_isProbability
    (lambda : ℝ) (hLambda : 0 < lambda) :
    IsProbabilityMeasure
      (independentExponentialStageMeasure
        (4 * lambda / 5) (2 * lambda / 3)) :=
  isProbabilityMeasure_independentExponentialStageMeasure
    (by positivity) (by positivity)

/-- A single exact certificate for every displayed clause of the continuous
completion-time theorem. -/
structure Certificate (lambda : ℝ) where
  independentStages :
    Prod.fst ⟂ᵢ[independentExponentialStageMeasure
      (4 * lambda / 5) (2 * lambda / 3)] Prod.snd
  firstStageLaw :
    Measure.map Prod.fst
        (independentExponentialStageMeasure
          (4 * lambda / 5) (2 * lambda / 3)) =
      expMeasure (4 * lambda / 5)
  secondStageLaw :
    Measure.map Prod.snd
        (independentExponentialStageMeasure
          (4 * lambda / 5) (2 * lambda / 3)) =
      expMeasure (2 * lambda / 3)
  completionLaw :
    Measure.map exponentialCompletionTime
        (independentExponentialStageMeasure
          (4 * lambda / 5) (2 * lambda / 3)) =
      independentExponentialCompletionLaw
        (4 * lambda / 5) (2 * lambda / 3)
  laplaceTransform :
    ∀ s : ℝ, 0 ≤ s →
      ∫ omega : ℝ × ℝ,
          Real.exp (-(s * exponentialCompletionTime omega))
          ∂independentExponentialStageMeasure
            (4 * lambda / 5) (2 * lambda / 3) =
        8 * lambda ^ 2 /
          ((4 * lambda + 5 * s) * (2 * lambda + 3 * s))
  meanCompletionTime :
    (∫ omega : ℝ × ℝ, exponentialCompletionTime omega
        ∂independentExponentialStageMeasure
          (4 * lambda / 5) (2 * lambda / 3)) =
      11 / (4 * lambda)
  physicalEventIntensity :
    (∫ omega : ℝ × ℝ, exponentialCompletionTime omega
        ∂independentExponentialStageMeasure
          (4 * lambda / 5) (2 * lambda / 3))⁻¹ =
      4 * lambda / 11
  holdingRateRecovery :
    HasDerivWithinAt
        (fun t : ℝ =>
          (expMeasure (4 * lambda / 5)).real (Set.Ioi t))
        (-(4 * lambda / 5)) (Set.Ici 0) 0 ∧
      HasDerivWithinAt
        (fun t : ℝ =>
          (expMeasure (2 * lambda / 3)).real (Set.Ioi t))
        (-(2 * lambda / 3)) (Set.Ici 0) 0

/-- **Continuous completion time and physical event intensity.**

Starting just after a completion, the canonical renewal construction gives
two independent exponential stages, their exact convolution law, the
substituted rational Laplace transform, mean `11/(4 lambda)`, and physical
event intensity `4 lambda/11`. -/
theorem continuous_completion_time_and_physical_event_intensity
    (lambda : ℝ) (hLambda : 0 < lambda) :
    Nonempty (Certificate lambda) := by
  let hRealization :=
    renewalCompletionTime_independent_exponential_realization lambda hLambda
  let hMoments :=
    renewalCompletionTime_mean_and_intensity lambda hLambda
  refine ⟨{
    independentStages := hRealization.1
    firstStageLaw := hRealization.2.1
    secondStageLaw := hRealization.2.2.1
    completionLaw := hRealization.2.2.2.symm
    laplaceTransform := fun s hs =>
      renewalCompletionTime_laplace lambda s hLambda hs
    meanCompletionTime := hMoments.1
    physicalEventIntensity := hMoments.2
    holdingRateRecovery :=
      renewal_exponentialStage_survival_derivatives lambda hLambda
  }⟩

end
end ContinuousRenewalCompletion
end NCG
