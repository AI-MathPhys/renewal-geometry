/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCHomogeneousRestartLawExact

/-!
# Conditional moments under the genuine restarted CTMC law

The homogeneous restart identity transports the concrete measurable path
observable to the point-start conditional moment. This is an equality of
Bochner integrals, not an assertion that exponential moments are integrable.
-/

open MeasureTheory ProbabilityTheory

namespace NCG.FiniteCTMCRestartMoment

open DrivenProcess DrivenProcess.FinitePath
open FiniteCTMCJumpSequenceLaw FiniteCTMCPathLawDisintegration
open FiniteCTMCHomogeneousRestartLaw FiniteCTMCAdmissiblePathLaw
open FiniteCTMCFeynmanKacPathMoment

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The restarted continuation gives exactly the physical point-start moment
at its current state, with no extraneous restart-law assumption. -/
theorem integral_restart_eq_conditionalPathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x)
    (a : ℕ) (h : Finset.Iic a → ℝ × S)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ)
    (hT : 0 ≤ T) :
    (∫ z, feynmanKacIntegrand v g k T f
      (admissibleProjection (currentState a h) (resetShift a z))
      ∂continuationKernel L hL hescape a h) =
      conditionalPathMoment L hL hescape v g k T f (currentState a h) := by
  have hm := (measurable_feynmanKacIntegrand v g k T f hT).comp
    (measurable_admissibleProjection (currentState a h))
  calc
    _ = ∫ z, feynmanKacIntegrand v g k T f
        (admissibleProjection (currentState a h) z)
        ∂((continuationKernel L hL hescape a h).map (resetShift a)) :=
      (integral_map (measurable_resetShift a).aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ z, feynmanKacIntegrand v g k T f
        (admissibleProjection (currentState a h) z)
        ∂jumpSequenceLaw (pointMass (currentState a h)) L hL hescape := by
      rw [map_continuation_resetShift_eq_jumpSequenceLaw]
    _ = conditionalPathMoment L hL hescape v g k T f (currentState a h) := by
      unfold conditionalPathMoment pathMoment admissiblePathLaw
      exact (integral_map (measurable_admissibleProjection (currentState a h)).aemeasurable
        (measurable_feynmanKacIntegrand v g k T f hT).aestronglyMeasurable).symm

end

end NCG.FiniteCTMCRestartMoment
