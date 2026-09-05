/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicStepFunctionLiftExact
import NCG.Grand.A3ProbabilityAverageEnergyExact

/-!
# Periodic probability smoothing with the exact A3 energy bound

The actual anchored discrete unit ball has globally bounded measurable
periodic lifts. Their averages against any probability measure exist,
remain periodic, and satisfy the full twelve-root energy constraint with
constant one. Smoothness requires an appropriate smooth averaging density
and is not asserted for arbitrary probability measures.
-/

open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.A3PeriodicProbabilitySmoothing

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open A3DiscreteUnitBallEquicontinuity A3DiscreteLipschitzExtension
open A3ConnesDistanceUniformBounds A3PeriodicStepFunctionLift
open A3ProbabilityAverageEnergy FiniteWeightedGraphHodgeDirac

noncomputable section

def average (μ : Measure Space) (d : ℕ) (f : Vertex d → ℝ) (p : Space) : ℝ :=
  ∫ z, lift d f (p - z) ∂μ

theorem abs_lift_le_uniform_bound
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) (p : Space) :
    |lift d f p| ≤ 108 := by
  have h := abs_difference_le_eighteen_norm d f hf 0 (index d p)
  rw [hzero, sub_zero, point_zero, sub_zero] at h
  have hp := norm_point_le_six d (index d p)
  change |f (index d p)| ≤ 108
  linarith

theorem integrable_lift_translate
    (μ : Measure Space) [IsFiniteMeasure μ] (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) (p : Space) :
    Integrable (fun z => lift d f (p - z)) μ := by
  have hm : Measurable (fun z : Space => lift d f (p - z)) :=
    (measurable_lift d f).comp (measurable_const.sub measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable 108
  exact Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using abs_lift_le_uniform_bound d f hf hzero (p - z))

theorem average_periodic (μ : Measure Space) (d : ℕ) (f : Vertex d → ℝ)
    (q : lattice) (p : Space) : average μ d f (p + q) = average μ d f p := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change lift d f (p + q.val - z) = lift d f (p - z)
  rw [show p + q.val - z = (p - z) + q.val by abel, lift_periodic]

theorem sampledEnergy_translate (f : Space → ℝ) (p z : Space) (h : ℝ) :
    sampledEnergy (fun x => f (x - z)) p h = sampledEnergy f (p - z) h := by
  unfold sampledEnergy rootDifference
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  dsimp only
  rw [show p + h • root r - z = (p - z) + h • root r by abel]

/-- Exact sharp energy bound for probability averages of the actual discrete lift. -/
theorem sampledEnergy_average_le_one
    (μ : Measure Space) [IsProbabilityMeasure μ] (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) (p : Space) :
    sampledEnergy (average μ d f) p (mesh d) ≤ 1 := by
  apply sampledEnergy_probability_average_le_one μ (fun z x => lift d f (x - z))
    (fun x => integrable_lift_translate μ d f hf hzero x)
  apply Eventually.of_forall
  intro z
  rw [sampledEnergy_translate]
  exact sampledEnergy_lift_le_one d f hf (p - z)

theorem abs_average_le_uniform_bound
    (μ : Measure Space) [IsProbabilityMeasure μ] (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) (p : Space) :
    |average μ d f p| ≤ 108 := by
  have hbound : ∀ᵐ z ∂μ, ‖lift d f (p - z)‖ ≤ 108 := Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using abs_lift_le_uniform_bound d f hf hzero (p - z))
  simpa [average, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const hbound

end

end NCG.A3PeriodicProbabilitySmoothing
