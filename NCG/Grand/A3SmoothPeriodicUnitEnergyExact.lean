/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicProbabilitySmoothingExact

/-!
# Smooth periodic representatives retaining the exact mesh energy bound

A normalized smooth compactly supported bump defines a genuine probability
measure. Convolving the actual step-function lift with this kernel gives a
smooth periodic function with the same twelve-root energy bound one. No
regularity or integrability of the discrete observable is assumed.
-/

open MeasureTheory Filter
open scoped Convolution ENNReal Matrix.Norms.L2Operator

namespace NCG.A3SmoothPeriodicUnitEnergy

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open A3PeriodicStepFunctionLift A3PeriodicProbabilitySmoothing FiniteWeightedGraphHodgeDirac

noncomputable section

def probabilityKernel (φ : ContDiffBump (0 : Space)) : Measure Space :=
  volume.withDensity (fun x => ENNReal.ofReal (φ.normed volume x))

instance probabilityKernel_isProbability (φ : ContDiffBump (0 : Space)) :
    IsProbabilityMeasure (probabilityKernel φ) where
  measure_univ := by
    rw [probabilityKernel, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (Eventually.of_forall (fun x => φ.nonneg_normed x)), φ.integral_normed]
    simp

theorem average_kernel_eq_convolution (φ : ContDiffBump (0 : Space))
    (d : ℕ) (f : Vertex d → ℝ) :
    average (probabilityKernel φ) d f = φ.normed volume ⋆ lift d f := by
  funext p
  unfold A3PeriodicProbabilitySmoothing.average probabilityKernel
  rw [integral_withDensity_eq_integral_toReal_smul
    φ.continuous_normed.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _), convolution_lsmul]

theorem locallyIntegrable_lift (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) :
    LocallyIntegrable (lift d f) volume := by
  apply (locallyIntegrable_const (μ := (volume : Measure Space)) (108 : ℝ)).mono
    (measurable_lift d f).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 108)] using
    abs_lift_le_uniform_bound d f hf hzero p

theorem contDiff_average_kernel (φ : ContDiffBump (0 : Space))
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (average (probabilityKernel φ) d f) := by
  rw [average_kernel_eq_convolution]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (locallyIntegrable_lift d f hf hzero)

/-- Actual smooth periodic averaging with no loss in the mesh energy constraint. -/
theorem smooth_periodic_unit_energy (φ : ContDiffBump (0 : Space))
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (average (probabilityKernel φ) d f) ∧
    (∀ q : lattice, ∀ p, average (probabilityKernel φ) d f (p + q) =
      average (probabilityKernel φ) d f p) ∧
    ∀ p, sampledEnergy (average (probabilityKernel φ) d f) p (mesh d) ≤ 1 := by
  exact ⟨contDiff_average_kernel φ d f hf hzero,
    fun q p => average_periodic _ d f q p,
    fun p => sampledEnergy_average_le_one _ d f hf hzero p⟩

end

end NCG.A3SmoothPeriodicUnitEnergy
