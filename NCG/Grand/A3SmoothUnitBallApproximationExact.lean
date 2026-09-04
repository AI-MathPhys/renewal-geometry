/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3SmoothPeriodicUnitEnergyExact
import NCG.Grand.A3PeriodicLiftOscillationExact

/-!
# Quantitative smooth periodic approximation of the actual A3 unit ball

A normalized bump of outer radius `r` smooths the true periodic lift with
uniform error at most `18*r + 9*h`. The resulting function is smooth and
periodic, preserves the exact mesh energy bound one, and approximates every
original grid value by the same bound. This does not yet identify the sharp
continuum gradient bound for a varying mesh sequence.
-/

open MeasureTheory
open scoped Convolution Matrix.Norms.L2Operator

namespace NCG.A3SmoothUnitBallApproximation

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open A3PeriodicStepFunctionLift A3PeriodicProbabilitySmoothing A3SmoothPeriodicUnitEnergy
open A3PeriodicLiftOscillation FiniteWeightedGraphHodgeDirac

noncomputable section

theorem abs_average_kernel_sub_lift_le
    (φ : ContDiffBump (0 : Space)) (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (p : Space) :
    |average (probabilityKernel φ) d f p - lift d f p| ≤ 18 * φ.rOut + 9 * mesh d := by
  rw [average_kernel_eq_convolution]
  have h := φ.dist_normed_convolution_le (μ := (volume : Measure Space))
    (x₀ := p) (ε := 18 * φ.rOut + 9 * mesh d) (measurable_lift d f).aestronglyMeasurable
    (fun x hx => by
      have hosc := abs_lift_sub_le_spatial_mesh_bound d f hf p x
      have hdist : ‖x - p‖ < φ.rOut := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hle : |lift d f x - lift d f p| ≤ 18 * φ.rOut + 9 * mesh d := by linarith
      simpa only [Real.dist_eq, Real.norm_eq_abs] using hle)
  simpa only [Real.dist_eq, Real.norm_eq_abs] using h

theorem abs_average_kernel_sample_sub_le
    (φ : ContDiffBump (0 : Space)) (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (x : Vertex d) :
    |average (probabilityKernel φ) d f (point d x) - f x| ≤ 18 * φ.rOut + 9 * mesh d := by
  simpa only [lift_point] using abs_average_kernel_sub_lift_le φ d f hf (point d x)

theorem exists_smooth_periodic_approximation_with_unit_energy
    (φ : ContDiffBump (0 : Space)) (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) :
    ∃ g : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ q : lattice, ∀ p, g (p + q) = g p) ∧
      (∀ p, sampledEnergy g p (mesh d) ≤ 1) ∧
      ∀ x, |g (point d x) - f x| ≤ 18 * φ.rOut + 9 * mesh d := by
  obtain ⟨hsmooth, hperiod, henergy⟩ := smooth_periodic_unit_energy φ d f hf hzero
  exact ⟨average (probabilityKernel φ) d f, hsmooth, hperiod, henergy,
    fun x => abs_average_kernel_sample_sub_le φ d f hf x⟩

end

end NCG.A3SmoothUnitBallApproximation
