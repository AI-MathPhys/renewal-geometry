/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3SmoothPeriodicUnitEnergyExact
import NCG.Grand.CompactKernelConvolutionDerivativeBoundExact
import NCG.Grand.LipschitzDerivativeFiniteDifferenceExact
import NCG.Grand.A3DerivativeEnergyComparisonExact

/-!
# Mesh-uniform sharp derivative control of the smoothed A3 unit ball

Fixing the smooth kernel gives one derivative Lipschitz bound for all scalar
periods and all anchored discrete unit-ball observables. The mesh energy bound
then implies eventual derivative norm at most 1+epsilon, uniformly over the
entire discrete unit ball and all Euclidean base points.
-/

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

namespace NCG.A3SmoothedDerivativeControl

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicGraphSampling
open A3PeriodicStepFunctionLift A3PeriodicProbabilitySmoothing A3SmoothPeriodicUnitEnergy
open FiniteWeightedGraphHodgeDirac CompactKernelConvolutionDerivativeBound
open LipschitzDerivativeFiniteDifference A3DerivativeEnergyComparison

noncomputable section

def kernelDerivativeBound (φ : ContDiffBump (0 : Space)) : ℝ :=
  derivativeBound volume (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume) 108

theorem kernelDerivativeBound_nonneg (φ : ContDiffBump (0 : Space)) :
    0 ≤ kernelDerivativeBound φ :=
  derivativeBound_nonneg _ _ _ _ (by norm_num)

theorem norm_fderiv_average_sub_le
    (φ : ContDiffBump (0 : Space)) (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) (p q : Space) :
    ‖fderiv ℝ (average (probabilityKernel φ) d f) q -
        fderiv ℝ (average (probabilityKernel φ) d f) p‖ ≤ kernelDerivativeBound φ * ‖q - p‖ := by
  rw [average_kernel_eq_convolution]
  exact norm_fderiv_convolution_sub_le volume (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.normed volume) φ.hasCompactSupport_normed φ.contDiff_normed (lift d f)
    (locallyIntegrable_lift d f hf hzero) 108
    (fun x => by simpa only [Real.norm_eq_abs] using abs_lift_le_uniform_bound d f hf hzero x) p q

theorem eventually_norm_fderiv_average_le
    (φ : ContDiffBump (0 : Space)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f : Vertex (n + 1) → ℝ,
      graphLipschitz (mass (n + 1)) (conductance (n + 1)) f ≤ 1 → f 0 = 0 →
      ∀ p, ‖fderiv ℝ (average (probabilityKernel φ) (n + 1) f) p‖ ≤ 1 + ε := by
  obtain ⟨δ, hδ, hdiff⟩ := uniform_bounded_direction_difference (E := Space)
    (kernelDerivativeBound φ) (kernelDerivativeBound_nonneg φ) 2 (by norm_num)
    (ε / 3) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => mesh (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mesh, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
  intro f hf hzero p
  let g := average (probabilityKernel φ) (n + 1) f
  have hg : ∀ x, HasFDerivAt g (fderiv ℝ g x) x := fun x =>
    ((contDiff_average_kernel φ (n + 1) f hf hzero).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hchannel (r : Fin 12) :
      |rootDifference g p (mesh (n + 1)) r - fderiv ℝ g p (root r)| ≤ ε / 3 := by
    exact hdiff g (fderiv ℝ g) hg
      (fun x y => norm_fderiv_average_sub_le φ (n + 1) f hf hzero x y)
      (mesh (n + 1)) (mesh_pos _) hn p (root r) (root_norm_le_two r)
  have hnorm := norm_derivative_le_of_energy_and_channel_error g p (mesh (n + 1))
    (fderiv ℝ g p) (ε / 3) (by positivity)
    (sampledEnergy_average_le_one _ (n + 1) f hf hzero p) hchannel
  change ‖fderiv ℝ g p‖ ≤ 1 + ε
  linarith

end

end NCG.A3SmoothedDerivativeControl
