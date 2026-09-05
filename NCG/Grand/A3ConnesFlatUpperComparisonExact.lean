/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3SmoothedDerivativeControlExact
import NCG.Grand.A3SmoothUnitBallApproximationExact
import NCG.Grand.A3FlatTorusMetricExact

/-!
# Uniform upper comparison of the actual A3 Connes and flat quotient distances

The exact Connes optimizer is anchored and smoothed. The common derivative
estimate controls its oscillation by the genuine flat quotient metric, while
the smoothing error controls its original grid values. No convergence or
variational optimizer is supplied as a hypothesis.
-/

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

namespace NCG.A3ConnesFlatUpperComparison

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling A3PeriodicConnesSmoothLowerBound
open A3PeriodicProbabilitySmoothing A3SmoothPeriodicUnitEnergy A3SmoothUnitBallApproximation
open A3SmoothedDerivativeControl A3FlatTorusMetric FiniteWeightedGraphHodgeDirac
open FiniteConnesDistanceAttainment

noncomputable section

theorem eventually_connesDistance_le_flat_with_smoothing_error
    (φ : ContDiffBump (0 : Space)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x y : Vertex (n + 1),
      connesDistance (mass (n + 1)) (conductance (n + 1)) x y ≤
        (1 + ε) * flatDistance (point (n + 1) x) (point (n + 1) y) +
          36 * φ.rOut + 18 * mesh (n + 1) := by
  filter_upwards [eventually_norm_fderiv_average_le φ ε hε] with n hn
  intro x y
  obtain ⟨f, hf, hopt⟩ := exists_connesDistance_optimizer (mass (n + 1))
    (conductance (n + 1)) x y (fun _ => pow_pos (mesh_pos _) _) (conductance_connected _)
  let F : Vertex (n + 1) → ℝ := fun z => f z - f 0
  have hF : graphLipschitz (mass (n + 1)) (conductance (n + 1)) F ≤ 1 := by
    rw [show F = (fun z => f z - f 0) from rfl, graphLipschitz_sub_constant]
    exact hf
  have hzero : F 0 = 0 := sub_self _
  let g : Space → ℝ := average (probabilityKernel φ) (n + 1) F
  have hgdiff : Differentiable ℝ g :=
    (contDiff_average_kernel φ (n + 1) F hF hzero).differentiable (by norm_num)
  have hnorm : ∀ p, ‖fderiv ℝ g p‖ ≤ 1 + ε := hn F hF hzero
  have hosc (p q : Space) : |g p - g q| ≤ (1 + ε) * ‖p - q‖ := by
    have h := (convex_univ : Convex ℝ (univ : Set Space)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hgdiff z) (fun z _ => hnorm z) (mem_univ q) (mem_univ p)
    simpa only [Real.norm_eq_abs] using h
  have hdual := PeriodicQuotientDistance.periodic_lipschitz_le_distance
    A3PeriodicSmoothEnergy.lattice g (1 + ε) (by linarith) hosc
    (fun q p => average_periodic _ _ _ q p) (point (n + 1) x) (point (n + 1) y)
  have hx := abs_average_kernel_sample_sub_le φ (n + 1) F hF x
  have hy := abs_average_kernel_sample_sub_le φ (n + 1) F hF y
  have ht₁ := abs_sub_le (F x) (g (point (n + 1) x)) (F y)
  have ht₂ := abs_sub_le (g (point (n + 1) x)) (g (point (n + 1) y)) (F y)
  have hscore : connesDistance (mass (n + 1)) (conductance (n + 1)) x y = |F x - F y| := by
    rw [hopt]
    congr 1
    dsimp [F]
    ring
  rw [hscore]
  rw [abs_sub_comm (F x) (g (point (n + 1) x))] at ht₁
  change |g (point (n + 1) x) - F x| ≤ _ at hx
  change |g (point (n + 1) y) - F y| ≤ _ at hy
  change |g (point (n + 1) x) - g (point (n + 1) y)| ≤
    (1 + ε) * flatDistance (point (n + 1) x) (point (n + 1) y) at hdual
  linarith

end

end NCG.A3ConnesFlatUpperComparison
