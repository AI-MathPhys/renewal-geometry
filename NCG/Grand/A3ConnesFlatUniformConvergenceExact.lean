/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3ConnesFlatUpperComparisonExact
import NCG.Grand.A3ConnesFlatLowerComparisonExact

/-!
# Uniform recovery of the genuine flat torus distance by periodic A3 graphs

The two quantitative comparisons imply convergence of the actual finite-pair
supremum error. All finite graph distances and the lattice quotient metric
are defined independently of this theorem.
-/

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

namespace NCG.A3ConnesFlatUniformConvergence

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling A3FlatTorusMetric
open A3ConnesFlatUpperComparison A3ConnesFlatLowerComparison A3SmoothedFlatDistance
open A3ConnesDistanceUniformBounds FiniteConnesDistanceAttainment

noncomputable section

theorem eventually_uniform_connes_flat_error (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x y : Vertex (n + 1),
      |connesDistance (mass (n + 1)) (conductance (n + 1)) x y -
        flatDistance (point (n + 1) x) (point (n + 1) y)| < ε := by
  let φ : ContDiffBump (0 : Space) :=
    ⟨ε / 2000, ε / 1000, by positivity, by linarith⟩
  have hsmall : 0 < ε / 1000 := by positivity
  have hmesh : Tendsto (fun n : ℕ => mesh (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mesh, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  filter_upwards [eventually_connesDistance_le_flat_with_smoothing_error φ _ hsmall,
    eventually_flatDistance_le_connes_with_smoothing_error φ _ hsmall,
    hmesh.eventually (gt_mem_nhds hsmall)] with n hu hl hm
  intro x y
  have hu' := hu x y
  have hl' := hl x y
  have hf := flatDistance_le_six (point (n + 1) x) (point (n + 1) y)
  have hc := connesDistance_le_uniform_diameter (n + 1) x y
  change _ ≤ _ + 36 * (ε / 1000) + 18 * mesh (n + 1) at hu'
  change _ ≤ _ + 2 * (ε / 1000) at hl'
  rw [abs_lt]
  constructor <;> nlinarith

/-- The actual maximum absolute error over all pairs of grid vertices. -/
def distanceError (n : ℕ) : ℝ :=
  ‖fun xy : Vertex (n + 1) × Vertex (n + 1) =>
    connesDistance (mass (n + 1)) (conductance (n + 1)) xy.1 xy.2 -
      flatDistance (point (n + 1) xy.1) (point (n + 1) xy.2)‖

/-- The finite supremum assertion (SP.19), with the actual flat quotient metric. -/
theorem tendsto_distanceError_zero : Tendsto distanceError atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_uniform_connes_flat_error (ε / 2) (by positivity)] with n hn
  have hbound : distanceError n ≤ ε / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ε / 2)).mpr
    intro xy
    simpa only [Real.norm_eq_abs] using (hn xy.1 xy.2).le
  have hnonneg : 0 ≤ distanceError n := norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

end

end NCG.A3ConnesFlatUniformConvergence
