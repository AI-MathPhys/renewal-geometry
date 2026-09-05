/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3SmoothedFlatDistanceExact
import NCG.Grand.LipschitzDerivativeFiniteDifferenceExact
import NCG.Grand.A3DerivativeEnergyComparisonExact

/-!
# Uniform lower comparison of A3 Connes distance with the flat torus

Smoothed genuine distance functions provide actual feasible graph tests.
One derivative modulus works for every center, so the mesh cutoff precedes
both vertex quantifiers. No continuum distance duality is assumed.
-/

open Filter
open scoped Topology Matrix.Norms.L2Operator

namespace NCG.A3ConnesFlatLowerComparison

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicGraphSampling
open A3SmoothedFlatDistance A3FlatTorusMetric A3DerivativeEnergyComparison
open FiniteWeightedGraphHodgeDirac FiniteConnesDistanceAttainment FiniteConnesDistanceMetric
open A3PeriodicConnesSmoothLowerBound LipschitzDerivativeFiniteDifference

noncomputable section

theorem eventually_graphLipschitz_smoothDistance_le
    (φ : ContDiffBump (0 : Space)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a : Space,
      graphLipschitz (mass (n + 1)) (conductance (n + 1))
        (fun y => smoothDistance φ a (point (n + 1) y)) ≤ 1 + ε := by
  obtain ⟨δ, hδ, hdiff⟩ := uniform_bounded_direction_difference (E := Space)
    (distanceDerivativeBound φ) (distanceDerivativeBound_nonneg φ) 2 (by norm_num)
    (ε / 3) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => mesh (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mesh, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
  intro a
  let g := smoothDistance φ a
  have hg : ∀ p, HasFDerivAt g (fderiv ℝ g p) p := fun p =>
    ((contDiff_smoothDistance φ a).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have henergy (p : Space) : sampledEnergy g p (mesh (n + 1)) ≤ (1 + ε) ^ 2 := by
    have herr (r : Fin 12) :
        |rootDifference g p (mesh (n + 1)) r -
          inner ℝ (derivativeVector (fderiv ℝ g p)) (root r)| ≤ ε / 3 := by
      rw [inner_derivativeVector]
      exact hdiff g (fderiv ℝ g) hg (norm_fderiv_smoothDistance_sub_le φ a)
        (mesh (n + 1)) (mesh_pos _) hn p (root r) (root_norm_le_two r)
    have he := sqrt_energy_error_le g p (derivativeVector (fderiv ℝ g p))
      (mesh (n + 1)) (ε / 3) (by positivity) herr
    rw [norm_derivativeVector] at he
    have hb := norm_fderiv_smoothDistance_le_one φ a p
    have hu := (le_abs_self _).trans he
    have hs := Real.sq_sqrt (sampledEnergy_nonneg g p (mesh (n + 1)))
    have hp := Real.sqrt_nonneg (sampledEnergy g p (mesh (n + 1)))
    change ‖fderiv ℝ g p‖ ≤ 1 at hb
    nlinarith
  have hnorm : ‖fun y : Vertex (n + 1) => sampledEnergy g (point (n + 1) y)
      (mesh (n + 1))‖ ≤ (1 + ε) ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (sampledEnergy_nonneg _ _ _)]
    exact henergy _
  have hsq := graphLipschitz_sample_sq_eq (n + 1) g (smoothDistance_periodic φ a)
  have hp : 0 ≤ graphLipschitz (mass (n + 1)) (conductance (n + 1))
      (fun y => g (point (n + 1) y)) := norm_nonneg _
  change graphLipschitz _ _ (fun y => g (point (n + 1) y)) ≤ 1 + ε
  nlinarith

theorem eventually_flatDistance_le_connes_with_smoothing_error
    (φ : ContDiffBump (0 : Space)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x y : Vertex (n + 1),
      flatDistance (point (n + 1) x) (point (n + 1) y) ≤
        (1 + ε) * connesDistance (mass (n + 1)) (conductance (n + 1)) x y +
          2 * φ.rOut := by
  filter_upwards [eventually_graphLipschitz_smoothDistance_le φ ε hε] with n hn
  intro x y
  let a := point (n + 1) x
  let f : Vertex (n + 1) → ℝ := fun z => smoothDistance φ a (point (n + 1) z)
  have hden : 0 < 1 + ε := by linarith
  have hfeasible : graphLipschitz (mass (n + 1)) (conductance (n + 1))
      ((1 + ε)⁻¹ • f) ≤ 1 := by
    rw [graphLipschitz_smul, abs_inv, abs_of_pos hden, ← div_eq_inv_mul]
    exact (div_le_one hden).mpr (hn a)
  have hbound := abs_sub_le_connesDistance (mass (n + 1)) (conductance (n + 1)) x y
    (fun _ => pow_pos (mesh_pos _) _) (conductance_connected _) _ hfeasible
  have htest : |f x - f y| ≤
      (1 + ε) * connesDistance (mass (n + 1)) (conductance (n + 1)) x y := by
    have hb : |f x - f y| / (1 + ε) ≤
        connesDistance (mass (n + 1)) (conductance (n + 1)) x y := by
      simpa only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_inv,
        abs_of_pos hden, div_eq_inv_mul] using hbound
    linarith [(div_le_iff₀ hden).mp hb]
  have hx := abs_smoothDistance_sub_le φ a a
  have hy := abs_smoothDistance_sub_le φ a (point (n + 1) y)
  have ha : flatDistance a a = 0 := PeriodicQuotientDistance.distance_self _ _
  rw [ha, sub_zero] at hx
  change |f x| ≤ φ.rOut at hx
  change |f y - flatDistance a (point (n + 1) y)| ≤ φ.rOut at hy
  have hx' := (le_abs_self (f x)).trans hx
  have hy' := (neg_le_abs (f y - flatDistance a (point (n + 1) y))).trans hy
  have ht := (neg_le_abs (f x - f y)).trans htest
  change flatDistance a (point (n + 1) y) ≤ _
  linarith

end

end NCG.A3ConnesFlatLowerComparison
