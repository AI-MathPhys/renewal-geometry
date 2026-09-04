/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicGraphSamplingExact
import NCG.Grand.FiniteCoordinateRootGraphConnectedExact
import NCG.Grand.FiniteConnesDistanceMetricExact

/-!
# Smooth-test lower bounds for the periodic A3 Connes distance

The actual finite graph is connected because the twelve-root packet contains
the three positive basis steps. Smooth periodic functions with gradient norm
at most one have discrete commutator norm at most `1+ε` at all sufficiently
large scalar periods. Their rescaled samples therefore give genuine Connes
distance lower bounds, uniformly over the pair of grid vertices.
-/

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace NCG.A3PeriodicConnesSmoothLowerBound

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open FiniteRootGraphEnergy FiniteWeightedGraphHodgeDirac
open FiniteConnesDistanceAttainment FiniteConnesDistanceMetric

noncomputable section

theorem rootStep_selected_basis (d : ℕ) (x : Vertex d) (i : Fin 3) :
    rootStep d x (![0, 4, 8] i) = x + Pi.single i 1 := by
  have hcoords : rootCoordinates (![0, 4, 8] i) = Pi.single i (1 : ℤ) := by
    fin_cases i <;> decide
  funext j
  change x j + (rootCoordinates (![0, 4, 8] i) j : ZMod d) =
    x j + (Pi.single i (1 : ZMod d) : Vertex d) j
  rw [hcoords]
  by_cases hij : i = j <;> simp [Pi.single_apply, hij]

theorem conductance_connected (d : ℕ) [NeZero d] :
    ConductanceConnected (conductance d) := by
  exact FiniteCoordinateRootGraphConnected.conductanceConnected_of_coordinate_steps d
    (rootStep d) (1 / 8) (mesh d) (by norm_num) (mesh_pos d)
    (fun i => ⟨![0, 4, 8] i, fun x => rootStep_selected_basis d x i⟩)

theorem eventually_graphLipschitz_sample_le
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : Continuous (fun x => innerSL ℝ (v x)))
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y)
    (hv : ∀ x, ‖v x‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      graphLipschitz (mass (n + 1)) (conductance (n + 1))
        (fun y => f (point (n + 1) y)) ≤ 1 + ε := by
  filter_upwards [eventually_uniform_localEnergy_sample f v hf hdf hperiod ε hε] with n hn
  let E : Vertex (n + 1) → ℝ := localEnergy (mass (n + 1)) (conductance (n + 1))
    (fun y => f (point (n + 1) y))
  have hEpos : ∀ x, 0 ≤ E x := by
    intro x
    unfold E localEnergy
    positivity
  have hEbound : ∀ x, E x ≤ (1 + ε) ^ 2 := by
    intro x
    have hnear := (le_abs_self (Real.sqrt (E x) - ‖v (point (n + 1) x)‖)).trans_lt (hn x)
    have hsqrt := Real.sq_sqrt (hEpos x)
    have hgrad := hv (point (n + 1) x)
    have hsnonneg := Real.sqrt_nonneg (E x)
    nlinarith
  have hnorm : ‖E‖ ≤ (1 + ε) ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hEpos x)]
    exact hEbound x
  have hsq := norm_sq_dirac_commutator (mass (n + 1)) (conductance (n + 1))
    (fun y => f (point (n + 1) y))
  change graphLipschitz _ _ _ ^ 2 = ‖E‖ at hsq
  have hpos : 0 ≤ graphLipschitz (mass (n + 1)) (conductance (n + 1))
    (fun y => f (point (n + 1) y)) := norm_nonneg _
  nlinarith

/-- Every smooth unit-gradient periodic function supplies a uniform lower test
for the genuine finite Connes metric after a factor tending to one. -/
theorem eventually_smooth_test_le_connesDistance
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : Continuous (fun x => innerSL ℝ (v x)))
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y)
    (hv : ∀ x, ‖v x‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x y : Vertex (n + 1),
      |f (point (n + 1) x) - f (point (n + 1) y)| / (1 + ε) ≤
        connesDistance (mass (n + 1)) (conductance (n + 1)) x y := by
  filter_upwards [eventually_graphLipschitz_sample_le f v hf hdf hperiod hv ε hε] with n hn
  intro x y
  have hden : 0 < 1 + ε := by linarith
  have hfeasible : graphLipschitz (mass (n + 1)) (conductance (n + 1))
      ((1 + ε)⁻¹ • (fun y => f (point (n + 1) y))) ≤ 1 := by
    rw [graphLipschitz_smul, abs_inv, abs_of_pos hden, ← div_eq_inv_mul]
    exact (div_le_one hden).mpr hn
  have hbound := abs_sub_le_connesDistance (mass (n + 1)) (conductance (n + 1)) x y
    (fun _ => pow_pos (mesh_pos (n + 1)) 3) (conductance_connected (n + 1)) _ hfeasible
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_inv,
    abs_of_pos hden, div_eq_inv_mul] using hbound

end

end NCG.A3PeriodicConnesSmoothLowerBound
