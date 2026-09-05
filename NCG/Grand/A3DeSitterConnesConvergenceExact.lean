/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3ConnesFlatUniformConvergenceExact

/-!
# Exact de Sitter scaling and uniform metric recovery on compact time slabs

The discrete distance below is the actual Connes supremum for the scaled
masses and conductances, not a distance defined by scaling the answer.
-/

open Filter Set
open scoped Topology Pointwise Matrix.Norms.L2Operator

namespace NCG.A3DeSitterConnesConvergence

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling A3FlatTorusMetric
open FiniteWeightedGraphHodgeDirac FiniteConnesDistanceAttainment FiniteConnesDistanceMetric
open A3PeriodicConnesSmoothLowerBound A3ConnesFlatUniformConvergence

noncomputable section

theorem conductance_nonneg (d : ℕ) [NeZero d] (x y : Vertex d) :
    0 ≤ conductance d x y :=
  FiniteRootGraphEnergy.rootConductance_nonneg (rootStep d) (1 / 8) (mesh d)
    (by norm_num) (mesh_pos d).le x y

def sliceConnesDistance (d : ℕ) [NeZero d] (H t : ℝ) (x y : Vertex d) : ℝ :=
  connesDistance (scaledMass (Real.exp (H * t)) (mass d))
    (scaledConductance (Real.exp (H * t)) (conductance d)) x y

/-- The metric of the homothetically scaled flat slice. -/
def sliceFlatDistance (H t : ℝ) (x y : Space) : ℝ :=
  Real.exp (H * t) * flatDistance x y

/-- Identification with Euclidean quotient distance on the physically scaled lattice. -/
theorem sliceFlatDistance_eq_scaled_infDist (H t : ℝ) (x y : Space) :
    sliceFlatDistance H t x y =
      Metric.infDist (Real.exp (H * t) • (x - y))
        (Real.exp (H * t) • (A3PeriodicSmoothEnergy.lattice : Set Space)) := by
  rw [infDist_smul₀ (Real.exp_ne_zero _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), sliceFlatDistance, flatDistance_eq_infDist]

theorem scaled_mass_eq_exp_three (d : ℕ) (H t : ℝ) (x : Vertex d) :
    scaledMass (Real.exp (H * t)) (mass d) x = Real.exp (3 * H * t) * mesh d ^ 3 := by
  have he := Real.exp_nat_mul (H * t) 3
  norm_num only [Nat.cast_ofNat] at he
  rw [scaledMass, mass, ← he]
  congr 2
  ring

theorem slice_graphLipschitz_eq (d : ℕ) [NeZero d] (H t : ℝ) (f : Vertex d → ℝ) :
    graphLipschitz (scaledMass (Real.exp (H * t)) (mass d))
      (scaledConductance (Real.exp (H * t)) (conductance d)) f =
        Real.exp (-H * t) * graphLipschitz (mass d) (conductance d) f :=
  deSitter_graphLipschitz H t (mass d) (conductance d)
    (fun _ => pow_pos (mesh_pos d) _) (conductance_nonneg d) f

theorem sliceConnesDistance_eq (d : ℕ) [NeZero d] (H t : ℝ) (x y : Vertex d) :
    sliceConnesDistance d H t x y =
      Real.exp (H * t) * connesDistance (mass d) (conductance d) x y :=
  deSitter_connesDistance H t (mass d) (conductance d)
    (fun _ => pow_pos (mesh_pos d) _) (conductance_nonneg d) (conductance_connected d) x y

theorem slice_distance_error_eq (d : ℕ) [NeZero d] (H t : ℝ) (x y : Vertex d) :
    |sliceConnesDistance d H t x y - sliceFlatDistance H t (point d x) (point d y)| =
      Real.exp (H * t) *
        |connesDistance (mass d) (conductance d) x y - flatDistance (point d x) (point d y)| := by
  rw [sliceConnesDistance_eq, sliceFlatDistance, ← mul_sub, abs_mul,
    abs_of_pos (Real.exp_pos _)]

/-- Uniform convergence simultaneously over every time in a compact slab
and every pair of vertices in the corresponding finite regulator. -/
theorem eventually_uniform_slice_distance_error
    (H : ℝ) (K : Set ℝ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, ∀ x y : Vertex (n + 1),
      |sliceConnesDistance (n + 1) H t x y -
        sliceFlatDistance H t (point (n + 1) x) (point (n + 1) y)| < ε := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn :
      ContinuousOn (fun t : ℝ => Real.exp (H * t)) K)
  let C := |B| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_uniform_connes_flat_error (ε / C) (div_pos hε hC)] with n hn
  intro t ht x y
  rw [slice_distance_error_eq]
  have hexp : Real.exp (H * t) ≤ C := by
    have hb := hB (mem_image_of_mem (fun t : ℝ => Real.exp (H * t)) ht)
    have hba := le_abs_self B
    dsimp [C]
    linarith
  calc
    _ ≤ C * |connesDistance (mass (n + 1)) (conductance (n + 1)) x y -
        flatDistance (point (n + 1) x) (point (n + 1) y)| :=
      mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn x y) hC
    _ = ε := by field_simp

end

end NCG.A3DeSitterConnesConvergence
