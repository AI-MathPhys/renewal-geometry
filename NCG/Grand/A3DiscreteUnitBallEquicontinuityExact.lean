/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicConnesSmoothLowerBoundExact
import NCG.Grand.FiniteRootGraphUnitBallBoundsExact
import NCG.Grand.DiscreteCoordinateDifferenceBoundExact

/-!
# Mesh-independent equicontinuity of the A3 graph unit ball

Every discrete commutator-unit-ball function is uniformly Lipschitz on the
Euclidean representatives of the periodic grid. The constant eighteen is
independent of the scalar period. It is a compactness bound, not the sharp
constant one required for convergence to the flat-torus distance.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.A3DiscreteUnitBallEquicontinuity

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open A3PeriodicConnesSmoothLowerBound FiniteWeightedGraphHodgeDirac
open FiniteRootGraphUnitBallBounds DiscreteCoordinateDifferenceBound

noncomputable section

theorem abs_coordinates_apply_le_two_norm (w : Space) (i : Fin 3) :
    |coordinates w i| ≤ 2 * ‖w‖ := by
  have h (j : Fin 3) : -‖w‖ ≤ w j ∧ w j ≤ ‖w‖ :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hn := norm_nonneg w
  fin_cases i <;> norm_num [coordinates, Matrix.cons_val_two] <;>
    rw [abs_le] <;> constructor <;> linarith

theorem coordinates_point (d : ℕ) (x : Vertex d) (i : Fin 3) :
    coordinates (point d x) i = ((x i).val : ℝ) / (d : ℝ) := by
  change basis.repr (∑ j, (((x j).val : ℝ) / (d : ℝ)) • basis j) i = _
  rw [basis.repr_sum_self]

theorem coordinates_point_sub (d : ℕ) (x y : Vertex d) (i : Fin 3) :
    coordinates (point d y - point d x) i =
      (((y i).val : ℝ) - ((x i).val : ℝ)) / (d : ℝ) := by
  rw [map_sub, Pi.sub_apply, coordinates_point, coordinates_point, sub_div]

theorem point_injective (d : ℕ) [NeZero d] : Function.Injective (point d) := by
  intro x y hxy
  funext i
  apply ZMod.val_injective
  have h := congrArg (fun w => coordinates w i) hxy
  rw [coordinates_point, coordinates_point] at h
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  exact_mod_cast (div_left_inj' hd).mp h

/-- Arbitrary discrete observables satisfy a period-independent spatial bound. -/
theorem abs_difference_le_eighteen_norm
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (x y : Vertex d) :
    |f y - f x| ≤ 18 * ‖point d y - point d x‖ := by
  have hstep (i : Fin 3) (z : Vertex d) :
      |f (z + Pi.single i 1) - f z| ≤ 3 * mesh d := by
    rw [← rootStep_selected_basis]
    exact root_step_difference_le_three_mesh (rootStep d) (mesh d) (mesh_pos d)
      f hf z (![0, 4, 8] i)
  have hpath := abs_difference_periodic_grid_le d f (fun _ => 3 * mesh d) hstep x y
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hterm (i : Fin 3) :
      (((((y i).val : ℤ) - ((x i).val : ℤ)).natAbs : ℕ) : ℝ) * (3 * mesh d) =
        3 * |coordinates (point d y - point d x) i| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      coordinates_point_sub, abs_div, abs_of_pos hd]
    unfold mesh
    ring
  simp only [hterm] at hpath
  apply hpath.trans
  calc
    (∑ i : Fin 3, 3 * |coordinates (point d y - point d x) i|) ≤
        ∑ _i : Fin 3, 3 * (2 * ‖point d y - point d x‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (abs_coordinates_apply_le_two_norm _ i) (by norm_num)
    _ = 18 * ‖point d y - point d x‖ := by simp; ring

end

end NCG.A3DiscreteUnitBallEquicontinuity
