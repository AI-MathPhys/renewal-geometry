/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicStepFunctionLiftExact

/-!
# Quantitative oscillation of periodic A3 step-function lifts

The true periodic lift, including all seams, has spatial oscillation bounded
by `18 * distance + 9 * mesh`. This estimate applies to every discrete
commutator-unit-ball function and needs no anchoring or smoothness.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.A3PeriodicLiftOscillation

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open A3PeriodicConnesSmoothLowerBound A3DiscreteUnitBallEquicontinuity
open A3PeriodicStepFunctionLift FiniteWeightedGraphHodgeDirac
open FiniteRootGraphUnitBallBounds DiscreteCoordinateDifferenceBound

noncomputable section

theorem abs_floor_sub_le (a b : ℝ) : |(⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)| ≤ |a - b| + 1 := by
  have ha := Int.floor_le a
  have hb := Int.floor_le b
  have ha' := Int.lt_floor_add_one a
  have hb' := Int.lt_floor_add_one b
  rw [abs_le]
  constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b)]

theorem index_integer_path (d : ℕ) (p q : Space) :
    index d p + ∑ i : Fin 3, (integerIndex d q i - integerIndex d p i) •
      (Pi.single i (1 : ZMod d) : Vertex d) = index d q := by
  funext j
  rw [Pi.add_apply, Finset.sum_apply]
  change (integerIndex d p j : ZMod d) +
    (∑ i : Fin 3, (integerIndex d q i - integerIndex d p i) •
      ((Pi.single i (1 : ZMod d) : Vertex d) j)) = (integerIndex d q j : ZMod d)
  simp only [Pi.single_apply, zsmul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Int.cast_sub]
  ring

theorem abs_lift_sub_le_spatial_mesh_bound
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (p q : Space) :
    |lift d f q - lift d f p| ≤ 18 * ‖q - p‖ + 9 * mesh d := by
  have hstep (i : Fin 3) (x : Vertex d) : |f (x + Pi.single i 1) - f x| ≤ 3 * mesh d := by
    rw [← rootStep_selected_basis]
    exact root_step_difference_le_three_mesh (rootStep d) (mesh d) (mesh_pos d)
      f hf x (![0, 4, 8] i)
  let z : Fin 3 → ℤ := fun i => integerIndex d q i - integerIndex d p i
  have hpath := abs_difference_sum_zsmul_le f (fun i => Pi.single i 1)
    (fun _ => 3 * mesh d) hstep z (index d p)
  rw [index_integer_path] at hpath
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hfloor (i : Fin 3) : |(z i : ℝ)| ≤ (d : ℝ) * |coordinates (q - p) i| + 1 := by
    have h := abs_floor_sub_le ((d : ℝ) * coordinates q i) ((d : ℝ) * coordinates p i)
    simpa only [z, integerIndex, Int.cast_sub, ← mul_sub, abs_mul, abs_of_pos hd,
      map_sub, Pi.sub_apply] using h
  have hterm (i : Fin 3) : ((z i).natAbs : ℝ) * (3 * mesh d) ≤
      3 * (2 * ‖q - p‖ + mesh d) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    calc
      _ ≤ ((d : ℝ) * |coordinates (q - p) i| + 1) * (3 * mesh d) :=
        mul_le_mul_of_nonneg_right (hfloor i) (mul_nonneg (by norm_num) (mesh_pos d).le)
      _ = 3 * (|coordinates (q - p) i| + mesh d) := by
        unfold mesh
        field_simp
        <;> ring
      _ ≤ 3 * (2 * ‖q - p‖ + mesh d) := by
        linarith [abs_coordinates_apply_le_two_norm (q - p) i]
  apply hpath.trans
  calc
    (∑ i : Fin 3, ((z i).natAbs : ℝ) * (3 * mesh d)) ≤
        ∑ _i : Fin 3, 3 * (2 * ‖q - p‖ + mesh d) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 18 * ‖q - p‖ + 9 * mesh d := by simp; ring

end

end NCG.A3PeriodicLiftOscillation
