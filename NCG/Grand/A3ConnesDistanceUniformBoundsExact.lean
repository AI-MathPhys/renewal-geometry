/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3DiscreteLipschitzExtensionExact

/-!
# A fixed compact carrier and uniform bounds for the A3 Connes metrics

Every Euclidean representative lies in the closed ball of radius six.
The actual supremal Connes distances obey the same spatial Lipschitz bound
as their unit-ball test functions. All constants are independent of period.
-/

open scoped BigOperators

namespace NCG.A3ConnesDistanceUniformBounds

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicSmoothEnergy
open A3PeriodicGraphSampling A3PeriodicConnesSmoothLowerBound
open A3DiscreteUnitBallEquicontinuity FiniteConnesDistanceAttainment

noncomputable section

theorem norm_point_le_six (d : ℕ) [NeZero d] (x : Vertex d) : ‖point d x‖ ≤ 6 := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hterm (i : Fin 3) : ‖(((x i).val : ℝ) / (d : ℝ)) • basis i‖ ≤ 2 := by
    have hc0 : 0 ≤ ((x i).val : ℝ) / (d : ℝ) := div_nonneg (Nat.cast_nonneg _) hd.le
    have hc1 : ((x i).val : ℝ) / (d : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hd).mpr
      simpa using (show ((x i).val : ℝ) ≤ (d : ℝ) by exact_mod_cast (ZMod.val_lt (x i)).le)
    have hb : ‖basis i‖ ≤ 2 := by rw [basis_eq_selected_root]; exact root_norm_le_two _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    nlinarith [norm_nonneg (basis i)]
  change ‖∑ i : Fin 3, (((x i).val : ℝ) / (d : ℝ)) • basis i‖ ≤ 6
  calc
    _ ≤ ∑ i : Fin 3, ‖(((x i).val : ℝ) / (d : ℝ)) • basis i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, (2 : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 6 := by norm_num

theorem point_mem_closedBall (d : ℕ) [NeZero d] (x : Vertex d) :
    point d x ∈ Metric.closedBall (0 : Space) 6 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_point_le_six d x

theorem connesDistance_le_eighteen_norm
    (d : ℕ) [NeZero d] (x y : Vertex d) :
    connesDistance (mass d) (conductance d) x y ≤ 18 * ‖point d y - point d x‖ := by
  obtain ⟨f, hf, heq⟩ := exists_connesDistance_optimizer (mass d) (conductance d) x y
    (fun _ => pow_pos (mesh_pos d) _) (conductance_connected d)
  rw [heq]
  rw [abs_sub_comm]
  exact abs_difference_le_eighteen_norm d f hf x y

theorem connesDistance_le_uniform_diameter
    (d : ℕ) [NeZero d] (x y : Vertex d) :
    connesDistance (mass d) (conductance d) x y ≤ 216 := by
  have hnorm := (norm_sub_le (point d y) (point d x)).trans
    (add_le_add (norm_point_le_six d y) (norm_point_le_six d x))
  have h := connesDistance_le_eighteen_norm d x y
  linarith

end

end NCG.A3ConnesDistanceUniformBounds
