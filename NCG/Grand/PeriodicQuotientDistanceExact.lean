/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The actual normed-group quotient distance and periodic dual bounds

The distance is Mathlib's quotient metric, not a supplied dual supremum.
It equals the infimum distance to the period subgroup. Periodic Lipschitz
functions satisfy the corresponding dual bound, and distance-to-a-point is
itself a periodic one-Lipschitz function.
-/

open Set Metric
open scoped NNReal

namespace NCG.PeriodicQuotientDistance

noncomputable section

variable {G : Type*} [NormedAddCommGroup G]

def distance (P : AddSubgroup G) (x y : G) : ℝ :=
  dist ((QuotientAddGroup.mk' P) x) ((QuotientAddGroup.mk' P) y)

theorem distance_eq_infDist (P : AddSubgroup G) (x y : G) :
    distance P x y = infDist (x - y) (P : Set G) := by
  rw [distance, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk _

theorem distance_le_norm (P : AddSubgroup G) (x y : G) : distance P x y ≤ ‖x - y‖ := by
  rw [distance, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem distance_nonneg (P : AddSubgroup G) (x y : G) : 0 ≤ distance P x y := dist_nonneg

theorem distance_self (P : AddSubgroup G) (x : G) : distance P x x = 0 := dist_self _

theorem distance_comm (P : AddSubgroup G) (x y : G) : distance P x y = distance P y x := dist_comm _ _

theorem distance_triangle (P : AddSubgroup G) (x y z : G) :
    distance P x z ≤ distance P x y + distance P y z := dist_triangle _ _ _

theorem distance_periodic_right (P : AddSubgroup G) (x y : G) (q : P) :
    distance P x (y + q) = distance P x y := by
  have hq : (QuotientAddGroup.mk' P) (q : G) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr q.property
  simp only [distance, map_add, hq, add_zero]

theorem projection_lipschitz (P : AddSubgroup G) : LipschitzWith 1 (QuotientAddGroup.mk' P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [distance, NNReal.coe_one, one_mul, dist_eq_norm] using distance_le_norm P x y

theorem distance_to_base_lipschitz (P : AddSubgroup G) (x : G) :
    LipschitzWith 1 (distance P x) := by
  have h := (LipschitzWith.dist_right ((QuotientAddGroup.mk' P) x)).comp (projection_lipschitz P)
  change LipschitzWith 1 (fun y => dist ((QuotientAddGroup.mk' P) x) ((QuotientAddGroup.mk' P) y))
  simpa only [one_mul, Function.comp_def] using h

/-- The periodic dual bound is derived from the quotient infimum metric. -/
theorem periodic_lipschitz_le_distance
    (P : AddSubgroup G) (f : G → ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ x y, |f x - f y| ≤ C * ‖x - y‖)
    (hperiod : ∀ q : P, ∀ y, f (y + q) = f y) (x y : G) :
    |f x - f y| ≤ C * distance P x y := by
  rw [distance_eq_infDist]
  rw [mul_comm C]
  apply (div_le_iff₀ hC).mp
  apply (le_infDist ⟨0, P.zero_mem⟩).mpr
  intro z hz
  apply (div_le_iff₀ hC).mpr
  have h := hf x (y + z)
  rw [hperiod ⟨z, hz⟩ y] at h
  have heq : x - (y + z) = x - y - z := by abel
  simpa only [dist_eq_norm, heq, mul_comm] using h

theorem distance_eq_zero_iff (P : AddSubgroup G) [IsClosed (P : Set G)] (x y : G) :
    distance P x y = 0 ↔ x - y ∈ P := by
  rw [distance, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk_eq_zero

end

end NCG.PeriodicQuotientDistance
