/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevSpace

/-!
# Pointwise precision controls the grid Sobolev norms (`thm:supp-open-finite-words`,
  precision step; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` with mesh `h = 1/N` and unit total volume, a pointwise error `η`
costs at most `h^{-s}` in the grid Sobolev norm `‖·‖_{s,h}`:

* `sobNorm_zero_le_of_pointwise`: `|u(x)| ≤ η` for all `x` gives `‖u‖_{0,h} ≤ η` (unit volume);
* `sobNorm_le_of_pointwise` (**`‖δu‖_{H^s_h} ≤ C_s h^{-s} η`**): with the mesh-independent
  constant `precConst s = Π_{k<s} invConst k`, iterating the inverse inequality
  `sobNorm_succ_le_inverse`.

This is the inequality used in the proof of `thm:supp-open-finite-words` to convert the
pointwise precision convention `c_s ε h^{s+10}` on the scaled endpoint jets into the Sobolev
endpoint bound `b_h ≤ C_s ε h^{10}` of `lem:supp-open-hermite-precision`.
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.PeriodicGridSobolev

open LatticeTorusPlancherel

variable {N : ℕ} [NeZero N]

/-- The precision constant `Π_{k<s} C_k` (`C_k = invConst k`), independent of the mesh. -/
noncomputable def precConst (s : ℕ) : ℝ := ∏ k ∈ range s, invConst k

theorem precConst_nonneg (s : ℕ) : 0 ≤ precConst s :=
  prod_nonneg fun k _ => invConst_nonneg k

/-- A pointwise bound gives the same bound on the unit-volume grid `L²` norm. -/
theorem sobNorm_zero_le_of_pointwise (u : Grid N → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hu : ∀ x, ‖u x‖ ≤ η) : sobNorm 0 u ≤ η := by
  have hN : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hsq : sobSq 0 u ≤ η ^ 2 := by
    rw [sobSq_zero, gridNormSq]
    have hsum : ∑ x, ‖u x‖ ^ 2 ≤ ∑ _x : Grid N, η ^ 2 :=
      sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hu x) 2
    rw [sum_const, card_univ, nsmul_eq_mul, card_grid] at hsum
    calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u x‖ ^ 2 ≤ ((N : ℝ) ^ 3)⁻¹ * ((N : ℝ) ^ 3 * η ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = η ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  rw [sobNorm]
  calc Real.sqrt (sobSq 0 u) ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hsq
    _ = η := Real.sqrt_sq hη

/-- **Pointwise precision in Sobolev norm**: if `|u(x)| ≤ η` at every grid point, then
`‖u‖_{s,h} ≤ C_s h^{-s} η` with `C_s = precConst s` independent of the mesh `h = 1/N`. -/
theorem sobNorm_le_of_pointwise (s : ℕ) (u : Grid N → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hu : ∀ x, ‖u x‖ ≤ η) : sobNorm s u ≤ precConst s * (N : ℝ) ^ s * η := by
  induction s with
  | zero => simpa [precConst] using sobNorm_zero_le_of_pointwise u hη hu
  | succ k ih =>
    have h1 := sobNorm_succ_le_inverse k u
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc sobNorm (k + 1) u ≤ invConst k * N * sobNorm k u := h1
      _ ≤ invConst k * N * (precConst k * (N : ℝ) ^ k * η) := by
          gcongr
          · exact mul_nonneg (invConst_nonneg k) hN
      _ = precConst (k + 1) * (N : ℝ) ^ (k + 1) * η := by
          simp only [precConst, prod_range_succ]; ring

end RenewalGeometry.PeriodicGridSobolev
