/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shift-difference energies on the periodic cubic grid `(ℤ/N)³`

Generic discrete calculus on the periodic grid `Grid N = (ℤ/N)³` with values in any seminormed
group: the coordinate unit vectors `e i`, the unweighted shift-difference energy
`shiftEnergy N r u = Σ_x ‖u(x + r) - u(x)‖²` with its shift invariance
(`shiftEnergy_translate`, `shiftEnergy_neg`) and two-step bound (`shiftEnergy_add_le`), and the
coordinate Dirichlet form `coordDirichlet N u = (1/N) Σ_i shiftEnergy N (e i) u`
(`= Σ_i ‖D_i⁺ u‖_h²` with `h = 1/N`).

Split out of `RootParityConnectorExact`, which builds the root and connector Dirichlet forms on
top of these definitions (declaration names unchanged).
-/

open scoped BigOperators Real
open Finset

namespace MathPhys.RootParityConnector

/-- The odd periodic grid `(ℤ/N)³`. -/
abbrev Grid (N : ℕ) := Fin 3 → ZMod N

/-- Coordinate unit vector `e_i` on the grid. -/
def e (N : ℕ) (i : Fin 3) : Grid N := Pi.single i 1

variable {E : Type*} [SeminormedAddCommGroup E]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_add_sq_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- Unweighted shift-difference energy `Σ_x ‖u(x + r) - u(x)‖²`; the
manuscript's `‖(S_r - I)u/h‖_h²` is `(1/N)` times this quantity. -/
def shiftEnergy (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) : ℝ :=
  ∑ x, ‖u (x + r) - u x‖ ^ 2

theorem shiftEnergy_nonneg (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) :
    0 ≤ shiftEnergy N r u :=
  sum_nonneg fun _ _ => by positivity

/-- Shift invariance of the grid sum: `‖(S_r - I) S_s u‖ = ‖(S_r - I) u‖`. -/
theorem shiftEnergy_translate (N : ℕ) [NeZero N] (r s : Grid N) (u : Grid N → E) :
    ∑ x, ‖u (x + s + r) - u (x + s)‖ ^ 2 = shiftEnergy N r u := by
  unfold shiftEnergy
  exact Fintype.sum_equiv (Equiv.addRight s) _ _ fun x => rfl

/-- `‖(S_{-r} - I)u‖ = ‖(S_r - I)u‖`. -/
theorem shiftEnergy_neg (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) :
    shiftEnergy N (-r) u = shiftEnergy N r u := by
  unfold shiftEnergy
  refine Fintype.sum_equiv (Equiv.addRight (-r)) _ _ fun x => ?_
  simp only [Equiv.coe_addRight]
  rw [neg_add_cancel_right, norm_sub_rev]

/-- Two-step bound: `‖(S_{r+s} - I)u‖² ≤ 2‖(S_r - I)u‖² + 2‖(S_s - I)u‖²`
(the identity `S_{r+s} - I = S_s (S_r - I) + (S_s - I)` and shift invariance). -/
theorem shiftEnergy_add_le (N : ℕ) [NeZero N] (r s : Grid N) (u : Grid N → E) :
    shiftEnergy N (r + s) u ≤ 2 * shiftEnergy N r u + 2 * shiftEnergy N s u := by
  rw [← shiftEnergy_translate N r s u]
  unfold shiftEnergy
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have hx : u (x + (r + s)) - u x = (u (x + s + r) - u (x + s)) + (u (x + s) - u x) := by
    rw [add_comm r s, ← add_assoc]
    abel
  rw [hx]
  exact norm_add_sq_le_two _ _

/-- Coordinate Dirichlet form `𝒟_C(u) = Σ_i ‖D_i⁺ u‖_h²`. -/
noncomputable def coordDirichlet (N : ℕ) [NeZero N] (u : Grid N → E) : ℝ :=
  (N : ℝ)⁻¹ * (shiftEnergy N (e N 0) u + shiftEnergy N (e N 1) u + shiftEnergy N (e N 2) u)

end MathPhys.RootParityConnector
