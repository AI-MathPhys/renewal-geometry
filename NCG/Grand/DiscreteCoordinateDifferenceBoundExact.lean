/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quantitative telescoping along discrete coordinate directions

A uniform one-step oscillation bound controls all integer translates and all
finite coordinate paths. On a scalar-period grid, the resulting bound uses
the absolute differences of the actual integer representatives. These bounds
apply to arbitrary discrete observables, not only to smooth samples.
-/

open scoped BigOperators

namespace NCG.DiscreteCoordinateDifferenceBound

variable {G ι : Type*} [AddCommGroup G]

theorem abs_difference_nsmul_le
    (f : G → ℝ) (g : G) (C : ℝ) (hstep : ∀ x, |f (x + g) - f x| ≤ C)
    (n : ℕ) (x : G) : |f (x + n • g) - f x| ≤ (n : ℝ) * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc]
    have h := (abs_sub_le (f (x + n • g + g)) (f (x + n • g)) (f x)).trans
      (add_le_add (hstep (x + n • g)) ih)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm C] using h

theorem abs_difference_zsmul_le
    (f : G → ℝ) (g : G) (C : ℝ) (hstep : ∀ x, |f (x + g) - f x| ≤ C)
    (z : ℤ) (x : G) : |f (x + z • g) - f x| ≤ (z.natAbs : ℝ) * C := by
  cases z with
  | ofNat n => simpa using abs_difference_nsmul_le f g C hstep n x
  | negSucc n =>
    have h := abs_difference_nsmul_le f g C hstep (n + 1) (x - (n + 1) • g)
    rw [sub_add_cancel, abs_sub_comm] at h
    simpa only [negSucc_zsmul, sub_eq_add_neg, Int.natAbs_negSucc] using h

theorem abs_difference_sum_zsmul_le
    [Fintype ι] [DecidableEq ι]
    (f : G → ℝ) (g : ι → G) (C : ι → ℝ)
    (hstep : ∀ i x, |f (x + g i) - f x| ≤ C i) (z : ι → ℤ) (x : G) :
    |f (x + ∑ i, z i • g i) - f x| ≤ ∑ i, ((z i).natAbs : ℝ) * C i := by
  have hsum : ∀ s : Finset ι, ∀ x : G,
      |f (x + ∑ i ∈ s, z i • g i) - f x| ≤ ∑ i ∈ s, ((z i).natAbs : ℝ) * C i := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      intro x
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← add_assoc]
      have h := (abs_sub_le (f (x + z i • g i + ∑ j ∈ s, z j • g j))
        (f (x + z i • g i)) (f x)).trans
        (add_le_add (ih (x + z i • g i))
          (abs_difference_zsmul_le f (g i) (C i) (hstep i) (z i) x))
      simpa only [add_comm] using h
  exact hsum Finset.univ x

/-- Coordinate representative bound on the actual finite periodic grid. -/
theorem abs_difference_periodic_grid_le
    [Fintype ι] [DecidableEq ι] (d : ℕ) [NeZero d]
    (f : (ι → ZMod d) → ℝ) (C : ι → ℝ)
    (hstep : ∀ i x, |f (x + Pi.single i 1) - f x| ≤ C i)
    (x y : ι → ZMod d) :
    |f y - f x| ≤ ∑ i, (((((y i).val : ℤ) - ((x i).val : ℤ)).natAbs : ℕ) : ℝ) * C i := by
  let z : ι → ℤ := fun i => ((y i).val : ℤ) - ((x i).val : ℤ)
  have h := abs_difference_sum_zsmul_le f (fun i => Pi.single i 1) C hstep z x
  have hdecomp : x + ∑ i, z i • (Pi.single i (1 : ZMod d) : ι → ZMod d) = y := by
    funext j
    rw [Pi.add_apply, Finset.sum_apply]
    change x j + (∑ i, z i • ((Pi.single i (1 : ZMod d) : ι → ZMod d) j)) = y j
    simp only [Pi.single_apply, zsmul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [z, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  rw [hdecomp] at h
  exact h

end NCG.DiscreteCoordinateDifferenceBound
