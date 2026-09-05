/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRootGraphEnergyExact
import Mathlib.Data.ZMod.Basic

/-!
# Connectedness of finite periodic direction-packet graphs

If a root packet contains every positive basis-coordinate step, repeated
steps reach any vertex of the scalar-period grid. This includes all small
periods and does not require an externally supplied path or spectral gap.
-/

open scoped BigOperators

namespace NCG.FiniteCoordinateRootGraphConnected

open FiniteRootGraphEnergy FiniteWeightedGraphHodgeDirac

noncomputable section

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]

theorem conductanceConnected_of_coordinate_steps
    (d : ℕ) [NeZero d] (step : (ι → ZMod d) → R → (ι → ZMod d))
    (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hcanonical : ∀ i : ι, ∃ r : R, ∀ x : ι → ZMod d,
      step x r = x + Pi.single i 1) :
    ConductanceConnected (rootConductance step κ h) := by
  let rel : (ι → ZMod d) → (ι → ZMod d) → Prop :=
    fun x y => 0 < rootConductance step κ h x y
  have hedge : ∀ x : ι → ZMod d, ∀ i : ι, rel x (x + Pi.single i 1) := by
    intro x i
    obtain ⟨r, hr⟩ := hcanonical i
    have hterm : κ * h ≤ rootConductance step κ h x (x + Pi.single i 1) := by
      have hle := Finset.single_le_sum
        (fun r' (_ : r' ∈ Finset.univ) =>
          show 0 ≤ (if step x r' = x + Pi.single i 1 then κ * h else 0) from by
            split_ifs <;> positivity)
        (Finset.mem_univ r)
      rw [hr x, if_pos rfl] at hle
      exact hle
    exact (mul_pos hκ hh).trans_le hterm
  have hnat : ∀ n : ℕ, ∀ x : ι → ZMod d, ∀ i : ι,
      Relation.ReflTransGen rel x (x + n • Pi.single i 1) := by
    intro n
    induction n with
    | zero => intro x i; simpa using (Relation.ReflTransGen.refl (a := x) (r := rel))
    | succ n ih =>
      intro x i
      simpa only [succ_nsmul, add_assoc] using
        (ih x i).tail (hedge (x + n • Pi.single i 1) i)
  intro x y
  let z := y - x
  have hsum : ∀ s : Finset ι, ∀ a : ι → ZMod d,
      Relation.ReflTransGen rel a (a + ∑ i ∈ s, (z i).val • Pi.single i 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro a; simpa using (Relation.ReflTransGen.refl (a := a) (r := rel))
    | @insert i s hi ih =>
      intro a
      simpa only [Finset.sum_insert hi, add_assoc] using
        (hnat (z i).val a i).trans (ih (a + (z i).val • Pi.single i 1))
  have hdecomp : (∑ i : ι, (z i).val • Pi.single i (1 : ZMod d)) = z := by
    ext j
    rw [Finset.sum_apply]
    change (∑ i : ι, (z i).val • ((Pi.single i (1 : ZMod d) : ι → ZMod d) j)) = z j
    simp only [Pi.single_apply, nsmul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact ZMod.natCast_zmod_val (z j)
  have hreach := hsum Finset.univ x
  rw [hdecomp] at hreach
  have hend : x + z = y := by dsimp [z]; abel
  rw [hend] at hreach
  exact hreach

end

end NCG.FiniteCoordinateRootGraphConnected
