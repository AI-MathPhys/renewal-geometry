/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IrreducibleMetzlerSCGFExact
import NCG.Grand.FiniteMarkovHeatKernel

/-!
# Exact transition semigroup of a finite continuous-time generator

For a finite Metzler matrix with zero row sums, its matrix exponential is a
row-stochastic transition kernel at every nonnegative time.  This file proves
that fact directly, together with identity, semigroup, and generator
commutation laws.  These are the finite-dimensional consistency data needed
before constructing the corresponding path-space law.
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace NCG.FiniteGeneratorTransitionSemigroup

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Matrix-exponential transition kernel of a finite generator. -/
def transition (L : Matrix S S ℝ) (t : ℝ) : Matrix S S ℝ :=
  NormedSpace.exp (t • L)

/-- Zero row sums say exactly that the all-ones vector is a zero right
eigenvector of the generator. -/
theorem generator_mulVec_one (L : Matrix S S ℝ)
    (hL : DrivenProcess.IsGenerator L) :
    L.mulVec (fun _ => 1) = 0 := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using hL.row_sum i

/-- A finite generator has an entrywise nonnegative transition kernel at every
nonnegative time. -/
theorem transition_nonnegative (L : Matrix S S ℝ)
    (hL : DrivenProcess.IsGenerator L) {t : ℝ} (ht : 0 ≤ t) :
    Matrix.EntrywiseNonnegative (transition L t) := by
  intro i j
  rw [transition, ← FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply]
  exact MetzlerExponentialPositivity.exponentialEntry_smul_entrywiseNonnegative_of_offDiag
    L hL.offDiag_nonneg t ht i j

/-- The matrix exponential preserves the all-ones vector. -/
theorem transition_mulVec_one (L : Matrix S S ℝ)
    (hL : DrivenProcess.IsGenerator L) (t : ℝ) :
    (transition L t).mulVec (fun _ => 1) = fun _ => 1 := by
  have heig : L.mulVec (fun _ : S => (1 : ℝ)) =
      (0 : ℝ) • (fun _ : S => (1 : ℝ)) := by
    simpa using generator_mulVec_one L hL
  have hprop :=
    IrreducibleMetzlerSCGF.exponentialEntry_smul_mulVec_eigenvector
      L (fun _ : S => (1 : ℝ)) 0 t heig
  have hmatrix : Matrix.exponentialEntry (t • L) = transition L t := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply (t • L) i j
  rw [hmatrix] at hprop
  simpa using hprop

/-- Every row of the transition kernel sums to one. -/
theorem transition_row_sum (L : Matrix S S ℝ)
    (hL : DrivenProcess.IsGenerator L) (t : ℝ) (i : S) :
    ∑ j, transition L t i j = 1 := by
  have hi := congrFun (transition_mulVec_one L hL t) i
  simpa [Matrix.mulVec, dotProduct] using hi

/-- Hence the nonnegative-time transition kernel is row-stochastic. -/
theorem transition_rowStochastic (L : Matrix S S ℝ)
    (hL : DrivenProcess.IsGenerator L) {t : ℝ} (ht : 0 ≤ t) :
    Matrix.RowStochastic (transition L t) :=
  ⟨transition_nonnegative L hL ht, transition_row_sum L hL t⟩

/-- The transition kernel at time zero is the identity. -/
@[simp] theorem transition_zero (L : Matrix S S ℝ) :
    transition L 0 = 1 := by
  simp [transition]

/-- Exact Chapman--Kolmogorov semigroup law. -/
theorem transition_add (L : Matrix S S ℝ) (s t : ℝ) :
    transition L (s + t) = transition L s * transition L t := by
  rw [transition, transition, transition, add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl L).smul_left s).smul_right t)

/-- The generator commutes with its transition semigroup, so the forward and
backward generator actions agree algebraically. -/
theorem transition_commutes_generator (L : Matrix S S ℝ) (t : ℝ) :
    transition L t * L = L * transition L t := by
  exact (Commute.exp_left (Commute.smul_left (Commute.refl L) t)).eq

end NCG.FiniteGeneratorTransitionSemigroup
