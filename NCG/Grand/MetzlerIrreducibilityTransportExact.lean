/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerPerronExponentExact

/-!
# Transport of irreducibility across Metzler supports

For a nontrivial finite state space, irreducibility of a nonnegative matrix
depends only on its positive off-diagonal support.  This file proves that
fact by transporting quiver paths while deleting diagonal loops.  It then
applies the result to protected tilts, whose positive off-diagonal support is
independent of the tilt parameter.
-/

open Matrix

noncomputable section

namespace NCG.MetzlerIrreducibilityTransport

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Transport a quiver path between matrices having the same positive
off-diagonal support, deleting diagonal loops when necessary. -/
def transportPath (A B : Matrix S S ℝ)
    (hsupport : ∀ i j, i ≠ j → (0 < A i j ↔ 0 < B i j))
    {i j : S} (p : @Quiver.Path S A.toQuiver i j) :
    @Quiver.Path S B.toQuiver i j := by
  letI : Quiver S := Matrix.toQuiver A
  induction p with
  | nil => exact @Quiver.Path.nil S B.toQuiver _
  | @cons b c q e ih =>
      by_cases hbc : b = c
      · subst c
        exact ih
      · exact @Quiver.Path.cons S B.toQuiver _ b c ih
          (PLift.up ((hsupport b c hbc).mp e.down))

/-- A transported path between distinct endpoints still has positive length,
even though diagonal loops may have been removed. -/
theorem transportPath_length_pos_of_ne (A B : Matrix S S ℝ)
    (hsupport : ∀ i j, i ≠ j → (0 < A i j ↔ 0 < B i j))
    {i j : S} (hij : i ≠ j) (p : @Quiver.Path S A.toQuiver i j) :
    0 < @Quiver.Path.length S B.toQuiver i j
      (transportPath A B hsupport p) := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hij (@Quiver.Path.eq_of_length_zero S B.toQuiver i j _ hz)

/-- On a nontrivial finite vertex set, a nonnegative matrix with the same
positive off-diagonal support as an irreducible matrix is irreducible. -/
theorem isIrreducible_of_offDiag_support
    [Nontrivial S] (A B : Matrix S S ℝ)
    (hA : A.IsIrreducible) (hBnonneg : ∀ i j, 0 ≤ B i j)
    (hsupport : ∀ i j, i ≠ j → (0 < A i j ↔ 0 < B i j)) :
    B.IsIrreducible := by
  refine ⟨hBnonneg, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    obtain ⟨u, hui⟩ := exists_ne i
    obtain ⟨p, _hp⟩ := hA.connected i u
    obtain ⟨q, _hq⟩ := hA.connected u i
    letI : Quiver S := B.toQuiver
    let p' := transportPath A B hsupport p
    let q' := transportPath A B hsupport q
    let pq := @Quiver.Path.comp S B.toQuiver i u i p' q'
    refine ⟨pq, ?_⟩
    dsimp only [pq]
    rw [Quiver.Path.length_comp]
    exact Nat.add_pos_left
      (transportPath_length_pos_of_ne A B hsupport hui.symm p) _
  · obtain ⟨p, _hp⟩ := hA.connected i j
    exact ⟨transportPath A B hsupport p,
      transportPath_length_pos_of_ne A B hsupport hij p⟩

/-- Protected finite-state tilts have the same irreducible Metzler
communication graph at every parameter. -/
theorem tilt_isIrreducibleMetzler_of_base
    [Nontrivial S]
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k q : ℝ)
    (hk : MetzlerExponentialPositivity.IsIrreducibleMetzler
      (DrivenProcess.tilt L v g k)) :
    MetzlerExponentialPositivity.IsIrreducibleMetzler
      (DrivenProcess.tilt L v g q) := by
  let A := DrivenProcess.tilt L v g k
  let B := DrivenProcess.tilt L v g q
  let Ashift := MetzlerExponentialPositivity.diagonalShift A
    (MetzlerExponentialPositivity.canonicalDiagonalShift A)
  let Bshift := MetzlerExponentialPositivity.diagonalShift B
    (MetzlerExponentialPositivity.canonicalDiagonalShift B)
  change Bshift.IsIrreducible
  apply isIrreducible_of_offDiag_support Ashift Bshift
  · exact hk
  · exact MetzlerExponentialPositivity.canonicalDiagonalShift_entrywiseNonnegative
      B (fun i j hij => by
        change 0 ≤ DrivenProcess.tilt L v g q i j
        rw [DrivenProcess.tilt_apply_ne L v g q hij]
        exact mul_nonneg (hL.offDiag_nonneg i j hij) (Real.exp_nonneg _))
  · intro i j hij
    simp only [Ashift, Bshift, MetzlerExponentialPositivity.diagonalShift,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij,
      if_false, smul_eq_mul, mul_zero, add_zero, A, B,
      DrivenProcess.tilt_apply_ne L v g k hij,
      DrivenProcess.tilt_apply_ne L v g q hij]
    constructor <;> intro h
    · have hLpos : 0 < L i j := by
        rcases (mul_pos_iff.mp h) with hpos | hneg
        · exact hpos.1
        · exact False.elim ((not_lt_of_ge (Real.exp_nonneg _)) hneg.2)
      exact mul_pos hLpos (Real.exp_pos _)
    · have hLpos : 0 < L i j := by
        rcases (mul_pos_iff.mp h) with hpos | hneg
        · exact hpos.1
        · exact False.elim ((not_lt_of_ge (Real.exp_nonneg _)) hneg.2)
      exact mul_pos hLpos (Real.exp_pos _)

end NCG.MetzlerIrreducibilityTransport
