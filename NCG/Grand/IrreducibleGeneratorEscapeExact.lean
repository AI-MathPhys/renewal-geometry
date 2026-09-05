/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerIrreducibilityTransportExact
import NCG.Grand.FiniteCTMCPathLikelihoodExact

/-!
# Escape rates and protected tilts of irreducible generators

On a nontrivial finite state space, an irreducible generator has a genuine
outgoing jump from every state. Hence its escape rates are strictly positive,
and the positive-rate path construction requires no extra hypothesis.
-/

namespace NCG.IrreducibleGeneratorEscape

open DrivenProcess DrivenProcess.FinitePath MetzlerExponentialPositivity
open MetzlerIrreducibilityTransport

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A vertex with no positive off-diagonal edge cannot reach another vertex. -/
theorem path_endpoint_eq_of_no_offDiag_edge (A : Matrix S S ℝ) (i : S)
    (hi : ∀ j, i ≠ j → ¬ 0 < A i j)
    {j : S} (p : @Quiver.Path S A.toQuiver i j) : i = j := by
  letI : Quiver S := Matrix.toQuiver A
  induction p with
  | nil => rfl
  | @cons b c q e ih =>
    by_cases hbc : b = c
    · exact ih.trans hbc
    · exact False.elim (hi c (ih ▸ hbc) (ih ▸ e.down))

/-- Irreducibility on at least two states forces a positive outgoing
off-diagonal entry in every row, not merely a positive diagonal loop. -/
theorem exists_pos_offDiag_of_isIrreducible [Nontrivial S]
    (A : Matrix S S ℝ) (hA : A.IsIrreducible) (i : S) :
    ∃ j, i ≠ j ∧ 0 < A i j := by
  by_contra! hn
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨p, _⟩ := hA.connected i j
  exact hji (path_endpoint_eq_of_no_offDiag_edge A i
    (fun j hij => not_lt_of_ge (hn j hij)) p).symm

/-- An irreducible finite generator on a nontrivial state space has
strictly positive physical escape rates. -/
theorem escapeRate_pos [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hirr : IsIrreducibleMetzler L) (i : S) : 0 < escapeRate L i := by
  obtain ⟨j, hij, hpos⟩ := exists_pos_offDiag_of_isIrreducible
    (diagonalShift L (canonicalDiagonalShift L)) hirr i
  have hLpos : 0 < L i j := by
    simpa [diagonalShift, Matrix.one_apply, hij] using hpos
  unfold escapeRate
  apply lt_of_lt_of_le hLpos
  exact Finset.single_le_sum
    (fun y hy => hL.offDiag_nonneg i y (Finset.ne_of_mem_erase hy).symm)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)

/-- At zero tilt, the protected tilted matrix is exactly the generator. -/
theorem tilt_zero (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) :
    tilt L v g 0 = L := by
  ext i j
  by_cases hij : i = j <;> simp [tilt, hij]

/-- Original-generator irreducibility supplies irreducibility at every
protected tilt parameter. -/
theorem tilt_isIrreducibleMetzler [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    IsIrreducibleMetzler (tilt L v g k) := by
  apply tilt_isIrreducibleMetzler_of_base L hL v g 0 k
  simpa only [tilt_zero] using hirr

end NCG.IrreducibleGeneratorEscape
