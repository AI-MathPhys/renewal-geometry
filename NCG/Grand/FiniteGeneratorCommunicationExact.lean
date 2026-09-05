/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerIrreducibilityTransportExact

/-!
# Standard irreducibility of finite generators, including one-state chains

Every state is reachable from every other by positive-rate edges. A path of
length zero is allowed from a state to itself, as required for the singleton
zero generator. On nontrivial carriers this is equivalent to the existing
shifted-Metzler irreducibility certificate.
-/

namespace NCG.FiniteGeneratorCommunication

open DrivenProcess MetzlerExponentialPositivity MetzlerIrreducibilityTransport

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Standard reachability irreducibility, allowing the empty path to oneself. -/
def IsCommunicating (L : Matrix S S ℝ) : Prop :=
  ∀ i j : S, Nonempty (@Quiver.Path S L.toQuiver i j)

theorem isCommunicating_of_subsingleton [Subsingleton S] (L : Matrix S S ℝ) :
    IsCommunicating L := by
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  exact ⟨@Quiver.Path.nil S L.toQuiver i⟩

theorem isCommunicating_of_isIrreducibleMetzler
    (L : Matrix S S ℝ) (hirr : IsIrreducibleMetzler L) : IsCommunicating L := by
  let B := diagonalShift L (canonicalDiagonalShift L)
  have hs : ∀ i j, i ≠ j → (0 < B i j ↔ 0 < L i j) := by
    intro i j hij
    simp [B, diagonalShift, Matrix.one_apply, hij]
  intro i j
  obtain ⟨p, _⟩ := hirr.connected i j
  exact ⟨transportPath B L hs p⟩

/-- On at least two states, standard generator irreducibility supplies the
existing Metzler certificate, including positive-length return cycles. -/
theorem isIrreducibleMetzler_of_isCommunicating [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hconn : IsCommunicating L) :
    IsIrreducibleMetzler L := by
  let B := diagonalShift L (canonicalDiagonalShift L)
  have hs : ∀ i j, i ≠ j → (0 < L i j ↔ 0 < B i j) := by
    intro i j hij
    simp [B, diagonalShift, Matrix.one_apply, hij]
  refine ⟨canonicalDiagonalShift_entrywiseNonnegative L hL.offDiag_nonneg, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    obtain ⟨u, hui⟩ := exists_ne i
    obtain ⟨p⟩ := hconn i u
    obtain ⟨q⟩ := hconn u i
    letI : Quiver S := B.toQuiver
    let p' := transportPath L B hs p
    let q' := transportPath L B hs q
    refine ⟨@Quiver.Path.comp S B.toQuiver i u i p' q', ?_⟩
    rw [Quiver.Path.length_comp]
    exact Nat.add_pos_left (transportPath_length_pos_of_ne L B hs hui.symm p) _
  · obtain ⟨p⟩ := hconn i j
    exact ⟨transportPath L B hs p, transportPath_length_pos_of_ne L B hs hij p⟩

theorem isCommunicating_iff_isIrreducibleMetzler [Nontrivial S]
    (L : Matrix S S ℝ) (hL : IsGenerator L) :
    IsCommunicating L ↔ IsIrreducibleMetzler L :=
  ⟨isIrreducibleMetzler_of_isCommunicating L hL,
    isCommunicating_of_isIrreducibleMetzler L⟩

end

end NCG.FiniteGeneratorCommunication
