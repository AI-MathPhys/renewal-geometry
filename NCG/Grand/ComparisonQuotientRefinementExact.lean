/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ComparisonSignatureQuotient

/-!
# Canonical finite refinement of the comparison quotient

This module completes the finite-refinement clause of
`thm:accepted-comparison-quotient`.  Once every admitted future actual and
comparator cylinder has been assembled into the two signatures, refinement of
the indiscrete initial record by that complete joint signature is terminal.
It takes zero strict splits when the signature is constant and one otherwise;
the latter can occur only when the finite initial state space has at least two
points.  Thus the canonical reconstruction uses at most `|Omega| - 1` strict
splits, and its terminal fibres are literally the comparison quotient fibres.
-/

namespace NCG
namespace ComparisonSignatureQuotient

/-- Number of strict splits made by the canonical complete-signature
refinement of the indiscrete initial record. -/
noncomputable def comparisonRefinementRounds
    {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) : ℕ := by
  classical
  exact if ∀ x y, comparisonSignature actual comparator x =
      comparisonSignature actual comparator y then 0 else 1

/-- The terminal record of complete-signature refinement identifies exactly
the histories with the same actual and comparator future rows. -/
theorem comparisonQuotient_terminal_fibres
    {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator)
    (x y : Omega) :
    quotientMap actual comparator x = quotientMap actual comparator y ↔
      comparisonSignature actual comparator x =
        comparisonSignature actual comparator y := by
  exact Subtype.ext_iff

/-- Zero rounds means that the indiscrete initial record was already terminal. -/
theorem comparisonRefinementRounds_eq_zero_iff
    {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    comparisonRefinementRounds actual comparator = 0 ↔
      ∀ x y, quotientMap actual comparator x =
        quotientMap actual comparator y := by
  classical
  by_cases h : ∀ x y, comparisonSignature actual comparator x =
      comparisonSignature actual comparator y
  · have hr : comparisonRefinementRounds actual comparator = 0 := by
      unfold comparisonRefinementRounds
      exact if_pos h
    rw [hr]
    simp only [true_iff]
    intro x y
    exact (comparisonQuotient_terminal_fibres actual comparator x y).2 (h x y)
  · have hr : comparisonRefinementRounds actual comparator = 1 := by
      unfold comparisonRefinementRounds
      exact if_neg h
    rw [hr]
    simp only [Nat.one_ne_zero, false_iff]
    intro hall
    apply h
    intro x y
    exact (comparisonQuotient_terminal_fibres actual comparator x y).1 (hall x y)

/-- One round means that the complete signature makes a genuine strict split
of the indiscrete initial record. -/
theorem comparisonRefinementRounds_eq_one_iff
    {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    comparisonRefinementRounds actual comparator = 1 ↔
      ∃ x y, quotientMap actual comparator x ≠
        quotientMap actual comparator y := by
  classical
  by_cases h : ∀ x y, comparisonSignature actual comparator x =
      comparisonSignature actual comparator y
  · have hr : comparisonRefinementRounds actual comparator = 0 := by
      unfold comparisonRefinementRounds
      exact if_pos h
    rw [hr]
    simp only [Nat.zero_ne_one, false_iff]
    rintro ⟨x, y, hxy⟩
    exact hxy ((comparisonQuotient_terminal_fibres actual comparator x y).2
      (h x y))
  · have hr : comparisonRefinementRounds actual comparator = 1 := by
      unfold comparisonRefinementRounds
      exact if_neg h
    rw [hr]
    simp only [true_iff]
    push Not at h
    obtain ⟨x, y, hxy⟩ := h
    exact ⟨x, y, fun hq ↦ hxy
      ((comparisonQuotient_terminal_fibres actual comparator x y).1 hq)⟩

/-- The complete-signature refinement satisfies the manuscript's sharp finite
termination bound. -/
theorem comparisonRefinementRounds_le_card_sub_one
    {Omega Actual Comparator : Type*} [Fintype Omega] [Nonempty Omega]
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    comparisonRefinementRounds actual comparator ≤
      Fintype.card Omega - 1 := by
  classical
  by_cases hconstant : ∀ x y, comparisonSignature actual comparator x =
      comparisonSignature actual comparator y
  · have hzero : comparisonRefinementRounds actual comparator = 0 := by
      unfold comparisonRefinementRounds
      exact if_pos hconstant
    rw [hzero]
    exact Nat.zero_le _
  · have hone : comparisonRefinementRounds actual comparator = 1 := by
      unfold comparisonRefinementRounds
      exact if_neg hconstant
    push Not at hconstant
    obtain ⟨x, y, hxy⟩ := hconstant
    have hxyq : quotientMap actual comparator x ≠
        quotientMap actual comparator y := fun hq ↦ hxy
      ((comparisonQuotient_terminal_fibres actual comparator x y).1 hq)
    have hxy' : x ≠ y := by
      intro h
      subst y
      exact hxyq rfl
    letI : Nontrivial Omega := ⟨⟨x, y, hxy'⟩⟩
    rw [hone]
    have hcard : 1 < Fintype.card Omega := Fintype.one_lt_card
    omega

/-- Exact manuscript package: factorization and the universal initial property,
together with an actual finite refinement certificate whose terminal relation
is the comparison relation and whose strict-round count is at most
`|Omega| - 1`. -/
theorem canonical_initial_comparison_quotient_exact
    {Omega Actual Comparator : Type*} [Fintype Omega] [Nonempty Omega]
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    (actualRow ∘ quotientMap actual comparator = actual ∧
      comparatorRow ∘ quotientMap actual comparator = comparator ∧
      (∀ {Theta : Type*} (record : Omega → Theta),
        Function.Surjective record →
        ∀ (actualOn : Theta → Actual) (comparatorOn : Theta → Comparator),
        actualOn ∘ record = actual →
        comparatorOn ∘ record = comparator →
        ∃! g : Theta → Quotient actual comparator,
          Function.Surjective g ∧
            g ∘ record = quotientMap actual comparator))
    ∧ comparisonRefinementRounds actual comparator ≤
        Fintype.card Omega - 1
    ∧ (∀ x y, quotientMap actual comparator x =
          quotientMap actual comparator y ↔
        comparisonSignature actual comparator x =
          comparisonSignature actual comparator y)
    ∧ (comparisonRefinementRounds actual comparator = 0 ↔
        ∀ x y, quotientMap actual comparator x =
          quotientMap actual comparator y)
    ∧ (comparisonRefinementRounds actual comparator = 1 ↔
        ∃ x y, quotientMap actual comparator x ≠
          quotientMap actual comparator y) := by
  refine ⟨canonical_initial_comparison_quotient actual comparator,
    comparisonRefinementRounds_le_card_sub_one actual comparator, ?_,
    comparisonRefinementRounds_eq_zero_iff actual comparator,
    comparisonRefinementRounds_eq_one_iff actual comparator⟩
  exact comparisonQuotient_terminal_fibres actual comparator

end ComparisonSignatureQuotient
end NCG
