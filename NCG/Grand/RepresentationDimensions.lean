/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConstraintCharacter

/-!
# Representation dimensions are not a symmetry duality
  (`countertheorem:representation-dimensions-are-not-a-symmetry-duality`,
   Gran-Tensor manuscript)

* `representation_dimensions_not_duality`: `ℤ/4ℤ` and
  `(ℤ/2ℤ)²` both carry exactly four (necessarily
  one-dimensional) irreducible complex characters — the same
  dimension multiset `{1,1,1,1}` — yet only the first has an
  element of order four, so the two symmetry groups are not
  isomorphic.  The multiset of irreducible representation
  dimensions does not determine the symmetry group.

Rendering disclosed: the character counts are
`Nat.card (G →* ℂˣ) = |G| = 4` via the finite abelian duality
of [[NCG.dual_card]]; that every irreducible complex
representation of an abelian group is one-dimensional (so the
common multiset is `{1,1,1,1}`) is the manuscript's standard
character-theory bookkeeping over these counts.
-/

namespace NCG

/-- `countertheorem:representation-dimensions`: `ℤ/4` and
`(ℤ/2)²` have the same four-fold one-dimensional character
count but only the first has an element of order four; the
dimension multiset does not determine the group. -/
theorem representation_dimensions_not_duality :
    (Nat.card (Multiplicative (ZMod 4) →* ℂˣ) = 4
      ∧ Nat.card (Multiplicative (ZMod 2 × ZMod 2) →* ℂˣ) = 4)
    ∧ addOrderOf (1 : ZMod 4) = 4
    ∧ (∀ x : ZMod 2 × ZMod 2, addOrderOf x ≠ 4)
    ∧ IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  have hall : ∀ y : ZMod 2 × ZMod 2, y + y = 0 := by decide
  have hord2 : ∀ x : ZMod 2 × ZMod 2, addOrderOf x ≠ 4 := by
    intro x h4
    have hdvd : addOrderOf x ∣ 2 :=
      addOrderOf_dvd_of_nsmul_eq_zero
        (by rw [two_nsmul]; exact hall x)
    rw [h4] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  refine ⟨⟨?_, ?_⟩, ZMod.addOrderOf_one 4, hord2, ?_⟩
  · rw [dual_card]
    rw [Nat.card_eq_fintype_card]
    decide
  · rw [dual_card]
    rw [Nat.card_eq_fintype_card]
    decide
  · constructor
    intro e
    have h2 : addOrderOf (e (1 : ZMod 4))
        = addOrderOf (1 : ZMod 4) :=
      addOrderOf_injective e.toAddMonoidHom e.injective 1
    rw [ZMod.addOrderOf_one] at h2
    exact hord2 (e 1) h2

end NCG
