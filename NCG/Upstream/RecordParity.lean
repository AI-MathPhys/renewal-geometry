/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniqueness of resolved-record parity

Theorem `thm:record-parity-unique` of `manuscripts/renewal_emergence/renewal_emergence.tex`: every
group homomorphism from the permutation group of `k` future-distinct
records to `{±1}` is either the trivial character or the permutation
sign (`perm_hom_eq_one_or_sign`) — all transpositions are conjugate,
a homomorphism into an abelian group is constant on conjugacy
classes, and transpositions generate.  For `k ≥ 2` the sign character
is nontrivial (`sign_ne_one_of_two_le_card`), so determinant parity
is the unique nontrivial one-dimensional real functorial invariant of
reversible record relabellings.  The identification of the sign with
the determinant of the permutation representation on the contrast
module is `NCG.recSign_permMatrix` (`NCG/Graph/RecordOrientation.lean`).
-/

namespace NCG

open Equiv

/-- A homomorphism into an abelian group is constant on conjugacy
classes. -/
theorem monoidHom_eq_of_isConj {G H : Type*} [Group G] [CommGroup H]
    (f : G →* H) {x y : G} (h : IsConj x y) : f x = f y := by
  obtain ⟨c, hc⟩ := h
  have h1 : f ((c : G) * x) = f (y * (c : G)) := congrArg f hc.eq
  rw [map_mul, map_mul] at h1
  have h2 : f (c : G) * f x = f (c : G) * f y := by
    rw [h1, mul_comm]
  exact mul_left_cancel h2

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Theorem `thm:record-parity-unique`**: every group homomorphism
from the permutations of the resolved records to `{±1}` is the
trivial character or the permutation sign. -/
theorem perm_hom_eq_one_or_sign (f : Perm α →* ℤˣ) :
    f = 1 ∨ f = Perm.sign := by
  by_cases hswap : ∀ a b : α, a ≠ b → f (swap a b) = 1
  · left
    refine MonoidHom.ext fun σ => ?_
    rw [MonoidHom.one_apply]
    refine Perm.swap_induction_on σ ?_ ?_
    · exact map_one f
    · intro g x y hxy ih
      rw [map_mul, hswap x y hxy, one_mul, ih]
  · right
    push_neg at hswap
    obtain ⟨a, b, hab, hfab⟩ := hswap
    have hval : f (swap a b) = -1 := by
      rcases Int.units_eq_one_or (f (swap a b)) with h | h
      · exact absurd h hfab
      · exact h
    have hallswap : ∀ c d : α, c ≠ d → f (swap c d) = -1 := by
      intro c d hcd
      rw [← monoidHom_eq_of_isConj f (Perm.isConj_swap hab hcd)]
      exact hval
    refine MonoidHom.ext fun σ => ?_
    refine Perm.swap_induction_on σ ?_ ?_
    · rw [map_one, map_one]
    · intro g x y hxy ih
      rw [map_mul, map_mul, ih, hallswap x y hxy,
        Perm.sign_swap hxy]

/-- **`thm:record-parity-unique`, nontriviality**: for at least two
records the sign character is not the trivial character, so
determinant parity is the unique **nontrivial** one-dimensional real
functorial invariant. -/
theorem sign_ne_one_of_two_le_card (h2 : 1 < Fintype.card α) :
    (Perm.sign : Perm α →* ℤˣ) ≠ 1 := by
  intro hcon
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨σ, hσ⟩ := Perm.sign_surjective α (-1)
  have h1 : (Perm.sign : Perm α →* ℤˣ) σ = 1 := by
    rw [hcon, MonoidHom.one_apply]
  rw [hσ] at h1
  exact absurd h1 (by decide)

end NCG
