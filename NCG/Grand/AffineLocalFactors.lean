/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact local obstruction and Chinese-remainder assembly
  (`thm:GT-affine-local-factors`,
  Gran-Tensor manuscript)

* `affine_local_positivity`: the boxed local criterion —
  the local density `β_p` (an average of nonnegative local
  indicators) is positive exactly when one residue class
  is unobstructed (`∃ n, p ∤ ∏ψᵢ(n)`).

* `affine_local_crt_factor`: the boxed CRT assembly — when
  a residue equivalence `e : A ≃ B × C` matches the
  unobstructedness predicates (`P_A x ↔ P_B ∧ P_C` through
  `e`), the counts multiply,
  `#{P_A} = #{P_B}·#{P_C}`, hence the densities factor,
  `β_{bc} = β_b β_c` — iterated over the prime
  factorization this is the boxed
  `β_q = ∏_{p|q} β_p` for squarefree `q`.

The instantiation of `e` with the Chinese remainder ring
equivalence `(ZMod (mn))^d ≃ (ZMod m)^d × (ZMod n)^d` for
coprime `m, n`, the compatibility of the affine-polynomial
unobstructedness predicate with it (naturality of integer
polynomials under ring maps), and the convergence and
nonvanishing of the infinite singular product are the
manuscript's arithmetic layer.
-/

open Finset

namespace NCG

/-- Local positivity of an averaged nonnegative
indicator. -/
theorem affine_local_positivity {α : Type} [Fintype α]
    [Nonempty α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 < (Fintype.card α : ℝ)⁻¹ * ∑ x, w x
      ↔ ∃ x, 0 < w x := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : ∀ x ∈ univ, w x = 0 := fun x _ =>
      le_antisymm (hall x) (hw x)
    rw [Finset.sum_eq_zero hzero, mul_zero] at h
    exact lt_irrefl 0 h
  · rintro ⟨x, hx⟩
    have hsum : 0 < ∑ y, w y :=
      Finset.sum_pos' (fun y _ => hw y)
        ⟨x, Finset.mem_univ x, hx⟩
    positivity

/-- CRT factorization of unobstructed counts and
densities. -/
theorem affine_local_crt_factor {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C)
    (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    [DecidablePred PA] [DecidablePred PB]
    [DecidablePred PC]
    (hcompat : ∀ x, PA x
      ↔ (PB (e x).1 ∧ PC (e x).2)) :
    -- the boxed count factorization
    ((univ.filter PA).card
      = (univ.filter PB).card * (univ.filter PC).card)
    -- hence the boxed density factorization
    ∧ ((Fintype.card A : ℝ)⁻¹ * (univ.filter PA).card
      = ((Fintype.card B : ℝ)⁻¹
          * (univ.filter PB).card)
        * ((Fintype.card C : ℝ)⁻¹
          * (univ.filter PC).card)
      ∨ Fintype.card B = 0 ∨ Fintype.card C = 0) := by
  have hcount : (univ.filter PA).card
      = (univ.filter PB).card
        * (univ.filter PC).card := by
    have hbij : (univ.filter PA).card
        = (univ.filter
            (fun p : B × C => PB p.1 ∧ PC p.2)).card := by
      apply Finset.card_bij (fun x _ => e x)
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _,
          (hcompat x).mp hx.2⟩
      · intro x hx y hy hxy
        exact e.injective hxy
      · intro p hp
        refine ⟨e.symm p, ?_, by simp⟩
        rw [Finset.mem_filter] at hp ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hcompat]
        simpa using hp.2
    rw [hbij, ← Finset.card_product]
    congr 1
    ext p
    simp [Finset.mem_filter, Finset.mem_product]
  refine ⟨hcount, ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card B) with hB | hB
  · exact Or.inr (Or.inl hB)
  rcases Nat.eq_zero_or_pos (Fintype.card C) with hC | hC
  · exact Or.inr (Or.inr hC)
  left
  have hcardA : Fintype.card A
      = Fintype.card B * Fintype.card C := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hBne : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hB
  have hCne : (Fintype.card C : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hC
  rw [hcount, hcardA]
  push_cast
  field_simp

end NCG
