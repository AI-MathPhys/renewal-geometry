/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Möbius inversion of subset actions and the physical
  subset secants (`thm:GT-Mobius-inversion` and
  `thm:GT-subset-secants`, Gran-Tensor manuscript)

* `gt_mobius_inversion_core`: the two-way Möbius/zeta
  sandwich on the boolean lattice of a finite index set —
  summing the alternating transforms over all subsets
  returns the original assignment.

* `gt_mobius_inversion`: the boxed display
  `L_A = ∑_{∅ ≠ B ⊆ A} K_B` for the signed connected
  interactions `K_B = ∑_{C ⊆ B} (-1)^{|B|-|C|} L_C`
  (vacuum-normalized `L_∅ = 0`).

* `gt_subset_secants`: the boxed secant compiler
  `𝔥(p_B) = ∑_{C ⊆ B} c_C` for the alternating secants
  `c_C`, and the inert-slot clause — if one intervention
  slot acts trivially on the whole cube, every secant
  containing that slot vanishes (pairing `C ↔ C ∪ {i}`).

The face-vanishing clause `(J_C^A)^* K_A J_C^A = 0` of the
Möbius theorem and the secants' product/limit clauses
(tensorization for independent occurrences, the
`2∂_A√p_θ` small-cube limit, and the shorted Fisher Gram)
are the manuscript's surrounding layers.
-/

open Finset

namespace NCG

/-- Alternating sum over a powerset interval `[D, B]`. -/
theorem gt_powerset_interval_alternating {ι : Type*}
    [DecidableEq ι] {D B : Finset ι} (hDB : D ⊆ B) :
    ∑ C ∈ B.powerset.filter (fun C => D ⊆ C),
        (-1 : ℤ) ^ (#C - #D)
      = if D = B then 1 else 0 := by
  have hbij : ∑ C ∈ B.powerset.filter (fun C => D ⊆ C),
      (-1 : ℤ) ^ (#C - #D)
      = ∑ E ∈ (B \ D).powerset, (-1 : ℤ) ^ #E := by
    refine Finset.sum_nbij' (fun C => C \ D)
      (fun E => D ∪ E) ?_ ?_ ?_ ?_ ?_
    · intro C hC
      rw [Finset.mem_filter, Finset.mem_powerset] at hC
      exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset_sdiff hC.1
          (Finset.Subset.refl D))
    · intro E hE
      rw [Finset.mem_powerset] at hE
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hDB
        (hE.trans (Finset.sdiff_subset)),
        Finset.subset_union_left⟩
    · intro C hC
      rw [Finset.mem_filter, Finset.mem_powerset] at hC
      exact Finset.union_sdiff_of_subset hC.2
    · intro E hE
      rw [Finset.mem_powerset] at hE
      exact Finset.union_sdiff_cancel_left
        (Finset.disjoint_of_subset_right hE
          (Finset.sdiff_disjoint).symm)
    · intro C hC
      rw [Finset.mem_filter, Finset.mem_powerset] at hC
      rw [Finset.card_sdiff,
        Finset.inter_eq_left.mpr hC.2]
  rw [hbij, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : D = B
  · simp [h]
  · have h1 : ¬(B \ D = ∅) := fun hc =>
      h (Finset.Subset.antisymm hDB
        (Finset.sdiff_eq_empty_iff_subset.mp hc))
    simp [h, h1]

/-- Möbius/zeta sandwich: summing the alternating
transforms over all subsets returns the assignment. -/
theorem gt_mobius_inversion_core {ι M : Type*}
    [AddCommGroup M]
    (f : Finset ι → M) (B : Finset ι) :
    ∑ C ∈ B.powerset, ∑ D ∈ C.powerset,
        (-1 : ℤ) ^ (#C - #D) • f D = f B := by
  classical
  rw [Finset.sum_comm' (t' := B.powerset)
    (s' := fun D => B.powerset.filter (fun C => D ⊆ C))
    (fun C D => by
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, h2.trans h1⟩,
        fun ⟨⟨h1, h2⟩, _⟩ => ⟨h1, h2⟩⟩)]
  rw [Finset.sum_congr rfl (fun D hD => by
    rw [← Finset.sum_smul,
      gt_powerset_interval_alternating
        (Finset.mem_powerset.mp hD)])]
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' B.powerset B f]
  simp

/-- `thm:GT-Mobius-inversion` (the boxed display). -/
theorem gt_mobius_inversion {ι M : Type*} [DecidableEq ι]
    [AddCommGroup M]
    (L : Finset ι → M) (hL0 : L ∅ = 0) (A : Finset ι) :
    L A = ∑ B ∈ A.powerset.filter (fun B => B ≠ ∅),
        ∑ C ∈ B.powerset, (-1 : ℤ) ^ (#B - #C) • L C := by
  rw [← gt_mobius_inversion_core L A]
  exact (Finset.sum_filter_of_ne (fun B _ hne => by
    rintro rfl
    exact hne (by simp [hL0]))).symm

/-- `thm:GT-subset-secants` (secant compiler + inert-slot
clause). -/
theorem gt_subset_secants {ι M : Type*} [DecidableEq ι]
    [AddCommGroup M] (h : Finset ι → M) :
    -- the boxed compiler 𝔥(p_B) = ∑_{C ⊆ B} c_C
    (∀ B : Finset ι,
      h B = ∑ C ∈ B.powerset, ∑ D ∈ C.powerset,
        (-1 : ℤ) ^ (#C - #D) • h D)
    -- an operationally inert slot kills every secant
    -- containing it
    ∧ (∀ (B : Finset ι) (i : ι), i ∈ B →
        (∀ C, i ∉ C → h (insert i C) = h C) →
        ∑ D ∈ B.powerset, (-1 : ℤ) ^ (#B - #D) • h D
          = 0) := by
  constructor
  · intro B
    exact (gt_mobius_inversion_core h B).symm
  · intro B i hiB hinert
    have hB : B = insert i (B.erase i) :=
      (Finset.insert_erase hiB).symm
    have hni : i ∉ B.erase i := Finset.notMem_erase i B
    rw [hB, Finset.sum_powerset_insert hni,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro D hD
    have hDs : D ⊆ B.erase i := Finset.mem_powerset.mp hD
    have hiD : i ∉ D := fun hc => hni (hDs hc)
    rw [hinert D hiD, Finset.card_insert_of_notMem hiD,
      Finset.card_insert_of_notMem hni]
    have hle : #D ≤ #(B.erase i) :=
      Finset.card_le_card hDs
    have e1 : #(B.erase i) + 1 - #D
        = (#(B.erase i) - #D) + 1 := by omega
    have e2 : #(B.erase i) + 1 - (#D + 1)
        = #(B.erase i) - #D := by omega
    rw [e1, e2, pow_succ]
    simp only [mul_neg_one, neg_smul]
    abel

end NCG
