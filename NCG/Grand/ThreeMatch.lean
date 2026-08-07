/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Microscopic transversality of nonzero near collisions
  (`thm:ar-three-match`, Gran-Tensor manuscript)

* `triple_transversality`: the twelve-slot combinatorics — if at
  most two of the twelve occupied atom slots can be matched by
  equal numerical values, then after any predetermined partition
  of the twelve slots into four triples, at least two entire
  triples contain no matched atom (the touched triples are at
  most the matched slots);
* `matched_triples_le`: the counting core — the image of the
  matched-slot set under the partition map has cardinality at
  most the number of matched slots.

Rendering disclosed: the number-theoretic input — that a nonzero
near collision `0 < |n-n'| ≤ Y^{1/5+o(1)}` of saturated
endpoints permits at most two equal-value atom pairings (the
divisor/spacing estimate on the twelve atom values) — is the
manuscript's analytic layer; the pigeonhole transfer from
`≤ 2` matched slots to `≥ 2` untouched triples on each endpoint
is proved here.
-/

open Finset

namespace NCG

/-- Counting core: the triples touched by the matched slots are
at most the matched slots themselves. -/
theorem matched_triples_le (P : Fin 12 → Fin 4)
    (M : Finset (Fin 12)) :
    (M.image P).card ≤ M.card :=
  Finset.card_image_le

/-- Boxed twelve-slot transversality: at most two matched slots
leave at least two entire triples unmatched, for any
predetermined partition of the twelve slots into four
triples. -/
theorem triple_transversality (P : Fin 12 → Fin 4)
    (M : Finset (Fin 12)) (hM : M.card ≤ 2) :
    2 ≤ (Finset.univ.filter
      (fun t : Fin 4 => ∀ s ∈ M, P s ≠ t)).card := by
  classical
  have huntouched : Finset.univ.filter
      (fun t : Fin 4 => ∀ s ∈ M, P s ≠ t)
      = Finset.univ \ M.image P := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_image]
    constructor
    · intro h hex
      obtain ⟨s, hs, hPs⟩ := hex
      exact h s hs hPs
    · intro h s hs hPs
      exact h ⟨s, hs, hPs⟩
  rw [huntouched, Finset.card_sdiff]
  have himg : (M.image P ∩ Finset.univ).card ≤ 2 := by
    refine le_trans (Finset.card_le_card
      Finset.inter_subset_left) ?_
    exact le_trans Finset.card_image_le hM
  have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by
    simp
  omega

end NCG
