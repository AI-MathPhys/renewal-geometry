/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minimality and transport of the canonical screen
  (`thm:GT-canonical-screen`, Gran-Tensor manuscript)

* `gt_canonical_screen`: in the reduced (simultaneously
  diagonal) model — `A` with spectrum `a : n → ℝ`, a
  commuting reducing screen given by its indicator
  `z : n → Prop`, and the canonical screen
  `Z_β(A) = 1{a < β}` —
  (i) the boxed SC.2 criterion:
      `A ⪰ β(1-Z) ⟺ Z ⊇ Z_β(A)` — the margin holds off
      the screen exactly when the screen contains every
      sub-threshold direction;
  (ii) minimality: any screen satisfying the margin has
      rank (cardinality) at least that of `Z_β(A)` —
      `Z_β(A)` is the minimum-rank reducing screen on
      which the margin can hold.

The reduction of a commuting projection pair `(A, Z)` to
the simultaneous diagonal model is the spectral theorem;
the boxed SC.3 perturbation clause (rank stability and
`2ε/(g-ε)` transport under a spectral gap) is the
manuscript's Davis–Kahan layer.
-/

open Finset

namespace NCG

/-- `thm:GT-canonical-screen` (SC.2 and minimality, in
the reduced diagonal model). -/
theorem gt_canonical_screen {n : Type} [Fintype n]
    (a : n → ℝ) (β : ℝ) (z : n → Prop)
    [DecidablePred z] :
    -- (i) the boxed SC.2 margin ⟺ screen-containment
    ((∀ i, ¬ z i → β ≤ a i)
      ↔ (∀ i, a i < β → z i))
    -- (ii) minimality: any margin screen dominates the
    -- canonical one in rank
    ∧ ((∀ i, ¬ z i → β ≤ a i) →
        (univ.filter (fun i => a i < β)).card
          ≤ (univ.filter (fun i => z i)).card) := by
  constructor
  · constructor
    · intro h i hai
      by_contra hz
      exact absurd (h i hz) (not_le.mpr hai)
    · intro h i hz
      by_contra hlt
      exact hz (h i (not_le.mp hlt))
  · intro h
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ i, ?_⟩
    by_contra hz
    exact absurd (h i hz) (not_le.mpr hi.2)

end NCG
