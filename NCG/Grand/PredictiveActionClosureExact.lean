/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GlobalWellFoundednessExact

/-!
# Source-anchored predictive action closure: termination on the finite head

Machinery for `thm:GT-source-anchored-predictive-action-closure` — the
record-local termination argument on top of the five anchor records: on the
bounded action-complete head produced by (P1)–(P2), an infinite nonterminal
history must revisit a state, producing an explicit **recurrent circulation**
witness (a strict cycle); when every recurrent component of the
obstruction-return graph is closed — the passing branch of (P4), the proved
`thm:GT-global-well-foundedness-alternative` — no such cycle exists among
nonterminal states, so **no infinite nonterminal history exists**.

* `walk_transGen`: a strictly later point of a history is reached by at least
  one step;
* `exists_revisit`: every infinite history on a finite head revisits some
  state at two distinct times;
* `infinite_history_gives_circulation`: an infinite history yields a strict
  cycle — the recurrent-circulation failure witness;
* `no_infinite_history_of_closed`: if no nonterminal state carries a strict
  cycle, there is no infinite nonterminal history;
* `predictive_action_closure`: the record-level alternative — either no
  infinite nonterminal history exists, or an explicit circulation witness is
  returned.
-/

namespace NCG
namespace PredictiveClosure

open NCG.GlobalWellFoundedness

variable {V : Type*} (step : V → V → Prop)

/-- A strictly later point of a history is reached by at least one step. -/
theorem walk_transGen {w : ℕ → V} (hw : IsWalk step w) {n m : ℕ}
    (hnm : n < m) : Relation.TransGen step (w n) (w m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Relation.TransGen.single (hw n)
  | succ m _ ih => exact ih.tail (hw m)

/-- Every infinite history on a finite head revisits some state. -/
theorem exists_revisit [Finite V] (w : ℕ → V) :
    ∃ (v : V) (n m : ℕ), n < m ∧ w n = v ∧ w m = v := by
  obtain ⟨v, hv⟩ := exists_cofinal_state w
  obtain ⟨n, hn⟩ := hv.nonempty
  obtain ⟨m, hm, hnm⟩ := hv.exists_gt n
  exact ⟨v, n, m, hnm, hn, hm⟩

/-- **The recurrent-circulation witness**: an infinite history on a finite
head yields a strict cycle through one of its states. -/
theorem infinite_history_gives_circulation [Finite V] {w : ℕ → V}
    (hw : IsWalk step w) : ∃ v : V, Relation.TransGen step v v := by
  obtain ⟨v, n, m, hnm, hn, hm⟩ := exists_revisit w
  refine ⟨v, ?_⟩
  have h := walk_transGen step hw hnm
  rwa [hn, hm] at h

/-- **The passing branch**: when no state of the closed head carries a strict
cycle — every recurrent component of the obstruction-return graph is closed by
the (P4) alternative — no infinite nonterminal history exists. -/
theorem no_infinite_history_of_closed [Finite V]
    (hclosed : ∀ v : V, ¬ Relation.TransGen step v v) :
    ¬ ∃ w : ℕ → V, IsWalk step w := by
  rintro ⟨w, hw⟩
  obtain ⟨v, hv⟩ := infinite_history_gives_circulation step hw
  exact hclosed v hv

/-- **The record-level alternative**: on the bounded action-complete head,
either no infinite nonterminal history exists, or the construction returns an
explicit recurrent-circulation witness. -/
theorem predictive_action_closure [Finite V] :
    (¬ ∃ w : ℕ → V, IsWalk step w) ∨
      (∃ v : V, Relation.TransGen step v v) := by
  by_cases h : ∃ w : ℕ → V, IsWalk step w
  · obtain ⟨w, hw⟩ := h
    exact Or.inr (infinite_history_gives_circulation step hw)
  · exact Or.inl h

end PredictiveClosure
end NCG
