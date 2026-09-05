/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pairwise simplicity and pair-homogeneous completion
  (`thm:dimension-pairwise-completion`,
  Gran-Tensor manuscript)

* `dimension_pairwise_completion`: clause (iii), the boxed
  `G_rel = K_N` — if a source-independent endpoint
  operation generates a permutation group `Γ` transitive
  on unordered pairs, and the relation set is nonempty
  (off-diagonal) and `Γ`-invariant, then the
  relation-colour-free skeleton contains every unordered
  pair of distinct events: the complete graph.

Clauses (i)–(ii) — that the primitive boundary type is
pairwise (each relation an oriented edge with incidence
`e_t - e_s`) and that same-endpoint edges are either
identified or an independently readable relation-colour
source after future minimization — are the manuscript's
cell-normalization layer; the countermodel content
(higher-arity cells need a different primitive boundary
type) rides on the dimension chapter's other records.
-/

namespace NCG

/-- `thm:dimension-pairwise-completion` (iii): the boxed
`G_rel = K_N`. -/
theorem dimension_pairwise_completion {X : Type*}
    (Γ : Subgroup (Equiv.Perm X)) (R : Set (Sym2 X))
    -- Γ is transitive on unordered pairs of distinct
    -- events
    (htrans : ∀ p q : Sym2 X, ¬p.IsDiag → ¬q.IsDiag →
      ∃ g ∈ Γ, Sym2.map (⇑g) p = q)
    -- the relation set is Γ-invariant
    (hRinv : ∀ g ∈ Γ, ∀ p ∈ R, Sym2.map (⇑g) p ∈ R)
    -- and contains at least one genuine (off-diagonal)
    -- relation
    (hne : ∃ p ∈ R, ¬p.IsDiag) :
    -- the skeleton is the complete graph
    ∀ q : Sym2 X, ¬q.IsDiag → q ∈ R := by
  intro q hq
  obtain ⟨p, hpR, hpd⟩ := hne
  obtain ⟨g, hgΓ, hgp⟩ := htrans p q hpd hq
  rw [← hgp]
  exact hRinv g hgΓ p hpR

end NCG
