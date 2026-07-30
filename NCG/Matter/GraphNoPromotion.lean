/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The graph-wide no-promotion theorem
  (`thm:graph-wide-no-promotion-main`, SM_emergence)

Deleting the predictive hubs `{0,1}` from the two-cell graph leaves
`G₂[{2,3,4,5}] = {2-3} ⊔ {4-5}`: the private graph is a perfect
matching.

* `privAdj_matching` — the matching property: a private vertex has a
  unique private neighbour (`privAdj a b → privAdj b c → a = c`);
* `no_three_private_steps` — a nonbacktracking private walk of three
  steps is impossible (the killed transfer satisfies `N² = 0`; the
  resolvent identity `(I - zN)⁻¹ = I + zN` is
  `NCG.nilpotent_depth_inverse`);
* `no_promotion_exactly_three` — every predictive-connected
  hub-to-hub word whose internal private segment meets a bridge edge
  has an internal segment of length exactly two, i.e. exactly three
  transfers (`hub → p₀ → p₁ → hub`): no longer connected word can be
  promoted to the same leading record order, and longer complete
  words contain an internal hub return.
-/

namespace NCG

/-- The private (bridge) adjacency of the two-cell graph after hub
deletion: the perfect matching `{2-3} ⊔ {4-5}` on `Fin 6`. -/
def privAdj : Fin 6 → Fin 6 → Prop := fun a b =>
  (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 4 ∧ b = 5) ∨
    (a = 5 ∧ b = 4)

instance : DecidableRel privAdj := fun a b => by
  unfold privAdj
  infer_instance

/-- The private graph is a perfect matching: private neighbours are
unique. -/
theorem privAdj_matching :
    ∀ a b c : Fin 6, privAdj a b → privAdj b c → a = c := by
  decide

/-- `N² = 0`: a nonbacktracking private walk cannot make three
steps. -/
theorem no_three_private_steps (p0 p1 p2 : Fin 6)
    (h1 : privAdj p0 p1) (h2 : privAdj p1 p2) (hnb : p2 ≠ p0) :
    False :=
  hnb ((privAdj_matching p0 p1 p2 h1 h2).symm)

/-- `thm:graph-wide-no-promotion-main`: a hub-to-hub word whose
internal private segment `p 0, …, p (k-1)` is consecutive along
private edges, nonbacktracking, and meets a bridge edge (`k ≥ 2`)
has internal length exactly two — the word has exactly three
transfers. -/
theorem no_promotion_exactly_three (k : ℕ) (p : ℕ → Fin 6)
    (hadj : ∀ i, i + 1 < k → privAdj (p i) (p (i + 1)))
    (hnb : ∀ i, i + 2 < k → p (i + 2) ≠ p i)
    (hbridge : 2 ≤ k) : k = 2 := by
  by_contra hne
  have hk3 : 3 ≤ k := by omega
  exact no_three_private_steps (p 0) (p 1) (p 2)
    (hadj 0 (by omega)) (hadj 1 (by omega)) (hnb 0 (by omega))

end NCG
