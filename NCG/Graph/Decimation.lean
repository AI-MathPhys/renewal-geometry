/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.BettiNumber

/-!
# Quotient decimation is non-increasing in `b₁`

**Lemma `lem:quotient-decimation`**: a quotient-type decimation
(identifying predictive classes, contracting or identifying edges,
deleting transient structure) induces a **surjection** from the original
cycle space onto the decimated cycle space, so the first Betti number
cannot increase: `b₁(𝒟G) ≤ b₁(G)`.  Consequently no ordinary renewal
coarse-graining can implement the access fixed-point map, which grows
like `2^b/e` (`NCG.not_accessFixedPoint_of_five_le` — Proposition
`prop:decimation-cannot-access`).

We formalise the load-bearing implication: any decimation whose induced
map on `H¹(·, ℤ/2)` is surjective decreases neither Betti rank
(`NCG.Multigraph.betti_le_of_surjective`) nor collapses in the wrong
direction on sector counts
(`NCG.Multigraph.card_H1_le_of_surjective`). -/

namespace NCG.Multigraph

variable {G G' : Multigraph}

/-- **Lemma `lem:quotient-decimation`**: if a decimation induces a
surjection of `ℤ/2` cycle spaces `H¹(G) ↠ H¹(𝒟G)`, the Betti rank is
non-increasing, `b₁(𝒟G) ≤ b₁(G)`. -/
theorem betti_le_of_surjective [Finite G.E]
    (f : H1 G →ₗ[ZMod 2] H1 G') (hf : Function.Surjective f) :
    Module.finrank (ZMod 2) (H1 G')
      ≤ Module.finrank (ZMod 2) (H1 G) :=
  LinearMap.finrank_le_finrank_of_surjective hf

/-- Sector counts are non-increasing under decimation
(Lemma `lem:quotient-decimation`, cardinality form): the number `2^{b₁}`
of signed sectors cannot grow. -/
theorem card_H1_le_of_surjective [Finite G.E]
    (f : H1 G →ₗ[ZMod 2] H1 G') (hf : Function.Surjective f) :
    Nat.card (H1 G') ≤ Nat.card (H1 G) :=
  Nat.card_le_card_of_surjective ⇑f hf

end NCG.Multigraph
