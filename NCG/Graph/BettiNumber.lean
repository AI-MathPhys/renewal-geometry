/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.Cohomology

/-!
# The Betti-number formula `dim H¹ = |E| − |V| + 1` for connected graphs

This file upgrades the bouquet computation of `NCG/Graph/Cohomology.lean`
to **every finite connected multigraph**, completing the graph side of
Theorem `thm:cover`, Corollary `cor:sector-count`, and the boxed
classification `π₀ Enr_min(G) ≅ H¹(G, ℤ/2) ≅ (ℤ/2)^{b₁(G)}` of Theorem
`thm:classification`:

* on a connected graph, the kernel of the coboundary
  `δ : C⁰ → C¹` consists exactly of the constant `0`-cochains
  (`NCG.Multigraph.ker_coboundaryMap`) — a kernel element is
  walk-invariant, and connectivity spreads its base value everywhere;
* rank–nullity then gives the **first Betti number**
  `dim H¹(G, ℤ/2) + |V| = |E| + 1`
  (`NCG.Multigraph.finrank_H1_add_card_vertices`), i.e.
  `b₁ = |E| − |V| + 1`, with no spanning tree ever chosen;
* consequently there are exactly `2^{b₁}` signed sectors
  (`NCG.Multigraph.card_H1_of_connected` — Corollary `cor:sector-count`
  in full generality).
-/

namespace NCG.Multigraph

variable {G : Multigraph}

/-- A `0`-cochain in the kernel of the coboundary is invariant along
every walk: each edge relation `g(src e) + g(tgt e) = 0` forces equality
of endpoint values over `ℤ/2`. -/
theorem eq_of_walk_of_coboundary_eq_zero {g : G.V → ZMod 2}
    (hg : coboundaryMap G g = 0) :
    ∀ {u v : G.V}, G.Walk u v → g u = g v := by
  have hz : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  intro u v p
  induction p with
  | nil w => rfl
  | fwd e p ih =>
      have he : g (G.src e) + g (G.tgt e) = 0 := congrFun hg e
      rw [hz _ _ he]
      exact ih
  | bwd e p ih =>
      have he : g (G.src e) + g (G.tgt e) = 0 := congrFun hg e
      rw [← hz _ _ he]
      exact ih

variable (G)

/-- The constant `0`-cochains, as a linear map `ℤ/2 → C⁰(G, ℤ/2)`. -/
def constMap : ZMod 2 →ₗ[ZMod 2] (G.V → ZMod 2) where
  toFun c := fun _ => c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {G}

/-- **The kernel of the coboundary on a connected graph is the constants**
(the `H⁰` computation feeding the Betti formula): a kernel cochain is
walk-invariant, and every constant is killed by `δ` in characteristic
two. -/
theorem ker_coboundaryMap {v₀ : G.V} (hconn : G.ConnectedTo v₀) :
    LinearMap.ker (coboundaryMap G) = LinearMap.range (constMap G) := by
  ext g
  constructor
  · intro hg
    refine ⟨g v₀, funext fun v => ?_⟩
    exact eq_of_walk_of_coboundary_eq_zero (LinearMap.mem_ker.mp hg)
      (hconn v).some
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    funext e
    show c + c = 0
    exact CharTwo.add_self_eq_zero c

/-- The constant embedding is injective (the graph has a vertex). -/
theorem constMap_injective (v₀ : G.V) :
    Function.Injective (constMap G) := fun c c' h => congrFun h v₀

/-- **The Betti-number formula** (Theorem `thm:cover`, general connected
case): for every finite connected multigraph,

`dim H¹(G, ℤ/2) + |V| = |E| + 1`,

i.e. `b₁(G) = |E| − |V| + 1`.  The proof is pure rank–nullity: the
coboundary `δ : C⁰ → C¹` has kernel the constants (dimension `1`), so its
range has dimension `|V| − 1`, and `H¹ = C¹/im δ` has dimension
`|E| − (|V| − 1)` — no spanning tree is ever chosen. -/
theorem finrank_H1_add_card_vertices [Fintype G.V] [Fintype G.E]
    {v₀ : G.V} (hconn : G.ConnectedTo v₀) :
    Module.finrank (ZMod 2) (H1 G) + Fintype.card G.V
      = Fintype.card G.E + 1 := by
  have hker : Module.finrank (ZMod 2)
      (LinearMap.ker (coboundaryMap G)) = 1 := by
    rw [ker_coboundaryMap hconn,
      LinearMap.finrank_range_of_inj (constMap_injective v₀),
      Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker (coboundaryMap G)
  rw [hker, Module.finrank_pi] at hrn
  have hquot := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (coboundaryMap G))
  rw [Module.finrank_pi] at hquot
  have hH1 : Module.finrank (ZMod 2) (H1 G)
      = Module.finrank (ZMod 2)
        ((G.E → ZMod 2) ⧸ LinearMap.range (coboundaryMap G)) := rfl
  omega

instance [Finite G.E] : Finite (H1 G) :=
  Finite.of_surjective _
    (Submodule.mkQ_surjective (LinearMap.range (coboundaryMap G)))

instance [Finite G.E] : Module.Finite (ZMod 2) (H1 G) :=
  Module.Finite.of_finite

/-- **Corollary `cor:sector-count` in full generality**: a finite
connected multigraph carries exactly `2^{b₁}` gauge classes of signed
sectors, `b₁ = |E| − |V| + 1`.  Together with the two-cochains lemma and
the rank-two structure group this is the boxed classification
`π₀ Enr_min(G) ≅ H¹(G, ℤ/2) ≅ (ℤ/2)^{b₁(G)}` of Theorem
`thm:classification`. -/
theorem card_H1_of_connected [Fintype G.V] [Fintype G.E]
    {v₀ : G.V} (hconn : G.ConnectedTo v₀) :
    Nat.card (H1 G) = 2 ^ (Fintype.card G.E + 1 - Fintype.card G.V) := by
  have hfin := finrank_H1_add_card_vertices hconn
  have hcard : Nat.card (H1 G)
      = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (H1 G) :=
    Module.natCard_eq_pow_finrank
  rw [hcard, Nat.card_eq_fintype_card, ZMod.card]
  congr 1
  omega

end NCG.Multigraph
