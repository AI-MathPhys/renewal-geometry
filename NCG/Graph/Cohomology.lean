/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.SignedCover

/-!
# Graph cohomology `H¹(G, ℤ/2)` and the classification of signed sectors

The gauge classes of signed sectors over a predictive graph are the classes
of `H¹(G, ℤ/2)` (Theorem `thm:cover`, Corollary `cor:removability`,
Corollary `cor:sector-count`).  This file constructs `H¹` as a
`ℤ/2`-module and connects it to the holonomy theory of
`NCG.Graph.SignCocycle`:

* `coboundaryMap` — the coboundary `δ : C⁰(G) → C¹(G)`,
  `(δg)(e) = g(src e) + g(tgt e)`; since a graph has no 2-cells, every
  1-cochain is a cocycle and `H¹ = C¹ / im δ`;
* `H1 G` — the quotient module, with `H1.mk` the projection;
* `H1.mk_eq_zero_iff` — a class vanishes iff the cocycle is a coboundary
  (the removability criterion `cor:removability` in cohomological form);
* `Walk.holonomy_congr` — holonomy around closed walks descends to `H¹`:
  cohomologous cocycles have equal loop holonomy;
* `H1.mk_eq_zero_of_holonomy_eq_zero` — on a connected graph the holonomy
  functionals **separate** `H¹`: a class with trivial holonomy is zero
  (the injectivity half of Theorem `thm:cover`);
* `bouquet r` — the bouquet of `r` loops, with
  `H1BouquetEquiv : H¹(bouquet r) ≃ₗ (ℤ/2)^r`,
  `finrank_H1_bouquet : dim H¹ = r = b₁`, and
  `card_H1_bouquet : #H¹ = 2^r` — Corollary `cor:sector-count` for the
  graphs realising every Betti number (used by
  Proposition `prop:primitive-all-odd`). -/

namespace NCG.Multigraph

variable (G : Multigraph)

/-- The **coboundary map** `δ : C⁰(G, ℤ/2) → C¹(G, ℤ/2)`,
`(δg)(e) = g(src e) + g(tgt e)` (Definition `def:sign-cocycle`: flat gauges
act by adding coboundaries). -/
def coboundaryMap : (G.V → ZMod 2) →ₗ[ZMod 2] (G.E → ZMod 2) where
  toFun g := fun e => g (G.src e) + g (G.tgt e)
  map_add' g₁ g₂ := by
    funext e
    simp only [Pi.add_apply]
    abel
  map_smul' c g := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem coboundaryMap_apply (g : G.V → ZMod 2) (e : G.E) :
    coboundaryMap G g e = g (G.src e) + g (G.tgt e) := rfl

/-- **First cohomology** `H¹(G, ℤ/2) = C¹ / im δ`.  A graph is a
1-complex, so every 1-cochain is a cocycle and no cocycle condition is
imposed. -/
def H1 :=
  (G.E → ZMod 2) ⧸ LinearMap.range (coboundaryMap G)

instance : AddCommGroup (H1 G) :=
  inferInstanceAs (AddCommGroup
    ((G.E → ZMod 2) ⧸ LinearMap.range (coboundaryMap G)))

instance : Module (ZMod 2) (H1 G) :=
  inferInstanceAs (Module (ZMod 2)
    ((G.E → ZMod 2) ⧸ LinearMap.range (coboundaryMap G)))

namespace H1

/-- The class of a sign cocycle in `H¹(G, ℤ/2)`. -/
def mk : (G.E → ZMod 2) →ₗ[ZMod 2] H1 G :=
  Submodule.mkQ _

variable {G}

/-- Membership in the coboundary submodule is exactly the
`IsCoboundary` predicate of the holonomy theory. -/
theorem mem_range_coboundaryMap_iff {χ : G.E → ZMod 2} :
    χ ∈ LinearMap.range (coboundaryMap G) ↔ IsCoboundary (G := G) χ := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, fun e => by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, funext fun e => (hg e).symm⟩

/-- **The removability criterion in cohomological form**
(`cor:removability`): the class of a sign cocycle vanishes iff the cocycle
is a coboundary, i.e. iff the signed sector is removable by a flat gauge. -/
theorem mk_eq_zero_iff {χ : G.E → ZMod 2} :
    mk G χ = 0 ↔ IsCoboundary (G := G) χ := by
  rw [← mem_range_coboundaryMap_iff]
  exact Submodule.Quotient.mk_eq_zero _

end H1

variable {G}

/-- Holonomy is additive in the cocycle. -/
theorem Walk.holonomy_add (χ₁ χ₂ : G.E → ZMod 2) {u v : G.V}
    (p : G.Walk u v) :
    p.holonomy (χ₁ + χ₂) = p.holonomy χ₁ + p.holonomy χ₂ := by
  induction p with
  | nil w => simp
  | fwd e p ih =>
      simp only [Walk.holonomy_fwd, Pi.add_apply, ih]
      abel
  | bwd e p ih =>
      simp only [Walk.holonomy_bwd, Pi.add_apply, ih]
      abel

/-- **Loop holonomy descends to `H¹`** (Theorem `thm:cover`, monodromy
side): cohomologous sign cocycles have the same holonomy around every
closed walk.  The pairing `⟨[χ], α⟩` used throughout the signed sector —
in particular in the canonical temporal row
(`NCG.krein_exchange_path`) — is therefore well defined on classes. -/
theorem Walk.holonomy_congr {χ χ' : G.E → ZMod 2}
    (h : H1.mk G χ = H1.mk G χ') {v : G.V} (p : G.Walk v v) :
    p.holonomy χ = p.holonomy χ' := by
  have hsub : χ - χ' ∈ LinearMap.range (coboundaryMap G) := by
    rw [← Submodule.Quotient.eq]
    exact h
  have hdecomp : χ = χ' + (χ - χ') := by abel
  rw [hdecomp, Walk.holonomy_add,
    holonomy_eq_zero_of_isCoboundary
      (H1.mem_range_coboundaryMap_iff.mp hsub) p, add_zero]

/-- **Holonomy functionals separate `H¹` on connected graphs** (the
injectivity half of Theorem `thm:cover`): a class whose holonomy vanishes
around all loops at a base vertex is zero.  Together with
`Walk.holonomy_congr` this identifies `H¹(G, ℤ/2)` with the group of
holonomy homomorphisms on cycles — the classification of non-removable
signed sectors. -/
theorem H1.mk_eq_zero_of_holonomy_eq_zero {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) {χ : G.E → ZMod 2}
    (h : ∀ p : G.Walk v₀ v₀, p.holonomy χ = 0) :
    H1.mk G χ = 0 :=
  H1.mk_eq_zero_iff.mpr (isCoboundary_of_holonomy_eq_zero hconn h)

/-! ### The bouquet of `r` loops: realising every Betti number -/

/-- The **bouquet of `r` loops**: one vertex, `r` loop edges.  It has
`b₁ = |E| − |V| + 1 = r`, and is the recurrent component used in
Proposition `prop:primitive-all-odd` to realise primitive revision data in
every odd spatial rank. -/
def bouquet (r : ℕ) : Multigraph where
  V := Unit
  E := Fin r
  src := fun _ => ()
  tgt := fun _ => ()

/-- On a bouquet every coboundary vanishes: `(δg)(e) = g(⋆) + g(⋆) = 0`. -/
theorem coboundaryMap_bouquet (r : ℕ) :
    LinearMap.range (coboundaryMap (bouquet r)) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro g
  funext e
  change g (()) + g (()) = 0
  exact CharTwo.add_self_eq_zero _

/-- **`H¹` of the bouquet** (Theorem `thm:cover` for the bouquet):
`H¹(bouquet r, ℤ/2) ≃ (ℤ/2)^r`, one sign per loop. -/
noncomputable def H1BouquetEquiv (r : ℕ) :
    H1 (bouquet r) ≃ₗ[ZMod 2] (Fin r → ZMod 2) :=
  Submodule.quotEquivOfEqBot _ (coboundaryMap_bouquet r)

/-- The Betti-rank formula on the bouquet:
`dim H¹(bouquet r) = r = |E| − |V| + 1 = b₁`. -/
theorem finrank_H1_bouquet (r : ℕ) :
    Module.finrank (ZMod 2) (H1 (bouquet r)) = r := by
  rw [LinearEquiv.finrank_eq (H1BouquetEquiv r)]
  simp []

/-- **Corollary `cor:sector-count`** for the bouquet: there are exactly
`2^{b₁}` gauge classes of signed sectors. -/
theorem card_H1_bouquet (r : ℕ) :
    Nat.card (H1 (bouquet r)) = 2 ^ r := by
  rw [Nat.card_congr (H1BouquetEquiv r).toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end NCG.Multigraph
