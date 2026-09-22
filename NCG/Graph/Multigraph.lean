/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Directed multigraphs and walks

The signed sector of renewal spectral geometry lives on the **predictive
graph** of a recurrent component (manuscript, §"Signed covers and the modular
Dirac operator"): vertices are predictive classes and an edge `e : x → y`
records a generator transition `y = σ · x`.

This file provides the bare combinatorial structure:

* `NCG.Multigraph` — a directed multigraph (parallel edges allowed), given
  by source and target maps `src tgt : E → V`;
* `NCG.Multigraph.Hom` — morphisms of multigraphs;
* `NCG.Multigraph.Walk` — walks that may traverse edges either forwards or
  backwards (needed because `H¹(G, ℤ/2)` is the cohomology of the underlying
  *undirected* graph), with concatenation and reversal.

Sign cocycles and their holonomy are in `NCG.Graph.SignCocycle`; the signed
double cover is in `NCG.Graph.SignedCover`.
-/

namespace NCG

universe u v

-- Vertex and edge types deliberately live in independent universes;
-- collapsing them would restrict downstream instantiations.
set_option linter.checkUnivs false in
/-- A **directed multigraph**: a type of vertices, a type of (oriented)
edges, and source/target maps.  Parallel edges and loops are allowed, as
required for predictive graphs. -/
structure Multigraph : Type (max (u + 1) (v + 1)) where
  /-- Vertices (predictive classes). -/
  V : Type u
  /-- Oriented edges (generator transitions). -/
  E : Type v
  /-- Source of an edge. -/
  src : E → V
  /-- Target of an edge. -/
  tgt : E → V

namespace Multigraph

/-- A morphism of multigraphs: maps on vertices and edges commuting with
source and target. -/
structure Hom (G H : Multigraph) where
  /-- The vertex map. -/
  vmap : G.V → H.V
  /-- The edge map. -/
  emap : G.E → H.E
  /-- Compatibility with sources. -/
  src_comm : ∀ e, H.src (emap e) = vmap (G.src e)
  /-- Compatibility with targets. -/
  tgt_comm : ∀ e, H.tgt (emap e) = vmap (G.tgt e)

variable (G : Multigraph.{u, v})

/-- A **walk** in a multigraph from `u` to `v`, allowed to traverse each
edge forwards (`fwd`) or backwards (`bwd`).  Walks in the underlying
undirected graph are what carry `ℤ/2`-holonomy. -/
inductive Walk : G.V → G.V → Type (max u v)
  | nil (v : G.V) : Walk v v
  | fwd (e : G.E) {w : G.V} (p : Walk (G.tgt e) w) : Walk (G.src e) w
  | bwd (e : G.E) {w : G.V} (p : Walk (G.src e) w) : Walk (G.tgt e) w

namespace Walk

variable {G}

/-- Concatenation of walks. -/
def append : ∀ {u v w : G.V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, .nil _, q => q
  | _, _, _, .fwd e p, q => .fwd e (p.append q)
  | _, _, _, .bwd e p, q => .bwd e (p.append q)

@[simp]
theorem nil_append {u v : G.V} (q : G.Walk u v) :
    (Walk.nil u).append q = q := rfl

@[simp]
theorem fwd_append {w x : G.V} (e : G.E) (p : G.Walk (G.tgt e) w)
    (q : G.Walk w x) : (Walk.fwd e p).append q = .fwd e (p.append q) := rfl

@[simp]
theorem bwd_append {w x : G.V} (e : G.E) (p : G.Walk (G.src e) w)
    (q : G.Walk w x) : (Walk.bwd e p).append q = .bwd e (p.append q) := rfl

/-- The one-edge forward walk along `e`. -/
def single (e : G.E) : G.Walk (G.src e) (G.tgt e) :=
  .fwd e (.nil _)

/-- The one-edge backward walk along `e`. -/
def singleRev (e : G.E) : G.Walk (G.tgt e) (G.src e) :=
  .bwd e (.nil _)

/-- Reversal of a walk. -/
def reverse : ∀ {u v : G.V}, G.Walk u v → G.Walk v u
  | _, _, .nil v => .nil v
  | _, _, .fwd e p => p.reverse.append (singleRev e)
  | _, _, .bwd e p => p.reverse.append (single e)

end Walk

/-- A multigraph is **connected to a base vertex** `v₀` when every vertex is
reachable from `v₀` by an (undirected) walk. -/
def ConnectedTo (v₀ : G.V) : Prop :=
  ∀ v : G.V, Nonempty (G.Walk v₀ v)

end Multigraph

end NCG
