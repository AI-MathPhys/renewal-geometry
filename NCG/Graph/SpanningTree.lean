/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Graph.BettiNumber

/-!
# Rooted spanning trees of multigraphs

Infrastructure for `thm:supp-marked-bundle` of `papers/predictive_spectral_geometry`
(spanning-tree normal form of flat bundles on a graph).

* `NCG.Multigraph.Walk.length` — the number of edge traversals of a walk.
* `NCG.Multigraph.SpanningTree G v₀` — a rooted spanning tree in breadth-first form: a depth
  function vanishing exactly at the root `v₀`, a parent edge for every other vertex joining it to
  a vertex of depth one less, and the tree path from `v₀` to every vertex, extending the path of
  the parent vertex by the parent edge.
* `NCG.Multigraph.SpanningTree.bfs` — **existence**: every multigraph connected to `v₀` has a
  rooted spanning tree (breadth-first search: depth = walk distance to `v₀`).
* `SpanningTree.parent_injective` — distinct non-root vertices have distinct parent edges, so a
  finite connected multigraph has exactly `|V| - 1` tree edges (`card_treeEdges`) and
  `|E| - |V| + 1 = b₁` chords (`card_chords_add_card`, `card_chords_eq_finrank_H1`: the number of
  chords is the first Betti number `dim H¹(G; ℤ/2)` of `NCG.Graph.BettiNumber`).
-/

namespace NCG.Multigraph

variable {G : Multigraph}

namespace Walk

/-- The number of edge traversals of a walk. -/
def length : ∀ {u v : G.V}, G.Walk u v → ℕ
  | _, _, .nil _ => 0
  | _, _, .fwd _ p => p.length + 1
  | _, _, .bwd _ p => p.length + 1

@[simp] theorem length_nil (v : G.V) : (Walk.nil v : G.Walk v v).length = 0 := rfl

@[simp] theorem length_fwd (e : G.E) {w : G.V} (p : G.Walk (G.tgt e) w) :
    (Walk.fwd e p).length = p.length + 1 := rfl

@[simp] theorem length_bwd (e : G.E) {w : G.V} (p : G.Walk (G.src e) w) :
    (Walk.bwd e p).length = p.length + 1 := rfl

end Walk

/-- A **rooted spanning tree** of `G` at `v₀`, in breadth-first form: the depth vanishes exactly
at the root, every other vertex `v` has a parent edge joining `v` to a vertex of depth one less,
and `path v` is the tree path from `v₀` to `v`, obtained from the path of the parent vertex by
traversing the parent edge. -/
structure SpanningTree (G : Multigraph) (v₀ : G.V) where
  /-- Tree distance from the root. -/
  depth : G.V → ℕ
  /-- The parent edge of a non-root vertex. -/
  parent : ∀ v : G.V, v ≠ v₀ → G.E
  /-- The tree path from the root. -/
  path : ∀ v : G.V, G.Walk v₀ v
  depth_eq_zero_iff : ∀ v, depth v = 0 ↔ v = v₀
  parent_spec : ∀ v (hv : v ≠ v₀),
    (G.src (parent v hv) = v ∧ depth (G.tgt (parent v hv)) + 1 = depth v) ∨
    (G.tgt (parent v hv) = v ∧ depth (G.src (parent v hv)) + 1 = depth v)
  path_root : path v₀ = Walk.nil v₀
  path_src : ∀ v (hv : v ≠ v₀), G.src (parent v hv) = v →
    path (G.src (parent v hv)) = (path (G.tgt (parent v hv))).append (Walk.singleRev (parent v hv))
  path_tgt : ∀ v (hv : v ≠ v₀), G.tgt (parent v hv) = v →
    path (G.tgt (parent v hv)) = (path (G.src (parent v hv))).append (Walk.single (parent v hv))

namespace SpanningTree

variable {v₀ : G.V} (T : SpanningTree G v₀)

/-- The tree edges `T = {parent v : v ≠ v₀}`. -/
def treeEdges : Set G.E := {e | ∃ v, ∃ hv : v ≠ v₀, T.parent v hv = e}

/-- The parent edge determines the vertex: it is the endpoint of larger depth. -/
theorem parent_injective {v w : G.V} (hv : v ≠ v₀) (hw : w ≠ v₀)
    (h : T.parent v hv = T.parent w hw) : v = w := by
  rcases T.parent_spec v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases T.parent_spec w hw with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h] at h1 h2
  · exact h1.symm.trans h3
  · rw [h1] at h4; rw [h3] at h2; omega
  · rw [h1] at h4; rw [h3] at h2; omega
  · exact h1.symm.trans h3

include T in
/-- A multigraph with a spanning tree at `v₀` is connected to `v₀`. -/
theorem connectedTo : G.ConnectedTo v₀ := fun v => ⟨T.path v⟩

/-- The tree path of a vertex consists of tree edges: the parent edge is a tree edge. -/
theorem parent_mem_treeEdges (v : G.V) (hv : v ≠ v₀) : T.parent v hv ∈ T.treeEdges :=
  ⟨v, hv, rfl⟩

section Finite

variable [Fintype G.V] [DecidableEq G.V] [Fintype G.E] [DecidableEq G.E]

/-- The tree edges as a finset. -/
noncomputable def treeFinset : Finset G.E :=
  (Finset.univ.erase v₀).attach.image fun v => T.parent v.1 (Finset.ne_of_mem_erase v.2)

theorem mem_treeFinset {e : G.E} : e ∈ T.treeFinset ↔ e ∈ T.treeEdges := by
  simp only [treeFinset, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_erase, Finset.mem_univ, and_true, treeEdges, Set.mem_ofPred_eq]

/-- **A spanning tree has `|V| - 1` edges.** -/
theorem card_treeFinset : T.treeFinset.card = Fintype.card G.V - 1 := by
  rw [treeFinset, Finset.card_image_of_injective]
  · rw [Finset.card_attach, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    exact Subtype.ext (T.parent_injective _ _ h)

/-- The chords `E \ T` as a finset. -/
noncomputable def chordFinset : Finset G.E := Finset.univ \ T.treeFinset

/-- **The chords number `|E| - |V| + 1`.** -/
theorem card_chords_add_card : T.chordFinset.card + Fintype.card G.V = Fintype.card G.E + 1 := by
  have h1 : T.chordFinset.card = Fintype.card G.E - T.treeFinset.card := by
    rw [chordFinset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have h2 : T.treeFinset.card ≤ Fintype.card G.E := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ _
  have h3 := T.card_treeFinset
  have hV : 0 < Fintype.card G.V := Fintype.card_pos_iff.2 ⟨v₀⟩
  omega

/-- **The number of chords is the first Betti number** `b₁ = dim H¹(G; ℤ/2)`. -/
theorem card_chords_eq_finrank_H1 :
    T.chordFinset.card = Module.finrank (ZMod 2) (H1 G) := by
  have h1 := T.card_chords_add_card
  have h2 := finrank_H1_add_card_vertices T.connectedTo
  omega

end Finite

end SpanningTree

/-! ## Existence: breadth-first search -/

section BFS

variable {v₀ : G.V}

/-- Walk distance to the root. -/
noncomputable def bfsDist (hconn : G.ConnectedTo v₀) (v : G.V) : ℕ :=
  @Nat.find (fun n => ∃ p : G.Walk v v₀, p.length = n) (Classical.decPred _)
    ⟨((hconn v).some.reverse).length, _, rfl⟩

variable {hconn : G.ConnectedTo v₀}

theorem bfsDist_spec (v : G.V) : ∃ p : G.Walk v v₀, p.length = bfsDist hconn v :=
  @Nat.find_spec (fun n => ∃ p : G.Walk v v₀, p.length = n) (Classical.decPred _) _

theorem bfsDist_le {v : G.V} (p : G.Walk v v₀) : bfsDist hconn v ≤ p.length :=
  @Nat.find_min' (fun n => ∃ p : G.Walk v v₀, p.length = n) (Classical.decPred _) _ _ ⟨p, rfl⟩

theorem bfsDist_eq_zero_iff (v : G.V) : bfsDist hconn v = 0 ↔ v = v₀ := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := bfsDist_spec (hconn := hconn) v
    rw [h] at hp
    cases p with
    | nil => rfl
    | fwd e p => simp at hp
    | bwd e p => simp at hp
  · intro h
    subst h
    exact Nat.le_zero.1 (bfsDist_le (Walk.nil _))

theorem bfsDist_src_le (e : G.E) : bfsDist hconn (G.src e) ≤ bfsDist hconn (G.tgt e) + 1 := by
  obtain ⟨p, hp⟩ := bfsDist_spec (hconn := hconn) (G.tgt e)
  have := bfsDist_le (hconn := hconn) (Walk.fwd e p)
  simpa [hp] using this

theorem bfsDist_tgt_le (e : G.E) : bfsDist hconn (G.tgt e) ≤ bfsDist hconn (G.src e) + 1 := by
  obtain ⟨p, hp⟩ := bfsDist_spec (hconn := hconn) (G.src e)
  have := bfsDist_le (hconn := hconn) (Walk.bwd e p)
  simpa [hp] using this

/-- Every non-root vertex has a neighbour one step closer to the root. -/
theorem exists_bfsParent {v : G.V} (hv : v ≠ v₀) :
    ∃ e : G.E, (G.src e = v ∧ bfsDist hconn (G.tgt e) + 1 = bfsDist hconn v) ∨
      (G.tgt e = v ∧ bfsDist hconn (G.src e) + 1 = bfsDist hconn v) := by
  obtain ⟨p, hp⟩ := bfsDist_spec (hconn := hconn) v
  cases p with
  | nil => exact absurd rfl hv
  | fwd e q =>
      refine ⟨e, Or.inl ⟨rfl, ?_⟩⟩
      have h1 := bfsDist_le (hconn := hconn) q
      have h2 := bfsDist_src_le (hconn := hconn) e
      simp only [Walk.length_fwd] at hp
      omega
  | bwd e q =>
      refine ⟨e, Or.inr ⟨rfl, ?_⟩⟩
      have h1 := bfsDist_le (hconn := hconn) q
      have h2 := bfsDist_tgt_le (hconn := hconn) e
      simp only [Walk.length_bwd] at hp
      omega

variable (hconn)

/-- The breadth-first parent edge. -/
noncomputable def bfsParent (v : G.V) (hv : v ≠ v₀) : G.E :=
  (exists_bfsParent (hconn := hconn) hv).choose

theorem bfsParent_spec (v : G.V) (hv : v ≠ v₀) :
    (G.src (bfsParent hconn v hv) = v ∧
        bfsDist hconn (G.tgt (bfsParent hconn v hv)) + 1 = bfsDist hconn v) ∨
      (G.tgt (bfsParent hconn v hv) = v ∧
        bfsDist hconn (G.src (bfsParent hconn v hv)) + 1 = bfsDist hconn v) :=
  (exists_bfsParent (hconn := hconn) hv).choose_spec

theorem bfsDist_tgt_lt_of_src {v : G.V} (hv : v ≠ v₀) (hs : G.src (bfsParent hconn v hv) = v) :
    bfsDist hconn (G.tgt (bfsParent hconn v hv)) < bfsDist hconn v := by
  rcases bfsParent_spec hconn v hv with ⟨-, h⟩ | ⟨h1, h⟩
  · omega
  · rw [hs] at h; omega

theorem tgt_eq_of_not_src {v : G.V} (hv : v ≠ v₀) (hs : G.src (bfsParent hconn v hv) ≠ v) :
    G.tgt (bfsParent hconn v hv) = v ∧
      bfsDist hconn (G.src (bfsParent hconn v hv)) + 1 = bfsDist hconn v := by
  rcases bfsParent_spec hconn v hv with ⟨h1, -⟩ | h
  · exact absurd h1 hs
  · exact h

open Classical in
/-- The breadth-first tree path from the root. -/
noncomputable def bfsPath (v : G.V) : G.Walk v₀ v :=
  if hv : v = v₀ then hv ▸ Walk.nil v₀
  else if hs : G.src (bfsParent hconn v hv) = v then
    hs ▸ (bfsPath (G.tgt (bfsParent hconn v hv))).append (Walk.singleRev (bfsParent hconn v hv))
  else
    (tgt_eq_of_not_src hconn hv hs).1 ▸
      (bfsPath (G.src (bfsParent hconn v hv))).append (Walk.single (bfsParent hconn v hv))
termination_by bfsDist hconn v
decreasing_by
  · exact bfsDist_tgt_lt_of_src hconn hv hs
  · have := (tgt_eq_of_not_src hconn hv hs).2
    omega

/-- Transport of a walk-valued function along an equality of endpoints. -/
theorem eq_of_eq_cast {a b : G.V} (h : a = b) (f : ∀ x, G.Walk v₀ x) (X : G.Walk v₀ a)
    (hf : f b = h ▸ X) : f a = X := by
  subst h
  exact hf

theorem bfsPath_root : bfsPath hconn v₀ = Walk.nil v₀ := by
  rw [bfsPath.eq_def, dite_eq_left rfl]

theorem bfsPath_src (v : G.V) (hv : v ≠ v₀) (hs : G.src (bfsParent hconn v hv) = v) :
    bfsPath hconn (G.src (bfsParent hconn v hv)) =
      (bfsPath hconn (G.tgt (bfsParent hconn v hv))).append
        (Walk.singleRev (bfsParent hconn v hv)) := by
  refine eq_of_eq_cast hs (bfsPath hconn) _ ?_
  rw [bfsPath.eq_def, dite_eq_right hv, dite_eq_left hs]

theorem bfsPath_tgt (v : G.V) (hv : v ≠ v₀) (ht : G.tgt (bfsParent hconn v hv) = v) :
    bfsPath hconn (G.tgt (bfsParent hconn v hv)) =
      (bfsPath hconn (G.src (bfsParent hconn v hv))).append
        (Walk.single (bfsParent hconn v hv)) := by
  have hs : G.src (bfsParent hconn v hv) ≠ v := by
    intro hs
    rcases bfsParent_spec hconn v hv with ⟨-, h⟩ | ⟨-, h⟩
    · rw [ht] at h; omega
    · rw [hs] at h; omega
  refine eq_of_eq_cast ht (bfsPath hconn) _ ?_
  rw [bfsPath.eq_def, dite_eq_right hv, dite_eq_right hs]

/-- **Existence of a rooted spanning tree** on a multigraph connected to `v₀`
(breadth-first search). -/
noncomputable def SpanningTree.bfs : SpanningTree G v₀ where
  depth := bfsDist hconn
  parent := bfsParent hconn
  path := bfsPath hconn
  depth_eq_zero_iff := bfsDist_eq_zero_iff
  parent_spec := bfsParent_spec hconn
  path_root := bfsPath_root hconn
  path_src := bfsPath_src hconn
  path_tgt := bfsPath_tgt hconn

theorem SpanningTree.nonempty (hconn : G.ConnectedTo v₀) : Nonempty (SpanningTree G v₀) :=
  ⟨SpanningTree.bfs hconn⟩

end BFS

end NCG.Multigraph
