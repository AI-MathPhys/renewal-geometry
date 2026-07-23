/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.Multigraph

/-!
# Sign cocycles, gauge equivalence, and holonomy

A **sign cocycle** on a predictive graph `G` is a map `χ : E → ℤ/2`
(manuscript, Definition `def:sign-cocycle`; we write the sign group
additively, so the manuscript's `{±1}` multiplicative sign is `(-1)^χ`).
Since a graph has no `2`-cells, every `1`-cochain is a cocycle.

A **flat gauge** is a vertex function `g : V → ℤ/2` acting by
`χ^g(e : x → y) = χ(e) + g(x) + g(y)`; the gauge-invariant content of `χ` is
its **holonomy**, the sum of `χ` around closed walks, i.e. its class in
`H¹(G, ℤ/2)`.

## Main results

* `NCG.Multigraph.Walk.holonomy_gauge` — a gauge changes the holonomy of a
  walk from `u` to `v` by the boundary term `g u + g v`; in particular
  loop holonomy is gauge invariant
  (`NCG.Multigraph.Walk.holonomy_gauge_loop`, part of Theorem `thm:cover`);
* `NCG.Multigraph.holonomy_eq_zero_of_isCoboundary` — coboundaries have
  trivial holonomy around every loop;
* `NCG.Multigraph.isCoboundary_of_holonomy_eq_zero` — on a connected graph,
  a cocycle with trivial holonomy around all loops at a base vertex is a
  coboundary.  Together these give the triviality criterion of
  Theorem `thm:cover` / Corollary `cor:removability`: the signed sector is
  removable by a flat gauge iff its holonomy class vanishes. -/

namespace NCG.Multigraph

variable {G : Multigraph}

namespace Walk

/-- The `ℤ/2`-**holonomy** (sign sum) of a walk with respect to a sign
cocycle `χ`.  Backward traversal contributes the same sign, since
`-1 = 1` in `ℤ/2`. -/
def holonomy (χ : G.E → ZMod 2) : ∀ {u v : G.V}, G.Walk u v → ZMod 2
  | _, _, .nil _ => 0
  | _, _, .fwd e p => χ e + p.holonomy χ
  | _, _, .bwd e p => χ e + p.holonomy χ

@[simp]
theorem holonomy_nil (χ : G.E → ZMod 2) (v : G.V) :
    (Walk.nil v).holonomy χ = 0 := rfl

@[simp]
theorem holonomy_fwd (χ : G.E → ZMod 2) (e : G.E) {w : G.V}
    (p : G.Walk (G.tgt e) w) :
    (Walk.fwd e p).holonomy χ = χ e + p.holonomy χ := rfl

@[simp]
theorem holonomy_bwd (χ : G.E → ZMod 2) (e : G.E) {w : G.V}
    (p : G.Walk (G.src e) w) :
    (Walk.bwd e p).holonomy χ = χ e + p.holonomy χ := rfl

@[simp]
theorem holonomy_append (χ : G.E → ZMod 2) {u v w : G.V} (p : G.Walk u v)
    (q : G.Walk v w) :
    (p.append q).holonomy χ = p.holonomy χ + q.holonomy χ := by
  induction p with
  | nil v => simp
  | fwd e p ih => simp [ih, add_assoc]
  | bwd e p ih => simp [ih, add_assoc]

@[simp]
theorem holonomy_reverse (χ : G.E → ZMod 2) {u v : G.V} (p : G.Walk u v) :
    p.reverse.holonomy χ = p.holonomy χ := by
  induction p with
  | nil v => simp [Walk.reverse]
  | fwd e p ih =>
      simp [Walk.reverse, Walk.singleRev, ih, add_comm]
  | bwd e p ih =>
      simp [Walk.reverse, Walk.single, ih, add_comm]

end Walk

/-- The action of a **flat gauge** `g : V → ℤ/2` on a sign cocycle
(Definition `def:sign-cocycle`): `χ^g(e) = χ(e) + g(src e) + g(tgt e)`. -/
def gaugeAct (g : G.V → ZMod 2) (χ : G.E → ZMod 2) : G.E → ZMod 2 :=
  fun e => χ e + g (G.src e) + g (G.tgt e)

@[simp]
theorem gaugeAct_apply (g : G.V → ZMod 2) (χ : G.E → ZMod 2) (e : G.E) :
    gaugeAct g χ e = χ e + g (G.src e) + g (G.tgt e) := rfl

/-- A cocycle is a **coboundary** when it is the gauge transform of `0`,
i.e. `χ(e) = g(src e) + g(tgt e)` for some vertex sign `g`. -/
def IsCoboundary (χ : G.E → ZMod 2) : Prop :=
  ∃ g : G.V → ZMod 2, ∀ e, χ e = g (G.src e) + g (G.tgt e)

namespace Walk

/-- A gauge changes the holonomy of a walk `u ⟶ v` by the boundary term
`g u + g v`. -/
theorem holonomy_gauge (g : G.V → ZMod 2) (χ : G.E → ZMod 2) {u v : G.V}
    (p : G.Walk u v) :
    p.holonomy (gaugeAct g χ) = p.holonomy χ + g u + g v := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  induction p with
  | nil v =>
      simp only [holonomy_nil, zero_add]
      exact (h2 (g v)).symm
  | fwd e p ih =>
      simp only [holonomy_fwd, gaugeAct_apply, ih]
      linear_combination h2 (g (G.tgt e))
  | bwd e p ih =>
      simp only [holonomy_bwd, gaugeAct_apply, ih]
      linear_combination h2 (g (G.src e))

/-- **Gauge invariance of loop holonomy** (part of Theorem `thm:cover` /
Proposition `prop:krein-datum`): flat gauges do not change the holonomy of
closed walks. -/
theorem holonomy_gauge_loop (g : G.V → ZMod 2) (χ : G.E → ZMod 2) {v : G.V}
    (p : G.Walk v v) :
    p.holonomy (gaugeAct g χ) = p.holonomy χ := by
  rw [holonomy_gauge, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The zero cocycle has zero holonomy along every walk. -/
@[simp]
theorem holonomy_zero {u v : G.V} (p : G.Walk u v) :
    p.holonomy (fun _ => 0) = 0 := by
  induction p with
  | nil v => simp
  | fwd e p ih => simpa using ih
  | bwd e p ih => simpa using ih

end Walk

/-- A coboundary has trivial holonomy around every closed walk (the easy
direction of the triviality criterion in Theorem `thm:cover`). -/
theorem holonomy_eq_zero_of_isCoboundary {χ : G.E → ZMod 2}
    (h : IsCoboundary (G := G) χ) {v : G.V} (p : G.Walk v v) :
    p.holonomy χ = 0 := by
  obtain ⟨g, hg⟩ := h
  have hχ : χ = gaugeAct g (fun _ => 0) := by
    funext e
    simp [gaugeAct, hg e]
  rw [hχ, Walk.holonomy_gauge_loop, Walk.holonomy_zero]

/-- On a connected graph, a sign cocycle whose holonomy vanishes around all
closed walks at a base vertex is a coboundary (the hard direction of the
triviality criterion in Theorem `thm:cover` / Corollary `cor:removability`).

The gauge is produced by transporting the sign from the base vertex along
any chosen walk; triviality of loop holonomy makes the transported sign
independent of the choice. -/
theorem isCoboundary_of_holonomy_eq_zero {χ : G.E → ZMod 2} {v₀ : G.V}
    (hconn : G.ConnectedTo v₀)
    (htriv : ∀ p : G.Walk v₀ v₀, p.holonomy χ = 0) :
    IsCoboundary (G := G) χ := by
  -- transport the sign along a chosen walk from the base vertex
  have walkTo : ∀ v, G.Walk v₀ v := fun v => (hconn v).some
  refine ⟨fun v => (walkTo v).holonomy χ, fun e => ?_⟩
  -- close up the walk `v₀ ⟶ src e ⟶ tgt e ⟶ v₀` and use triviality
  have hloop :=
    htriv (((walkTo (G.src e)).append (Walk.single e)).append
      (walkTo (G.tgt e)).reverse)
  simp only [Walk.holonomy_append, Walk.holonomy_reverse] at hloop
  have hsingle : (Walk.single e).holonomy χ = χ e := by
    simp [Walk.single]
  rw [hsingle] at hloop
  -- in `ℤ/2`, `a + χ e + b = 0` rearranges to `χ e = a + b`
  have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  linear_combination hloop - h2 ((walkTo (G.src e)).holonomy χ)
    - h2 ((walkTo (G.tgt e)).holonomy χ)

end NCG.Multigraph
