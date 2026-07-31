/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The `K₄` topological core and subdivision conductances
  (`thm:k4-topological-core-sm`, `prop:subdivision-conductances-sm`,
   SM_emergence)

* `k4_topological_core` — a finite loopless simple graph with
  `|E| = |V| + 2` (cycle rank three after pass-through suppression)
  and minimum degree at least three has exactly four vertices and
  is complete: `G_core ≅ K₄`.  Handshake gives `3|V| ≤ 2|E| =
  2|V| + 4`, so `|V| ≤ 4`; a vertex of degree `≥ 3` forces
  `|V| ≥ 4`; then `|E| = 6 = C(4,2)` forces completeness;
* `schur_series_step` — eliminating one pass-through vertex of a
  two-edge series with conductances `a, b` by the Schur complement
  of the weighted path Laplacian gives the effective conductance
  `ab/(a+b) = (a⁻¹ + b⁻¹)⁻¹`;
* `series_conductance` / `unit_subdivision_conductance` — the
  general series law `c_eff = (Σ_r c_r⁻¹)⁻¹`, and `c_eff = 1/L`
  for a path of `L` unit conductances.

The cycle-rank bookkeeping under pass-through suppression
(`b₁ = |E| - |V| + 1` invariant) is the counting step recorded in
the theorem's hypothesis `|E| = |V| + 2`.
-/

namespace NCG

open Finset

/-- `thm:k4-topological-core-sm`: a finite loopless simple graph
with `|E| = |V| + 2` and minimum degree at least three has four
vertices and is complete — the core is `K₄`. -/
theorem k4_topological_core {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = Fintype.card V + 2)
    (hdeg : ∀ v, 3 ≤ G.degree v) :
    Fintype.card V = 4 ∧ G = ⊤ := by
  classical
  have hne : Nonempty V := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hc0 : Fintype.card V = 0 := Fintype.card_eq_zero
    have hE0 : G.edgeFinset.card = 2 := by rw [hE, hc0]
    have hle : G.edgeFinset.card ≤ Nat.choose 0 2 :=
      hc0 ▸ SimpleGraph.card_edgeFinset_le_card_choose_two
    rw [hE0, show Nat.choose 0 2 = 0 from rfl] at hle
    exact absurd hle (by norm_num)
  obtain ⟨v0⟩ := hne
  -- handshake: 3|V| ≤ Σ deg = 2|E| = 2|V| + 4
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hlow : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
    calc 3 * Fintype.card V = ∑ _v : V, 3 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
            mul_comm]
    _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  have hVle : Fintype.card V ≤ 4 := by
    rw [hhand, hE] at hlow
    omega
  -- a degree-three vertex needs at least four vertices
  have hVge : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts v0
    have := hdeg v0
    omega
  have hV4 : Fintype.card V = 4 := le_antisymm hVle hVge
  refine ⟨hV4, ?_⟩
  -- |E| = 6 = C(4,2) forces completeness
  have hE6 : G.edgeFinset.card = 6 := by rw [hE, hV4]
  have htop : (⊤ : SimpleGraph V).edgeFinset.card = 6 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hV4]
    rfl
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    apply SimpleGraph.edgeFinset_mono
    exact le_top
  have heq : G.edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact SimpleGraph.edgeFinset_inj.mp heq

/-- `prop:subdivision-conductances-sm` (elimination step): the
Schur complement of the weighted two-edge path Laplacian
`[[a,-a,0],[-a,a+b,-b],[0,-b,b]]` eliminating the pass-through
middle vertex is the single-edge Laplacian with effective
conductance `ab/(a+b) = (a⁻¹+b⁻¹)⁻¹`. -/
theorem schur_series_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - a * a / (a + b) = (a⁻¹ + b⁻¹)⁻¹
      ∧ a * b / (a + b) = (a⁻¹ + b⁻¹)⁻¹)
      ∧ b - b * b / (a + b) = (a⁻¹ + b⁻¹)⁻¹ := by
  have hab : a + b ≠ 0 := by positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    · field_simp
      ring

/-- The general series law: iterating the pairwise Schur
elimination over a chain of positive conductances yields the
harmonic sum `c_eff = (Σ_r c_r⁻¹)⁻¹`. -/
theorem series_conductance (a : ℝ) (l : List ℝ) (ha : 0 < a)
    (hl : ∀ x ∈ l, 0 < x) :
    l.foldl (fun acc x => (acc⁻¹ + x⁻¹)⁻¹) a
      = (a⁻¹ + (l.map (·⁻¹)).sum)⁻¹ := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
      have hx : 0 < x := hl x (List.mem_cons_self ..)
      have ht : ∀ y ∈ t, 0 < y := fun y hy =>
        hl y (List.mem_cons_of_mem x hy)
      have hstep : (0 : ℝ) < (a⁻¹ + x⁻¹)⁻¹ := by positivity
      rw [List.foldl_cons, ih _ hstep ht,
        inv_inv, List.map_cons, List.sum_cons]
      ring_nf

/-- Unit subdivisions: a path of `L ≥ 1` unit-conductance edges has
effective conductance `c_eff = 1/L`. -/
theorem unit_subdivision_conductance (L : ℕ) :
    ((∑ _r : Fin L, ((1 : ℝ))⁻¹)⁻¹ : ℝ) = (L : ℝ)⁻¹ := by
  simp

end NCG
