/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionCliffordEasy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Exact regular-graph dimension selection

The graph handshake identity turns equality of the connected cut and cycle
ranks into the manuscript balance equation.  Its unique nontrivial regular
simple-graph solution is the complete graph on four vertices.
-/

open Finset

namespace NCG

/-- `cor:dimension-regular-graph`, including the graph-theoretic derivation
and the literal identification with the complete graph. -/
theorem dimension_regular_graph_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hv : 2 ≤ Fintype.card V)
    (hregular : ∀ v, G.degree v = k)
    (hbalance : (Fintype.card V : ℤ) - 1 =
      (G.edgeFinset.card : ℤ) - Fintype.card V + 1) :
    Fintype.card V = 4 ∧ k = 3 ∧ G = ⊤ := by
  classical
  let v := Fintype.card V
  let m := G.edgeFinset.card
  have hhandNat : v * k = 2 * m := by
    calc
      v * k = ∑ x, G.degree x := by simp [v, hregular]
      _ = 2 * m := G.sum_degrees_eq_twice_card_edges
  have hhand : (v : ℤ) * k = 2 * m := by
    exact_mod_cast hhandNat
  have hbal : (v : ℤ) - 1 = (m : ℤ) - v + 1 := by
    exact hbalance
  have heq : ((4 : ℤ) - k) * v = 4 := by
    push_cast at hhand hbal ⊢
    nlinarith
  have hvpos : (0 : ℤ) < v := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hv)
  have hklt : k < 4 := by
    by_contra hk
    have hnonpos : (4 : ℤ) - k ≤ 0 := by omega
    have hmul : ((4 : ℤ) - k) * v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hvpos.le
    rw [heq] at hmul
    norm_num at hmul
  have hkcard : k < v := by
    have hVpos : 0 < Fintype.card V := by omega
    let x : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
    have hx := G.degree_lt_card_verts x
    rw [hregular x] at hx
    exact hx
  have hvk : v = 4 ∧ k = 3 := by
    interval_cases k <;> norm_num at heq ⊢ <;> omega
  refine ⟨hvk.1, hvk.2, ?_⟩
  apply G.eq_top_iff_forall_isUniversal.mpr
  intro x
  rw [← G.degree_eq_card_sub_one, hregular x]
  change k = v - 1
  omega

end NCG
