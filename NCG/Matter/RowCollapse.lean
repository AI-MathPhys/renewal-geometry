/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Row normalisation collapses the fixed carrier
  (`prop:row-normalised-collapse`, SM_emergence)

* `stochastic_fixed_constant` — the elementary Perron maximum
  principle: a fixed vector of a row-stochastic nonnegative matrix
  whose positivity digraph is strongly connected is constant, so
  `Ker(T - I) = ℂ𝟙` is one-dimensional;
* `g2_fwd_closure` / `g2_bwd_closure` — the directed
  nonbacktracking graph of the shared-edge complex `G₂` (two `K₄`
  cells glued along `{0,1}`, twenty-two oriented edges) is strongly
  connected: kernel-checked forward and backward closures from the
  shared oriented edge `(0,1)`;
* `row_normalised_collapse` — hence every fixed vector of the
  row-normalised nonbacktracking transition `T_{G₂}` is constant:
  `dim Ker(T_{G₂} - I) = 1`, in contrast with the six-dimensional
  fixed carrier `JH¹(G₂;ℂ)` of the unnormalised amplitude operator
  (the declared cohomological count `b₁(G₂) = 6`).
-/

namespace NCG

open Finset

/-- Elementary Perron maximum principle: a fixed vector of a
nonnegative row-stochastic matrix with strongly connected
positivity digraph is constant. -/
theorem stochastic_fixed_constant {V : Type*} [Fintype V]
    [Nonempty V] (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ i j, Relation.ReflTransGen
      (fun a b => 0 < P a b) i j)
    (v : V → ℝ) (hfix : P.mulVec v = v) (i j : V) :
    v i = v j := by
  classical
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset V) v
    ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hstep : ∀ a, v a = v i0 → ∀ b, 0 < P a b → v b = v i0 := by
    intro a ha b hpb
    have hfa := congrFun hfix a
    rw [Matrix.mulVec, dotProduct] at hfa
    have hzero : ∑ k, P a k * (v i0 - v k) = 0 := by
      have h1 : ∑ k, P a k * (v i0 - v k)
          = (∑ k, P a k) * v i0 - ∑ k, P a k * v k := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h1, hrow a, hfa, ha]
      ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hnn a k)
        (sub_nonneg.mpr (hmax k (Finset.mem_univ k))))).mp
      hzero b (Finset.mem_univ b)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt hpb)
    · have := sub_eq_zero.mp h
      linarith
  have hall : ∀ b, Relation.ReflTransGen
      (fun a b => 0 < P a b) i0 b → v b = v i0 := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail hab hbc ih => exact hstep _ ih _ hbc
  rw [hall i (hirr i0 i), hall j (hirr i0 j)]

/-- Adjacency of the shared-edge complex `G₂`: two `K₄` cells
`{0,1,2,3}` and `{0,1,4,5}` glued along the edge `{0,1}`. -/
def g2adj (i j : Fin 6) : Bool :=
  i != j && ((i.val ≤ 3 && j.val ≤ 3)
    || ((i.val ≤ 1 || 4 ≤ i.val) && (j.val ≤ 1 || 4 ≤ j.val)))

/-- The twenty-two oriented edges of `G₂`. -/
abbrev G2Edge := {p : Fin 6 × Fin 6 // g2adj p.1 p.2 = true}

/-- Nonbacktracking continuation on oriented edges. -/
def g2NbStep (e f : G2Edge) : Prop :=
  f.val.1 = e.val.2 ∧ f.val.2 ≠ e.val.1

instance : DecidablePred fun ef : G2Edge × G2Edge =>
    g2NbStep ef.1 ef.2 := fun _ => by
  unfold g2NbStep
  infer_instance

instance (e f : G2Edge) : Decidable (g2NbStep e f) := by
  unfold g2NbStep
  infer_instance

/-- One forward-closure step of the nonbacktracking digraph. -/
def g2Fwd (S : Finset G2Edge) : Finset G2Edge :=
  S ∪ Finset.univ.filter (fun f => ∃ e ∈ S, g2NbStep e f)

/-- One backward-closure step of the nonbacktracking digraph. -/
def g2Bwd (S : Finset G2Edge) : Finset G2Edge :=
  S ∪ Finset.univ.filter (fun e => ∃ f ∈ S, g2NbStep e f)

/-- The shared oriented edge `(0,1)`. -/
def g2e0 : G2Edge := ⟨(0, 1), by decide⟩

instance : Nonempty G2Edge := ⟨g2e0⟩

set_option maxRecDepth 40000 in
/-- Every oriented edge is forward-reachable from `(0,1)`. -/
theorem g2_fwd_closure : g2Fwd^[22] {g2e0} = Finset.univ := by
  decide

set_option maxRecDepth 40000 in
/-- Every oriented edge backward-reaches `(0,1)`. -/
theorem g2_bwd_closure : g2Bwd^[22] {g2e0} = Finset.univ := by
  decide

/-- Forward-closure membership yields a nonbacktracking path. -/
theorem g2_fwd_extract : ∀ (n : ℕ) (S0 : Finset G2Edge)
    (x : G2Edge), x ∈ g2Fwd^[n] S0 →
    ∃ e ∈ S0, Relation.ReflTransGen g2NbStep e x := by
  intro n
  induction n with
  | zero =>
      intro S0 x hx
      exact ⟨x, by simpa using hx, .refl⟩
  | succ n ih =>
      intro S0 x hx
      rw [Function.iterate_succ_apply'] at hx
      simp only [g2Fwd, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx
      rcases hx with hx | ⟨e, he, hstep⟩
      · exact ih S0 x hx
      · obtain ⟨s, hs, hpath⟩ := ih S0 e he
        exact ⟨s, hs, hpath.tail hstep⟩

/-- Backward-closure membership yields a nonbacktracking path. -/
theorem g2_bwd_extract : ∀ (n : ℕ) (S0 : Finset G2Edge)
    (x : G2Edge), x ∈ g2Bwd^[n] S0 →
    ∃ f ∈ S0, Relation.ReflTransGen g2NbStep x f := by
  intro n
  induction n with
  | zero =>
      intro S0 x hx
      exact ⟨x, by simpa using hx, .refl⟩
  | succ n ih =>
      intro S0 x hx
      rw [Function.iterate_succ_apply'] at hx
      simp only [g2Bwd, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx
      rcases hx with hx | ⟨f, hf, hstep⟩
      · exact ih S0 x hx
      · obtain ⟨s, hs, hpath⟩ := ih S0 f hf
        exact ⟨s, hs, Relation.ReflTransGen.head hstep hpath⟩

/-- The nonbacktracking digraph of `G₂` is strongly connected. -/
theorem g2_strongly_connected (e f : G2Edge) :
    Relation.ReflTransGen g2NbStep e f := by
  have h1 : e ∈ g2Bwd^[22] {g2e0} := by
    rw [g2_bwd_closure]
    exact Finset.mem_univ e
  have h2 : f ∈ g2Fwd^[22] {g2e0} := by
    rw [g2_fwd_closure]
    exact Finset.mem_univ f
  obtain ⟨s1, hs1, hp1⟩ := g2_bwd_extract 22 {g2e0} e h1
  obtain ⟨s2, hs2, hp2⟩ := g2_fwd_extract 22 {g2e0} f h2
  rw [Finset.mem_singleton] at hs1 hs2
  subst hs1
  subst hs2
  exact hp1.trans hp2

/-- `prop:row-normalised-collapse`: any nonnegative row-stochastic
transition on the oriented edges of `G₂` whose support is exactly
the nonbacktracking continuations — in particular the
row-normalised `T_{G₂}` with entries `1/(deg(j)-1)` — has only
constant fixed vectors: `Ker(T_{G₂} - I) = ℂ𝟙` and
`dim Ker(T_{G₂} - I) = 1`. -/
theorem row_normalised_collapse (P : Matrix G2Edge G2Edge ℝ)
    (hnn : ∀ e f, 0 ≤ P e f) (hrow : ∀ e, ∑ f, P e f = 1)
    (hsupp : ∀ e f, 0 < P e f ↔ g2NbStep e f)
    (v : G2Edge → ℝ) (hfix : P.mulVec v = v) (e f : G2Edge) :
    v e = v f := by
  refine stochastic_fixed_constant P hnn hrow
    (fun a b => Relation.ReflTransGen.mono
      (fun x y hxy => (hsupp x y).mpr hxy) a b
      (g2_strongly_connected a b)) v hfix e f

/-- The constant vector is fixed: `T𝟙 = 𝟙`, so the collapsed
kernel is exactly the line `ℂ𝟙`. -/
theorem row_normalised_ones_fixed (P : Matrix G2Edge G2Edge ℝ)
    (hrow : ∀ e, ∑ f, P e f = 1) :
    P.mulVec (fun _ => 1) = fun _ => 1 := by
  funext e
  rw [Matrix.mulVec, dotProduct]
  simpa using hrow e

end NCG
