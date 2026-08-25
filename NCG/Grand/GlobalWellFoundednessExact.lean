/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The global well-foundedness alternative: finite SCC condensation

Machinery for `thm:GT-global-well-foundedness-alternative` (W1–W6): the
record-local exhaustiveness content — "the list is exhaustive by finite SCC
condensation and the first-passage alternative" — on a finite family of
stopping packets with transition relation `step`.

* `exists_recurrent_reachable`: **finite condensation is well-founded** —
  every packet reaches a recurrent state (one whose every successor can
  return), by strict descent of the reachable-set cardinality;
* `recurrent_of_reaches`: recurrence propagates along reachability, so the
  recurrent states reached form genuine closed recurrent components;
* `walk_reaches` / `exists_cofinal_state` / `cofinal_mutually_reachable`:
  every infinite history concentrates cofinally on finitely many states, and
  all cofinally visited states are mutually reachable — the support of a
  cofinal history is contained in one strongly connected class;
* `global_well_foundedness_alternative`: the six-branch alternative — the
  passing branch (W1) holds exactly when every reachable recurrent component
  is closed by one of the three declared modes and all global screens close;
  otherwise a finite witness (W2–W4, via the per-component classification) or
  a screen failure (W5) is returned, and the reachable condensation is
  nonempty so the alternative is never vacuous.
-/

open Relation

namespace NCG
namespace GlobalWellFoundedness

variable {V : Type*} (step : V → V → Prop)

/-- Reachability: the reflexive-transitive closure of the packet transition. -/
def Reaches : V → V → Prop := Relation.ReflTransGen step

/-- The set of states reachable from `x`. -/
def reachSet (x : V) : Set V := {y | Reaches step x y}

theorem self_mem_reachSet (x : V) : x ∈ reachSet step x :=
  Relation.ReflTransGen.refl

theorem reachSet_subset {x z : V} (hxz : Reaches step x z) :
    reachSet step z ⊆ reachSet step x := fun _ hzw => hxz.trans hzw

/-- A state is recurrent when every reachable state can return: it lies in a
closed (bottom) strongly connected component of the condensation. -/
def IsRecurrent (y : V) : Prop := ∀ z, Reaches step y z → Reaches step z y

/-- Recurrence propagates along reachability: the class of a recurrent state
is a closed strongly connected component. -/
theorem recurrent_of_reaches {y z : V} (hy : IsRecurrent step y)
    (hyz : Reaches step y z) : IsRecurrent step z := by
  intro w hzw
  exact (hy w (hyz.trans hzw)).trans hyz

/-- **Finite SCC condensation is well-founded**: every packet reaches a
recurrent state. Strict descent of the reachable-set cardinality. -/
theorem exists_recurrent_reachable [Finite V] (x : V) :
    ∃ y, Reaches step x y ∧ IsRecurrent step y := by
  classical
  have H : ∀ n, ∀ x : V, (reachSet step x).ncard ≤ n →
      ∃ y, Reaches step x y ∧ IsRecurrent step y := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exfalso
      have h0 : (reachSet step x).ncard = 0 := Nat.le_zero.mp hx
      have he : reachSet step x = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp h0
      have hself := self_mem_reachSet step x
      rw [he] at hself
      exact Set.notMem_empty x hself
    | succ n ih =>
      intro x hx
      by_cases hrec : IsRecurrent step x
      · exact ⟨x, Relation.ReflTransGen.refl, hrec⟩
      · obtain ⟨z, hz⟩ := not_forall.mp hrec
        obtain ⟨hxz, hnzx⟩ := Classical.not_imp.mp hz
        have hsub : reachSet step z ⊆ reachSet step x := reachSet_subset step hxz
        have hne : reachSet step z ≠ reachSet step x := by
          intro he
          have hself := self_mem_reachSet step x
          rw [← he] at hself
          exact hnzx hself
        have hlt : (reachSet step z).ncard < (reachSet step x).ncard :=
          Set.ncard_lt_ncard (hsub.ssubset_of_ne hne) (Set.toFinite _)
        obtain ⟨y, hzy, hyrec⟩ := ih z (by omega)
        exact ⟨y, hxz.trans hzy, hyrec⟩
  exact H (reachSet step x).ncard x le_rfl

/-! ### Cofinal histories -/

/-- An infinite history through the packet family. -/
def IsWalk (w : ℕ → V) : Prop := ∀ n, step (w n) (w (n + 1))

theorem walk_reaches {w : ℕ → V} (hw : IsWalk step w) {n m : ℕ}
    (hnm : n ≤ m) : Reaches step (w n) (w m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ m _ ih => exact Relation.ReflTransGen.tail ih (hw m)

/-- Every infinite history visits some state cofinally. -/
theorem exists_cofinal_state [Finite V] (w : ℕ → V) :
    ∃ v, {n | w n = v}.Infinite := by
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber w
  have h1 : (w ⁻¹' {v}).Infinite := Set.infinite_coe_iff.mp hv
  have he : w ⁻¹' {v} = {n | w n = v} := by
    ext n
    simp
  rw [he] at h1
  exact ⟨v, h1⟩

/-- All cofinally visited states of one history are mutually reachable: the
cofinal support lies in a single strongly connected class. -/
theorem cofinal_mutually_reachable {w : ℕ → V} (hw : IsWalk step w)
    {u v : V} (hu : {n | w n = u}.Nonempty) (hv : {n | w n = v}.Infinite) :
    Reaches step u v := by
  obtain ⟨n, hn⟩ := hu
  obtain ⟨m, hm, hnm⟩ := hv.exists_gt n
  have h := walk_reaches step hw (le_of_lt hnm)
  rw [hn, hm] at h
  exact h

/-! ### The six-branch alternative -/

/-- **The global well-foundedness alternative** (W1–W5): given the
per-component classification — every reachable recurrent component is either
closed by a physically paid Bellman current, a finite holonomy/resource
budget, or an independent ancestry order, or else carries one of the finite
failure witnesses (a defeating balanced circulation, a separator without
finite common source balance, or a source-flat component) — either the
passing branch W1 holds (all components closed and all global screens close),
or one of the witnesses W2–W4 is returned, or a screen fails (W5). The
reachable condensation is nonempty, so the alternative is never vacuous. -/
theorem global_well_foundedness_alternative [Finite V] (source : V)
    (Bellman Holo Anc Circ Sep Flat : V → Prop)
    (Margin Screen Joint : Prop)
    (hclassify : ∀ y, IsRecurrent step y → Reaches step source y →
      (Bellman y ∨ Holo y ∨ Anc y) ∨ (Circ y ∨ Sep y ∨ Flat y)) :
    (∃ y, Reaches step source y ∧ IsRecurrent step y) ∧
      (((∀ y, IsRecurrent step y → Reaches step source y →
            Bellman y ∨ Holo y ∨ Anc y) ∧ Margin ∧ Screen ∧ Joint) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Circ y) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Sep y) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Flat y) ∨
        (¬Margin ∨ ¬Screen ∨ ¬Joint)) := by
  classical
  refine ⟨exists_recurrent_reachable step source, ?_⟩
  by_cases hall : ∀ y, IsRecurrent step y → Reaches step source y →
      Bellman y ∨ Holo y ∨ Anc y
  · by_cases hM : Margin
    · by_cases hS : Screen
      · by_cases hJ : Joint
        · exact Or.inl ⟨hall, hM, hS, hJ⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · obtain ⟨y, hy⟩ := not_forall.mp hall
    obtain ⟨hrec, hy2⟩ := Classical.not_imp.mp hy
    obtain ⟨hreach, hy3⟩ := Classical.not_imp.mp hy2
    rcases hclassify y hrec hreach with hgood | hbad
    · exact absurd hgood hy3
    · rcases hbad with hC | hSp | hF
      · exact Or.inr (Or.inl ⟨y, hrec, hreach, hC⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨y, hrec, hreach, hSp⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hrec, hreach, hF⟩)))

end GlobalWellFoundedness
end NCG
