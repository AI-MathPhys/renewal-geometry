/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The condensation of a finite directed graph is acyclic

Clause (i) of `prop:terminal-component` in `manuscripts/renewal_emergence/renewal_emergence.tex`:
the condensation graph of the strongly connected components of a
finite directed graph is finite and acyclic.

Strong connectivity is mutual reachability (`MutualReach`), an
equivalence relation; the condensation is its quotient
(`Condensation`), finite whenever the vertex type is
(`condensation_finite`).  Reachability descends to the condensation
(`creach`), where it is reflexive, transitive and — the acyclicity —
**antisymmetric** (`creach_antisymm`): a directed cycle through two
distinct components would merge them.  Equivalently the condensation
carries a partial order (`condensationPartialOrder`).
-/

namespace NCG.Condense

variable {V : Type*} (adj : V → V → Prop)

/-- Reachability: the reflexive-transitive closure of the edge
relation. -/
def Reaches : V → V → Prop := Relation.ReflTransGen adj

/-- Strong connectivity: mutual reachability. -/
def MutualReach (x y : V) : Prop := Reaches adj x y ∧ Reaches adj y x

theorem mutualReach_equivalence : Equivalence (MutualReach adj) :=
  ⟨fun _ => ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩⟩

/-- The setoid of strongly connected components. -/
def sccSetoid : Setoid V := ⟨MutualReach adj, mutualReach_equivalence adj⟩

/-- The condensation: the quotient by strong connectivity. -/
def Condensation := Quotient (sccSetoid adj)

/-- **Clause (i), finiteness**: the condensation of a finite graph
is finite. -/
theorem condensation_finite [Finite V] : Finite (Condensation adj) :=
  Quotient.finite _

/-- Reachability descends to the condensation. -/
def creach : Condensation adj → Condensation adj → Prop :=
  Quotient.lift₂ (Reaches adj) (by
    intro x y x' y' hx hy
    have h1 : Reaches adj x y ↔ Reaches adj x' y' := by
      constructor
      · intro h
        exact (hx.2.trans h).trans hy.1
      · intro h
        exact (hx.1.trans h).trans hy.2
    exact propext h1)

@[simp] theorem creach_mk (x y : V) :
    creach adj (Quotient.mk (sccSetoid adj) x)
        (Quotient.mk (sccSetoid adj) y)
      ↔ Reaches adj x y := Iff.rfl

theorem creach_refl (a : Condensation adj) : creach adj a a := by
  induction a using Quotient.ind with | _ x =>
  exact Relation.ReflTransGen.refl

theorem creach_trans {a b c : Condensation adj}
    (hab : creach adj a b) (hbc : creach adj b c) :
    creach adj a c := by
  induction a using Quotient.ind with | _ x =>
  induction b using Quotient.ind with | _ y =>
  induction c using Quotient.ind with | _ z =>
  exact Relation.ReflTransGen.trans hab hbc

/-- **Clause (i), acyclicity**: descended reachability is
antisymmetric — a directed cycle through two components merges them,
so the condensation has no nontrivial directed cycles. -/
theorem creach_antisymm {a b : Condensation adj}
    (hab : creach adj a b) (hba : creach adj b a) : a = b := by
  induction a using Quotient.ind with | _ x =>
  induction b using Quotient.ind with | _ y =>
  exact Quotient.sound ⟨hab, hba⟩

/-- **Proposition `prop:terminal-component` (i)**: the condensation
carries the reachability partial order — finite and acyclic. -/
@[reducible] noncomputable def condensationPartialOrder :
    PartialOrder (Condensation adj) where
  le := creach adj
  le_refl := creach_refl adj
  le_trans _ _ _ := creach_trans adj
  le_antisymm _ _ := creach_antisymm adj

end NCG.Condense
