/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Graph.SpanningTree
import RenewalGeometry.Spectralization.MarkedSpectralBundleDescentExact

/-!
# Spanning-tree normal form of flat marked bundles

This file completes `thm:supp-marked-bundle` of `papers/predictive_spectral_geometry` on top of
`MarkedSpectralBundleDescentExact` (walk holonomy, (B2)–(B4) at the level of closed walks) and the
spanning-tree infrastructure `NCG.Graph.SpanningTree`.

Fix a rooted spanning tree `T` of the graph at the base vertex `v₀` (one exists on every connected
graph, `NCG.Multigraph.SpanningTree.bfs`) and let the chords be the non-tree edges; there are
`b₁ = |E| - |V| + 1 = dim H¹(G;ℤ/2)` of them (`SpanningTree.card_chords_eq_finrank_H1`).

* **Gauge fixing.**  The frame `g(v) = (hol_U(tree path to v))⁻¹` makes every tree edge trivial
  (`isTreeNormal_gaugeAct_treeGauge`) and turns each chord label into the holonomy of its
  fundamental cycle (`gaugeAct_treeGauge_apply`).
* **(B1), chord holonomies.**  `rho T U : FreeGroup (chords) →* G_𝖲` is the homomorphism sending a
  chord to the holonomy of its fundamental cycle.  Every closed-walk monodromy factors through it,
  `hol_U(p) = ρ_U(chordWord p)` (`holonomy_eq_rho_chordWord`), where the chord word of a walk is
  multiplicative, inverted by reversal, invariant under backtracking, and surjective from closed
  walks at `v₀` onto the free group on the chords (`chordWord_surjective`).
* **(B2)–(B4) for `ρ_U`.**  A frame change conjugates `ρ_U` by one element (`rho_gaugeAct`); a
  global
  trivialisation exists iff `ρ_U = 1` (`isGloballyTrivial_iff_rho_eq_one`); two bundles are
  isomorphic iff their `ρ`'s are conjugate (`gaugeEquivalent_iff_rho_conj`).
* **Determination by `b₁` elements.**  Tree-normal bundles are gauge equivalent iff their chord
  tuples are simultaneously conjugate (`gaugeEquivalent_iff_of_isTreeNormal`), every chord tuple
  is realised by exactly one tree-normal bundle (`existsUnique_isTreeNormal`), and the isomorphism
  classes of flat marked bundles are in bijection with `b₁`-tuples of elements of `G_𝖲` modulo
  simultaneous conjugation (`gaugeClassEquiv`).

The fundamental group `π₁(Γ, v₀)` is not defined as a group in the library; its role is played by
the free group on the chords together with the surjective, multiplicative, backtracking-invariant
chord-word map from closed walks.
-/

namespace RenewalGeometry
namespace MarkedBundle

open NCG NCG.Multigraph

variable {G : Multigraph} {Γ : Type*} [Group Γ] {v₀ : G.V} (T : SpanningTree G v₀)

namespace TreeGauge

/-! ## Tree paths and fundamental cycles -/

/-- Along a tree edge, the tree path to the source followed by the edge has the holonomy of the
tree path to the target. -/
theorem holonomy_path_mul_parent (U : G.E → Γ) (v : G.V) (hv : v ≠ v₀) :
    holonomy U (T.path (G.src (T.parent v hv))) * U (T.parent v hv) =
      holonomy U (T.path (G.tgt (T.parent v hv))) := by
  rcases T.parent_spec v hv with ⟨hs, -⟩ | ⟨ht, -⟩
  · rw [T.path_src v hv hs, holonomy_append, holonomy_singleRev, inv_mul_cancel_right]
  · rw [T.path_tgt v hv ht, holonomy_append, holonomy_single]

theorem holonomy_path_mul_of_mem (U : G.E → Γ) {e : G.E} (he : e ∈ T.treeEdges) :
    holonomy U (T.path (G.src e)) * U e = holonomy U (T.path (G.tgt e)) := by
  obtain ⟨v, hv, rfl⟩ := he
  exact holonomy_path_mul_parent T U v hv

/-- The fundamental cycle of an edge: tree path to its source, the edge, and the tree path back
from its target. -/
def fundCycle (e : G.E) : G.Walk v₀ v₀ :=
  ((T.path (G.src e)).append (Walk.single e)).append (T.path (G.tgt e)).reverse

theorem holonomy_fundCycle (U : G.E → Γ) (e : G.E) :
    holonomy U (fundCycle T e) =
      holonomy U (T.path (G.src e)) * U e * (holonomy U (T.path (G.tgt e)))⁻¹ := by
  simp [fundCycle]

/-! ## Gauge fixing along the tree -/

/-- The tree frame `g(v) = (hol_U(tree path to v))⁻¹`. -/
def treeGauge (U : G.E → Γ) : G.V → Γ := fun v => (holonomy U (T.path v))⁻¹

theorem treeGauge_root (U : G.E → Γ) : treeGauge T U v₀ = 1 := by
  simp [treeGauge, T.path_root]

/-- In the tree frame every edge label becomes the holonomy of its fundamental cycle. -/
theorem gaugeAct_treeGauge_apply (U : G.E → Γ) (e : G.E) :
    gaugeAct (treeGauge T U) U e = holonomy U (fundCycle T e) := by
  rw [gaugeAct_apply, holonomy_fundCycle, treeGauge, treeGauge, inv_inv]

/-- A bundle datum is in tree normal form when it is trivial on every tree edge. -/
def IsTreeNormal (U : G.E → Γ) : Prop := ∀ e ∈ T.treeEdges, U e = 1

/-- **Gauge fixing**: the tree frame makes every tree edge trivial. -/
theorem isTreeNormal_gaugeAct_treeGauge (U : G.E → Γ) :
    IsTreeNormal T (gaugeAct (treeGauge T U) U) := fun e he => by
  rw [gaugeAct_treeGauge_apply, holonomy_fundCycle, holonomy_path_mul_of_mem T U he,
    mul_inv_cancel]

/-- For a tree-normal bundle, tree paths have trivial holonomy. -/
theorem holonomy_path_of_isTreeNormal {U : G.E → Γ} (hU : IsTreeNormal T U) (v : G.V) :
    holonomy U (T.path v) = 1 := by
  induction h : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = v₀
    · subst hv
      rw [T.path_root]
      rfl
    · have hmem := hU _ (T.parent_mem_treeEdges v hv)
      rcases T.parent_spec v hv with ⟨hs, hd⟩ | ⟨ht, hd⟩
      · have hih := ih _ (by omega) (G.tgt (T.parent v hv)) rfl
        have key : holonomy U (T.path (G.src (T.parent v hv))) = 1 := by
          rw [T.path_src v hv hs, holonomy_append, hih, holonomy_singleRev, hmem]
          simp
        rwa [hs] at key
      · have hih := ih _ (by omega) (G.src (T.parent v hv)) rfl
        have key : holonomy U (T.path (G.tgt (T.parent v hv))) = 1 := by
          rw [T.path_tgt v hv ht, holonomy_append, hih, holonomy_single, hmem]
          simp
        rwa [ht] at key

/-- For a tree-normal bundle, the fundamental cycle of `e` has holonomy `U e`. -/
theorem holonomy_fundCycle_of_isTreeNormal {U : G.E → Γ} (hU : IsTreeNormal T U) (e : G.E) :
    holonomy U (fundCycle T e) = U e := by
  rw [holonomy_fundCycle, holonomy_path_of_isTreeNormal T hU,
    holonomy_path_of_isTreeNormal T hU]
  simp

/-- Every bundle is gauge equivalent to a tree-normal one, whose labels are the
fundamental-cycle holonomies of the original bundle. -/
theorem exists_isTreeNormal_gaugeEquivalent (U : G.E → Γ) :
    ∃ U' : G.E → Γ, IsTreeNormal T U' ∧ GaugeEquivalent U U' ∧
      ∀ e, U' e = holonomy U (fundCycle T e) :=
  ⟨_, isTreeNormal_gaugeAct_treeGauge T U, ⟨_, rfl⟩, gaugeAct_treeGauge_apply T U⟩

/-! ## Classification of tree normal forms -/

/-- **Tree-normal bundles are isomorphic iff their chord labels are simultaneously
conjugate.** -/
theorem gaugeEquivalent_iff_of_isTreeNormal {U U' : G.E → Γ} (hU : IsTreeNormal T U)
    (hU' : IsTreeNormal T U') :
    GaugeEquivalent U U' ↔ ∃ c : Γ, ∀ e, e ∉ T.treeEdges → U' e = c⁻¹ * U e * c := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g v₀, fun e _ => ?_⟩
    rw [← holonomy_fundCycle_of_isTreeNormal T hU' e, holonomy_gaugeAct_loop,
      holonomy_fundCycle_of_isTreeNormal T hU e]
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, funext fun e => ?_⟩
    by_cases he : e ∈ T.treeEdges
    · rw [gaugeAct_apply, hU e he, hU' e he]
      group
    · rw [gaugeAct_apply, hc e he]

/-- The chords `E \ T`. -/
abbrev Chord : Type _ := {e : G.E // e ∉ T.treeEdges}

/-- **Every chord tuple is realised by exactly one tree-normal bundle.** -/
theorem existsUnique_isTreeNormal (x : Chord T → Γ) :
    ∃! U : G.E → Γ, IsTreeNormal T U ∧ ∀ c : Chord T, U c.1 = x c := by
  classical
  refine ⟨fun e => if he : e ∈ T.treeEdges then 1 else x ⟨e, he⟩,
    ⟨fun e he => by simp [he], fun c => by simp [c.2]⟩, ?_⟩
  rintro U ⟨hU, hx⟩
  funext e
  by_cases he : e ∈ T.treeEdges
  · simp [he, hU e he]
  · simp only [he, dite_false]
    exact hx ⟨e, he⟩

/-! ## (B1): the chord-holonomy homomorphism on the free group of chords -/

/-- The chord labelling `e ↦ [e]` (trivial on tree edges) with values in the free group on the
chords. -/
noncomputable def chordLabel : G.E → FreeGroup (Chord T) := by
  classical
  exact fun e => if he : e ∈ T.treeEdges then 1 else FreeGroup.of ⟨e, he⟩

theorem isTreeNormal_chordLabel : IsTreeNormal T (chordLabel T) := fun e he => by
  classical
  simp [chordLabel, he]

/-- The chord word of a walk: the ordered product of the chords it traverses (with inverses for
backward traversals). -/
noncomputable def chordWord {u v : G.V} (p : G.Walk u v) : FreeGroup (Chord T) :=
  holonomy (chordLabel T) p

theorem chordWord_append {u v w : G.V} (p : G.Walk u v) (q : G.Walk v w) :
    chordWord T (p.append q) = chordWord T p * chordWord T q :=
  holonomy_append _ p q

theorem chordWord_reverse {u v : G.V} (p : G.Walk u v) :
    chordWord T p.reverse = (chordWord T p)⁻¹ :=
  holonomy_reverse _ p

theorem chordWord_fwd_bwd (e : G.E) {w : G.V} (p : G.Walk (G.src e) w) :
    chordWord T (Walk.fwd e (Walk.bwd e p)) = chordWord T p :=
  holonomy_fwd_bwd _ e p

theorem chordWord_fundCycle (c : Chord T) : chordWord T (fundCycle T c.1) = FreeGroup.of c := by
  classical
  rw [chordWord, holonomy_fundCycle_of_isTreeNormal T (isTreeNormal_chordLabel T)]
  simp [chordLabel, c.2]

/-- The chord word is onto the free group on the chords (closed walks at `v₀`). -/
theorem chordWord_surjective :
    Function.Surjective (fun p : G.Walk v₀ v₀ => chordWord T p) := by
  intro w
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨Walk.nil v₀, rfl⟩
  | of c => exact ⟨fundCycle T c.1, chordWord_fundCycle T c⟩
  | inv_of c _ => exact ⟨(fundCycle T c.1).reverse, by
      simp only [chordWord_reverse, chordWord_fundCycle]⟩
  | mul x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p.append q, chordWord_append T p q⟩

/-- The chord-holonomy homomorphism `ρ_U : F(chords) → G_𝖲`, sending a chord to the holonomy of
its fundamental cycle (B1). -/
noncomputable def rho (U : G.E → Γ) : FreeGroup (Chord T) →* Γ :=
  FreeGroup.lift fun c => holonomy U (fundCycle T c.1)

theorem rho_of (U : G.E → Γ) (c : Chord T) :
    rho T U (FreeGroup.of c) = holonomy U (fundCycle T c.1) :=
  FreeGroup.lift_apply_of

/-- For a tree-normal bundle the holonomy of any walk is read off its chord word. -/
theorem holonomy_eq_lift_chordWord {U : G.E → Γ} (hU : IsTreeNormal T U) {u v : G.V}
    (p : G.Walk u v) :
    holonomy U p = FreeGroup.lift (fun c : Chord T => U c.1) (chordWord T p) := by
  classical
  have hlab : ∀ e, FreeGroup.lift (fun c : Chord T => U c.1) (chordLabel T e) = U e := by
    intro e
    by_cases he : e ∈ T.treeEdges
    · simp [chordLabel, he, hU e he]
    · simp [chordLabel, he]
  induction p with
  | nil v => simp [chordWord]
  | fwd e p ih =>
      simp only [chordWord, holonomy_fwd, map_mul] at ih ⊢
      rw [ih, hlab]
  | bwd e p ih =>
      simp only [chordWord, holonomy_bwd, map_mul, map_inv] at ih ⊢
      rw [ih, hlab]

/-- **(B1)**: every closed-walk monodromy factors through the chord-holonomy homomorphism,
`hol_U(p) = ρ_U(chordWord p)`. -/
theorem holonomy_eq_rho_chordWord (U : G.E → Γ) (p : G.Walk v₀ v₀) :
    holonomy U p = rho T U (chordWord T p) := by
  have h1 : holonomy (gaugeAct (treeGauge T U) U) p = holonomy U p := by
    rw [holonomy_gaugeAct_loop, treeGauge_root]
    group
  rw [← h1, holonomy_eq_lift_chordWord T (isTreeNormal_gaugeAct_treeGauge T U), rho]
  congr 2
  funext c
  exact gaugeAct_treeGauge_apply T U c.1

/-- `ρ_U` is determined by the `b₁` chord holonomies: two bundles with the same
fundamental-cycle holonomies have the same `ρ`. -/
theorem rho_eq_iff (U U' : G.E → Γ) :
    rho T U = rho T U' ↔
      ∀ c : Chord T, holonomy U (fundCycle T c.1) = holonomy U' (fundCycle T c.1) := by
  constructor
  · intro h c
    rw [← rho_of, ← rho_of, h]
  · intro h
    exact FreeGroup.ext_hom _ _ fun c => by rw [rho_of, rho_of, h c]

/-- **(B2)**: a frame change conjugates `ρ_U` by the single element `g v₀`. -/
theorem rho_gaugeAct (g : G.V → Γ) (U : G.E → Γ) (w : FreeGroup (Chord T)) :
    rho T (gaugeAct g U) w = (g v₀)⁻¹ * rho T U w * g v₀ := by
  obtain ⟨p, rfl⟩ := chordWord_surjective T w
  rw [← holonomy_eq_rho_chordWord, ← holonomy_eq_rho_chordWord, holonomy_gaugeAct_loop]

/-- **(B3)**: a global marked trivialisation exists iff `ρ_U` is trivial. -/
theorem isGloballyTrivial_iff_rho_eq_one (U : G.E → Γ) :
    IsGloballyTrivial U ↔ rho T U = 1 := by
  rw [globallyTrivial_iff_holonomy_eq_one U T.connectedTo]
  constructor
  · intro h
    refine FreeGroup.ext_hom _ _ fun c => ?_
    rw [rho_of, h, MonoidHom.one_apply]
  · intro h p
    rw [holonomy_eq_rho_chordWord T U p, h, MonoidHom.one_apply]

/-- **(B4)**: two flat marked bundles are isomorphic iff their chord-holonomy homomorphisms are
conjugate by one element: the class `[ρ_U] ∈ Hom(F(chords), G_𝖲)/G_𝖲`. -/
theorem gaugeEquivalent_iff_rho_conj (U U' : G.E → Γ) :
    GaugeEquivalent U U' ↔ ∃ c : Γ, ∀ w, rho T U' w = c⁻¹ * rho T U w * c := by
  rw [gaugeEquivalent_iff_holonomy_conj U U' T.connectedTo]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun w => ?_⟩
    obtain ⟨p, rfl⟩ := chordWord_surjective T w
    simp only
    rw [← holonomy_eq_rho_chordWord, ← holonomy_eq_rho_chordWord, hc p]
  · rintro ⟨c, hc⟩
    exact ⟨c, fun p => by rw [holonomy_eq_rho_chordWord T U' p, holonomy_eq_rho_chordWord T U p,
      hc]⟩

/-! ## Isomorphism classes = `b₁`-tuples modulo simultaneous conjugation -/

/-- Gauge equivalence is an equivalence relation. -/
def gaugeSetoid (G : Multigraph) (Γ : Type*) [Group Γ] : Setoid (G.E → Γ) where
  r := GaugeEquivalent
  iseqv := by
    refine ⟨fun U => ⟨fun _ => 1, funext fun e => by simp⟩, ?_, ?_⟩
    · rintro U U' ⟨g, rfl⟩
      refine ⟨fun v => (g v)⁻¹, ?_⟩
      rw [gaugeAct_gaugeAct]
      funext e
      simp
    · rintro U U' U'' ⟨g, rfl⟩ ⟨g', rfl⟩
      exact ⟨_, (gaugeAct_gaugeAct g g' U).symm⟩

/-- Simultaneous conjugation of chord tuples. -/
def conjSetoid (ι Γ : Type*) [Group Γ] : Setoid (ι → Γ) where
  r x y := ∃ c : Γ, ∀ i, y i = c⁻¹ * x i * c
  iseqv := by
    refine ⟨fun x => ⟨1, fun i => by simp⟩, ?_, ?_⟩
    · rintro x y ⟨c, hc⟩
      exact ⟨c⁻¹, fun i => by rw [hc i]; group⟩
    · rintro x y z ⟨c, hc⟩ ⟨d, hd⟩
      exact ⟨c * d, fun i => by rw [hd i, hc i]; group⟩

/-- The chord-holonomy tuple of a bundle. -/
def chordHolonomy (U : G.E → Γ) : Chord T → Γ := fun c => holonomy U (fundCycle T c.1)

theorem gaugeEquivalent_iff_chordHolonomy_conj (U U' : G.E → Γ) :
    GaugeEquivalent U U' ↔ (conjSetoid (Chord T) Γ).r (chordHolonomy T U) (chordHolonomy T U') := by
  rw [gaugeEquivalent_iff_rho_conj T]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun i => by simpa only [chordHolonomy, rho_of] using hc (FreeGroup.of i)⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun w => ?_⟩
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of i => simpa only [chordHolonomy, rho_of] using hc i
    | inv_of i h => rw [map_inv, map_inv, h]; group
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy]; group

/-- **Classification (`thm:supp-marked-bundle`, last sentence).**  After choosing a spanning
tree, isomorphism classes of flat marked bundles correspond bijectively to tuples of elements of
`G_𝖲` indexed by the `b₁` chords, modulo simultaneous conjugation. -/
noncomputable def gaugeClassEquiv :
    Quotient (gaugeSetoid G Γ) ≃ Quotient (conjSetoid (Chord T) Γ) where
  toFun := Quotient.map (chordHolonomy T) fun U U' h =>
    (gaugeEquivalent_iff_chordHolonomy_conj T U U').1 h
  invFun := Quotient.map (fun x => Classical.choose (existsUnique_isTreeNormal T x))
    fun x y h => by
      have hx := (Classical.choose_spec (existsUnique_isTreeNormal T x)).1
      have hy := (Classical.choose_spec (existsUnique_isTreeNormal T y)).1
      refine (gaugeEquivalent_iff_of_isTreeNormal T hx.1 hy.1).2 ?_
      obtain ⟨c, hc⟩ := h
      exact ⟨c, fun e he => by rw [hy.2 ⟨e, he⟩, hx.2 ⟨e, he⟩, hc]⟩
  left_inv := by
    rintro ⟨U⟩
    refine Quotient.sound ?_
    show GaugeEquivalent _ U
    set x := chordHolonomy T U
    have hx := (Classical.choose_spec (existsUnique_isTreeNormal T x)).1
    obtain ⟨U', hU', hUU', hval⟩ := exists_isTreeNormal_gaugeEquivalent T U
    have h1 : GaugeEquivalent (Classical.choose (existsUnique_isTreeNormal T x)) U' :=
      (gaugeEquivalent_iff_of_isTreeNormal T hx.1 hU').2
        ⟨1, fun e he => by rw [hval, hx.2 ⟨e, he⟩]; simp [x, chordHolonomy]⟩
    exact (gaugeSetoid G Γ).iseqv.trans h1 ((gaugeSetoid G Γ).iseqv.symm hUU')
  right_inv := by
    rintro ⟨x⟩
    refine Quotient.sound ?_
    have hx := (Classical.choose_spec (existsUnique_isTreeNormal T x)).1
    refine ⟨1, fun c => ?_⟩
    simp only [chordHolonomy, holonomy_fundCycle_of_isTreeNormal T hx.1, hx.2 c]
    group

/-- **`thm:supp-marked-bundle` with the spanning-tree normal form.**  On a finite connected
multigraph with a rooted spanning tree `T` at `v₀` (one exists, `SpanningTree.bfs`):

* there are exactly `b₁ = dim H¹(G;ℤ/2) = |E| - |V| + 1` chords;
* (B1) every closed-walk monodromy factors as `hol_U(p) = ρ_U(chordWord p)` through the
  chord-holonomy homomorphism `ρ_U : F(chords) →* G_𝖲`, the chord word being onto;
* (B2) a frame change conjugates `ρ_U` by one element;
* (B3) a global marked trivialisation exists iff `ρ_U = 1`;
* (B4) two bundles are isomorphic iff their `ρ`'s are conjugate by one element;
* every bundle is gauge equivalent to a tree-normal one, and tree-normal bundles are isomorphic
  iff their chord tuples (`b₁` elements of `G_𝖲`) are simultaneously conjugate. -/
theorem marked_bundle_spanning_tree [Fintype G.V] [DecidableEq G.V] [Fintype G.E]
    [DecidableEq G.E] (U : G.E → Γ) :
    T.chordFinset.card = Module.finrank (ZMod 2) (H1 G) ∧
    T.chordFinset.card + Fintype.card G.V = Fintype.card G.E + 1 ∧
    (∀ p : G.Walk v₀ v₀, holonomy U p = rho T U (chordWord T p)) ∧
    Function.Surjective (fun p : G.Walk v₀ v₀ => chordWord T p) ∧
    (∀ g : G.V → Γ, ∀ w, rho T (gaugeAct g U) w = (g v₀)⁻¹ * rho T U w * g v₀) ∧
    (IsGloballyTrivial U ↔ rho T U = 1) ∧
    (∀ U' : G.E → Γ, GaugeEquivalent U U' ↔ ∃ c : Γ, ∀ w, rho T U' w = c⁻¹ * rho T U w * c) ∧
    (∃ U' : G.E → Γ, IsTreeNormal T U' ∧ GaugeEquivalent U U') ∧
    (∀ U₁ U₂ : G.E → Γ, IsTreeNormal T U₁ → IsTreeNormal T U₂ →
      (GaugeEquivalent U₁ U₂ ↔ ∃ c : Γ, ∀ e, e ∉ T.treeEdges → U₂ e = c⁻¹ * U₁ e * c)) :=
  ⟨T.card_chords_eq_finrank_H1, T.card_chords_add_card, holonomy_eq_rho_chordWord T U,
    chordWord_surjective T, fun g w => rho_gaugeAct T g U w, isGloballyTrivial_iff_rho_eq_one T U,
    gaugeEquivalent_iff_rho_conj T U,
    (exists_isTreeNormal_gaugeEquivalent T U).imp fun _ h => ⟨h.1, h.2.1⟩,
    fun _ _ h₁ h₂ => gaugeEquivalent_iff_of_isTreeNormal T h₁ h₂⟩

/-! ## Non-vacuity: the one-loop graph has one chord -/

/-- The one-vertex, one-loop graph (`b₁ = 1`). -/
def loopGraph : Multigraph := ⟨Unit, Unit, fun _ => (), fun _ => ()⟩

instance : Fintype loopGraph.V := inferInstanceAs (Fintype Unit)
instance : Fintype loopGraph.E := inferInstanceAs (Fintype Unit)
instance : DecidableEq loopGraph.V := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq loopGraph.E := inferInstanceAs (DecidableEq Unit)

theorem loopGraph_connectedTo : loopGraph.ConnectedTo () := fun _ => ⟨Walk.nil _⟩

/-- The breadth-first spanning tree of the one-loop graph has exactly one chord, so flat marked
bundles on it are classified by one element of `G_𝖲` up to conjugation. -/
theorem loopGraph_card_chords :
    (SpanningTree.bfs loopGraph_connectedTo).chordFinset.card = 1 := by
  have := (SpanningTree.bfs loopGraph_connectedTo).card_chords_add_card
  have hV : Fintype.card loopGraph.V = 1 := rfl
  have hE : Fintype.card loopGraph.E = 1 := rfl
  omega

end TreeGauge

end MarkedBundle
end RenewalGeometry
