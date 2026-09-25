/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.Multigraph

/-!
# Marked spectral-bundle descent on a graph

Paper `predictive_spectral_geometry`, labels `thm:supp-marked-bundle`
(marked spectral-bundle descent) and `cor:supp-twisted-bundle` (nontrivial
monodromy is a twisted geometry).

After identifying every vertex packet with the reference marked packet `𝖲`,
a flat marked spectral bundle over a multigraph `Γ` is an edge labelling
`U : E → G_𝖲` by marked unitary isomorphisms, with the backward edge carrying
`U_{ē} = U_e⁻¹`.  The group `G_𝖲 = Aut(𝖲)` is modelled by an arbitrary group
`Γ` (the paper's compactness plays no role in the descent statements).

* `holonomy U p` is the ordered product of the edge labels along a walk
  (backward traversals contribute inverses).  It is multiplicative under
  concatenation (`holonomy_append`), unital (`holonomy_nil`), inverts under
  reversal (`holonomy_reverse`) and is invariant under backtracking
  (`holonomy_fwd_bwd`, `holonomy_bwd_fwd`); restricted to closed walks at a
  base vertex `v₀` this is the monodromy homomorphism `ρ_U : π₁(Γ, v₀) → G_𝖲`
  of (B1), with `π₁` presented by closed walks modulo backtracking.
* (B2) `holonomy_gaugeAct_loop`: a change of vertex frames `g : V → Γ`
  conjugates every loop holonomy by the single element `g v₀`.
* (B3) `globallyTrivial_iff_holonomy_eq_one`: on a connected graph a global
  marked trivialisation (a frame change making every edge map the identity)
  exists iff `ρ_U` is trivial.
* (B4) `gaugeEquivalent_iff_holonomy_conj`: two flat marked bundles are
  isomorphic (gauge equivalent) iff their monodromies at `v₀` are conjugate by
  one element of `Γ` — the clutching classification
  `[ρ_U] ∈ Hom(π₁(Γ), G_𝖲)/G_𝖲`.
* `cor:supp-twisted-bundle`: `isFlatTwisted_of_holonomy_ne_one` — nontrivial
  monodromy forbids any global marked trivialisation.

Not formalised: the presentation of `π₁(Γ)` as the free group on the chords of
a spanning tree (so that `ρ_U` is determined by `b₁(Γ)` elements of `G_𝖲`);
the walk-level statements above are the ones the paper's proof establishes.
-/

namespace RenewalGeometry
namespace MarkedBundle

open NCG NCG.Multigraph

variable {G : Multigraph} {Γ : Type*} [Group Γ]

/-! ### Walk holonomy of an edge labelling -/

/-- The holonomy (ordered product of edge labels) of a walk for the flat
bundle datum `U : E → Γ`; a backward traversal of `e` contributes
`U_{ē} = U_e⁻¹`. -/
def holonomy (U : G.E → Γ) : ∀ {u v : G.V}, G.Walk u v → Γ
  | _, _, .nil _ => 1
  | _, _, .fwd e p => U e * holonomy U p
  | _, _, .bwd e p => (U e)⁻¹ * holonomy U p

@[simp] theorem holonomy_nil (U : G.E → Γ) (v : G.V) :
    holonomy U (Walk.nil v) = 1 := rfl

@[simp] theorem holonomy_fwd (U : G.E → Γ) (e : G.E) {w : G.V}
    (p : G.Walk (G.tgt e) w) :
    holonomy U (Walk.fwd e p) = U e * holonomy U p := rfl

@[simp] theorem holonomy_bwd (U : G.E → Γ) (e : G.E) {w : G.V}
    (p : G.Walk (G.src e) w) :
    holonomy U (Walk.bwd e p) = (U e)⁻¹ * holonomy U p := rfl

/-- Holonomy is multiplicative under concatenation (the homomorphism property
of `ρ_U`, (B1)). -/
@[simp] theorem holonomy_append (U : G.E → Γ) {u v w : G.V} (p : G.Walk u v)
    (q : G.Walk v w) :
    holonomy U (p.append q) = holonomy U p * holonomy U q := by
  induction p with
  | nil v => simp
  | fwd e p ih => simp [ih, mul_assoc]
  | bwd e p ih => simp [ih, mul_assoc]

@[simp] theorem holonomy_single (U : G.E → Γ) (e : G.E) :
    holonomy U (Walk.single e) = U e := by
  simp [Walk.single]

@[simp] theorem holonomy_singleRev (U : G.E → Γ) (e : G.E) :
    holonomy U (Walk.singleRev e) = (U e)⁻¹ := by
  simp [Walk.singleRev]

/-- Holonomy inverts under reversal of the walk. -/
@[simp] theorem holonomy_reverse (U : G.E → Γ) {u v : G.V} (p : G.Walk u v) :
    holonomy U p.reverse = (holonomy U p)⁻¹ := by
  induction p with
  | nil v => simp [Walk.reverse]
  | fwd e p ih => simp [Walk.reverse, ih, mul_inv_rev]
  | bwd e p ih => simp [Walk.reverse, ih, mul_inv_rev]

/-- Backtracking invariance: traversing `e` forwards and immediately
backwards does not change the holonomy, so `holonomy` descends to
homotopy classes of walks (`π₁`). -/
@[simp] theorem holonomy_fwd_bwd (U : G.E → Γ) (e : G.E) {w : G.V}
    (p : G.Walk (G.src e) w) :
    holonomy U (Walk.fwd e (Walk.bwd e p)) = holonomy U p := by
  simp [mul_inv_cancel_left]

@[simp] theorem holonomy_bwd_fwd (U : G.E → Γ) (e : G.E) {w : G.V}
    (p : G.Walk (G.tgt e) w) :
    holonomy U (Walk.bwd e (Walk.fwd e p)) = holonomy U p := by
  simp [inv_mul_cancel_left]

/-- The walk-level monodromy `ρ_U` at the base vertex `v₀`: the holonomy
function on closed walks at `v₀` (a homomorphism by `holonomy_append`,
`holonomy_nil`, invariant under backtracking). -/
def monodromy (U : G.E → Γ) (v₀ : G.V) : G.Walk v₀ v₀ → Γ :=
  fun p => holonomy U p

theorem monodromy_mul (U : G.E → Γ) (v₀ : G.V) (p q : G.Walk v₀ v₀) :
    monodromy U v₀ (p.append q) = monodromy U v₀ p * monodromy U v₀ q :=
  holonomy_append U p q

theorem monodromy_one (U : G.E → Γ) (v₀ : G.V) :
    monodromy U v₀ (Walk.nil v₀) = 1 := rfl

/-! ### Frame changes (gauge transformations) -/

/-- The action of a change of vertex frames `g : V → Γ` on the edge labels:
`(g • U)_e = g(src e)⁻¹ U_e g(tgt e)`. -/
def gaugeAct (g : G.V → Γ) (U : G.E → Γ) : G.E → Γ :=
  fun e => (g (G.src e))⁻¹ * U e * g (G.tgt e)

@[simp] theorem gaugeAct_apply (g : G.V → Γ) (U : G.E → Γ) (e : G.E) :
    gaugeAct g U e = (g (G.src e))⁻¹ * U e * g (G.tgt e) := rfl

/-- A frame change transforms the holonomy of a walk `u ⟶ v` by
`g(u)⁻¹ (·) g(v)`. -/
theorem holonomy_gaugeAct (g : G.V → Γ) (U : G.E → Γ) {u v : G.V}
    (p : G.Walk u v) :
    holonomy (gaugeAct g U) p = (g u)⁻¹ * holonomy U p * g v := by
  induction p with
  | nil v => simp
  | fwd e p ih =>
      simp only [holonomy_fwd, gaugeAct_apply, ih]
      group
  | bwd e p ih =>
      simp only [holonomy_bwd, gaugeAct_apply, ih, mul_inv_rev, inv_inv]
      group

/-- **(B2) of `thm:supp-marked-bundle`.**  Changing vertex frames conjugates
the monodromy `ρ_U` by the single element `g v₀`. -/
theorem holonomy_gaugeAct_loop (g : G.V → Γ) (U : G.E → Γ) {v₀ : G.V}
    (p : G.Walk v₀ v₀) :
    holonomy (gaugeAct g U) p = (g v₀)⁻¹ * holonomy U p * g v₀ :=
  holonomy_gaugeAct g U p

theorem monodromy_gaugeAct (g : G.V → Γ) (U : G.E → Γ) (v₀ : G.V) :
    monodromy (gaugeAct g U) v₀ = fun p => (g v₀)⁻¹ * monodromy U v₀ p * g v₀ :=
  funext fun p => holonomy_gaugeAct_loop g U p

/-- Gauge transformations compose: `g' • (g • U) = (g · g') • U`. -/
theorem gaugeAct_gaugeAct (g g' : G.V → Γ) (U : G.E → Γ) :
    gaugeAct g' (gaugeAct g U) = gaugeAct (fun v => g v * g' v) U := by
  funext e
  simp only [gaugeAct_apply, mul_inv_rev]
  group

/-- A global marked trivialisation: a frame change in which every edge map
becomes the identity. -/
def IsGlobalTrivialization (g : G.V → Γ) (U : G.E → Γ) : Prop :=
  ∀ e, gaugeAct g U e = 1

/-- The flat marked bundle is globally trivial (a globally trivial marked
packet): some frame change trivialises every edge map. -/
def IsGloballyTrivial (U : G.E → Γ) : Prop :=
  ∃ g : G.V → Γ, IsGlobalTrivialization g U

/-- Two flat marked bundle data are isomorphic (gauge equivalent). -/
def GaugeEquivalent (U U' : G.E → Γ) : Prop :=
  ∃ g : G.V → Γ, gaugeAct g U = U'

theorem holonomy_eq_one_of_forall_eq_one {U : G.E → Γ} (hU : ∀ e, U e = 1)
    {u v : G.V} (p : G.Walk u v) : holonomy U p = 1 := by
  induction p with
  | nil v => rfl
  | fwd e p ih => simp [hU e, ih]
  | bwd e p ih => simp [hU e, ih]

/-- A globally trivial bundle has trivial monodromy (the easy direction of
(B3): a global frame telescopes every cycle product). -/
theorem holonomy_eq_one_of_isGloballyTrivial {U : G.E → Γ}
    (h : IsGloballyTrivial U) {v₀ : G.V} (p : G.Walk v₀ v₀) :
    holonomy U p = 1 := by
  obtain ⟨g, hg⟩ := h
  have h1 : holonomy (gaugeAct g U) p = 1 := holonomy_eq_one_of_forall_eq_one hg p
  rw [holonomy_gaugeAct_loop] at h1
  have : holonomy U p = g v₀ * ((g v₀)⁻¹ * holonomy U p * g v₀) * (g v₀)⁻¹ := by group
  rw [this, h1]
  group

/-- **(B3) of `thm:supp-marked-bundle`.**  On a connected graph, a global
marked trivialisation exists if and only if the monodromy `ρ_U` at the base
vertex is trivial.  The trivialising frame is the inverse of the holonomy
transported from `v₀` along any chosen walk; trivial loop holonomy makes it
path independent. -/
theorem globallyTrivial_iff_holonomy_eq_one (U : G.E → Γ) {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) :
    IsGloballyTrivial U ↔ ∀ p : G.Walk v₀ v₀, holonomy U p = 1 := by
  constructor
  · intro h p
    exact holonomy_eq_one_of_isGloballyTrivial h p
  · intro htriv
    have walkTo : ∀ v, G.Walk v₀ v := fun v => (hconn v).some
    refine ⟨fun v => (holonomy U (walkTo v))⁻¹, fun e => ?_⟩
    have hloop := htriv (((walkTo (G.src e)).append (Walk.single e)).append
      (walkTo (G.tgt e)).reverse)
    simp only [holonomy_append, holonomy_single, holonomy_reverse] at hloop
    simp only [gaugeAct_apply, inv_inv]
    exact hloop

/-- **(B4) of `thm:supp-marked-bundle` (clutching classification).**  On a
connected graph, two flat marked bundle data are isomorphic exactly when
their monodromies at `v₀` are conjugate by one element of `Γ`: the
isomorphism class of the bundle is `[ρ_U] ∈ Hom(π₁(Γ, v₀), Γ)/Γ`. -/
theorem gaugeEquivalent_iff_holonomy_conj (U U' : G.E → Γ) {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) :
    GaugeEquivalent U U' ↔
      ∃ c : Γ, ∀ p : G.Walk v₀ v₀, holonomy U' p = c⁻¹ * holonomy U p * c := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g v₀, fun p => holonomy_gaugeAct_loop g U p⟩
  · rintro ⟨c, hc⟩
    have walkTo : ∀ v, G.Walk v₀ v := fun v => (hconn v).some
    refine ⟨fun v => (holonomy U (walkTo v))⁻¹ * c * holonomy U' (walkTo v), ?_⟩
    funext e
    have hloop := hc (((walkTo (G.src e)).append (Walk.single e)).append
      (walkTo (G.tgt e)).reverse)
    simp only [holonomy_append, holonomy_single, holonomy_reverse] at hloop
    have hU' : U' e = (holonomy U' (walkTo (G.src e)))⁻¹ *
        (c⁻¹ * (holonomy U (walkTo (G.src e)) * U e *
          (holonomy U (walkTo (G.tgt e)))⁻¹) * c) * holonomy U' (walkTo (G.tgt e)) := by
      rw [← hloop]
      group
    rw [gaugeAct_apply, hU']
    group

/-- Triviality of the conjugacy class `[ρ_U]` is triviality of `ρ_U`. -/
theorem monodromy_class_trivial_iff (U : G.E → Γ) (v₀ : G.V) :
    (∃ c : Γ, ∀ p : G.Walk v₀ v₀, holonomy U p = c⁻¹ * 1 * c) ↔
      ∀ p : G.Walk v₀ v₀, holonomy U p = 1 := by
  constructor
  · rintro ⟨c, hc⟩ p
    rw [hc p]; group
  · intro h
    exact ⟨1, fun p => by rw [h p]; group⟩

/-- **`thm:supp-marked-bundle` (assembled).**  For a connected graph and a
flat marked bundle datum `U`: (B1) `ρ_U` is multiplicative and unital on
closed walks; (B2) frame changes conjugate `ρ_U` by one element; (B3) a global
marked trivialisation exists iff `ρ_U` is trivial; (B4) gauge equivalence of
bundle data is conjugacy of monodromies. -/
theorem marked_spectral_bundle_descent (U : G.E → Γ) {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) :
    (∀ p q : G.Walk v₀ v₀,
        monodromy U v₀ (p.append q) = monodromy U v₀ p * monodromy U v₀ q) ∧
      monodromy U v₀ (Walk.nil v₀) = 1 ∧
      (∀ p : G.Walk v₀ v₀, monodromy U v₀ p.reverse = (monodromy U v₀ p)⁻¹) ∧
      (∀ g : G.V → Γ, monodromy (gaugeAct g U) v₀ =
        fun p => (g v₀)⁻¹ * monodromy U v₀ p * g v₀) ∧
      (IsGloballyTrivial U ↔ ∀ p : G.Walk v₀ v₀, monodromy U v₀ p = 1) ∧
      (∀ U' : G.E → Γ, GaugeEquivalent U U' ↔
        ∃ c : Γ, ∀ p : G.Walk v₀ v₀,
          monodromy U' v₀ p = c⁻¹ * monodromy U v₀ p * c) :=
  ⟨monodromy_mul U v₀, monodromy_one U v₀, fun p => holonomy_reverse U p,
    fun g => monodromy_gaugeAct g U v₀,
    globallyTrivial_iff_holonomy_eq_one U hconn,
    fun U' => gaugeEquivalent_iff_holonomy_conj U U' hconn⟩

/-! ### `cor:supp-twisted-bundle` -/

/-- A flat twisted spectral geometry: the flat bundle datum admits no global
marked trivialisation (it is not a globally trivial marked packet). -/
def IsFlatTwisted (U : G.E → Γ) : Prop := ¬ IsGloballyTrivial U

/-- **`cor:supp-twisted-bundle`.**  If the monodromy class `[ρ_U]` is
nontrivial (some closed walk has holonomy `≠ 1`), the flat marked bundle is a
flat twisted spectral geometry: no global marked trivialisation exists. -/
theorem isFlatTwisted_of_holonomy_ne_one (U : G.E → Γ) {v₀ : G.V}
    (hnontriv : ∃ p : G.Walk v₀ v₀, holonomy U p ≠ 1) :
    IsFlatTwisted U := by
  rintro htriv
  obtain ⟨p, hp⟩ := hnontriv
  exact hp (holonomy_eq_one_of_isGloballyTrivial htriv p)

/-- The class form of `cor:supp-twisted-bundle`: a nontrivial class
`[ρ_U] ≠ [1]` gives a twisted geometry. -/
theorem isFlatTwisted_of_class_nontrivial (U : G.E → Γ) (v₀ : G.V)
    (hnontriv : ¬ ∃ c : Γ, ∀ p : G.Walk v₀ v₀, holonomy U p = c⁻¹ * 1 * c) :
    IsFlatTwisted U := by
  apply isFlatTwisted_of_holonomy_ne_one U (v₀ := v₀)
  by_contra h
  have h' : ∀ p : G.Walk v₀ v₀, holonomy U p = 1 := fun p => by
    by_contra hp
    exact h ⟨p, hp⟩
  exact hnontriv ((monodromy_class_trivial_iff U v₀).mpr h')

end MarkedBundle
end RenewalGeometry
