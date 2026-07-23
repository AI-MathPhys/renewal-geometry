/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.SignCocycle

/-!
# The signed predictive cover

The **signed predictive cover** associated with a sign cocycle `χ`
(manuscript, Construction `constr:signed-cover`): the two-sheeted graph with
vertices `V × ℤ/2` and, for every edge `e : x → y` and sheet `η`, a lifted
edge `(x, η) → (y, η + χ e)`.

## Main definitions

* `NCG.Multigraph.signedCover` — the cover graph `G^χ`;
* `NCG.Multigraph.coverProj` — the projection `π : G^χ → G`;
* `NCG.Multigraph.deck` — the deck transformation `τ(x, η) = (x, η + 1)`.

## Main results

* `deck_deck_vmap`, `deck_vmap_ne` — the deck transformation is a free
  involution;
* `deck_transitive_on_fibre` — the deck action is transitive on fibres,
  making `π` a principal `ℤ/2`-cover (Theorem `thm:cover`, existence part);
* `trivializeHom` — if `χ` is a coboundary, the cover is isomorphic (over
  `G`) to the trivial double cover `G^0`; this is the removable direction
  of Theorem `thm:cover` / Corollary `cor:removability`.  The converse is
  `NCG.Multigraph.isCoboundary_of_holonomy_eq_zero` combined with the
  monodromy computation `liftWalk` (lifting a loop shifts the sheet by its
  `χ`-holonomy).
-/

namespace NCG.Multigraph

variable (G : Multigraph)

/-- The **signed predictive cover** `G^χ` (Construction
`constr:signed-cover`): vertices `V × ℤ/2`, and for each edge `e : x → y`
and sheet `η` a lifted edge `(x, η) → (y, η + χ e)`. -/
def signedCover (χ : G.E → ZMod 2) : Multigraph where
  V := G.V × ZMod 2
  E := G.E × ZMod 2
  src := fun p => (G.src p.1, p.2)
  tgt := fun p => (G.tgt p.1, p.2 + χ p.1)

variable {G}

@[simp]
theorem signedCover_src (χ : G.E → ZMod 2) (p : G.E × ZMod 2) :
    (G.signedCover χ).src p = (G.src p.1, p.2) := rfl

@[simp]
theorem signedCover_tgt (χ : G.E → ZMod 2) (p : G.E × ZMod 2) :
    (G.signedCover χ).tgt p = (G.tgt p.1, p.2 + χ p.1) := rfl

/-- The covering projection `π : G^χ → G`. -/
def coverProj (χ : G.E → ZMod 2) : Hom (G.signedCover χ) G where
  vmap := Prod.fst
  emap := Prod.fst
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

/-- The **deck transformation** `τ(x, η) = (x, -η) = (x, η + 1)` of the
signed cover. -/
def deck (χ : G.E → ZMod 2) : Hom (G.signedCover χ) (G.signedCover χ) where
  vmap := fun p => (p.1, p.2 + 1)
  emap := fun p => (p.1, p.2 + 1)
  src_comm := fun _ => rfl
  tgt_comm := fun e => by
    change (G.tgt e.1, e.2 + 1 + χ e.1) = (G.tgt e.1, e.2 + χ e.1 + 1)
    rw [add_right_comm]

/-- The deck transformation is an involution on vertices. -/
@[simp]
theorem deck_deck_vmap (χ : G.E → ZMod 2) (p : (G.signedCover χ).V) :
    (deck χ).vmap ((deck χ).vmap p) = p := by
  cases p with
  | mk x η =>
      change (x, η + 1 + 1) = (x, η)
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The deck transformation acts freely: it fixes no vertex. -/
theorem deck_vmap_ne (χ : G.E → ZMod 2) (p : (G.signedCover χ).V) :
    (deck χ).vmap p ≠ p := by
  cases p with
  | mk x η =>
      intro h
      have hsnd : η + 1 = η := congrArg Prod.snd h
      have h1 : (1 : ZMod 2) = 0 := by
        have := congrArg (fun t => t - η) hsnd
        simp at this
      exact one_ne_zero h1

/-- The deck transformation commutes with the covering projection. -/
@[simp]
theorem coverProj_deck_vmap (χ : G.E → ZMod 2) (p : (G.signedCover χ).V) :
    (coverProj χ).vmap ((deck χ).vmap p) = (coverProj χ).vmap p := rfl

/-- The two sheets over a vertex are exchanged by the deck transformation:
the cover is a **principal `ℤ/2`-cover** (Theorem `thm:cover`). -/
theorem deck_transitive_on_fibre (χ : G.E → ZMod 2) (x : G.V)
    (p q : (G.signedCover χ).V) (hp : (coverProj χ).vmap p = x)
    (hq : (coverProj χ).vmap q = x) :
    q = p ∨ q = (deck χ).vmap p := by
  cases p with
  | mk px pη =>
      cases q with
      | mk qx qη =>
          cases hp
          have hx : qx = px := hq
          subst hx
          have hcases : qη = pη ∨ qη = pη + 1 := by
            have h2 : ∀ a b : ZMod 2, a = b ∨ a = b + 1 := by decide
            exact h2 qη pη
          rcases hcases with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (by change (qx, qη) = (qx, pη + 1); rw [h])

/-- If `χ` is the coboundary of a vertex sign `g`, the signed cover is
isomorphic over `G` to the trivial double cover `G^0` via the sheet gauge
`(v, η) ↦ (v, η + g v)` (removable direction of Theorem `thm:cover`).  The
map below is the underlying morphism; it is bijective on vertices and edges
by construction. -/
def trivializeHom (χ : G.E → ZMod 2) (g : G.V → ZMod 2)
    (hg : ∀ e, χ e = g (G.src e) + g (G.tgt e)) :
    Hom (G.signedCover χ) (G.signedCover fun _ => 0) where
  vmap := fun p => (p.1, p.2 + g p.1)
  emap := fun p => (p.1, p.2 + g (G.src p.1))
  src_comm := fun _ => rfl
  tgt_comm := fun e => by
    change (G.tgt e.1, e.2 + g (G.src e.1) + 0)
      = (G.tgt e.1, e.2 + χ e.1 + g (G.tgt e.1))
    have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
    rw [hg e.1]
    exact Prod.ext rfl (by linear_combination -h2 (g (G.tgt e.1)))

/-- Monodromy of the signed cover: lifting a walk multiplies the sheet label
by the walk's holonomy.  Formally: a walk in `G` from `u` to `v` with
holonomy `h` lifts, from the sheet `η`, to a walk in `G^χ` from `(u, η)` to
`(v, η + h)`.  This is the monodromy statement of Theorem `thm:cover`. -/
def liftWalk (χ : G.E → ZMod 2) :
    ∀ {u v : G.V}, (p : G.Walk u v) → (η : ZMod 2) →
      (G.signedCover χ).Walk (u, η) (v, η + p.holonomy χ)
  | _, _, .nil v, η => by
      simpa using Walk.nil (G := G.signedCover χ) (v, η)
  | _, _, .fwd e p, η => by
      have q := liftWalk χ p (η + χ e)
      have step := Walk.fwd (G := G.signedCover χ) (e, η) (by simpa using q)
      simpa [add_assoc] using step
  | _, _, .bwd e p, η => by
      have q := liftWalk χ p (η + χ e)
      have step := Walk.bwd (G := G.signedCover χ) (e, η + χ e)
        (by simpa using q)
      have hη : η + χ e + χ e = η := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [show ((G.signedCover χ).tgt (e, η + χ e)) = (G.tgt e, η) from
        congrArg (fun t => (G.tgt e, t)) hη] at step
      simpa [add_assoc] using step

end NCG.Multigraph
