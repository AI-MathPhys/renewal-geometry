/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.FiniteVariationCanonicalHodgeExact

/-!
# Per-component anchoring of the common action
  (`thm:main-common-action`, uniqueness clause; emergent-spacetime manuscript)

`thm:main-common-action` states that, once `α_X = d₀ 𝒮_X` is known to be exact, the
common action `𝒮_X` is unique *after one additive anchor is fixed on each connected
component* of the finite protected variation complex.  The connected case (kernel of `d₀`
= constants, one anchor) is `finiteVariationComplex_commonAction_anchor_unique`; this file
proves the per-component clause.

* `finiteVariationComplex_commonAction_anchor_unique_components` — abstract form: if
  the kernel of `d₀` consists of functions that are constant on the fibres of a component
  labelling `comp : V → ι`, then two common actions with the same coboundary that agree
  at one anchor vertex on each component are equal.
* `finiteVariationComplex_commonAction_anchored_existsUnique` — with the converse
  inclusion (locally constant functions are closed), every exact `α` has exactly one
  common action with prescribed values at the anchors.
* `edgeCoboundary`, `incidenceGraph`, `edgeCoboundary_eq_zero_iff` — on the concrete
  one-skeleton of the complex (oriented edges `src, tgt : E → V`,
  `(d₀ S) e = S (tgt e) - S (src e)`), the kernel of `d₀` is exactly the functions that
  are constant on the connected components of the incidence graph.
* `edgeCoboundary_anchor_unique_components`,
  `edgeCoboundary_anchored_existsUnique` — the uniqueness clause of
  `thm:main-common-action` on the concrete one-skeleton, with one anchor vertex on each
  `SimpleGraph.ConnectedComponent` of the incidence graph.
-/

namespace RenewalGeometry

/-! ### Abstract per-component anchoring -/

/-- `thm:main-common-action`, uniqueness clause (abstract form): if every function in the
kernel of `d₀` is constant on each fibre of the component labelling `comp` (the kernel of
`d₀` consists of locally constant functions), then two common actions with the same
coboundary `α` which agree at one anchor vertex on every component coincide. -/
theorem finiteVariationComplex_commonAction_anchor_unique_components
    {V C₁ ι : Type*} [AddCommGroup C₁] [Module ℝ C₁]
    (d₀ : (V → ℝ) →ₗ[ℝ] C₁) (comp : V → ι)
    (hker : ∀ f : V → ℝ, d₀ f = 0 → ∀ v w, comp v = comp w → f v = f w)
    (α : C₁) (S T : V → ℝ) (anchor : ι → V) (hanchor_comp : ∀ i, comp (anchor i) = i)
    (hS : d₀ S = α) (hT : d₀ T = α)
    (hanchor : ∀ i, S (anchor i) = T (anchor i)) : S = T := by
  have hzero : d₀ (S - T) = 0 := by
    rw [map_sub, hS, hT, sub_self]
  funext v
  have h := hker (S - T) hzero v (anchor (comp v)) (by rw [hanchor_comp])
  simp only [Pi.sub_apply] at h
  have := hanchor (comp v)
  linarith

/-- `thm:main-common-action`, uniqueness clause with existence: when the kernel of `d₀`
is exactly the space of functions constant on each component, every exact one-cochain
`α = d₀ S₀` has exactly one common action taking prescribed values `c i` at the anchor
vertex `anchor i` of each component `i`. -/
theorem finiteVariationComplex_commonAction_anchored_existsUnique
    {V C₁ ι : Type*} [AddCommGroup C₁] [Module ℝ C₁]
    (d₀ : (V → ℝ) →ₗ[ℝ] C₁) (comp : V → ι)
    (hker : ∀ f : V → ℝ, d₀ f = 0 → ∀ v w, comp v = comp w → f v = f w)
    (hlc : ∀ f : V → ℝ, (∀ v w, comp v = comp w → f v = f w) → d₀ f = 0)
    (anchor : ι → V) (hanchor_comp : ∀ i, comp (anchor i) = i)
    (α : C₁) (S₀ : V → ℝ) (hS₀ : d₀ S₀ = α) (c : ι → ℝ) :
    ∃! S : V → ℝ, d₀ S = α ∧ ∀ i, S (anchor i) = c i := by
  refine ⟨S₀ + fun v => c (comp v) - S₀ (anchor (comp v)), ⟨?_, ?_⟩, ?_⟩
  · have hshift : d₀ (fun v => c (comp v) - S₀ (anchor (comp v))) = 0 := by
      refine hlc _ fun v w h => ?_
      simp only [h]
    rw [map_add, hS₀, hshift, add_zero]
  · intro i
    simp [hanchor_comp]
  · rintro S ⟨hS, hSa⟩
    refine finiteVariationComplex_commonAction_anchor_unique_components d₀ comp hker α S _
      anchor hanchor_comp hS ?_ ?_
    · have hshift : d₀ (fun v => c (comp v) - S₀ (anchor (comp v))) = 0 := by
        refine hlc _ fun v w h => ?_
        simp only [h]
      rw [map_add, hS₀, hshift, add_zero]
    · intro i
      simp [hanchor_comp, hSa]

/-! ### The concrete one-skeleton -/

/-- The zeroth coboundary of the one-skeleton of a variation complex with oriented edges
`src, tgt : E → V`: `(d₀ S) e = S (tgt e) - S (src e)`. -/
def edgeCoboundary {V E : Type*} (src tgt : E → V) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f e := f (tgt e) - f (src e)
  map_add' f g := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem edgeCoboundary_apply {V E : Type*} (src tgt : E → V) (f : V → ℝ) (e : E) :
    edgeCoboundary src tgt f e = f (tgt e) - f (src e) := rfl

/-- The incidence graph of the one-skeleton: two distinct vertices are adjacent when some
declared edge joins them (in either orientation). -/
def incidenceGraph {V E : Type*} (src tgt : E → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun v w => ∃ e, src e = v ∧ tgt e = w

/-- The kernel of the edge coboundary is exactly the space of functions that are constant
on the connected components of the incidence graph (locally constant functions). -/
theorem edgeCoboundary_eq_zero_iff {V E : Type*} (src tgt : E → V) (f : V → ℝ) :
    edgeCoboundary src tgt f = 0 ↔
      ∀ v w, (incidenceGraph src tgt).Reachable v w → f v = f w := by
  constructor
  · intro hf v w hvw
    obtain ⟨p⟩ := hvw
    induction p with
    | nil => rfl
    | cons hadj _ ih =>
      refine Eq.trans ?_ ih
      rw [incidenceGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := hadj
      · have h := congrFun hf e
        simp only [edgeCoboundary_apply, Pi.zero_apply] at h
        linarith
      · have h := congrFun hf e
        simp only [edgeCoboundary_apply, Pi.zero_apply] at h
        linarith
  · intro h
    funext e
    simp only [edgeCoboundary_apply, Pi.zero_apply]
    by_cases hse : src e = tgt e
    · rw [hse, sub_self]
    · have hadj : (incidenceGraph src tgt).Adj (src e) (tgt e) := by
        rw [incidenceGraph, SimpleGraph.fromRel_adj]
        exact ⟨hse, Or.inl ⟨e, rfl, rfl⟩⟩
      rw [h _ _ hadj.reachable, sub_self]

/-- Functions in the kernel of the edge coboundary are constant on each connected
component of the incidence graph. -/
theorem edgeCoboundary_ker_locally_constant {V E : Type*} (src tgt : E → V) (f : V → ℝ)
    (hf : edgeCoboundary src tgt f = 0) (v w : V)
    (hvw : (incidenceGraph src tgt).connectedComponentMk v =
      (incidenceGraph src tgt).connectedComponentMk w) : f v = f w :=
  (edgeCoboundary_eq_zero_iff src tgt f).1 hf v w (SimpleGraph.ConnectedComponent.exact hvw)

/-- Functions constant on each connected component of the incidence graph lie in the
kernel of the edge coboundary. -/
theorem edgeCoboundary_eq_zero_of_locally_constant {V E : Type*} (src tgt : E → V)
    (f : V → ℝ)
    (hf : ∀ v w, (incidenceGraph src tgt).connectedComponentMk v =
      (incidenceGraph src tgt).connectedComponentMk w → f v = f w) :
    edgeCoboundary src tgt f = 0 :=
  (edgeCoboundary_eq_zero_iff src tgt f).2 fun v w hvw =>
    hf v w (SimpleGraph.ConnectedComponent.sound hvw)

/-- **`thm:main-common-action`, uniqueness clause** on the concrete one-skeleton: after
one additive anchor is fixed on each connected component of the variation complex (one
anchor vertex `anchor c` in every `SimpleGraph.ConnectedComponent c` of the incidence
graph), a common action with coboundary `α` is unique. -/
theorem edgeCoboundary_anchor_unique_components {V E : Type*} (src tgt : E → V)
    (anchor : (incidenceGraph src tgt).ConnectedComponent → V)
    (hanchor_comp : ∀ c, (incidenceGraph src tgt).connectedComponentMk (anchor c) = c)
    (α : E → ℝ) (S T : V → ℝ)
    (hS : edgeCoboundary src tgt S = α) (hT : edgeCoboundary src tgt T = α)
    (hanchor : ∀ c, S (anchor c) = T (anchor c)) : S = T :=
  finiteVariationComplex_commonAction_anchor_unique_components (edgeCoboundary src tgt)
    (incidenceGraph src tgt).connectedComponentMk
    (edgeCoboundary_ker_locally_constant src tgt) α S T anchor hanchor_comp hS hT hanchor

/-- **`thm:main-common-action`, anchored reconstruction** on the concrete one-skeleton:
every exact one-cochain `α` has exactly one common action with prescribed anchor values on
each connected component. -/
theorem edgeCoboundary_anchored_existsUnique {V E : Type*} (src tgt : E → V)
    (anchor : (incidenceGraph src tgt).ConnectedComponent → V)
    (hanchor_comp : ∀ c, (incidenceGraph src tgt).connectedComponentMk (anchor c) = c)
    (α : E → ℝ) (hα : ∃ S₀ : V → ℝ, edgeCoboundary src tgt S₀ = α)
    (c : (incidenceGraph src tgt).ConnectedComponent → ℝ) :
    ∃! S : V → ℝ, edgeCoboundary src tgt S = α ∧ ∀ i, S (anchor i) = c i := by
  obtain ⟨S₀, hS₀⟩ := hα
  exact finiteVariationComplex_commonAction_anchored_existsUnique (edgeCoboundary src tgt)
    (incidenceGraph src tgt).connectedComponentMk
    (edgeCoboundary_ker_locally_constant src tgt)
    (edgeCoboundary_eq_zero_of_locally_constant src tgt) anchor hanchor_comp α S₀ hS₀ c

/-- On a connected one-skeleton (a single connected component) one anchor suffices: the
connected clause `finiteVariationComplex_commonAction_anchor_unique` is recovered. -/
theorem edgeCoboundary_anchor_unique_of_preconnected {V E : Type*} (src tgt : E → V)
    (hconn : (incidenceGraph src tgt).Preconnected)
    (α : E → ℝ) (S T : V → ℝ) (anchor : V)
    (hS : edgeCoboundary src tgt S = α) (hT : edgeCoboundary src tgt T = α)
    (hanchor : S anchor = T anchor) : S = T :=
  finiteVariationComplex_commonAction_anchor_unique (edgeCoboundary src tgt)
    (fun f hf => ⟨f anchor, funext fun v =>
      (edgeCoboundary_eq_zero_iff src tgt f).1 hf v anchor (hconn v anchor)⟩)
    α S T anchor hS hT hanchor

end RenewalGeometry
