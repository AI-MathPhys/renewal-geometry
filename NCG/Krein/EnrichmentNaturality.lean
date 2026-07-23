/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.EnrichmentClassification

/-!
# Contravariant naturality of the enrichment classification

Closes the naturality rider of `thm:classification`
(`manuscripts/lorentzian_emergence/lorentzian_emergence.tex`): the classification bijection
`π₀ Enr_min(G) ≅ H¹(G, ℤ/2)` is **contravariantly natural** under
renewal (graph) morphisms.

* `cochainPullback` — pullback of transition cochains along a
  morphism, `φ*(c) = c ∘ φ_E`, a linear map;
* `cochainPullback_coboundary` — pullback carries coboundaries to
  coboundaries (`δ'a ∘ φ_E = δ(a ∘ φ_V)`, by source/target
  compatibility), so both quotients receive induced maps;
* `EnrichmentDatum.classesPullback` / `H1Pullback` — the induced
  maps on gauge classes and on `H¹`;
* `classification_natural` — the naturality square commutes:
  `classificationEquiv ∘ classesPullback = H1Pullback ∘
  classificationEquiv`;
* `classesPullback_comp` / `H1Pullback_comp` — contravariant
  functoriality under composition of morphisms.
-/

namespace NCG

namespace Multigraph

variable {G G' G'' : Multigraph}

/-- **Pullback of transition cochains** along a graph morphism. -/
def cochainPullback (φ : Hom G G') :
    (G'.E → ZMod 2) →ₗ[ZMod 2] (G.E → ZMod 2) where
  toFun c := fun e => c (φ.emap e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem cochainPullback_apply (φ : Hom G G') (c : G'.E → ZMod 2)
    (e : G.E) : cochainPullback φ c e = c (φ.emap e) := rfl

/-- **Coboundaries pull back to coboundaries**: by source/target
compatibility of the morphism, `φ*(δ'a) = δ(a ∘ φ_V)` — the key
step making the pullback descend to both quotients. -/
theorem cochainPullback_coboundary (φ : Hom G G')
    (a : G'.V → ZMod 2) :
    cochainPullback φ (coboundaryMap G' a)
      = coboundaryMap G (fun v => a (φ.vmap v)) := by
  funext e
  rw [cochainPullback_apply, coboundaryMap_apply, coboundaryMap_apply,
    φ.src_comm, φ.tgt_comm]

theorem cochainPullback_range (φ : Hom G G')
    {c : G'.E → ZMod 2}
    (hc : c ∈ LinearMap.range (coboundaryMap G')) :
    cochainPullback φ c ∈ LinearMap.range (coboundaryMap G) := by
  obtain ⟨a, rfl⟩ := hc
  exact ⟨fun v => a (φ.vmap v),
    (cochainPullback_coboundary φ a).symm⟩

namespace EnrichmentDatum

/-- The induced pullback on gauge classes of enrichment data. -/
def classesPullback (φ : Hom G G') :
    EnrichmentClasses G' → EnrichmentClasses G :=
  Quotient.map' (fun c => cochainPullback φ c) (by
    rintro c c' ⟨a, rfl⟩
    exact ⟨fun v => a (φ.vmap v), by
      rw [map_add, cochainPullback_coboundary]⟩)

/-- The induced pullback on `H¹(·, ℤ/2)`. -/
def H1Pullback (φ : Hom G G') : H1 G' → H1 G :=
  Quotient.map' (fun c => cochainPullback φ c) (by
    intro c c' h
    have hmem : c - c' ∈ LinearMap.range (coboundaryMap G') :=
      (Submodule.quotientRel_def _).mp h
    refine (Submodule.quotientRel_def _).mpr ?_
    have := cochainPullback_range φ hmem
    rwa [map_sub] at this)

/-- **`thm:classification` (contravariant naturality)**: the
classification bijection intertwines the pullbacks — the naturality
square

`EnrichmentClasses G' → H¹(G')`
`        ↓                ↓`
`EnrichmentClasses G  → H¹(G)`

commutes. -/
theorem classification_natural (φ : Hom G G')
    (x : EnrichmentClasses G') :
    classificationEquiv G (classesPullback φ x)
      = H1Pullback φ (classificationEquiv G' x) := by
  induction x using Quotient.ind with | _ c => rfl

/-- **Contravariant functoriality** on gauge classes: pullback along
a composite is the composite of pullbacks in reverse order. -/
theorem classesPullback_comp (φ : Hom G G') (ψ : Hom G' G'')
    (x : EnrichmentClasses G'') :
    classesPullback φ (classesPullback ψ x)
      = classesPullback
          ⟨ψ.vmap ∘ φ.vmap, ψ.emap ∘ φ.emap,
            fun e => by
              show G''.src (ψ.emap (φ.emap e)) = ψ.vmap (φ.vmap _)
              rw [ψ.src_comm, φ.src_comm],
            fun e => by
              show G''.tgt (ψ.emap (φ.emap e)) = ψ.vmap (φ.vmap _)
              rw [ψ.tgt_comm, φ.tgt_comm]⟩ x := by
  induction x using Quotient.ind with | _ c => rfl

/-- **Contravariant functoriality** on `H¹`. -/
theorem H1Pullback_comp (φ : Hom G G') (ψ : Hom G' G'')
    (x : H1 G'') :
    H1Pullback φ (H1Pullback ψ x)
      = H1Pullback
          ⟨ψ.vmap ∘ φ.vmap, ψ.emap ∘ φ.emap,
            fun e => by
              show G''.src (ψ.emap (φ.emap e)) = ψ.vmap (φ.vmap _)
              rw [ψ.src_comm, φ.src_comm],
            fun e => by
              show G''.tgt (ψ.emap (φ.emap e)) = ψ.vmap (φ.vmap _)
              rw [ψ.tgt_comm, φ.tgt_comm]⟩ x := by
  induction x using Quotient.ind with | _ c => rfl

end EnrichmentDatum

end Multigraph

end NCG
