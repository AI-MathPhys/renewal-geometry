/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.CoverModel

/-!
# The canonical temporal row: Krein exchange along cycles

The manuscript's **canonical temporal row** (`thm:canonical-temporal-row`)
states that the temporal row of the modular commutator form is *forced* by
the signed cover: for a revision operator whose sheet action is the
geometric transport along a recurrent cycle `α`,

`J_χ R_α = (−1)^{⟨[χ], α⟩} R_α J_χ`,

where `⟨[χ], α⟩` is the cohomology–homology pairing, i.e. the sum of the
edge signs along the cycle (`lem:cycle-krein-exchange`).

This file proves the operator identity behind both statements: the
fundamental symmetry `J_χ` exchanges with the **composite lifted shift**
along any directed edge path at the cost of the sign
`(−1)^{Σ χ(eᵢ)}` — obtained by iterating the single-edge exchange relation
`NCG.krein_exchange`.  For a closed path the exponent is exactly the
`χ`-holonomy of the cycle, which depends only on `[χ] ∈ H¹(G, ℤ/2)`
(`NCG.Multigraph.Walk.holonomy_gauge_loop`), so the sign is the pairing
`⟨[χ], α⟩` and is representative-independent — the content of
Lemma `lem:cycle-krein-exchange`.

## Main results

* `NCG.pathShift` — the composite lifted shift `S̃_{e₁} ⋯ S̃_{e_k}` along a
  list of edges;
* `NCG.krein_exchange_path` — the cycle Krein exchange relation
  (`lem:cycle-krein-exchange` / `thm:canonical-temporal-row`):

  `J_χ ∘ S̃_p = (−1)^{Σ χ(e)} · (S̃_p ∘ J_χ)`.
-/

namespace NCG

open Multigraph

variable {G : Multigraph} [DecidableEq G.V]

/-- The **composite lifted shift** along a list of edges (a directed path,
first edge of the list applied last): the operator `S̃_{e₁} ∘ ⋯ ∘ S̃_{e_k}`
implementing a multi-step renewal transport on the signed cover. -/
noncomputable def pathShift (χ : G.E → ZMod 2) :
    List G.E → ((G.V × ZMod 2) →₀ ℂ) →ₗ[ℂ] ((G.V × ZMod 2) →₀ ℂ)
  | [] => LinearMap.id
  | e :: es => edgeShift χ e ∘ₗ pathShift χ es

@[simp]
theorem pathShift_nil (χ : G.E → ZMod 2) :
    pathShift χ ([] : List G.E) = LinearMap.id := rfl

@[simp]
theorem pathShift_cons (χ : G.E → ZMod 2) (e : G.E) (es : List G.E) :
    pathShift χ (e :: es) = edgeShift χ e ∘ₗ pathShift χ es := rfl

/-- **The cycle Krein exchange relation**
(`lem:cycle-krein-exchange`, `thm:canonical-temporal-row`): the fundamental
symmetry exchanges with a composite lifted shift at the cost of the product
of the edge signs,

`J_χ ∘ S̃_p = (−1)^{Σᵢ χ(eᵢ)} · (S̃_p ∘ J_χ)`.

For a *closed* path the exponent `Σᵢ χ(eᵢ)` is the `χ`-holonomy of the
cycle, which is gauge-invariant and depends only on the class
`[χ] ∈ H¹(G, ℤ/2)` (`NCG.Multigraph.Walk.holonomy_gauge_loop`).  The
exchange constant is therefore the cohomology–homology pairing
`(−1)^{⟨[χ], α⟩}`: the temporal row `ω(α, t) = ⟨[χ], α⟩` of the modular
commutator form is forced by the signed cover and is not a free datum. -/
theorem krein_exchange_path (χ : G.E → ZMod 2) (es : List G.E) :
    kreinJ G ∘ₗ pathShift χ es
      = signValue ((es.map χ).sum) • (pathShift χ es ∘ₗ kreinJ G) := by
  induction es with
  | nil =>
      simp
  | cons e es ih =>
      calc kreinJ G ∘ₗ pathShift χ (e :: es)
          = (kreinJ G ∘ₗ edgeShift χ e) ∘ₗ pathShift χ es := by
            rw [pathShift_cons, ← LinearMap.comp_assoc]
        _ = (signValue (χ e) • (edgeShift χ e ∘ₗ kreinJ G))
              ∘ₗ pathShift χ es := by
            rw [krein_exchange]
        _ = signValue (χ e)
              • (edgeShift χ e ∘ₗ (kreinJ G ∘ₗ pathShift χ es)) := by
            rw [LinearMap.smul_comp, LinearMap.comp_assoc]
        _ = signValue (χ e)
              • (edgeShift χ e ∘ₗ (signValue ((es.map χ).sum)
                • (pathShift χ es ∘ₗ kreinJ G))) := by
            rw [ih]
        _ = (signValue (χ e) * signValue ((es.map χ).sum))
              • ((edgeShift χ e ∘ₗ pathShift χ es) ∘ₗ kreinJ G) := by
            rw [LinearMap.comp_smul, smul_smul, ← LinearMap.comp_assoc]
        _ = signValue (((e :: es).map χ).sum)
              • (pathShift χ (e :: es) ∘ₗ kreinJ G) := by
            rw [← signValue_add, List.map_cons, List.sum_cons,
              pathShift_cons]

/-- The list of edges traversed by a walk (in order, forgetting
orientation of traversal). -/
def _root_.NCG.Multigraph.Walk.edges :
    ∀ {u v : G.V}, G.Walk u v → List G.E
  | _, _, .nil _ => []
  | _, _, .fwd e p => e :: p.edges
  | _, _, .bwd e p => e :: p.edges

omit [DecidableEq G.V] in
/-- The exchange sign of `krein_exchange_path` along the edge list of a
walk is exactly the walk's `χ`-holonomy.  For closed walks the holonomy is
gauge-invariant (`NCG.Multigraph.Walk.holonomy_gauge_loop`), so the Krein
exchange constant of a recurrent cycle depends only on the class
`[χ] ∈ H¹(G, ℤ/2)` — the pairing `⟨[χ], α⟩` of
Lemma `lem:cycle-krein-exchange`. -/
theorem holonomy_eq_edge_sign_sum (χ : G.E → ZMod 2) {u v : G.V}
    (p : G.Walk u v) :
    p.holonomy χ = ((p.edges.map χ).sum) := by
  induction p with
  | nil w => simp [Multigraph.Walk.edges]
  | fwd e p ih => simp [Multigraph.Walk.edges, ih]
  | bwd e p ih => simp [Multigraph.Walk.edges, ih]

end NCG
