/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.BettiNumber

/-!
# The classification of minimal signed enrichments

* **Definition `def:fixed-enrichment`**: by the rank-two reduction
  (`NCG.structure_group_rank_two`) and the two-cochains lemma
  (`NCG.homogeneity_degree`), an objectwise-minimal renewal-positive
  fibrewise-indefinite enrichment over `G` is, in a sheet
  trivialisation, exactly a transition cochain `c : E → ℤ/2` (edge
  transport `S^{c(e)}`, rank-two fibres, vertex symmetries gauge data).

* **Definition `def:fixed-gauge`**: sheet changes `a : V → ℤ/2` act by
  the coboundary, `c ↦ c + δa` (`NCG.gauge_transport`); gauge
  equivalence is the coboundary relation.

* **Theorem `thm:classification`** (categorical minimality of the
  signed enrichment): the set of gauge classes is canonically
  `π₀ Enr_min(G) ≅ H¹(G, ℤ/2)`
  (`NCG.Multigraph.EnrichmentDatum.classificationEquiv`), and on a
  finite connected component there are exactly `2^{b₁(G)}` classes
  (`NCG.Multigraph.EnrichmentDatum.card_enrichmentClasses`), with
  `b₁ = |E| − |V| + 1` — every such enrichment is the signed cover of
  its class.  (Contravariant naturality under renewal isomorphisms is
  not formalised.) -/

namespace NCG.Multigraph

variable (G : Multigraph)

/-- **Definition `def:fixed-enrichment`** (sheet-trivialised form): an
objectwise-minimal enrichment datum is its transition cochain
`c : E → ℤ/2` — the edge transport is `S^{c(e)}` on the rank-two model
fibre, by `lem:minimal-rank-two`. -/
abbrev EnrichmentDatum := G.E → ZMod 2

namespace EnrichmentDatum

/-- **Definition `def:fixed-gauge`**: two enrichment data are gauge
equivalent when a sheet change `a : V → ℤ/2` carries one to the other,
`c' = c + δa`. -/
def GaugeEquiv (c c' : EnrichmentDatum G) : Prop :=
  ∃ a : G.V → ZMod 2, c' = c + coboundaryMap G a

variable {G}

theorem gaugeEquiv_iff_sub_mem {c c' : EnrichmentDatum G} :
    GaugeEquiv G c c'
      ↔ c - c' ∈ LinearMap.range (coboundaryMap G) := by
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, funext fun e => ?_⟩
    change coboundaryMap G a e = (c - (c + coboundaryMap G a)) e
    simp only [Pi.sub_apply, Pi.add_apply]
    have h : c e - (c e + coboundaryMap G a e)
        = -(coboundaryMap G a e) := by ring
    rw [h, hneg]
  · rintro ⟨a, ha⟩
    refine ⟨a, funext fun e => ?_⟩
    have he := congrFun ha e
    simp only [Pi.sub_apply] at he
    change c' e = (c + coboundaryMap G a) e
    simp only [Pi.add_apply]
    have h : c' e = c e - (c e - c' e) := by ring
    rw [h, ← he, sub_eq_add_neg, hneg]

variable (G)

/-- Gauge equivalence is an equivalence relation on enrichment data. -/
def gaugeSetoid : Setoid (EnrichmentDatum G) where
  r := GaugeEquiv G
  iseqv := by
    constructor
    · intro c
      exact ⟨0, by simp⟩
    · intro c c' h
      rw [gaugeEquiv_iff_sub_mem] at h ⊢
      have : c' - c = -(c - c') := by abel
      rw [this]
      exact neg_mem h
    · intro c₁ c₂ c₃ h12 h23
      rw [gaugeEquiv_iff_sub_mem] at h12 h23 ⊢
      have : c₁ - c₃ = (c₁ - c₂) + (c₂ - c₃) := by abel
      rw [this]
      exact add_mem h12 h23

/-- **`π₀ Enr_min(G)`**: the gauge classes of objectwise-minimal signed
enrichments (Theorem `thm:classification`). -/
def EnrichmentClasses := Quotient (gaugeSetoid G)

/-- **Theorem `thm:classification`** (boxed formula, first half):
`π₀ Enr_min(G) ≅ H¹(G, ℤ/2)` — gauge classes of minimal enrichments are
exactly the signed cohomology classes; every minimal enrichment is the
signed cover of its class. -/
def classificationEquiv : EnrichmentClasses G ≃ H1 G :=
  Quotient.congr (Equiv.refl _) fun _ _ =>
    gaugeEquiv_iff_sub_mem.trans (Submodule.quotientRel_def _).symm

/-- **Theorem `thm:classification`** (boxed formula, second half): on a
finite connected recurrent component there are exactly `2^{b₁}` gauge
classes of minimal signed enrichments, `b₁ = |E| − |V| + 1`. -/
theorem card_enrichmentClasses [Fintype G.V] [Fintype G.E] {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) :
    Nat.card (EnrichmentClasses G)
      = 2 ^ (Fintype.card G.E + 1 - Fintype.card G.V) := by
  rw [Nat.card_congr (classificationEquiv G)]
  exact card_H1_of_connected hconn

end EnrichmentDatum

end NCG.Multigraph
