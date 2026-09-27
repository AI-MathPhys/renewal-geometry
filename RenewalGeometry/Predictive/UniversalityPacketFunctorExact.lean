/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CurrentChainFunctorExact
import RenewalGeometry.Spectralization.MarkedMonodromyDescentExact
import RenewalGeometry.Spectralization.OperatorTailMeasureCompressionExact
import RenewalGeometry.Predictive.NevanlinnaKernelCompression
/-!
# The functorial principal universality packet

This file closes `thm:supp-fibre-RG` of `papers/predictive_spectral_geometry`.

* `UniversalityPacket` bundles `𝔘(G,c;A,μ;ρ) = (Curr(G,c), (A,μ), [ρ])` (`eq:supp-U-packet`): an
  oriented finite graph with positive conductances, an effective operator with a positive memory
  measure, and a marked monodromy `ρ : F →* G` (`F` the fundamental group, `G` the structure
  group).
* `CoarseGraining` is a morphism datum: a vertex quotient with connected fibres retaining every
  inter-fibre edge class, a memory threshold `Λ > 0`, an isometric effective-space compression
  `W` (`Wᴴ W = 1`), and a surjection `q_*` of fundamental groups satisfying the monodromy kernel
  condition `ker q_* ≤ ker ρ`.
* `CoarseGraining.image` is the map **`eq:supp-U-map`**
  `𝔘 ↦ (Q_E Curr(G,c), (W^*(A - Q_{>Λ})W, W^* μ|_{(0,Λ]} W), [ρ̄])`.
* `CoarseGraining.comp` composes two coarse grainings (composable graph quotients
  `VertexQuotient.comp`, nested thresholds `Λ₂ ≤ Λ₁`, compatible head maps `W₁ W₂`, composite
  contraction `q₂ ∘ q₁`) and **`image_comp`** shows the map composes strictly:
  `(d₁.comp d₂).image = d₂.image` where `d₂` is a coarse graining of `d₁.image`.
* `universality_packet_functor` assembles the theorem: the map is canonical (the descended
  monodromy is the unique factorisation `ρ = ρ̄ ∘ q_*`), composes strictly, entropy production
  cannot increase (`eq:supp-entropy-contraction`), the zero-energy Schur complement is preserved
  before compression (`eq:supp-memory-static-preserved`), the source rank of the minimal dilation
  cannot increase (`sourceRank_compress_le`, `sourceRank_cutoff_le`), the number of negative squares
  of any head function with bounded Gram inertia cannot increase under the compression
  (`negSquares_compress_le`), and marked monodromy descends exactly when the collapsed cycles lie
  in its kernel (`monodromy_descends_iff`).

Disclosed conventions: "minimal dilation rank" is formalised as the **source rank**
`rank μ((0,∞)) = rank B_μ^*` of the minimal dilation (`IsMinimalRealization.finrank_range_eq`),
which is what the paper's proof sentence ("compression of a positive minimal memory dilation carrier
cannot increase source rank") establishes.  The negative-square clause is stated, as in
`NevanlinnaKernelCompression`, for kernels whose finite Gram inertia is bounded on the domain.
-/

open MeasureTheory Set
open scoped InnerProductSpace Matrix

namespace RenewalGeometry

/-! ## Composition of vertex quotients -/

namespace CurrentChain
namespace VertexQuotient

variable {V E V' E' V'' E'' : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
  [Fintype V''] [Fintype E''] [DecidableEq V] [DecidableEq V'] [DecidableEq V''] [DecidableEq E]
  [DecidableEq E'] [DecidableEq E'']
  {tail head : E → V} {tail' head' : E' → V'} {tail'' head'' : E'' → V''}

/-- **Composition of vertex quotients** (composable graph quotients). -/
def comp (q₁ : VertexQuotient tail head tail' head') (q₂ : VertexQuotient tail' head' tail'' head'') :
    VertexQuotient tail head tail'' head'' where
  vmap := q₂.vmap ∘ q₁.vmap
  emap e := (q₁.emap e).bind q₂.emap
  tail_comm e e'' h := by
    rcases h1 : q₁.emap e with _ | e'
    · rw [h1] at h; simp at h
    · rw [h1, Option.bind_some] at h
      show tail'' e'' = q₂.vmap (q₁.vmap (tail e))
      rw [q₂.tail_comm e' e'' h, q₁.tail_comm e e' h1]
  head_comm e e'' h := by
    rcases h1 : q₁.emap e with _ | e'
    · rw [h1] at h; simp at h
    · rw [h1, Option.bind_some] at h
      show head'' e'' = q₂.vmap (q₁.vmap (head e))
      rw [q₂.head_comm e' e'' h, q₁.head_comm e e' h1]
  internal e h := by
    rcases h1 : q₁.emap e with _ | e'
    · show q₂.vmap (q₁.vmap (tail e)) = q₂.vmap (q₁.vmap (head e))
      rw [q₁.internal e h1]
    · rw [h1, Option.bind_some] at h
      show q₂.vmap (q₁.vmap (tail e)) = q₂.vmap (q₁.vmap (head e))
      rw [← q₁.tail_comm e e' h1, ← q₁.head_comm e e' h1]
      exact q₂.internal e' h

variable (q₁ : VertexQuotient tail head tail' head') (q₂ : VertexQuotient tail' head' tail'' head'')

@[simp] theorem comp_vmap (x : V) : (q₁.comp q₂).vmap x = q₂.vmap (q₁.vmap x) := rfl

@[simp] theorem comp_emap (e : E) : (q₁.comp q₂).emap e = (q₁.emap e).bind q₂.emap := rfl

/-- `Q_E` is functorial: the edge-summation matrix of a composite is the product. -/
theorem edgeMatrix_comp : (q₁.comp q₂).edgeMatrix = q₂.edgeMatrix * q₁.edgeMatrix := by
  ext e'' e
  simp only [edgeMatrix, comp_emap, Matrix.mul_apply]
  obtain ⟨o, ho⟩ : ∃ o, q₁.emap e = o := ⟨_, rfl⟩
  simp only [ho]
  rcases o with _ | e₀
  · simp
  · simp only [Option.bind_some, Option.some.injEq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ e₀]
    simp

theorem edgeSum_comp (j : E → ℝ) : (q₁.comp q₂).edgeSum j = q₂.edgeSum (q₁.edgeSum j) := by
  simp only [edgeSum, edgeMatrix_comp, Matrix.mulVec_mulVec]

theorem coarseConductance_comp (c : E → ℝ) :
    (q₁.comp q₂).coarseConductance c = q₂.coarseConductance (q₁.coarseConductance c) :=
  edgeSum_comp q₁ q₂ c

theorem retainsInterFibreEdges_comp (h₁ : q₁.RetainsInterFibreEdges)
    (h₂ : q₂.RetainsInterFibreEdges) : (q₁.comp q₂).RetainsInterFibreEdges := by
  intro e''
  obtain ⟨e', he'⟩ := h₂ e''
  obtain ⟨e, he⟩ := h₁ e'
  exact ⟨e, by rw [comp_emap, he, Option.bind_some, he']⟩

theorem InternalAdj.symm {q : VertexQuotient tail head tail' head'} {x y : V}
    (h : q.InternalAdj x y) : q.InternalAdj y x := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.symm⟩

theorem internalAdj_comp_of_left {x y : V} (h : q₁.InternalAdj x y) : (q₁.comp q₂).InternalAdj x y := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, by rw [comp_emap, he, Option.bind_none], h⟩

/-- Connected fibres compose (using that the first quotient retains inter-fibre edge classes, so
that every internal coarse edge lifts to a fine edge). -/
theorem fibresConnected_comp (h₁ : q₁.FibresConnected) (h₂ : q₂.FibresConnected)
    (hret₁ : q₁.RetainsInterFibreEdges) : (q₁.comp q₂).FibresConnected := by
  have lift₁ : ∀ x y, Relation.ReflTransGen q₁.InternalAdj x y →
      Relation.ReflTransGen (q₁.comp q₂).InternalAdj x y :=
    fun x y h => by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail (q₁.internalAdj_comp_of_left q₂ hbc)
  have key : ∀ a b : V', Relation.ReflTransGen q₂.InternalAdj a b → ∀ x y : V,
      q₁.vmap x = a → q₁.vmap y = b → Relation.ReflTransGen (q₁.comp q₂).InternalAdj x y := by
    intro a b hab
    induction hab with
    | refl => exact fun x y hx hy => lift₁ x y (h₁ x y (hx.trans hy.symm))
    | tail _ hbc ih =>
      intro x y hx hy
      obtain ⟨e', he', hor⟩ := hbc
      obtain ⟨e, he⟩ := hret₁ e'
      have ht := q₁.tail_comm e e' he
      have hh := q₁.head_comm e e' he
      have hint : (q₁.comp q₂).InternalAdj (tail e) (head e) :=
        ⟨e, by rw [comp_emap, he, Option.bind_some, he'], Or.inl ⟨rfl, rfl⟩⟩
      rcases hor with ⟨hb, hc⟩ | ⟨hc, hb⟩
      · refine ((ih x (tail e) hx (by rw [← ht, hb])).trans
          (Relation.ReflTransGen.single hint)).trans ?_
        exact lift₁ _ _ (h₁ (head e) y (by rw [← hh, hc, hy]))
      · refine ((ih x (head e) hx (by rw [← hh, hb])).trans
          (Relation.ReflTransGen.single hint.symm)).trans ?_
        exact lift₁ _ _ (h₁ (tail e) y (by rw [← ht, hc, hy]))
  intro x y hxy
  exact key _ _ (h₂ _ _ hxy) x y rfl rfl

end VertexQuotient
end CurrentChain

/-! ## The packet and its coarse grainings -/

open CurrentChain OperatorTailMeasure FiniteGraphSpectralUniversalityFibre

/-- **The principal universality packet `𝔘(G,c;A,μ;ρ)`** (`eq:supp-U-packet`): an oriented finite
graph `(tail, head)` with positive conductances `c`, an effective operator `A` with a positive
memory measure `μ` on the head space `H`, and a marked monodromy `ρ : F →* G`. -/
@[ext]
structure UniversalityPacket (V E H F G : Type*) [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] [Fintype H] [DecidableEq H] [Group F] [Group G] where
  tail : E → V
  head : E → V
  cond : E → ℝ
  cond_pos : ∀ e, 0 < cond e
  A : Matrix H H ℂ
  μ : PositiveTailMeasure H
  ρ : F →* G

namespace UniversalityPacket

variable {V E H F G : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype H]
  [DecidableEq H] [Group F] [Group G]
variable {V' E' H' F' : Type*} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
  [Fintype H'] [DecidableEq H'] [Group F']
variable {V'' E'' H'' F'' : Type*} [Fintype V''] [Fintype E''] [DecidableEq V''] [DecidableEq E'']
  [Fintype H''] [DecidableEq H''] [Group F'']

/-- The head function `z ↦ F_{A,μ}(z)` of a packet as an operator function on `EuclideanSpace ℂ H`
(the object to which the Nevanlinna-kernel machinery applies). -/
noncomputable def headFunction (U : UniversalityPacket V E H F G) :
    ℂ → EuclideanSpace ℂ H →L[ℂ] EuclideanSpace ℂ H :=
  fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (U.μ.dynamicFunction U.A z)

/-- The memory-RG step `RG_Λ` alone (`eq:supp-memory-RG`), before effective-space compression. -/
noncomputable def rgPacket (U : UniversalityPacket V E H F G) (Λ : ℝ) :
    UniversalityPacket V E H F G :=
  { U with A := (U.μ.rg U.A Λ).1, μ := (U.μ.rg U.A Λ).2 }

/-- **A coarse graining of a packet**: a connected-fibre vertex quotient retaining every inter-fibre
edge class, a memory threshold `Λ > 0`, a compatible isometric effective-space compression `W`
(`Wᴴ W = 1`), and a surjective contraction `q_*` of fundamental groups satisfying the monodromy
kernel condition `ker q_* ⊆ ker ρ` (`eq:supp-monodromy-kernel`). -/
structure CoarseGraining (U : UniversalityPacket V E H F G) (V' E' H' F' : Type*) [Fintype V']
    [Fintype E'] [DecidableEq V'] [DecidableEq E'] [Fintype H'] [DecidableEq H'] [Group F'] where
  tail' : E' → V'
  head' : E' → V'
  q : VertexQuotient U.tail U.head tail' head'
  fibresConnected : q.FibresConnected
  retains : q.RetainsInterFibreEdges
  Λ : ℝ
  Λ_pos : 0 < Λ
  W : Matrix H H' ℂ
  isometry : Wᴴ * W = 1
  qstar : F →* F'
  surjective : Function.Surjective qstar
  ker_le : qstar.ker ≤ U.ρ.ker

namespace CoarseGraining

variable {U : UniversalityPacket V E H F G} (d : CoarseGraining U V' E' H' F')

theorem coarseConductance_pos (e' : E') : 0 < d.q.coarseConductance U.cond e' := by
  rw [VertexQuotient.coarseConductance, VertexQuotient.edgeSum_apply]
  obtain ⟨e₀, he₀⟩ := d.retains e'
  refine Finset.sum_pos' (fun e _ => ?_) ⟨e₀, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (U.cond_pos e).le
    · exact le_rfl
  · simp [he₀, U.cond_pos e₀]

/-- **The map `eq:supp-U-map`**:
`𝔘 ↦ (Q_E Curr(G,c), (W^*(A - Q_{>Λ})W, W^* μ|_{(0,Λ]} W), [ρ̄])`. -/
noncomputable def image : UniversalityPacket V' E' H' F' G where
  tail := d.tail'
  head := d.head'
  cond := d.q.coarseConductance U.cond
  cond_pos := d.coarseConductance_pos
  A := d.Wᴴ * (U.μ.rg U.A d.Λ).1 * d.W
  μ := (U.μ.rg U.A d.Λ).2.compress d.W
  ρ := monodromyDescent d.qstar d.surjective U.ρ d.ker_le

@[simp] theorem image_tail : d.image.tail = d.tail' := rfl
@[simp] theorem image_head : d.image.head = d.head' := rfl
@[simp] theorem image_cond : d.image.cond = d.q.coarseConductance U.cond := rfl
@[simp] theorem image_A : d.image.A = d.Wᴴ * (U.μ.rg U.A d.Λ).1 * d.W := rfl
@[simp] theorem image_μ : d.image.μ = (U.μ.rg U.A d.Λ).2.compress d.W := rfl
@[simp] theorem image_ρ : d.image.ρ = monodromyDescent d.qstar d.surjective U.ρ d.ker_le := rfl

/-- The image head function is the compression `W^* F_{RG_Λ(A,μ)} W` of the head function of the
memory-RG'd packet, off `[0,∞)`. -/
theorem headFunction_image {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    d.image.headFunction z =
      PontryaginRealization.compress
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin d.W))
        (U.rgPacket d.Λ).headFunction z := by
  unfold headFunction PontryaginRealization.compress rgPacket
  simp only [image_A, image_μ]
  rw [(U.μ.rg U.A d.Λ).2.dynamicFunction_compress d.W d.isometry _ hz]
  refine ContinuousLinearMap.ext fun x => ?_
  have hadj : ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin d.W)) = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin d.Wᴴ) := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  simp only [ContinuousLinearMap.comp_apply, hadj, LinearMap.coe_toContinuousLinearMap']
  change Matrix.toEuclideanLin _ x = Matrix.toEuclideanLin d.Wᴴ
    (Matrix.toEuclideanLin _ (Matrix.toEuclideanLin d.W x))
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Composition of coarse grainings**: composable graph quotients, nested thresholds `Λ₂ ≤ Λ₁`,
compatible head maps `W₁ W₂` and the composite contraction `q₂ ∘ q₁`. -/
noncomputable def comp (d₂ : CoarseGraining d.image V'' E'' H'' F'') :
    CoarseGraining U V'' E'' H'' F'' where
  tail' := d₂.tail'
  head' := d₂.head'
  q := d.q.comp d₂.q
  fibresConnected := d.q.fibresConnected_comp d₂.q d.fibresConnected d₂.fibresConnected d.retains
  retains := d.q.retainsInterFibreEdges_comp d₂.q d.retains d₂.retains
  Λ := d₂.Λ
  Λ_pos := d₂.Λ_pos
  W := d.W * d₂.W
  isometry := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d.Wᴴ, d.isometry,
      Matrix.one_mul, d₂.isometry]
  qstar := d₂.qstar.comp d.qstar
  surjective := d₂.surjective.comp d.surjective
  ker_le := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have h1 : d.qstar x ∈ d₂.qstar.ker := MonoidHom.mem_ker.mpr hx
    have h2 := d₂.ker_le h1
    rw [MonoidHom.mem_ker, image_ρ] at h2
    have h3 := congrArg (fun φ : F →* G => φ x) (monodromyDescent_comp d.qstar d.surjective U.ρ d.ker_le)
    simp only [MonoidHom.comp_apply] at h3
    rw [MonoidHom.mem_ker, ← h3, h2]

/-- **The map composes strictly**: for nested thresholds `Λ₂ ≤ Λ₁` the image of the composite coarse
graining is the image of the second one applied to the image of the first. -/
theorem image_comp (d₂ : CoarseGraining d.image V'' E'' H'' F'') (hΛ : d₂.Λ ≤ d.Λ) :
    (d.comp d₂).image = d₂.image := by
  have hrg : (U.μ.rg U.A d.Λ).2.rg (U.μ.rg U.A d.Λ).1 d₂.Λ = U.μ.rg U.A d₂.Λ :=
    U.μ.rg_rg U.A d₂.Λ_pos hΛ
  have hc : ((U.μ.rg U.A d.Λ).2.compress d.W).rg (d.Wᴴ * (U.μ.rg U.A d.Λ).1 * d.W) d₂.Λ =
      (d.Wᴴ * (U.μ.rg U.A d₂.Λ).1 * d.W, (U.μ.rg U.A d₂.Λ).2.compress d.W) := by
    rw [(U.μ.rg U.A d.Λ).2.rg_compress d.W _ d₂.Λ_pos, hrg]
  ext1
  · rfl
  · rfl
  · exact d.q.coarseConductance_comp d₂.q U.cond
  · show (d.W * d₂.W)ᴴ * (U.μ.rg U.A d₂.Λ).1 * (d.W * d₂.W) =
      d₂.Wᴴ * (d.image.μ.rg d.image.A d₂.Λ).1 * d₂.W
    rw [image_μ, image_A, hc]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · show (U.μ.rg U.A d₂.Λ).2.compress (d.W * d₂.W) = (d.image.μ.rg d.image.A d₂.Λ).2.compress d₂.W
    rw [image_μ, image_A, hc, PositiveTailMeasure.compress_compress]
  · exact (monodromyDescent_comp_surjective d.qstar d.surjective d₂.qstar d₂.surjective U.ρ _).symm

end CoarseGraining

/-- **`thm:supp-fibre-RG` (Functorial principal universality packet).**  For a packet `𝔘` and a
coarse graining `d` (connected-fibre graph quotient, memory threshold `Λ`, compatible isometric
effective-space compression `W`, contraction `q_*` with the monodromy kernel condition), the map
`eq:supp-U-map` `d.image`:
1. is canonical — its monodromy component is the unique `ρ̄` with `ρ = ρ̄ ∘ q_*` (the other
   components are the explicit formulas `Q_E Curr(G,c)` and `RG_Λ` followed by `W^* · W`);
2. composes strictly for composable graph quotients, nested thresholds and compatible head maps;
3. maps currents to currents and cannot increase the entropy production;
4. preserves the zero-energy Schur complement before effective-space compression;
5. cannot increase the minimal dilation (source) rank;
6. cannot increase the number of negative squares of any head function with bounded Gram inertia
   under the effective-space compression `W`;
7. and marked monodromy descends along a surjective contraction exactly when the collapsed cycles
   lie in its kernel. -/
theorem universality_packet_functor (U : UniversalityPacket V E H F G)
    (d : CoarseGraining U V' E' H' F') :
    (∀ ρ' : F' →* G, ρ'.comp d.qstar = U.ρ → ρ' = d.image.ρ) ∧
    (∀ (d₂ : CoarseGraining d.image V'' E'' H'' F''), d₂.Λ ≤ d.Λ →
      (d.comp d₂).image = d₂.image) ∧
    (∀ j ∈ currentPolytope U.tail U.head U.cond,
      d.q.edgeSum j ∈ currentPolytope d.image.tail d.image.head d.image.cond ∧
      entropyProduction d.image.cond (d.q.edgeSum j) ≤ entropyProduction U.cond j) ∧
    (Integrable (fun lam : ℝ => ((lam : ℂ))⁻¹) U.μ.toVectorMeasure.variation →
      (U.rgPacket d.Λ).μ.dynamicFunction (U.rgPacket d.Λ).A 0 = U.μ.dynamicFunction U.A 0) ∧
    d.image.μ.sourceRank ≤ U.μ.sourceRank ∧
    (∀ (Q : ℂ → EuclideanSpace ℂ H →L[ℂ] EuclideanSpace ℂ H) (D : Set ℂ),
      BddAbove {κ | ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → ℂ)
        (h : ι → EuclideanSpace ℂ H), (∀ i, z i ∈ D) ∧
        negInertia (PontryaginRealization.kernelGram (PontryaginRealization.nevanlinnaKernel Q) z h)
          = κ} →
      PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel
        (PontryaginRealization.compress (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin d.W)) Q))
          D ≤ PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel Q) D) ∧
    (∀ (q : F →* F'), Function.Surjective q →
      ((∃! ρbar : F' →* G, U.ρ = ρbar.comp q) ↔ q.ker ≤ U.ρ.ker)) := by
  refine ⟨?_, fun d₂ hΛ => d.image_comp d₂ hΛ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ' hρ'
    exact monodromyDescent_unique d.qstar d.surjective U.ρ d.ker_le ρ' hρ'
  · intro j hj
    exact ⟨d.q.edgeSum_mem_currentPolytope d.retains U.cond hj,
      d.q.entropyProduction_edgeSum_le U.cond j U.cond_pos hj.2⟩
  · intro hint
    exact U.μ.dynamicFunction_rg_zero U.A d.Λ hint
  · rw [CoarseGraining.image_μ]
    exact (PositiveTailMeasure.sourceRank_compress_le _ d.W).trans
      (U.μ.sourceRank_cutoff_le d.Λ)
  · intro Q D hbdd
    exact PontryaginRealization.negSquares_compress_le _ Q D hbdd
  · intro q hq
    exact monodromy_descends_iff q hq U.ρ

end UniversalityPacket
end RenewalGeometry
