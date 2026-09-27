/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.StationaryRenewalGraphCurrentFibreExact
import RenewalGeometry.Spectralization.NonlinearAffinityHodgeExact
import RenewalGeometry.Spectralization.OperatorTailMeasureNaimarkUniquenessExact
import RenewalGeometry.Predictive.RationalKreinCanonicalRealization
import RenewalGeometry.Spectralization.MarkedSpectralBundleDescentExact
import RenewalGeometry.Predictive.UniversalityPacketFunctorExact
import RenewalGeometry.Spectralization.StratifiedInverseFibreExhaustionExact

/-!
# Universality fibres and coarse graining (assembly)

Paper `predictive_spectral_geometry`, label `thm:summary-universality`, assembled from its
proved component records.

* (i) the stationary realization fibre of a metric graph triple is `𝒥(G,c)`
  (`thm:supp-graph-realization`, `stationary_markov_realization_fibre`: every stationary
  realization with masses `m` and conductances `c` is uniquely `(c + j)/m`, the open current
  polytope is in bijection with the positive-edge stationary realizations and every member has
  the same Hodge–Dirac operator), and the modular class recovers the complete directed
  generator: the affinity map `𝔄 : j ↦ [artanh(j/c)]` is a bijection `𝒥(G,c) → H¹(G;ℝ)`
  (`thm:supp-nonlinear-Hodge`, `affinityClass_bijOn`) and two currents with the same modular
  class coincide (`cor:supp-faithful-modular`, `current_eq_of_affinity_class_eq`), so the class
  determines the directed rates `(c ± j)/m`;
* (ii) positive hidden memory is classified by its minimal operator-valued Stieltjes measure:
  the canonical dilation is a minimal realization and any two minimal realizations of `μ` are
  related by a unique unitary intertwining the spectral measures and the sources
  (`thm:supp-Naimark-realization`, `eq:supp-Naimark-unitary`, `naimark_realization_unitary`);
  finite rational Hermitian indefinite memory (strictly proper part, Laurent data of finite
  Hankel rank) has the canonical source-minimal Pontryagin realization with the given Markov
  parameters, unique up to a source-fixing Pontryagin unitary
  (`thm:supp-complete-rational-Krein`, `canonical_isCyclic`, `canonical_markov`,
  `existsUnique_sourceFixing_unitary`);
* (iii) locally identical marked packets glued over a connected graph are globally classified
  by the monodromy class `[ρ] ∈ Hom(π₁(Γ), G_𝖲)/G_𝖲`: two flat marked bundle data are gauge
  equivalent iff their loop holonomies are conjugate by one element
  (`thm:supp-marked-bundle`, `gaugeEquivalent_iff_holonomy_conj`);
* (iv) current, memory and monodromy admit the canonical composable coarse-graining map
  `eq:supp-U-map` with the entropy/rank/index monotonicity statements and exact monodromy
  descent (`thm:supp-fibre-RG`, `universality_packet_functor`);
* (v) the fully reduced finite inverse fibre is the stratified stabilizer quotient
  (`thm:supp-finite-exhaustion`, `finite_stratified_exhaustion`) and the completed fibre of a
  completed finite-stage system (separation, tightness, compact strata, continuous bonding) is
  the inverse limit of the finite strata, nonempty exactly when the stable-image system is
  (`thm:supp-semifinite-exhaustion`, `CompletedStageSystem.completedEquivSections`,
  `nonempty_completed_iff_stableImage`).

Inherited disclosures: the descriptor (pencil) part of the indefinite-memory classification
(`cor:supp-all-rational`, the polynomial part of a general rational Hermitian function) is not
part of this statement — clause (ii) covers the strictly proper Pontryagin part; the retained
factors of clause (v) enter as gauge-sets and the completed system's separation/tightness
hypotheses are structure fields; the finite index and packet types are taken in `Type`.
-/

open Filter Topology Matrix MeasureTheory
open scoped InnerProductSpace

namespace RenewalGeometry.SummaryUniversality

open StationaryRenewalGraphFibre StationaryFluxAdjoint FiniteWeightedGraphHodgeDirac
  ModularAffinityReversalPacket NonlinearAffinityHodge OperatorTailMeasure MarkedBundle
  UniversalityPacket CurrentChain FiniteGraphSpectralUniversalityFibre StratifiedInverseFibre

universe u₁ u₂ u₃ u₄ u₅ uV uE uΓ uS

/-- **`thm:summary-universality` (Universality fibres and coarse graining)**, assembled from its
component records; see the module docstring for the clause by clause correspondence. -/
theorem summary_universality :
    -- (i) the stationary realization fibre is 𝒥(G,c) ...
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : SimpleOrientation V E) {m : V → ℝ}, (∀ x, 0 < m x) → ∀ (c : E → ℝ), (∀ e, 0 < c e) →
      (G.IsRealization m c (G.reversibleRates m c) ∧
        ∀ x y, m x * G.reversibleRates m c x y = m y * G.reversibleRates m c y x) ∧
      (∀ j ∈ G.currentPolytope c, G.IsRealization m c (G.rates m c j) ∧
        ∀ e, 0 < G.rates m c j (G.tail e) (G.head e) ∧
          0 < G.rates m c j (G.head e) (G.tail e)) ∧
      (∀ k, G.IsRealization m c k →
        ∃! j, j ∈ G.closedCurrentPolytope c ∧ k = G.rates m c j) ∧
      (∀ j, dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j x y)) =
        dirac m (G.pairConductance c)) ∧
      Nonempty (G.currentPolytope c ≃
        {k : V → V → ℝ // G.IsRealization m c k ∧
          ∀ e, 0 < k (G.tail e) (G.head e) ∧ 0 < k (G.head e) (G.tail e)})) ∧
    -- ... and the modular class recovers the directed generator
    (∀ {V E : Type} [Fintype V] [Fintype E] (B : Matrix V E ℝ) (c : E → ℝ),
      NonlinearAffinityHodge.IsConnectedIncidence B → (∀ e, 0 < c e) →
      Set.BijOn (affinityClass B c) (CurrentFibre B c) Set.univ ∧
      ∀ {j j' : E → ℝ}, j ∈ CurrentFibre B c → j' ∈ CurrentFibre B c →
        IsExact B (affinity c j - affinity c j') → j = j') ∧
    -- (ii) positive memory: the minimal operator-valued Stieltjes measure classification
    (∀ {H : Type} [Fintype H] [DecidableEq H] (μ : PositiveTailMeasure H),
      IsMinimalRealization μ μ.spectralProj μ.embedV ∧
      ∀ {K₁ : Type u₁} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
        {P₁ : ∀ s : Set ℝ, MeasurableSet s → K₁ →L[ℂ] K₁} {V₁ : EuclideanSpace ℂ H →L[ℂ] K₁}
        {K₂ : Type u₂} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
        {P₂ : ∀ s : Set ℝ, MeasurableSet s → K₂ →L[ℂ] K₂} {V₂ : EuclideanSpace ℂ H →L[ℂ] K₂},
        IsMinimalRealization μ P₁ V₁ → IsMinimalRealization μ P₂ V₂ →
        ∃! U : K₁ ≃ₗᵢ[ℂ] K₂,
          (∀ (s : Set ℝ) (hs : MeasurableSet s) (x : K₁), U (P₁ s hs x) = P₂ s hs (U x)) ∧
          ∀ ξ : EuclideanSpace ℂ H, U (V₁ ξ) = V₂ ξ) ∧
    -- (ii) indefinite rational memory: canonical minimal Pontryagin realization ...
    (∀ {H : Type u₃} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
      (Q : NormalizedRationalHermitianData H),
      Q.canonical.IsCyclic ∧ ∀ n, (Q.canonical.markov n : H →ₗ[ℂ] H) = Q.coeff n) ∧
    -- ... unique up to a source-fixing Pontryagin unitary
    (∀ {H : Type u₃} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {N₁ : Type u₄} [NormedAddCommGroup N₁] [InnerProductSpace ℂ N₁] [CompleteSpace N₁]
      [FiniteDimensional ℂ N₁]
      {N₂ : Type u₅} [NormedAddCommGroup N₂] [InnerProductSpace ℂ N₂] [CompleteSpace N₂]
      [FiniteDimensional ℂ N₂]
      (P₁ : PontryaginRealization H N₁) (P₂ : PontryaginRealization H N₂),
      P₁.IsCyclic → P₂.IsCyclic → (∀ n, P₁.markov n = P₂.markov n) →
      ∃! S : N₁ ≃ₗ[ℂ] N₂,
        (∀ h, S (P₁.Γ h) = P₂.Γ h) ∧ (∀ x, S (P₁.A x) = P₂.A (S x)) ∧
          (∀ x y, P₂.form (S x) (S y) = P₁.form x y)) ∧
    -- (iii) global classification by the monodromy class
    (∀ {G : NCG.Multigraph.{uV, uE}} {Γ : Type uΓ} [Group Γ] (U U' : G.E → Γ) {v₀ : G.V},
      G.ConnectedTo v₀ →
      (GaugeEquivalent U U' ↔
        ∃ c : Γ, ∀ p : G.Walk v₀ v₀, holonomy U' p = c⁻¹ * holonomy U p * c)) ∧
    -- (iv) canonical composable coarse graining with monotonicity and exact descent
    (∀ {V E H F G : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype H]
      [DecidableEq H] [Group F] [Group G]
      {V' E' H' F' : Type} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      [Fintype H'] [DecidableEq H'] [Group F']
      (U : UniversalityPacket V E H F G) (d : CoarseGraining U V' E' H' F'),
      (∀ ρ' : F' →* G, ρ'.comp d.qstar = U.ρ → ρ' = d.image.ρ) ∧
      (∀ {V'' E'' H'' F'' : Type} [Fintype V''] [Fintype E''] [DecidableEq V''] [DecidableEq E'']
        [Fintype H''] [DecidableEq H''] [Group F'']
        (d₂ : CoarseGraining d.image V'' E'' H'' F''), d₂.Λ ≤ d.Λ →
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
          negInertia (PontryaginRealization.kernelGram
            (PontryaginRealization.nevanlinnaKernel Q) z h) = κ} →
        PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel
          (PontryaginRealization.compress
            (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin d.W)) Q)) D ≤
          PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel Q) D) ∧
      (∀ (q : F →* F'), Function.Surjective q →
        ((∃! ρbar : F' →* G, U.ρ = ρbar.comp q) ↔ q.ker ≤ U.ρ.ker))) ∧
    -- (v) the fully reduced finite inverse fibre is a stratified stabilizer quotient ...
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → Type} [∀ a, Fintype (n a)]
      [∀ a, DecidableEq (n a)] (J M P C R : Type) [MulAction (JointGram.GaugeGroup n) J]
      [MulAction (JointGram.GaugeGroup n) M] [MulAction (JointGram.GaugeGroup n) P]
      [MulAction (JointGram.GaugeGroup n) C] [MulAction (JointGram.GaugeGroup n) R],
      ∃ e : RealizationSpace (n := n) J M P C R ≃ StratifiedQuotient (n := n) J M P C R,
        ∀ x : FullyReducedRealization n J M P C R, (e ⟦x⟧).1 = ⟦x.1⟧) ∧
    -- ... and the completed fibre is the inverse limit of the finite strata
    (∀ S : CompletedStageSystem.{uS},
      Nonempty (S.Completed ≃ S.toInverseSystem.Sections) ∧
      (Nonempty S.Completed ↔ ∀ n, (S.toInverseSystem.stableImage n).Nonempty)) :=
  ⟨fun G => fun hm c hc => G.stationary_markov_realization_fibre hm c hc,
    fun B c hB hc => ⟨affinityClass_bijOn hB hc,
      fun hj hj' ha => current_eq_of_affinity_class_eq B c hj hj' ha⟩,
    fun μ => naimark_realization_unitary μ,
    fun Q => ⟨Q.canonical_isCyclic, Q.canonical_markov⟩,
    fun P₁ P₂ h₁ h₂ hm => P₁.existsUnique_sourceFixing_unitary P₂ h₁ h₂ hm,
    fun U U' => fun hconn => gaugeEquivalent_iff_holonomy_conj U U' hconn,
    fun {V E H F G} _ _ _ _ _ _ _ _ {V' E' H' F'} _ _ _ _ _ _ _ U d =>
      ⟨(universality_packet_functor (V'' := V') (E'' := E') (H'' := H') (F'' := F') U d).1,
        fun d₂ hΛ => (universality_packet_functor U d).2.1 d₂ hΛ,
        (universality_packet_functor (V'' := V') (E'' := E') (H'' := H') (F'' := F') U d).2.2⟩,
    fun {ι} _ _ {n} _ _ J M P C R _ _ _ _ _ => (finite_stratified_exhaustion (n := n) J M P C R).1,
    fun S => ⟨⟨S.completedEquivSections⟩, S.nonempty_completed_iff_stableImage⟩⟩

end RenewalGeometry.SummaryUniversality
