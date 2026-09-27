/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.CanonicalGraphSpectralizationExact
import RenewalGeometry.Spectralization.UniversalOneFormDiracKernelGrowthExact
import RenewalGeometry.Spectralization.PeriodicTorusCubicalHarmonicExact
import RenewalGeometry.DiscreteAnalysis.CoframeDirichletFormLimitExact
import RenewalGeometry.DiscreteAnalysis.VariableWilsonGardingExact
import RenewalGeometry.DiscreteAnalysis.CovariantWilsonCoreConsistencyExact
import RenewalGeometry.Spectralization.CompactSpinMainAssemblyExact

/-!
# Independent metric reconstruction and stable compact-spin convergence (assembly)

Paper `predictive_spectral_geometry`, label `thm:summary-metric`, assembled from its proved
component records.

* (i) `canonical_graph_spectralization` (the graph identities `eq:summary-graph-identities`,
  `thm:supp-A3-finite`) and `tendsto_distanceError_zero` (uniform convergence of the periodic
  `A₃` Connes distance to the flat torus quotient metric, `eq:summary-A3-distance`,
  `thm:supp-A3-distance`).
* (ii) the one-step universal graph calculus has the extensive one-form kernel
  `dim Ker D = 2e - n + 2`, unbounded on the periodic `A₃` root graphs
  (`cth:supp-extensive-kernel`, `extensive_universal_oneform_kernel`), whereas the
  relation-adapted cellular completion carries the Hodge decomposition of
  `thm:supp-modular-Hodge` (`cellular_modular_hodge`) with a finite harmonic one-form space —
  of dimension `b₁ = 3` on the periodic three-torus (`finrank_harmonicSpace_eq_three`); the
  continuum limit is rendered by the Dirichlet-form limit of the coframe renewal packet,
  `-⟨f, L_h f⟩ → ∫ ½ g^{ij} ∂_i f ∂_j f ρ` (`eq:supp-general-form-limit`,
  `tendsto_dirichletForm_metric`).
* (iii) the covariant Wilson construction has one low-energy species (the frozen symbol
  vanishes only at `θ = 0` on the Brillouin torus, `frozenSymbol_eq_zero_iff`), satisfies the
  local uniform graph estimate `eq:supp-general-Garding` with variable coefficients
  (`variable_garding`) and is consistent on the smooth core
  (`norm_covariantWilson_sample_sub_densitySymmetricDirac_le`, `eq:supp-general-core`).
* (iv) for a compatible stable spin discretisation (`def:stable-spin-atlas`, the abstract
  atlas `CompatibleStableAtlas`), `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every non-real
  `z` (`eq:summary-spin-resolvent`, `compactSpinMain_norm_resolvent`).
* (v) every compact chain metric space (the closed Riemannian manifold with its geodesic
  distance) admits finite metric triples on refining meshes with
  `sup_{x,y ∈ V_h} |d_h^met(x,y) - d_g(x,y)| → 0` (`eq:summary-global-metric`,
  `compactSpinMain_exists_metricHeads`).

The surrogates of the component records are inherited: the closed spin manifold and its Dirac
operator are the abstract atlas (a Hilbert space with a self-adjoint operator given by resolvent
data, a compact Sobolev embedding, finite stages), the Riemannian distance is a compact metric
space with the chain property, the Wilson estimates live on the periodic lattice torus, and the
compact-resolvent continuum limit of the cellular Hodge–Dirac operator itself is not a
supplement theorem and is rendered by the Dirichlet-form limit.
-/

open Filter Topology Matrix
open RenewalGeometry.CanonicalGraphSpectralization RenewalGeometry.A3ConnesFlatUniformConvergence
  RenewalGeometry.StationaryFluxAdjoint RenewalGeometry.FiniteWeightedGraphHodgeDirac
  RenewalGeometry.UniversalOneFormDiracKernelGrowth RenewalGeometry.CellularModularHodge
  RenewalGeometry.PeriodicTorusCubical RenewalGeometry.CoframeRenewalPacket
  RenewalGeometry.FrozenWilsonSymbol RenewalGeometry.FrozenWilsonGarding
  RenewalGeometry.VariableWilsonGarding RenewalGeometry.LatticeTorusPlancherel
  RenewalGeometry.CovariantWilsonCoreConsistency RenewalGeometry.MeshGraphDistanceConvergence
  RenewalGeometry.EndpointBlockMetricHead

namespace RenewalGeometry.SummaryMetric

universe u v w x

/-- **`thm:summary-metric` (Independent metric reconstruction and stable compact-spin
convergence)**, assembled from its component records; see the module docstring for the clause
by clause correspondence and the inherited surrogates. -/
theorem summary_metric :
    -- (i) graph identities and uniform A₃ Connes-distance convergence
    (∀ {V : Type} [Fintype V] [DecidableEq V] (mass : V → ℝ) (k : V → V → ℝ),
      (∀ x, 0 < mass x) → (∀ x y, 0 ≤ k x y) →
      (∀ x, ∑ y, mass x * k x y = ∑ y, mass y * k y x) →
      ConductanceConnected (symmetrizedConductance (fun x y => mass x * k x y)) →
      SpectralizationConclusion mass k) ∧
    Tendsto distanceError atTop (𝓝 0) ∧
    -- (ii) extensive one-step kernel versus the finite harmonic space of the cellular
    -- completion, and the Dirichlet-form continuum limit
    (∀ {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      (d : V →L[ℝ] W) (n e : ℕ), Module.finrank ℝ V = n → Module.finrank ℝ W = 2 * e →
      Module.finrank ℝ (LinearMap.ker d.toLinearMap) = 1 →
      Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) = 2 * e + 2 - n ∧
      (e = 6 * n →
        Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) = 11 * n + 2) ∧
      (∀ M : ℕ, ∃ k : ℕ, M < 11 * k + 2)) ∧
    (∀ (n : ℕ) [NeZero n],
      Module.finrank ℝ (harmonicSpace (PeriodicTorusCubical.d₀ n) (PeriodicTorusCubical.d₁ n)) =
        3) ∧
    (∀ {d : ℕ} {ι : Type} [Fintype ι] (P : CoframePacket d ι), 2 ≤ d →
      ∀ {ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}, P.IsDecomposition ginv →
      ∀ (f : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 f → Periodic f → ∀ (F1 F2 : ℝ),
      (∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ F1) → (∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ F2) →
      (∀ r, ContDiff ℝ 1 (P.coeff r)) → (∀ r, Periodic (P.coeff r)) → ∀ (A0 A1 : ι → ℝ),
      (∀ r y, ‖iteratedFDeriv ℝ 0 (P.coeff r) y‖ ≤ A0 r) →
      (∀ r y, ‖iteratedFDeriv ℝ 1 (P.coeff r) y‖ ≤ A1 r) →
      (∀ x, P.density x ≠ 0) → P.IntegerDirections →
      Tendsto (fun n : ℕ => P.dirichletForm (n + 1) f) atTop
        (𝓝 (∫ x in Set.Icc (0 : Fin d → ℝ) 1, (1 / 2) * ∑ i, ∑ j, ginv x i j *
          fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1) * P.density x))) ∧
    -- (iii) one low-energy species, the variable-coefficient Gårding estimate and smooth-core
    -- consistency of the covariant Wilson operator
    (∀ {d N : ℕ} (h ϖ : ℝ), h ≠ 0 → ϖ ≠ 0 → ∀ [NeZero N]
      (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin d) (Fin d) ℝ), DoubledCliffordData c Γ g →
      (∀ ξ : Fin d → ℝ, 0 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)) → ∀ (θ : Fin d → ℝ),
      frozenSymbol h ϖ c Γ θ = 0 ↔ ∀ j, ∃ n : ℤ, θ j = n * (2 * Real.pi)) ∧
    (∀ {d n N : ℕ} [NeZero n] (h ϖ lam Lam : ℝ), 0 < h → 0 < lam → ϖ ≠ 0 → 0 ≤ Lam →
      ∀ (c : CoefficientField d n N) (Γ : Matrix (Fin N) (Fin N) ℂ), Γᴴ = Γ →
      ∀ {m : ℕ} (χ : Fin m → Grid d n → ℝ), (∀ x, ∑ α, χ α x ^ 2 = 1) →
      ∀ (x₀ : Fin m → Grid d n), (∀ α, UniformlyElliptic (c (x₀ α)) Γ lam Lam) →
      ∀ {ω K L B G : ℝ}, 0 ≤ ω → 0 ≤ K → 0 ≤ L → 0 ≤ B → 0 ≤ G →
      (∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K) →
      (∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w) →
      (∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w) →
      (∀ α (j : Fin d) x, NearSupport (χ α) j x →
        ∀ w, euclNormSq ((c x j - c (x₀ α) j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w) →
      (∀ (j : Fin d) x w,
        euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w) →
      4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1 → ∀ (u : TorusSection d n N),
      h1NormSq h u ≤ gardingConstant d m lam ϖ K L B G *
        (gridNormSq h (varWilson h ϖ c Γ u) + gridNormSq h u)) ∧
    -- (iv) norm-resolvent convergence for compatible stable spin discretisations
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
      [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
      (A : CompatibleStableAtlas H V Hn) (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) ∧
    -- (v) independent metric heads on refining meshes converging to the distance
    (∀ {X : Type x} [MetricSpace X] [CompactSpace X], HasChains X →
      ∃ (Vh Eh : ℕ → Type x) (_ : ∀ n, Fintype (Vh n)) (_ : ∀ n, Fintype (Eh n))
        (S : MeshSequence X Vh Eh),
        (∀ n e, 0 < (S.mesh n).graph.len e) ∧
        (∀ n (x y : Vh n), edgeConnesDistance (S.mesh n).graph x y =
          graphDistance (S.mesh n).graph x y) ∧
        ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
          ∀ n (x y : Vh n), |graphDistance (S.mesh n).graph x y -
            dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n) :=
  ⟨fun mass k hmass hk hst hconn => canonical_graph_spectralization mass k hmass hk hst hconn,
    tendsto_distanceError_zero,
    fun d n e hV hW hconn => extensive_universal_oneform_kernel d n e hV hW hconn,
    fun n _ => finrank_harmonicSpace_eq_three,
    fun P hd => fun hg f hf hfp F1 F2 hF1 hF2 hC hap A0 A1 hA0 hA1 hρ hdir =>
      P.tendsto_dirichletForm_metric hd hg f hf hfp F1 F2 hF1 hF2 hC hap A0 A1 hA0 hA1 hρ hdir,
    fun h ϖ hh hϖ => fun c Γ g hc hg θ => frozenSymbol_eq_zero_iff h ϖ hh hϖ c Γ g hc hg θ,
    fun h ϖ lam Lam hh hlam hϖ hLam c Γ hΓ => fun χ hpart x₀ hell =>
      fun hω hK hL hB hG hgrad hc hΓb hfreeze hLip habs u =>
        variable_garding h ϖ lam Lam hh hlam hϖ hLam c Γ hΓ χ hpart x₀ hell hω hK hL hB hG hgrad
          hc hΓb hfreeze hLip habs u,
    fun A z hz => A.compactSpinMain_norm_resolvent z hz,
    fun hX => compactSpinMain_exists_metricHeads hX⟩

end RenewalGeometry.SummaryMetric
