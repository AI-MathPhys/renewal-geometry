/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent
import RenewalGeometry.Spectralization.MeshGraphDistanceConvergenceExact
import RenewalGeometry.Spectralization.StableCompactSpinApproximationExact

/-!
# Norm-resolvent convergence under atlas stability, with convergent metric heads

Paper `predictive_spectral_geometry`, labels `thm:compact-spin-main` and
`cor:supp-compact-spin-image`, assembled in the abstract surrogate.

* The spin clause `eq:compact-spin-resolvent-main` is
  `CompatibleStableAtlas.compactSpinMain_norm_resolvent` (the compatible stable spin
  discretisation of `def:stable-spin-atlas` is rendered as the atlas structure on a fixed
  Hilbert space with the doubled Dirac operator given by its resolvent data).
* The metric clause `eq:compact-spin-distance-main` is the metric-space surrogate of
  `MeshGraphDistanceConvergenceExact`: the closed Riemannian manifold is a compact metric
  space with the chain property (`HasChains`, geodesic partitioning), the finite metric
  triples on refining meshes are `MeshSequence`s, which exist on every compact metric space
  (`exists_meshSequence`), and `sup_{x,y ∈ V_h} |d_h^met(x,y) - d_g(x,y)| → 0`.

`compactSpinMain` states both clauses together; `compactSpinMain_exists_metricHeads` is the
existence form of the metric clause.  `ConvergentMarkedSpinDiscretization` is the data of
`cor:supp-compact-spin-image` (atlas plus convergent independent metric heads), and
`ConvergentMarkedSpinDiscretization.approximation` its conclusion: norm-resolvent
approximation for every non-real `z`, exactness of every metric head (pure-state Connes
distance = graph distance) and uniform convergence of the metric heads to the distance;
`convergentStableCompactSpinApproximation_forall` is the essential-surjectivity clause.
-/

open Filter Topology
open RenewalGeometry.EndpointBlockMetricHead RenewalGeometry.MeshGraphDistanceConvergence

noncomputable section

namespace RenewalGeometry

universe u v w u' v' x

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

/-- **`thm:compact-spin-main`** (abstract surrogate).  For a compatible stable spin
discretisation `A` of the doubled Dirac operator, the compressed stage resolvents converge in
operator norm to the resolvent of the limit for every non-real `z`
(`eq:compact-spin-resolvent-main`); independently, for every refining mesh sequence `S` on a
compact chain space (the closed Riemannian manifold with its geodesic distance), the graph
distances of the finite metric triples converge uniformly to the distance
(`eq:compact-spin-distance-main`). -/
theorem compactSpinMain (A : CompatibleStableAtlas H V Hn) {X : Type x} [PseudoMetricSpace X]
    [CompactSpace X] (hX : HasChains X) {Vh : ℕ → Type u'} {Eh : ℕ → Type v'}
    (S : MeshSequence X Vh Eh) :
    (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : Vh n), |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n) :=
  ⟨fun z hz => A.compactSpinMain_norm_resolvent z hz,
    S.exists_error_tendsto_zero_of_compactSpace hX⟩

/-- **`eq:compact-spin-distance-main`, existence form.** Every compact chain metric space
admits finite metric triples (finite vertex and edge sets, positive edge lengths) on refining
meshes whose graph distances — equal to the pure-state Connes distances of the endpoint
metric heads — converge uniformly to the distance. -/
theorem compactSpinMain_exists_metricHeads {X : Type x} [MetricSpace X] [CompactSpace X]
    (hX : HasChains X) :
    ∃ (Vh Eh : ℕ → Type x) (_ : ∀ n, Fintype (Vh n)) (_ : ∀ n, Fintype (Eh n))
      (S : MeshSequence X Vh Eh),
      (∀ n e, 0 < (S.mesh n).graph.len e) ∧
      (∀ n (x y : Vh n), edgeConnesDistance (S.mesh n).graph x y =
        graphDistance (S.mesh n).graph x y) ∧
      ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
        ∀ n (x y : Vh n), |graphDistance (S.mesh n).graph x y -
          dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n := by
  obtain ⟨Vh, Eh, hV, hE, S, hpos⟩ := exists_meshSequence (X := X)
  exact ⟨Vh, Eh, hV, hE, S, hpos,
    fun n x y => edgeConnesDistance_eq_graphDistance _ (hpos n) ((S.mesh n).connected hX) x y,
    S.exists_error_tendsto_zero_of_compactSpace hX⟩

/-- The data of `cor:supp-compact-spin-image`: a closed marked Riemannian spin manifold with a
compatible stable spin discretisation and convergent independent metric heads, in the abstract
surrogate — a compatible stable atlas for the doubled Dirac operator, a compact chain metric
space `X` (the manifold with its geodesic distance) and a refining mesh sequence of finite
endpoint metric heads with positive edge lengths. -/
structure ConvergentMarkedSpinDiscretization (H : Type u) (V : Type v) (Hn : ℕ → Type w)
    (X : Type x) [PseudoMetricSpace X] [CompactSpace X]
    (Vh : ℕ → Type u') (Eh : ℕ → Type v') [∀ n, Fintype (Eh n)]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
    [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)] where
  /-- The compatible stable spin atlas. -/
  atlas : CompatibleStableAtlas H V Hn
  /-- The refining meshes carrying the independent metric heads. -/
  meshes : MeshSequence X Vh Eh
  /-- Every edge is the length of an actual short curve, hence positive. -/
  len_pos : ∀ n e, 0 < (meshes.mesh n).graph.len e
  /-- The geodesic (chain) property of the underlying space. -/
  chains : HasChains X

namespace ConvergentMarkedSpinDiscretization

variable {X : Type x} [PseudoMetricSpace X] [CompactSpace X]
variable {Vh : ℕ → Type u'} {Eh : ℕ → Type v'} [∀ n, Fintype (Eh n)]

/-- The underlying data of `StableCompactSpinApproximationExact` (finite exact metric heads). -/
def toMarkedSpinDiscretization (D : ConvergentMarkedSpinDiscretization H V Hn X Vh Eh) :
    MarkedSpinDiscretization H V Hn Vh Eh where
  atlas := D.atlas
  metricHead n := (D.meshes.mesh n).graph
  metricHead_len_pos := D.len_pos
  metricHead_connected n := (D.meshes.mesh n).connected D.chains

/-- **`cor:supp-compact-spin-image`** (abstract surrogate).  The doubled spin Dirac operator is
approximated in norm resolvent by the finite stage operators for every non-real `z`; every
independent metric head is exact (pure-state Connes distance = graph shortest-path metric);
and the metric heads converge: an error sequence tending to zero bounds
`|d_h^met(x,y) - d_g(x,y)|` over all vertex pairs. -/
theorem approximation (D : ConvergentMarkedSpinDiscretization H V Hn X Vh Eh) :
    (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖D.atlas.embeddedResolvent z hz n - D.atlas.limit.resolvent z hz‖)
        atTop (𝓝 0)) ∧
    (∀ n (x y : Vh n), edgeConnesDistance (D.meshes.mesh n).graph x y =
      graphDistance (D.meshes.mesh n).graph x y) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : Vh n), |edgeConnesDistance (D.meshes.mesh n).graph x y -
        dist ((D.meshes.mesh n).point x) ((D.meshes.mesh n).point y)| ≤ err n) :=
  ⟨fun _ hz => D.atlas.tendsto_norm_embeddedResolvent_sub hz,
    fun n x y => edgeConnesDistance_eq_graphDistance _ (D.len_pos n)
      ((D.meshes.mesh n).connected D.chains) x y,
    D.meshes.exists_error_tendsto_zero_connes D.chains
      (fun z w => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ z)
        (Set.mem_univ w)) D.len_pos⟩

/-- The limit resolvents are compact operators. -/
theorem isCompactOperator_limit_resolvent (D : ConvergentMarkedSpinDiscretization H V Hn X Vh Eh)
    {z : ℂ} (hz : z.im ≠ 0) : IsCompactOperator (D.atlas.limit.resolvent z hz) :=
  D.atlas.isCompactOperator_limit_resolvent hz

end ConvergentMarkedSpinDiscretization

/-- **`cor:supp-compact-spin-image`, essential-surjectivity clause** (abstract surrogate).  If
compatible stable discretisations with convergent metric heads are supplied for every target
in a family, every target admits the finite-dimensional approximation of its doubled spin
Dirac operator in norm resolvent together with exact, convergent metric heads. -/
theorem convergentStableCompactSpinApproximation_forall {ι : Type*}
    {H : ι → Type u} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    {V : ι → Type v} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
    {Hn : ι → ℕ → Type w} [∀ i n, NormedAddCommGroup (Hn i n)]
    [∀ i n, InnerProductSpace ℂ (Hn i n)] [∀ i n, CompleteSpace (Hn i n)]
    [∀ i n, FiniteDimensional ℂ (Hn i n)]
    {X : ι → Type x} [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]
    {Vh : ι → ℕ → Type u'} {Eh : ι → ℕ → Type v'} [∀ i n, Fintype (Eh i n)]
    (D : ∀ i, ConvergentMarkedSpinDiscretization (H i) (V i) (Hn i) (X i) (Vh i) (Eh i)) :
    ∀ i, (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖(D i).atlas.embeddedResolvent z hz n - (D i).atlas.limit.resolvent z hz‖)
        atTop (𝓝 0)) ∧
    (∀ n (x y : Vh i n), edgeConnesDistance ((D i).meshes.mesh n).graph x y =
      graphDistance ((D i).meshes.mesh n).graph x y) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : Vh i n), |edgeConnesDistance ((D i).meshes.mesh n).graph x y -
        dist (((D i).meshes.mesh n).point x) (((D i).meshes.mesh n).point y)| ≤ err n) :=
  fun i => (D i).approximation

end RenewalGeometry
