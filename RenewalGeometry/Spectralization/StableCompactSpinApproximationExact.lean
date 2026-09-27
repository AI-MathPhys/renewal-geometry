/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent
import RenewalGeometry.Spectralization.EndpointBlockMetricHeadExact

/-!
# Conditional stable compact-spin approximation

Paper `predictive_spectral_geometry`, label `cor:supp-compact-spin-image`, in the abstract
surrogate.  A closed marked Riemannian spin manifold together with its discretisation data is
rendered as `MarkedSpinDiscretization`: a compatible stable atlas for the doubled Dirac operator
(`CompatibleStableAtlas`, the surrogate of `def:stable-spin-atlas`) and a sequence of finite
endpoint metric heads (`EdgeGraph`, the finite metric triples of `thm:supp-global-metric`) with
positive edge lengths and connected vertex sets.

* `stableCompactSpinApproximation`: the spin operator is approximated in norm resolvent by the
  finite stage operators for every non-real `z` (`thm:supp-compact-spin-resolvent`), and every
  metric head is an exact finite metric triple whose pure-state Connes distance is its graph
  shortest-path metric (`thm:supp-global-metric`, finite clauses).
* `stableCompactSpinApproximation_forall`: the "essential surjectivity" clause — supplying such
  data for every target in a family yields the approximation for every member.

The geodesic-convergence clause of `thm:supp-global-metric` (uniform convergence of the graph
distances to the Riemannian distance) is not part of this surrogate.
-/

open Filter Topology
open RenewalGeometry.EndpointBlockMetricHead

noncomputable section

namespace RenewalGeometry

universe u v w u' v'

/-- The surrogate of a closed marked Riemannian spin manifold with a compatible stable spin
discretisation: the atlas of `def:stable-spin-atlas` for the doubled Dirac operator and a
sequence of finite endpoint metric heads with positive edge lengths and connected graphs. -/
structure MarkedSpinDiscretization (H : Type u) (V : Type v) (Hn : ℕ → Type w)
    (Vh : ℕ → Type u') (Eh : ℕ → Type v') [∀ n, Fintype (Eh n)]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
    [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)] where
  /-- The compatible stable spin atlas. -/
  atlas : CompatibleStableAtlas H V Hn
  /-- The independent finite metric heads (endpoint-block graphs on the mesh vertices). -/
  metricHead : ∀ n, EdgeGraph (Vh n) (Eh n)
  /-- Every edge is the length of an actual short curve, hence positive. -/
  metricHead_len_pos : ∀ n e, 0 < (metricHead n).len e
  /-- The mesh graph is connected. -/
  metricHead_connected : ∀ n, Connected (metricHead n)

namespace MarkedSpinDiscretization

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
variable {Vh : ℕ → Type u'} {Eh : ℕ → Type v'} [∀ n, Fintype (Eh n)]

/-- **`cor:supp-compact-spin-image`** (abstract surrogate).  The doubled spin Dirac operator is
approximated in norm resolvent by the finite stage operators for every non-real `z`, and every
independent metric head is an exact finite metric triple: its pure-state Connes distance is the
graph shortest-path metric. -/
theorem stableCompactSpinApproximation (D : MarkedSpinDiscretization H V Hn Vh Eh) :
    (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖D.atlas.embeddedResolvent z hz n - D.atlas.limit.resolvent z hz‖)
        atTop (𝓝 0)) ∧
    (∀ n (x y : Vh n),
      edgeConnesDistance (D.metricHead n) x y = graphDistance (D.metricHead n) x y) :=
  ⟨fun _ hz => D.atlas.tendsto_norm_embeddedResolvent_sub hz,
    fun n x y => edgeConnesDistance_eq_graphDistance (D.metricHead n)
      (D.metricHead_len_pos n) (D.metricHead_connected n) x y⟩

/-- The limit resolvents are compact operators (the finite-dimensional approximation is of a
compact-resolvent operator). -/
theorem isCompactOperator_limit_resolvent (D : MarkedSpinDiscretization H V Hn Vh Eh)
    {z : ℂ} (hz : z.im ≠ 0) : IsCompactOperator (D.atlas.limit.resolvent z hz) :=
  D.atlas.isCompactOperator_limit_resolvent hz

end MarkedSpinDiscretization

/-- **`cor:supp-compact-spin-image`, essential-surjectivity clause** (abstract surrogate).  If
compatible stable discretisations with finite metric heads are supplied for every target in a
family indexed by `ι`, then every target admits the finite-dimensional approximation of its
doubled spin Dirac operator in norm resolvent together with exact finite metric heads. -/
theorem stableCompactSpinApproximation_forall {ι : Type*}
    {H : ι → Type u} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    {V : ι → Type v} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
    {Hn : ι → ℕ → Type w} [∀ i n, NormedAddCommGroup (Hn i n)]
    [∀ i n, InnerProductSpace ℂ (Hn i n)] [∀ i n, CompleteSpace (Hn i n)]
    [∀ i n, FiniteDimensional ℂ (Hn i n)]
    {Vh : ι → ℕ → Type u'} {Eh : ι → ℕ → Type v'} [∀ i n, Fintype (Eh i n)]
    (D : ∀ i, MarkedSpinDiscretization (H i) (V i) (Hn i) (Vh i) (Eh i)) :
    ∀ i, (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖(D i).atlas.embeddedResolvent z hz n - (D i).atlas.limit.resolvent z hz‖)
        atTop (𝓝 0)) ∧
    (∀ n (x y : Vh i n),
      edgeConnesDistance ((D i).metricHead n) x y = graphDistance ((D i).metricHead n) x y) :=
  fun i => (D i).stableCompactSpinApproximation

end RenewalGeometry
