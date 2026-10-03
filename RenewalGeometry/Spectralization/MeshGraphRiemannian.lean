/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.MeshGraphApproxChains
import RenewalGeometry.Analysis.RiemannianDistanceLipschitz

/-!
# Endpoint spectral triples and geodesic convergence on closed Riemannian manifolds

Paper `predictive_spectral_geometry`, label `thm:supp-global-metric`, on a genuine closed
Riemannian manifold in Mathlib's sense: a compact manifold `M` modelled on `I` without boundary,
with a continuous Riemannian metric (`RiemannianBundle`, `IsContinuousRiemannianBundle`), whose
distance is the Riemannian distance (`IsRiemannianManifold I M`: `edist = riemannianEDist`, the
infimum of the lengths of `C¹` paths).  The distance is assumed finite (`MetricSpace M`), which is
automatic for a connected manifold (`edist_ne_top_of_connectedSpace`).

* `hasApproxChains_of_isRiemannianManifold`: a Riemannian manifold has the approximate chain
  property (near-geodesic paths, `exists_nearGeodesic_path`).
* `exists_sub_mul_dist_le_abs_sub_of_iSup`: for a `C¹` function on a compact boundaryless
  Riemannian manifold, `‖∇_g f‖_∞ = ⨆ p, ‖df_p‖` is the optimal Lipschitz constant.
* `ApproxMeshSequence.tendsto_edgeLipschitz_riemannian` (smooth seminorm clause):
  `L_h^met(f|_{V_h}) → ⨆ p, ‖df_p‖`; `..._gradient` with `‖∇_g f(p)‖` (Riesz gradient).
* `ApproxMeshSequence.global_metric_riemannian`: **all four clauses of
  `thm:supp-global-metric`** for every refining sequence of approximate meshes (`h`-nets,
  `h/ρ_h → 0`, `ρ_h → 0`, all pairs within `ρ_h` joined, positive lengths with
  `sup |ℓ_h/d_g - 1| → 0`).
* `exists_approxMeshSequence`: such mesh sequences exist on every compact metric space (exact
  lengths `ℓ_h = d_g`).

The injectivity-radius condition of the paper is not needed.  Mathlib provides no compact
Riemannian manifold of positive dimension yet (its only `RiemannianBundle` instance is the flat
metric of an inner product space), so the full packet is instantiated below on the one-point
space only; each Riemannian ingredient is instantiated non-trivially on the Euclidean line
(`RiemannianDistanceLipschitz`, and `hasApproxChains_real` below).
-/

open Filter Topology Set Manifold Bundle
open scoped ContDiff
open RenewalGeometry.EndpointBlockMetricHead RenewalGeometry.RiemannianDistanceLipschitz

namespace RenewalGeometry.MeshGraphDistanceConvergence

/-! ### Existence of approximate mesh sequences on compact metric spaces -/

universe u

/-- **Existence of refining meshes satisfying the paper's assumptions.** Every compact metric
space admits an `ApproxMeshSequence` (`h_n = (n+1)⁻²`, `ρ_n = (n+1)⁻¹`, exact lengths `ℓ = d`,
so `ε = 0`) with finite vertex and edge sets: the vertices are finite `h_n`-nets and the edges
join distinct vertices within `ρ_n`. -/
theorem exists_approxMeshSequence {X : Type u} [MetricSpace X] [CompactSpace X] :
    ∃ (Vh Eh : ℕ → Type u) (_ : ∀ n, Fintype (Vh n)) (_ : ∀ n, Fintype (Eh n)),
      Nonempty (ApproxMeshSequence X Vh Eh) := by
  classical
  have hh : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  choose t ht using fun n : ℕ => finite_cover_balls_of_compact (isCompact_univ (X := X)) (hh n)
  let Vh : ℕ → Type u := fun n => ↥(t n)
  let Eh : ℕ → Type u := fun n => {p : Vh n × Vh n // p.1 ≠ p.2 ∧
    dist (p.1 : X) (p.2 : X) ≤ 1 / ((n : ℝ) + 1)}
  let _ : ∀ n, Fintype (Vh n) := fun n => (ht n).2.1.fintype
  let Γ : ∀ n, EdgeGraph (Vh n) (Eh n) := fun n =>
    { src := fun e => e.1.1, tgt := fun e => e.1.2, len := fun e => dist (e.1.1 : X) (e.1.2 : X) }
  let mesh : ∀ n, ApproxMeshGraph X (Vh n) (Eh n) := fun n =>
    ApproxMeshGraph.ofExact (Γ n) (fun v => (v : X)) (1 / ((n : ℝ) + 1) ^ 2) (1 / ((n : ℝ) + 1))
      (hh n).le (by positivity) (fun _ => rfl)
      (fun e => dist_pos.mpr (Subtype.val_injective.ne e.2.1))
      (fun z => by
        have hz := (ht n).2.2 (Set.mem_univ z)
        rw [Set.mem_iUnion₂] at hz
        obtain ⟨x, hx, hxz⟩ := hz
        exact ⟨⟨x, hx⟩, (Metric.mem_ball.mp hxz).le⟩)
      (fun u v huv hd => ⟨⟨(u, v), huv, hd⟩, Or.inl ⟨rfl, rfl⟩⟩)
  have hρ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Vh, Eh, inferInstance, fun n => Subtype.fintype _,
    ⟨{ mesh := mesh
       h_div_ρ := ?_
       ε_tendsto := tendsto_const_nhds
       ρ_tendsto := hρ }⟩⟩
  refine hρ.congr fun n => ?_
  show 1 / ((n : ℝ) + 1) = (1 / ((n : ℝ) + 1) ^ 2) / (1 / ((n : ℝ) + 1))
  field_simp

/-! ### Riemannian manifolds -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
include I in
/-- **Riemannian manifolds have the approximate chain property**: approximate chains are cut out
of near-minimising `C¹` paths (`exists_nearGeodesic_path`, `hasApproxChains_of_nearGeodesic`). -/
theorem hasApproxChains_of_isRiemannianManifold : HasApproxChains M :=
  hasApproxChains_of_nearGeodesic fun x y δ hδ => exists_nearGeodesic_path I x y δ hδ

/-- Non-vacuity: the Euclidean line, as a Riemannian manifold, has the approximate chain
property by the Riemannian route. -/
theorem hasApproxChains_real : HasApproxChains ℝ :=
  hasApproxChains_of_isRiemannianManifold 𝓘(ℝ, ℝ)

section Compact

variable [I.Boundaryless] [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace I x)]
  [CompactSpace M]

omit [IsRiemannianManifold I M] in
/-- `‖∇_g f‖_∞ = ⨆ p, ‖df_p‖` is nonnegative and bounds every `‖df_p‖`. -/
theorem norm_differential_le_iSup {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (p : M) :
    ‖differential I f p‖ ≤ ⨆ q, ‖differential I f q‖ :=
  le_ciSup (bddAbove_norm_differential hf) p

/-- **`‖∇_g f‖_∞` is the optimal Lipschitz constant** (lower half): if `‖∇_g f‖_∞ > 0`, then for
every `ε > 0` there are points `x ≠ y` with `(‖∇_g f‖_∞ - ε) d(x,y) ≤ |f x - f y|`. -/
theorem exists_sub_mul_dist_le_abs_sub_of_iSup {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hL : 0 < ⨆ p, ‖differential I f p‖) :
    ∀ ε > (0 : ℝ), ∃ x y : M, 0 < dist x y ∧
      ((⨆ p, ‖differential I f p‖) - ε) * dist x y ≤ |f x - f y| := by
  intro ε hε
  set L := ⨆ p, ‖differential I f p‖ with hLdef
  set ε₁ := min ε L with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hε hL
  have hε₁L : ε₁ ≤ L := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hne : Nonempty M := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : L = 0 := by rw [hLdef]; exact Real.iSup_of_isEmpty _
    linarith
  obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup (show L - ε₁ / 2 < L by linarith)
  obtain ⟨y, hy0, hy⟩ := exists_sub_mul_dist_le_abs_sub (I := I) p
    ((hf p).mdifferentiableAt one_ne_zero) (ε := ε₁ / 2) (by positivity) (by linarith)
  refine ⟨y, p, by rwa [dist_comm], ?_⟩
  rw [dist_comm]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg) hy
  linarith

/-- **Smooth seminorm clause of `thm:supp-global-metric`** on a closed Riemannian manifold:
for every `C¹` function `f` and every refining sequence of approximate meshes,
`L_h^met(f|_{V_h}) → ‖∇_g f‖_∞ = ⨆ p, ‖df_p‖`. -/
theorem ApproxMeshSequence.tendsto_edgeLipschitz_riemannian {Vh Eh : ℕ → Type*}
    (S : ApproxMeshSequence M Vh Eh) [∀ n, Fintype (Eh n)] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (⨆ p, ‖differential I f p‖)) := by
  set L := ⨆ p, ‖differential I f p‖ with hLdef
  have hL0 : 0 ≤ L := Real.iSup_nonneg fun p => by positivity
  have hlip : LipschitzWith ⟨L, hL0⟩ f :=
    lipschitzWith_of_norm_differential_le hf fun p => norm_differential_le_iSup hf p
  rcases hL0.eq_or_lt with h0 | hpos
  · -- `‖∇f‖_∞ = 0`: `f` is constant and all edge seminorms vanish
    have hconst : ∀ x y, f x = f y := by
      intro x y
      have h1 : dist (f x) (f y) ≤ L * dist x y := hlip.dist_le_mul x y
      rw [← h0, zero_mul] at h1
      exact dist_le_zero.1 h1
    have hzero : ∀ n, edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point) = 0 := by
      intro n
      refine le_antisymm ?_ (edgeLipschitz_nonneg _ _)
      rw [edgeLipschitz_le_iff _ _ le_rfl]
      intro e
      unfold edgeQuotient
      simp [Function.comp, hconst ((S.mesh n).point ((S.mesh n).graph.tgt e))
        ((S.mesh n).point ((S.mesh n).graph.src e))]
    rw [← h0]
    simp only [hzero]
    exact tendsto_const_nhds
  · exact S.tendsto_edgeLipschitz_of_approx (hasApproxChains_of_isRiemannianManifold I) hlip
      (exists_sub_mul_dist_le_abs_sub_of_iSup hf hpos)

/-- The smooth seminorm clause with the Riemannian gradient: `L_h^met(f|_{V_h}) → ‖∇_g f‖_∞`
where `∇_g f(p)` is the Riesz representative of `df_p` (finite-dimensional model). -/
theorem ApproxMeshSequence.tendsto_edgeLipschitz_gradient [FiniteDimensional ℝ F]
    {Vh Eh : ℕ → Type*} (S : ApproxMeshSequence M Vh Eh) [∀ n, Fintype (Eh n)] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (⨆ p, ‖gradient I f p‖)) := by
  simp_rw [norm_gradient]
  exact S.tendsto_edgeLipschitz_riemannian hf

section Packaged

open scoped Matrix.Norms.L2Operator

/-- **`thm:supp-global-metric` on a closed Riemannian manifold.**  Let `M` be a compact
boundaryless `C¹` manifold with a continuous Riemannian metric and its (finite) Riemannian
distance `d_g`.  For every refining sequence of approximate meshes (`h`-nets `V_h`, `h/ρ_h → 0`,
`ρ_h → 0`, all pairs within `ρ_h` joined, positive lengths with `sup_{E_h} |ℓ_h/d_g - 1| → 0`):
1. `L_h^met(g) = ‖[D_h^met, π_h(g)]‖ = max_e |g(x_e) - g(y_e)|/ℓ_e` (`eq:supp-edge-lip`);
2. eventually the pure-state Connes distance is the graph shortest-path metric;
3. `sup_{x,y ∈ V_h} |d_h^met(x,y) - d_g(x,y)| → 0` (`eq:supp-global-metric-convergence`, as an
   explicit error sequence tending to zero that eventually bounds every vertex pair);
4. for every `C¹` function `f`, `L_h^met(f|_{V_h}) → ‖∇_g f‖_∞ = ⨆ p, ‖df_p‖`. -/
theorem ApproxMeshSequence.global_metric_riemannian {Vh Eh : ℕ → Type*}
    (S : ApproxMeshSequence M Vh Eh) [∀ n, Fintype (Eh n)] [∀ n, DecidableEq (Eh n)] :
    (∀ n (g : Vh n → ℝ),
      ‖metricDirac (S.mesh n).graph * endpointRepresentation (S.mesh n).graph g -
        endpointRepresentation (S.mesh n).graph g * metricDirac (S.mesh n).graph‖ =
        edgeLipschitz (S.mesh n).graph g) ∧
    (∀ᶠ n in atTop, ∀ x y : Vh n,
      edgeConnesDistance (S.mesh n).graph x y = graphDistance (S.mesh n).graph x y) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : Vh n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n) ∧
    (∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
        (𝓝 (⨆ p, ‖differential I f p‖))) := by
  obtain ⟨h1, h2, h3, -⟩ := S.global_metric_of_approx (hasApproxChains_of_isRiemannianManifold I)
  exact ⟨h1, h2, h3, fun f hf => S.tendsto_edgeLipschitz_riemannian hf⟩

end Packaged

end Compact

/-! ### Instantiation of the full packet -/

section Instances

attribute [local instance] isContinuousRiemannianBundle_vectorSpace

/-- The full hypothesis packet of `ApproxMeshSequence.global_metric_riemannian` elaborates and is
satisfied by the compact Riemannian manifold `EuclideanSpace ℝ (Fin 0)` (a point) with a mesh
sequence from `exists_approxMeshSequence`.  (Mathlib has no compact Riemannian manifold of
positive dimension yet; the non-trivial content of each ingredient is instantiated on the
Euclidean line, see `hasApproxChains_real` and the examples of `RiemannianDistanceLipschitz`.) -/
example : ∃ (Vh Eh : ℕ → Type) (_ : ∀ n, Fintype (Eh n)) (_ : ∀ n, DecidableEq (Eh n))
    (S : ApproxMeshSequence (EuclideanSpace ℝ (Fin 0)) Vh Eh),
    ∀ f : EuclideanSpace ℝ (Fin 0) → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ, ℝ) 1 f →
      Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
        (𝓝 (⨆ p, ‖differential 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) f p‖)) := by
  classical
  obtain ⟨Vh, Eh, _, hE, ⟨S⟩⟩ := exists_approxMeshSequence (X := EuclideanSpace ℝ (Fin 0))
  exact ⟨Vh, Eh, hE, fun _ => Classical.decEq _, S,
    fun f hf => S.tendsto_edgeLipschitz_riemannian hf⟩

end Instances

end RenewalGeometry.MeshGraphDistanceConvergence
