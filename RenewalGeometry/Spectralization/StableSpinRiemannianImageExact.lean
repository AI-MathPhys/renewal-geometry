/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.MeshGraphRiemannian
import RenewalGeometry.Spectralization.StableSpinAtlasRealGradingExact

/-!
# Stable compact-spin approximation on closed Riemannian manifolds

Paper `predictive_spectral_geometry`, label `cor:supp-compact-spin-image`:

> A closed marked Riemannian spin manifold admitting a compatible stable spin discretization has
> a finite-dimensional approximation of its doubled spin Dirac operator in generalized norm
> resolvent, together with convergent independent metric heads.  Consequently, essential
> surjectivity of this particular atlas-based spin construction follows if such compatible
> stable discretizations are supplied for all target manifolds.

The proof applies `thm:supp-compact-spin-resolvent` to the spin operators and
`thm:supp-global-metric` to the independent metric heads.  Here:

* the manifold is a genuine closed Riemannian manifold in Mathlib's sense (compact, modelled on
  a boundaryless model, continuous Riemannian metric, `IsRiemannianManifold`: the distance is the
  Riemannian distance), and the metric heads are the endpoint metric triples on **every**
  refining mesh sequence satisfying the paper's mesh assumptions (`ApproxMeshSequence`), via
  `ApproxMeshSequence.global_metric_riemannian`;
* the compatible stable spin discretization is exactly the encoded `def:stable-spin-atlas`:
  `CompatibleStableAtlas` ((A1)–(A3)) and, for the marks, `AtlasRealGrading` (asserted real and
  grading structures intertwining the reconstructions).  As in that definition, the doubled spin
  Dirac operator `D̂` on `L²(M; S ⊗ ℂ²)` enters through its abstract surrogate (a self-adjoint
  operator with a core and a compact first-order embedding); Mathlib has no spinor bundles.

Retention of the marks (new infrastructure, derived from `AtlasRealGrading`, not assumed):

* `inner_antiunitary_map_map`: an antiunitary `J` satisfies `⟪J x, J y⟫ = ⟪y, x⟫`;
* `embedAdjoint_grading`, `embedAdjoint_realJ`: `W_h^* γ = γ_h W_h^*`, `W_h^* J = J_h W_h^*`;
* `stageGrading_stageResolvent`, `stageReal_stageResolvent`:
  `γ_h (D_h - z)⁻¹ = -(D_h + z)⁻¹ γ_h` and `J_h (D_h - z)⁻¹ = ε' (D_h - ε' z̄)⁻¹ J_h`;
* `grading_embeddedResolvent`, `realJ_embeddedResolvent`: the same identities for the compressed
  resolvents `W_h (D_h - z)⁻¹ W_h^*` on `ℋ`, exactly at every stage;
* `grading_limit_resolvent`, `realJ_limit_resolvent`: the identities pass to the norm limit
  `(D̂ - z)⁻¹`.

Main results:

* `compactSpinImage_riemannian`: for every compatible stable atlas and every refining mesh
  sequence on a closed Riemannian manifold — norm-resolvent convergence for every non-real `z`
  with compact limit resolvent, the exact commutator formula, eventual equality of the
  pure-state Connes distance with the graph metric, uniform convergence of the Connes distances
  of the metric heads to `d_g`, and `L_h^met(f|_{V_h}) → ‖∇_g f‖_∞` for `C¹` functions;
* `compactSpinImage_riemannian_marked`: the same together with the retained marks;
* `IsMarkedStableSpinImage` (the image of the construction: targets that are generalized
  norm-resolvent limits of finite marked stage triples, with convergent finite metric heads on
  `h`-nets, `h → 0`) and `isMarkedStableSpinImage_of_atlas`: every closed Riemannian manifold with
  a marked compatible stable spin discretization is in the image (the metric heads exist
  unconditionally, `exists_approxMeshSequence`);
* `isMarkedStableSpinImage_forall`: the essential-surjectivity clause for any family of targets
  supplied with such discretizations.

Non-vacuity: the full hypothesis packet is instantiated (examples at the end) with the one-point
closed Riemannian manifold `EuclideanSpace ℝ (Fin 0)` (Mathlib has no compact Riemannian
manifold of positive dimension) and the doubled one-point spin model `ℋ = ℂ²`, `D̂ = σ₁`,
`γ = σ₃`, `J` = complex conjugation (`exampleAtlas`, `exampleRealGrading`).
-/

open Filter Topology Manifold Bundle ComplexConjugate
open scoped InnerProductSpace ContDiff Matrix.Norms.L2Operator
open RenewalGeometry.EndpointBlockMetricHead RenewalGeometry.MeshGraphDistanceConvergence
  RenewalGeometry.RiemannianDistanceLipschitz RenewalGeometry.StableSpinAtlasRealGrading

noncomputable section

namespace RenewalGeometry

namespace StableSpinRiemannianImage

universe u v w x

/-! ### Antiunitary maps -/

section antiunitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An antiunitary map `J` (a conjugate-linear isometric equivalence) satisfies
`⟪J x, J y⟫ = ⟪y, x⟫ = conj ⟪x, y⟫`. -/
theorem inner_antiunitary_map_map (J : E ≃ₗᵢ⋆[ℂ] E) (a b : E) :
    ⟪J a, J b⟫_ℂ = ⟪b, a⟫_ℂ := by
  have h1 : ‖J a + J b‖ = ‖b + a‖ := by rw [← map_add, J.norm_map, add_comm]
  have h2 : ‖J a - J b‖ = ‖b - a‖ := by rw [← map_sub, J.norm_map, norm_sub_rev]
  have h3 : ‖J a - Complex.I • J b‖ = ‖b - Complex.I • a‖ := by
    have : J a - Complex.I • J b = J (a + Complex.I • b) := by
      rw [map_add, J.map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]
    rw [this, J.norm_map]
    calc ‖a + Complex.I • b‖ = ‖Complex.I • (b - Complex.I • a)‖ := by
          rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
      _ = ‖b - Complex.I • a‖ := by rw [norm_smul]; simp
  have h4 : ‖J a + Complex.I • J b‖ = ‖b + Complex.I • a‖ := by
    have : J a + Complex.I • J b = J (a - Complex.I • b) := by
      rw [map_sub, J.map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]
    rw [this, J.norm_map]
    calc ‖a - Complex.I • b‖ = ‖(-Complex.I) • (b + Complex.I • a)‖ := by
          rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
            sub_eq_add_neg, add_comm]
      _ = ‖b + Complex.I • a‖ := by rw [norm_smul]; simp
  rw [inner_eq_sum_norm_sq_div_four (J a) (J b), inner_eq_sum_norm_sq_div_four b a]
  simp only [show (RCLike.I : ℂ) = Complex.I from rfl]
  rw [h1, h2, h3, h4]

end antiunitary

/-! ### Retention of the real and grading structures -/

section retention

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
variable {A : CompatibleStableAtlas H V Hn} (R : AtlasRealGrading A)

/-- `W_h^*` as a continuous linear map. -/
abbrev embedAdjoint (A : CompatibleStableAtlas H V Hn) (n : ℕ) : H →L[ℂ] Hn n :=
  ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap

/-- **`W_h^* γ = γ_h W_h^*`**: the grading preserves the range of `W_h` and, being
self-adjoint, commutes with the compression. -/
theorem embedAdjoint_grading (n : ℕ) (f : H) :
    embedAdjoint A n (R.grading f) = R.stageGrading n (embedAdjoint A n f) := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]
  have hγ : ⟪A.embed n u, R.grading f⟫_ℂ = ⟪R.grading (A.embed n u), f⟫_ℂ :=
    (R.isSelfAdjoint_grading.isSymmetric _ _).symm
  have hγh : ⟪R.stageGrading n u, embedAdjoint A n f⟫_ℂ =
      ⟪u, R.stageGrading n (embedAdjoint A n f)⟫_ℂ :=
    (R.isSelfAdjoint_stageGrading n).isSymmetric _ _
  rw [hγ, ← R.embed_stageGrading, ← hγh, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap]

/-- **`W_h^* J = J_h W_h^*`** for the antiunitary real structures. -/
theorem embedAdjoint_realJ (n : ℕ) (f : H) :
    embedAdjoint A n (R.realJ f) = R.stageReal n (embedAdjoint A n f) := by
  apply ext_inner_left ℂ
  intro u
  set v := (R.stageReal n).symm u with hv
  have hu : u = R.stageReal n v := by rw [hv, LinearIsometryEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap, hu,
    R.embed_stageReal, inner_antiunitary_map_map, inner_antiunitary_map_map,
    ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap]

/-- `-z` is non-real when `z` is. -/
theorem neg_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : (-z).im ≠ 0 := by
  rw [Complex.neg_im]; exact neg_ne_zero.mpr hz

/-- `ε z̄` is non-real when `z` is and `ε = ±1`. -/
theorem sign_mul_conj_im_ne_zero {ε : ℝ} (hε : IsSign ε) {z : ℂ} (hz : z.im ≠ 0) :
    ((ε : ℂ) * conj z).im ≠ 0 := by
  rcases hε with h | h <;> subst h <;> simp [hz]

/-- `(ε : ℂ)² = 1` for a sign. -/
theorem sign_mul_self {ε : ℝ} (hε : IsSign ε) : (ε : ℂ) * ε = 1 := by
  rcases hε with h | h <;> subst h <;> norm_num

/-- **Grading at stage level**: `γ_h (D_h - z)⁻¹ = -(D_h + z)⁻¹ γ_h`. -/
theorem stageGrading_stageResolvent (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0)
    (f : Hn n) :
    R.stageGrading n (A.stageResolvent n z hz f) =
      -A.stageResolvent n (-z) hz' (R.stageGrading n f) := by
  set u := A.stageResolvent n z hz f
  have hu : A.stage n u - z • u = f := A.stage_stageResolvent n hz f
  have key : A.stage n (R.stageGrading n u) - (-z) • R.stageGrading n u =
      -R.stageGrading n f := by
    rw [R.stage_stageGrading, ← hu, map_sub, map_smul]
    simp only [neg_smul]
    abel
  rw [← A.stageResolvent_apply_sub n hz' (R.stageGrading n u), key, map_neg]

/-- **Real structure at stage level**: `J_h (D_h - z)⁻¹ = ε' (D_h - ε' z̄)⁻¹ J_h`. -/
theorem stageReal_stageResolvent (n : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (hz' : ((R.diracSign : ℂ) * conj z).im ≠ 0) (f : Hn n) :
    R.stageReal n (A.stageResolvent n z hz f) =
      (R.diracSign : ℂ) • A.stageResolvent n ((R.diracSign : ℂ) * conj z) hz'
        (R.stageReal n f) := by
  have hεε : (R.diracSign : ℂ) * R.diracSign = 1 := sign_mul_self R.diracSign_isSign
  set u := A.stageResolvent n z hz f
  have hu : A.stage n u - z • u = f := A.stage_stageResolvent n hz f
  have hJ : R.stageReal n (A.stage n u) =
      (R.diracSign : ℂ) • A.stage n (R.stageReal n u) := by
    rw [R.stage_stageReal, smul_smul, hεε, one_smul]
  have key : A.stage n (R.stageReal n u) - ((R.diracSign : ℂ) * conj z) • R.stageReal n u =
      (R.diracSign : ℂ) • R.stageReal n f := by
    rw [← hu, map_sub, LinearIsometryEquiv.map_smulₛₗ, hJ, smul_sub, smul_smul, smul_smul, hεε,
      one_smul]
  rw [← A.stageResolvent_apply_sub n hz' (R.stageReal n u), key, map_smul]

/-- **Grading retained by the compressed resolvents**:
`γ W_h (D_h - z)⁻¹ W_h^* = -W_h (D_h + z)⁻¹ W_h^* γ`, exactly at every stage. -/
theorem grading_embeddedResolvent (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0) (f : H) :
    R.grading (A.embeddedResolvent z hz n f) = -A.embeddedResolvent (-z) hz' n (R.grading f) := by
  rw [A.embeddedResolvent_apply, A.embeddedResolvent_apply, ← R.embed_stageGrading,
    stageGrading_stageResolvent R n hz hz', ← embedAdjoint_grading R, map_neg]

/-- **Real structure retained by the compressed resolvents**:
`J W_h (D_h - z)⁻¹ W_h^* = ε' W_h (D_h - ε' z̄)⁻¹ W_h^* J`, exactly at every stage. -/
theorem realJ_embeddedResolvent (n : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (hz' : ((R.diracSign : ℂ) * conj z).im ≠ 0) (f : H) :
    R.realJ (A.embeddedResolvent z hz n f) =
      (R.diracSign : ℂ) • A.embeddedResolvent ((R.diracSign : ℂ) * conj z) hz' n (R.realJ f) := by
  rw [A.embeddedResolvent_apply, A.embeddedResolvent_apply, ← R.embed_stageReal,
    stageReal_stageResolvent R n hz hz', ← embedAdjoint_realJ R, map_smul]

/-- **Grading in the limit**: `γ (D̂ - z)⁻¹ = -(D̂ + z)⁻¹ γ`, obtained by passing the exact
stage identity to the norm limit. -/
theorem grading_limit_resolvent {z : ℂ} (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0) (f : H) :
    R.grading (A.limit.resolvent z hz f) = -A.limit.resolvent (-z) hz' (R.grading f) := by
  have h1 : Tendsto (fun n => R.grading (A.embeddedResolvent z hz n f)) atTop
      (𝓝 (R.grading (A.limit.resolvent z hz f))) :=
    (R.grading.continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℂ H f).continuous.tendsto _).comp
        (A.tendsto_embeddedResolvent hz))
  have h2 : Tendsto (fun n => -A.embeddedResolvent (-z) hz' n (R.grading f)) atTop
      (𝓝 (-A.limit.resolvent (-z) hz' (R.grading f))) :=
    ((((ContinuousLinearMap.apply ℂ H (R.grading f)).continuous.tendsto _).comp
        (A.tendsto_embeddedResolvent hz'))).neg
  exact tendsto_nhds_unique (h1.congr fun n => grading_embeddedResolvent R n hz hz' f) h2

/-- **Real structure in the limit**: `J (D̂ - z)⁻¹ = ε' (D̂ - ε' z̄)⁻¹ J`. -/
theorem realJ_limit_resolvent {z : ℂ} (hz : z.im ≠ 0)
    (hz' : ((R.diracSign : ℂ) * conj z).im ≠ 0) (f : H) :
    R.realJ (A.limit.resolvent z hz f) =
      (R.diracSign : ℂ) • A.limit.resolvent ((R.diracSign : ℂ) * conj z) hz' (R.realJ f) := by
  have h1 : Tendsto (fun n => R.realJ (A.embeddedResolvent z hz n f)) atTop
      (𝓝 (R.realJ (A.limit.resolvent z hz f))) :=
    (R.realJ.continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℂ H f).continuous.tendsto _).comp
        (A.tendsto_embeddedResolvent hz))
  have h2 : Tendsto (fun n => (R.diracSign : ℂ) •
      A.embeddedResolvent ((R.diracSign : ℂ) * conj z) hz' n (R.realJ f)) atTop
      (𝓝 ((R.diracSign : ℂ) •
        A.limit.resolvent ((R.diracSign : ℂ) * conj z) hz' (R.realJ f))) :=
    ((((ContinuousLinearMap.apply ℂ H (R.realJ f)).continuous.tendsto _).comp
        (A.tendsto_embeddedResolvent hz'))).const_smul _
  exact tendsto_nhds_unique (h1.congr fun n => realJ_embeddedResolvent R n hz hz' f) h2

end retention

/-! ### The corollary on closed Riemannian manifolds -/

section Riemannian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ F HM}
  {M : Type x} [MetricSpace M] [ChartedSpace HM M] [IsManifold I 1 M]
  [RiemannianBundle (fun p : M ↦ TangentSpace I p)] [IsRiemannianManifold I M]
  [I.Boundaryless] [IsContinuousRiemannianBundle F (fun p : M ↦ TangentSpace I p)]
  [CompactSpace M]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

/-- **`cor:supp-compact-spin-image`** on a closed Riemannian manifold `M` (compact, boundaryless
model, continuous Riemannian metric, distance `d_g` = Riemannian distance).  For every compatible
stable spin discretization `A` (`def:stable-spin-atlas`, (A1)–(A3)) of the doubled spin Dirac
operator `D̂` and every refining mesh sequence `S` on `M` satisfying the mesh assumptions of
`thm:supp-global-metric`:
1. generalized norm-resolvent approximation: `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every
   non-real `z` (`thm:supp-compact-spin-resolvent`, `eq:supp-global-norm-resolvent`);
2. the limit resolvents are compact;
3. the metric heads are endpoint triples: `‖[D_h^met, π_h(g)]‖ = max_e |g(x_e) - g(y_e)|/ℓ_e`;
4. eventually their pure-state Connes distance is the graph shortest-path metric;
5. the metric heads converge: an error sequence tending to zero eventually bounds
   `|d_{Connes,h}(x,y) - d_g(x,y)|` uniformly over all vertex pairs;
6. for every `C¹` function `f`, `L_h^met(f|_{V_h}) → ‖∇_g f‖_∞ = ⨆ p, ‖df_p‖`. -/
theorem compactSpinImage_riemannian (A : CompatibleStableAtlas H V Hn) {Vh Eh : ℕ → Type*}
    (S : ApproxMeshSequence M Vh Eh) [∀ n, Fintype (Eh n)] [∀ n, DecidableEq (Eh n)] :
    (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) ∧
    (∀ (z : ℂ) (hz : z.im ≠ 0), IsCompactOperator (A.limit.resolvent z hz)) ∧
    (∀ n (g : Vh n → ℝ),
      ‖metricDirac (S.mesh n).graph * endpointRepresentation (S.mesh n).graph g -
        endpointRepresentation (S.mesh n).graph g * metricDirac (S.mesh n).graph‖ =
        edgeLipschitz (S.mesh n).graph g) ∧
    (∀ᶠ n in atTop, ∀ a b : Vh n,
      edgeConnesDistance (S.mesh n).graph a b = graphDistance (S.mesh n).graph a b) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ a b : Vh n, |edgeConnesDistance (S.mesh n).graph a b -
        dist ((S.mesh n).point a) ((S.mesh n).point b)| ≤ err n) ∧
    (∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
        (𝓝 (⨆ p, ‖differential I f p‖))) := by
  obtain ⟨h1, h2, ⟨err, herr, h3⟩, h4⟩ := S.global_metric_riemannian (I := I)
  refine ⟨fun _ hz => A.tendsto_norm_embeddedResolvent_sub hz,
    fun _ hz => A.isCompactOperator_limit_resolvent hz, h1, h2, ⟨err, herr, ?_⟩, h4⟩
  filter_upwards [h2, h3] with n hn2 hn3 a b
  rw [hn2 a b]
  exact hn3 a b

/-- **`cor:supp-compact-spin-image` with its marks.**  If the compatible stable spin
discretization carries the asserted real and grading structures (`AtlasRealGrading`,
`def:stable-spin-atlas`), then, in addition to the six clauses of
`compactSpinImage_riemannian`, the finite approximation is marked and retains them:
1. the stage actions satisfy the declared KO relations `J_h² = ε`, `γ_h² = 1`,
   `J_h γ_h = ε'' γ_h J_h`, `γ_h` self-adjoint (derived from the intertwining);
2. `W_h J_h W_h^* → J` and `W_h γ_h W_h^* → γ` strongly;
3. exactly at every stage, `γ W_h (D_h - z)⁻¹ W_h^* = -W_h (D_h + z)⁻¹ W_h^* γ` and
   `J W_h (D_h - z)⁻¹ W_h^* = ε' W_h (D_h - ε' z̄)⁻¹ W_h^* J`;
4. the same identities hold for `(D̂ - z)⁻¹` in the limit. -/
theorem compactSpinImage_riemannian_marked (A : CompatibleStableAtlas H V Hn)
    (R : AtlasRealGrading A) {Vh Eh : ℕ → Type*} (S : ApproxMeshSequence M Vh Eh)
    [∀ n, Fintype (Eh n)] [∀ n, DecidableEq (Eh n)] :
    ((∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) ∧
    (∀ (z : ℂ) (hz : z.im ≠ 0), IsCompactOperator (A.limit.resolvent z hz)) ∧
    (∀ n (g : Vh n → ℝ),
      ‖metricDirac (S.mesh n).graph * endpointRepresentation (S.mesh n).graph g -
        endpointRepresentation (S.mesh n).graph g * metricDirac (S.mesh n).graph‖ =
        edgeLipschitz (S.mesh n).graph g) ∧
    (∀ᶠ n in atTop, ∀ a b : Vh n,
      edgeConnesDistance (S.mesh n).graph a b = graphDistance (S.mesh n).graph a b) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ a b : Vh n, |edgeConnesDistance (S.mesh n).graph a b -
        dist ((S.mesh n).point a) ((S.mesh n).point b)| ≤ err n) ∧
    (∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
        (𝓝 (⨆ p, ‖differential I f p‖)))) ∧
    (∀ n (u : Hn n), R.stageReal n (R.stageReal n u) = (R.realSign : ℂ) • u ∧
      R.stageGrading n (R.stageGrading n u) = u ∧
      R.stageReal n (R.stageGrading n u) =
        (R.gradingSign : ℂ) • R.stageGrading n (R.stageReal n u)) ∧
    (∀ n, IsSelfAdjoint (R.stageGrading n)) ∧
    (∀ f : H, Tendsto (fun n => A.embed n (R.stageReal n (embedAdjoint A n f))) atTop
        (𝓝 (R.realJ f)) ∧
      Tendsto (fun n => A.embed n (R.stageGrading n (embedAdjoint A n f))) atTop
        (𝓝 (R.grading f))) ∧
    (∀ n (z : ℂ) (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0) (f : H),
      R.grading (A.embeddedResolvent z hz n f) =
        -A.embeddedResolvent (-z) hz' n (R.grading f)) ∧
    (∀ n (z : ℂ) (hz : z.im ≠ 0) (hz' : ((R.diracSign : ℂ) * conj z).im ≠ 0) (f : H),
      R.realJ (A.embeddedResolvent z hz n f) =
        (R.diracSign : ℂ) •
          A.embeddedResolvent ((R.diracSign : ℂ) * conj z) hz' n (R.realJ f)) ∧
    (∀ (z : ℂ) (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0) (f : H),
      R.grading (A.limit.resolvent z hz f) = -A.limit.resolvent (-z) hz' (R.grading f)) ∧
    (∀ (z : ℂ) (hz : z.im ≠ 0) (hz' : ((R.diracSign : ℂ) * conj z).im ≠ 0) (f : H),
      R.realJ (A.limit.resolvent z hz f) =
        (R.diracSign : ℂ) • A.limit.resolvent ((R.diracSign : ℂ) * conj z) hz' (R.realJ f)) :=
  ⟨compactSpinImage_riemannian A S,
    fun n u => ⟨R.stageReal_sq n u, R.stageGrading_sq n u, R.stageReal_stageGrading n u⟩,
    R.isSelfAdjoint_stageGrading,
    fun f => ⟨R.tendsto_embed_stageReal_adjoint f, R.tendsto_embed_stageGrading_adjoint f⟩,
    fun n _ hz hz' f => grading_embeddedResolvent R n hz hz' f,
    fun n _ hz hz' f => realJ_embeddedResolvent R n hz hz' f,
    fun _ hz hz' f => grading_limit_resolvent R hz hz' f,
    fun _ hz hz' f => realJ_limit_resolvent R hz hz' f⟩

end Riemannian

/-! ### The image of the construction and essential surjectivity -/

/-- **The image of the marked atlas-based spin construction.**  A target — a metric space `M`
(the closed Riemannian manifold with `d_g`) together with a self-adjoint operator `T` on `ℋ` (the
doubled spin Dirac operator), an antiunitary real structure `J`, a grading `γ` and the Dirac
sign `ε'` — lies in the image when
* there are finite-dimensional marked stage triples: Hilbert spaces `ℋ_h`, self-adjoint `D_h`,
  isometries `W_h : ℋ_h → ℋ`, antiunitaries `J_h` and self-adjoint gradings `γ_h` with
  `D_h J_h = ε' J_h D_h`, `D_h γ_h = -γ_h D_h`, `W_h J_h = J W_h`, `W_h γ_h = γ W_h`, such that
  `‖W_h (D_h - z)⁻¹ W_h^* - (T - z)⁻¹‖ → 0` for every non-real `z` (generalized norm resolvent);
* there are finite metric heads (endpoint triples with finitely many edges of positive length)
  on `h`-nets of `M` with `h → 0`, whose pure-state Connes distances converge uniformly to `d_g`
  on the vertices. -/
def IsMarkedStableSpinImage.{uM, uH, uS} (M : Type uM) [MetricSpace M] {H : Type uH}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : SelfAdjointResolventData H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (γ : H →L[ℂ] H) (ε' : ℝ) : Prop :=
  (∃ (Hn : ℕ → Type uS) (_ : ∀ n, NormedAddCommGroup (Hn n)) (_ : ∀ n, InnerProductSpace ℂ (Hn n))
      (_ : ∀ n, CompleteSpace (Hn n)) (_ : ∀ n, FiniteDimensional ℂ (Hn n))
      (D : ∀ n, Hn n →L[ℂ] Hn n) (hD : ∀ n, IsSelfAdjoint (D n)) (W : ∀ n, Hn n →ₗᵢ[ℂ] H)
      (Jh : ∀ n, Hn n ≃ₗᵢ⋆[ℂ] Hn n) (γh : ∀ n, Hn n →L[ℂ] Hn n),
    (∀ (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖(W n).toContinuousLinearMap ∘L
        (SelfAdjointResolventData.ofBounded (D n) (hD n)).resolvent z hz ∘L
        ContinuousLinearMap.adjoint (W n).toContinuousLinearMap - T.resolvent z hz‖) atTop
        (𝓝 0)) ∧
    (∀ n u, D n (Jh n u) = (ε' : ℂ) • Jh n (D n u)) ∧
    (∀ n u, D n (γh n u) = -γh n (D n u)) ∧
    (∀ n, IsSelfAdjoint (γh n)) ∧
    (∀ n u, W n (Jh n u) = J (W n u)) ∧
    (∀ n u, W n (γh n u) = γ (W n u))) ∧
  (∃ (Vh Eh : ℕ → Type uM) (_ : ∀ n, Fintype (Eh n)) (Γ : ∀ n, EdgeGraph (Vh n) (Eh n))
      (p : ∀ n, Vh n → M) (h : ℕ → ℝ),
    Tendsto h atTop (𝓝 0) ∧ (∀ n (y : M), ∃ a, dist y (p n a) ≤ h n) ∧
    (∀ n e, 0 < (Γ n).len e) ∧
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ a b : Vh n, |edgeConnesDistance (Γ n) a b - dist (p n a) (p n b)| ≤ err n)

/-- A target `(T, J, γ, ε')` **admits a marked compatible stable spin discretization**
(`def:stable-spin-atlas` with asserted real and grading structures): there are a first-order
space `V` with compact embedding, finite stage spaces and a `CompatibleStableAtlas` whose limit
operator is `T`, with an `AtlasRealGrading` whose declared continuum actions are `J`, `γ` with
Dirac sign `ε'`. -/
def AdmitsMarkedStableSpinDiscretization.{uH, uV, uS} {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : SelfAdjointResolventData H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (γ : H →L[ℂ] H) (ε' : ℝ) : Prop :=
  ∃ (V : Type uV) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V)
    (Hn : ℕ → Type uS) (_ : ∀ n, NormedAddCommGroup (Hn n)) (_ : ∀ n, InnerProductSpace ℂ (Hn n))
    (_ : ∀ n, CompleteSpace (Hn n)) (_ : ∀ n, FiniteDimensional ℂ (Hn n))
    (A : CompatibleStableAtlas H V Hn) (R : AtlasRealGrading A),
    A.limit = T ∧ R.realJ = J ∧ R.grading = γ ∧ R.diracSign = ε'

section Image

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ F HM)
  {M : Type x} [MetricSpace M] [ChartedSpace HM M] [IsManifold I 1 M]
  [RiemannianBundle (fun p : M ↦ TangentSpace I p)] [IsRiemannianManifold I M]
  [I.Boundaryless] [IsContinuousRiemannianBundle F (fun p : M ↦ TangentSpace I p)]
  [CompactSpace M]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

include I in
/-- **`cor:supp-compact-spin-image`, first sentence, image form.**  A closed Riemannian manifold
whose doubled spin Dirac operator admits a marked compatible stable spin discretization lies in
the image of the construction: its operator is a generalized norm-resolvent limit of finite
marked stage triples, and finite metric heads on `h`-nets (`h → 0`) converge to `d_g` (these
exist on every closed Riemannian manifold, `exists_approxMeshSequence`). -/
theorem isMarkedStableSpinImage_of_admits {T : SelfAdjointResolventData H}
    {J : H ≃ₗᵢ⋆[ℂ] H} {γ : H →L[ℂ] H} {ε' : ℝ}
    (hT : AdmitsMarkedStableSpinDiscretization.{u, v, w} T J γ ε') :
    IsMarkedStableSpinImage.{x, u, w} M T J γ ε' := by
  classical
  obtain ⟨V, _, _, Hn, _, _, _, _, A, R, rfl, rfl, rfl, rfl⟩ := hT
  refine ⟨⟨Hn, inferInstance, inferInstance, inferInstance, inferInstance, A.stage,
    A.stage_selfAdjoint, A.embed, R.stageReal, R.stageGrading,
    fun _ hz => A.tendsto_norm_embeddedResolvent_sub hz, R.stage_stageReal,
    R.stage_stageGrading, R.isSelfAdjoint_stageGrading, R.embed_stageReal,
    R.embed_stageGrading⟩, ?_⟩
  obtain ⟨Vh, Eh, _, hE, ⟨S⟩⟩ := exists_approxMeshSequence (X := M)
  obtain ⟨-, -, -, -, herr, -⟩ := compactSpinImage_riemannian (I := I) A S
  exact ⟨Vh, Eh, hE, fun n => (S.mesh n).graph, fun n => (S.mesh n).point,
    fun n => (S.mesh n).h, S.h_tendsto, fun n => (S.mesh n).net, fun n => (S.mesh n).len_pos,
    herr⟩

end Image

section ImageConnected

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ F HM)
  {M : Type x} [EMetricSpace M] [ConnectedSpace M] [ChartedSpace HM M] [IsManifold I 1 M]
  [RiemannianBundle (fun p : M ↦ TangentSpace I p)] [IsRiemannianManifold I M]
  [I.Boundaryless] [IsContinuousRiemannianBundle F (fun p : M ↦ TangentSpace I p)]
  [CompactSpace M]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

include I in
/-- `isMarkedStableSpinImage_of_admits` for a closed **connected** Riemannian manifold in
Mathlib's standard setting (`EMetricSpace M`, `ConnectedSpace M`): the Riemannian distance is
finite (`edist_ne_top_of_connectedSpace`) and `d_g` is the distance of
`EMetricSpace.toMetricSpace`, which has the same `edist`. -/
theorem isMarkedStableSpinImage_of_admits_of_connectedSpace {T : SelfAdjointResolventData H}
    {J : H ≃ₗᵢ⋆[ℂ] H} {γ : H →L[ℂ] H} {ε' : ℝ}
    (hT : AdmitsMarkedStableSpinDiscretization.{u, v, w} T J γ ε') :
    letI := EMetricSpace.toMetricSpace (edist_ne_top_of_connectedSpace (X := M))
    IsMarkedStableSpinImage.{x, u, w} M T J γ ε' := by
  letI := EMetricSpace.toMetricSpace (edist_ne_top_of_connectedSpace (X := M))
  exact isMarkedStableSpinImage_of_admits I hT

end ImageConnected

/-- **`cor:supp-compact-spin-image`, essential-surjectivity clause.**  For any family of target
closed Riemannian manifolds `M i` with doubled spin Dirac operators `T i`, real structures `J i`,
gradings `γ i` and Dirac signs `ε' i`: if a marked compatible stable spin discretization is
supplied for every target, then every target lies in the image of the construction. -/
theorem isMarkedStableSpinImage_forall {ι : Type*}
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {HM : ι → Type*} [∀ i, TopologicalSpace (HM i)] (I : ∀ i, ModelWithCorners ℝ (F i) (HM i))
    {M : ι → Type x} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace (HM i) (M i)]
    [∀ i, IsManifold (I i) 1 (M i)] [∀ i, RiemannianBundle (fun p : M i ↦ TangentSpace (I i) p)]
    [∀ i, IsRiemannianManifold (I i) (M i)] [∀ i, (I i).Boundaryless]
    [∀ i, IsContinuousRiemannianBundle (F i) (fun p : M i ↦ TangentSpace (I i) p)]
    [∀ i, CompactSpace (M i)]
    {H : ι → Type u} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, SelfAdjointResolventData (H i)) (J : ∀ i, H i ≃ₗᵢ⋆[ℂ] H i)
    (γ : ∀ i, H i →L[ℂ] H i) (ε' : ι → ℝ)
    (hT : ∀ i, AdmitsMarkedStableSpinDiscretization.{u, v, w} (T i) (J i) (γ i) (ε' i)) :
    ∀ i, IsMarkedStableSpinImage.{x, u, w} (M i) (T i) (J i) (γ i) (ε' i) :=
  fun i => isMarkedStableSpinImage_of_admits (I i) (hT i)

/-! ### Non-vacuity -/

section Instances

attribute [local instance] isContinuousRiemannianBundle_vectorSpace

/-- The doubled one-point spin model (`ℋ = ℂ²`, `D̂ = σ₁`, `J` = complex conjugation, `γ = σ₃`,
which anticommutes with `D̂`) admits a marked compatible stable spin discretization. -/
theorem admitsMarkedStableSpinDiscretization_example :
    AdmitsMarkedStableSpinDiscretization.{0, 0, 0} exampleAtlas.limit conjC2 opZ 1 :=
  ⟨C2, inferInstance, inferInstance, fun _ => C2, inferInstance, inferInstance, inferInstance,
    inferInstance, exampleAtlas, exampleRealGrading, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity of the image form: the full hypothesis packet (closed Riemannian manifold
`EuclideanSpace ℝ (Fin 0)`, marked compatible stable spin discretization) is satisfiable. -/
example : IsMarkedStableSpinImage.{0, 0, 0} (EuclideanSpace ℝ (Fin 0)) exampleAtlas.limit conjC2
    opZ 1 :=
  isMarkedStableSpinImage_of_admits 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
    admitsMarkedStableSpinDiscretization_example

/-- Non-vacuity of `compactSpinImage_riemannian_marked`: with a mesh sequence from
`exists_approxMeshSequence` and the one-point marked spin model, the theorem applies; e.g. its
grading-retention clause `σ₃ (σ₁ - z)⁻¹ = -(σ₁ + z)⁻¹ σ₃` in the limit. -/
example : ∃ (Vh Eh : ℕ → Type) (_ : ∀ n, Fintype (Eh n)) (_ : ∀ n, DecidableEq (Eh n))
    (_ : ApproxMeshSequence (EuclideanSpace ℝ (Fin 0)) Vh Eh),
    ∀ (z : ℂ) (hz : z.im ≠ 0) (hz' : (-z).im ≠ 0) (f : C2),
      opZ (exampleAtlas.limit.resolvent z hz f) =
        -exampleAtlas.limit.resolvent (-z) hz' (opZ f) := by
  classical
  obtain ⟨Vh, Eh, _, hE, ⟨S⟩⟩ := exists_approxMeshSequence (X := EuclideanSpace ℝ (Fin 0))
  exact ⟨Vh, Eh, hE, fun _ => Classical.decEq _, S,
    (compactSpinImage_riemannian_marked (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) exampleAtlas
      exampleRealGrading S).2.2.2.2.2.2.1⟩

end Instances

end StableSpinRiemannianImage

end RenewalGeometry
