/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Riemannian distance: near-geodesic paths and the optimal Lipschitz constant

Infrastructure for `thm:supp-global-metric` of the paper `predictive_spectral_geometry`, built on
Mathlib's Riemannian manifolds (`Mathlib.Geometry.Manifold.Riemannian`: `IsRiemannianManifold`,
`riemannianEDist` = infimum of the lengths `pathELength` of `C¹` paths).  The manifold `M` carries a
`MetricSpace` structure whose extended distance is the Riemannian one (on a connected manifold all
Riemannian distances are finite, `edist_ne_top_of_connectedSpace`).

* `exists_nearGeodesic_path`: for every `δ > 0` any two points are joined by a continuous path
  with `d(x,γ s) + d(γ s,γ t) + d(γ t,y) ≤ d(x,y) + δ` (`0 ≤ s ≤ t ≤ 1`); this gives the
  approximate chain property used for the mesh graphs.
* `differential I f p : T_pM →L[ℝ] ℝ` is `df_p` with the Riemannian norm on `T_pM`; for a
  finite-dimensional model, `gradient I f p` is the Riesz representative (`∇_g f(p)`), with
  `‖∇_g f(p)‖ = ‖df_p‖` (`norm_gradient`) and `⟪∇_g f(p), v⟫ = df_p v` (`inner_gradient`).
* `lipschitzWith_of_norm_differential_le`: `‖df‖ ≤ L` everywhere ⇒ `f` is `L`-Lipschitz
  (fundamental theorem of calculus along near-minimising `C¹` paths).
* `exists_sub_mul_dist_le_abs_sub` (boundaryless model, continuous metric): if
  `0 < ε < ‖df_p‖` there is `y ≠ p` with `(‖df_p‖ - ε) d(p,y) ≤ |f y - f p|` (chart line in an
  almost-maximising direction; the trivialization is almost isometric near `p`).
* `bddAbove_norm_differential`: on a compact manifold `‖df‖` is bounded for `C¹` `f`.

Together: the optimal Lipschitz constant of a `C¹` function on a compact boundaryless Riemannian
manifold is `‖∇_g f‖_∞ = ⨆ p, ‖df_p‖`.
-/

open Set MeasureTheory Filter Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology Bundle

namespace RenewalGeometry.RiemannianDistanceLipschitz

/-- In a connected pseudo-emetric space all extended distances are finite: the ball
`eball x ⊤` is open and closed.  In particular a connected Riemannian manifold (with
`EMetricSpace.ofRiemannianMetric`) has finite distance and carries a `MetricSpace` structure with
the same `edist` (`EMetricSpace.toMetricSpace`), which is the setting of this file. -/
theorem edist_ne_top_of_connectedSpace {X : Type*} [PseudoEMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have hcl : IsClopen (Metric.eball x ⊤) := ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hne : (Metric.eball x ⊤).Nonempty := ⟨x, by simp [Metric.mem_eball]⟩
  have hy : y ∈ Metric.eball x ⊤ := (hcl.eq_univ hne) ▸ mem_univ y
  rw [Metric.mem_eball] at hy
  rw [edist_comm]
  exact hy.ne

/-- The flat Riemannian metric of an inner product space is continuous (it is even smooth). -/
theorem isContinuousRiemannianBundle_vectorSpace (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] :
    IsContinuousRiemannianBundle F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  ⟨⟨(riemannianMetricVectorSpace F).inner, (riemannianMetricVectorSpace F).contMDiff.continuous,
    fun _ _ _ => rfl⟩⟩

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

variable (I) in
/-- On a Riemannian manifold (`IsRiemannianManifold`), the extended distance is the
Riemannian distance `riemannianEDist`, the infimum of the lengths of `C¹` paths. -/
theorem edist_eq_riemannianEDist (x y : M) : edist x y = riemannianEDist I x y := IsRiemannianManifold.out x y

variable (I) in
include I in
/-- **Near-geodesic paths.** On a Riemannian manifold with finite distance, for every `δ > 0`
any two points `x, y` are joined by a path `γ`, continuous on `[0,1]`, such that
`d(x,γ s) + d(γ s,γ t) + d(γ t,y) ≤ d(x,y) + δ` for `0 ≤ s ≤ t ≤ 1`: take a `C¹` path of length
`< d(x,y) + δ` (`exists_lt_of_riemannianEDist_lt`), split its length additively
(`pathELength_add`) and bound each distance by the length of the corresponding piece
(`riemannianEDist_le_pathELength`). -/
theorem exists_nearGeodesic_path (x y : M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ → M, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
        dist x (γ s) + dist (γ s) (γ t) + dist (γ t) y ≤ dist x y + δ := by
  have hlt : riemannianEDist I x y < ENNReal.ofReal (dist x y + δ) := by
    rw [← edist_eq_riemannianEDist I, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  refine ⟨γ, hγ.continuousOn, hγ0, hγ1, fun s t hs hst ht => ?_⟩
  have h1 : edist x (γ s) ≤ pathELength I γ 0 s := by
    rw [edist_eq_riemannianEDist I]
    exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl (hst.trans ht)))
      hγ0 rfl hs
  have h2 : edist (γ s) (γ t) ≤ pathELength I γ s t := by
    rw [edist_eq_riemannianEDist I]
    exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc hs ht)) rfl rfl hst
  have h3 : edist (γ t) y ≤ pathELength I γ t 1 := by
    rw [edist_eq_riemannianEDist I]
    exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc (hs.trans hst) le_rfl))
      rfl hγ1 ht
  have hsum : pathELength I γ 0 s + pathELength I γ s t + pathELength I γ t 1 =
      pathELength I γ 0 1 := by
    rw [pathELength_add hs hst, pathELength_add (hs.trans hst) ht]
  have htot : edist x (γ s) + edist (γ s) (γ t) + edist (γ t) y < ENNReal.ofReal (dist x y + δ) :=
    lt_of_le_of_lt (by rw [← hsum]; gcongr) hlen
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ← ENNReal.ofReal_add (by positivity) dist_nonneg,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)] at htot
  exact htot.le


variable (I) in
/-- The differential `df_p` of a real function, as a continuous linear functional on the tangent
space `T_pM` carrying its Riemannian norm.  Its operator norm `‖df_p‖` is the Riemannian length
of the gradient (`norm_gradient`). -/
noncomputable def differential (f : M → ℝ) (p : M) : TangentSpace I p →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f p

/-- Chain rule along a curve: `(f ∘ γ)'(t) = df_{γ t}(γ'(t))`. -/
theorem deriv_comp_eq_differential {f : M → ℝ} {γ : ℝ → M} {t : ℝ} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (f ∘ γ) t = differential I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv, mfderiv_comp t hf hγ]
  rfl

/-- **Mean-value inequality along near-minimising paths.** If `‖df_p‖ ≤ L` everywhere, then
`|f y - f x| ≤ L (d(x,y) + δ)` for every `δ > 0` (integrate `|(f ∘ γ)'| ≤ L ‖γ'‖` along a `C¹`
path of length `< d(x,y) + δ`). -/
theorem abs_sub_le_of_norm_differential_le {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ p, ‖differential I f p‖ ≤ L) (x y : M) {δ : ℝ} (hδ : 0 < δ) :
    |f y - f x| ≤ L * (dist x y + δ) := by
  have hlt : riemannianEDist I x y < ENNReal.ofReal (dist x y + δ) := by
    rw [← edist_eq_riemannianEDist I, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  have hF : ContDiffOn ℝ 1 (f ∘ γ) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hγ)
  have key := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF zero_le_one
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖ₑ ≤
      ENNReal.ofReal L * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ := by
    intro t ht
    have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    have hft : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) := (hf (γ t)).mdifferentiableAt one_ne_zero
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), deriv_comp_eq_differential hft hγt]
    refine (ContinuousLinearMap.le_opENorm _ _).trans ?_
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb _)
  have hint : ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖ₑ ≤
      ENNReal.ofReal L * pathELength I γ 0 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc, pathELength_eq_lintegral_mfderiv_Ioo,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ioo hpt
  have h3 : ‖(f ∘ γ) 1 - (f ∘ γ) 0‖ₑ ≤ ENNReal.ofReal (L * (dist x y + δ)) := by
    refine key.trans (hint.trans ?_)
    rw [ENNReal.ofReal_mul hL]
    gcongr
  simp only [Function.comp_apply, hγ0, hγ1, Real.enorm_eq_ofReal_abs] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- **Lipschitz constant ≤ `sup ‖∇f‖`.** A `C¹` function with `‖df_p‖ ≤ L` at every point is
`L`-Lipschitz for the Riemannian distance. -/
theorem lipschitzWith_of_norm_differential_le {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) {L : NNReal}
    (hb : ∀ p, ‖differential I f p‖ ≤ L) : LipschitzWith L f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, abs_sub_comm]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := abs_sub_le_of_norm_differential_le hf L.coe_nonneg hb x y (δ := ε / ((L : ℝ) + 1)) (by positivity)
  refine h.trans ?_
  rw [mul_add]
  gcongr
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [L.coe_nonneg]


/-! ### The Riemannian gradient -/

section Gradient

variable [FiniteDimensional ℝ E]

omit [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] in
/-- Tangent spaces of a manifold modelled on a finite-dimensional space are finite-dimensional. -/
theorem finiteDimensional_tangentSpace (p : M) : FiniteDimensional ℝ (TangentSpace I p) :=
  inferInstanceAs (FiniteDimensional ℝ E)

variable (I) in
/-- The Riemannian gradient `∇_g f(p) ∈ T_pM`: the Riesz representative of `df_p` for the inner
product `g_p`. -/
noncomputable def gradient (f : M → ℝ) (p : M) : TangentSpace I p :=
  haveI := finiteDimensional_tangentSpace (I := I) p
  haveI : CompleteSpace (TangentSpace I p) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ (TangentSpace I p)).symm (differential I f p)

omit [IsRiemannianManifold I M] in
/-- `g_p(∇_g f(p), v) = df_p(v)`. -/
theorem inner_gradient (f : M → ℝ) (p : M) (v : TangentSpace I p) :
    inner ℝ (gradient I f p) v = differential I f p v := by
  have := finiteDimensional_tangentSpace (I := I) p
  have : CompleteSpace (TangentSpace I p) := FiniteDimensional.complete ℝ _
  simp [gradient]

omit [IsRiemannianManifold I M] in
/-- `‖∇_g f(p)‖_g = ‖df_p‖`: the operator norm of the differential is the Riemannian length of the
gradient, so `⨆ p, ‖df_p‖ = ‖∇_g f‖_∞`. -/
theorem norm_gradient (f : M → ℝ) (p : M) : ‖gradient I f p‖ = ‖differential I f p‖ := by
  have := finiteDimensional_tangentSpace (I := I) p
  have : CompleteSpace (TangentSpace I p) := FiniteDimensional.complete ℝ _
  simp [gradient]

end Gradient

/-! ### Lower bound and boundedness (boundaryless, continuous metric) -/

section Lower

variable [I.Boundaryless] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The chart line through `p` in direction `u`: `t ↦ φ_p⁻¹(φ_p(p) + t u)` for the extended
chart `φ_p = extChartAt I p`. -/
noncomputable def chartLine (p : M) (u : E) (t : ℝ) : M :=
  (extChartAt I p).symm (extChartAt I p p + t • u)

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] in
/-- The chart line starts at `p`. -/
theorem chartLine_zero (p : M) (u : E) : chartLine (I := I) p u 0 = p := by
  simp [chartLine]

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] in
/-- An affine line in the model space is differentiable with velocity `u`. -/
theorem line_mdifferentiableAt_mfderiv (c u : E) (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c + t • u) t ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c + t • u) t 1 = u := by
  have hd : HasDerivAt (fun t : ℝ => c + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add c
  refine ⟨mdifferentiableAt_iff_differentiableAt.2 hd.differentiableAt, ?_⟩
  rw [mfderiv_eq_fderiv]
  exact hd.deriv

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] in
/-- Velocity of the chart line: inside the chart target, `σ'(t)` is the tangent vector at `σ t`
whose coordinates in the trivialization at `p` are `u`. -/
theorem chartLine_mfderiv (p : M) (u : E) {t : ℝ}
    (ht : extChartAt I p p + t • u ∈ (extChartAt I p).target) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (chartLine (I := I) p u) t ∧
      mfderiv 𝓘(ℝ, ℝ) I (chartLine (I := I) p u) t 1 =
        (trivializationAt E (TangentSpace I) p).symmL ℝ (chartLine (I := I) p u t) u := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm (extChartAt I p p + t • u) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := I) ht
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
  obtain ⟨hline, hline'⟩ := line_mdifferentiableAt_mfderiv (extChartAt I p p) u t
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (chartLine (I := I) p u) t := hsymm.comp t hline
  refine ⟨hc, ?_⟩
  have hsrc : chartLine (I := I) p u t ∈ (chartAt H p).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I p).map_target ht
  have hinv : extChartAt I p (chartLine (I := I) p u t) = extChartAt I p p + t • u :=
    (extChartAt I p).right_inv ht
  have e1 : chartLine (I := I) p u = (extChartAt I p).symm ∘ (fun t : ℝ => extChartAt I p p + t • u) :=
    rfl
  rw [TangentBundle.symmL_trivializationAt hsrc, hinv, I.range_eq_univ, mfderivWithin_univ, e1,
    mfderiv_comp t hsymm hline]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hline']
  rfl

/-- **Optimal Lipschitz constant ≥ `‖∇f(p)‖`.** On a boundaryless manifold with a continuous
Riemannian metric, if `f` is differentiable at `p` and `0 < ε < ‖df_p‖`, there is a point `y ≠ p`
with `(‖df_p‖ - ε) d(p,y) ≤ |f y - f p|`.  One moves a short time `s` along the chart line in a
direction `u` where `df_p(u)` almost attains `‖df_p‖`; near `p` the line has Riemannian speed
`< r`, with `r > 1` arbitrarily close to `1` (`eventually_norm_symmL_trivializationAt_comp_self_lt`),
so `d(p,σ s) ≤ r s`, while `f(σ s) - f p ≥ s(‖df_p‖ - ε/2)` by differentiability. -/
theorem exists_sub_mul_dist_le_abs_sub (p : M) {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) {ε : ℝ}
    (hε : 0 < ε) (hεN : ε < ‖differential I f p‖) :
    ∃ y : M, 0 < dist p y ∧ (‖differential I f p‖ - ε) * dist p y ≤ |f y - f p| := by
  set D := differential I f p with hD
  set N := ‖D‖ with hN
  -- a direction in which `D` almost attains its norm
  obtain ⟨u, hu1, hu⟩ : ∃ u : TangentSpace I p, ‖u‖ < 1 ∧ N - ε / 4 < D u := by
    obtain ⟨v, hv1, hv⟩ := D.exists_lt_apply_of_lt_opNorm (r := N - ε / 4) (by linarith)
    rw [Real.norm_eq_abs] at hv
    rcases le_or_gt 0 (D v) with h | h
    · exact ⟨v, hv1, by rwa [abs_of_nonneg h] at hv⟩
    · refine ⟨-v, by rwa [norm_neg], ?_⟩
      rw [map_neg]
      rw [abs_of_neg h] at hv
      exact hv
  obtain ⟨w, hw⟩ : ∃ w : E,
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p u = w := ⟨_, rfl⟩
  -- the distortion factor
  set r : ℝ := (N - ε / 2) / (N - ε) with hr
  have hNε : 0 < N - ε := by linarith
  have hr1 : 1 < r := by rw [hr, one_lt_div hNε]; linarith
  have hrN : r * (N - ε) = N - ε / 2 := by rw [hr]; field_simp
  have hU := eventually_norm_symmL_trivializationAt_comp_self_lt E
    (fun x : M ↦ TangentSpace I x) p hr1
  set σ := chartLine (I := I) p w with hσ
  set η : ℝ → E := fun t => extChartAt I p p + t • w with hη
  have hηc : Continuous η := by fun_prop
  have hη0 : η 0 = extChartAt I p p := by simp [hη]
  have hσ0 : σ 0 = p := chartLine_zero p w
  have hσc : ContinuousAt σ 0 := by
    have h1 : ContinuousAt (extChartAt I p).symm (η 0) := by
      rw [hη0]; exact continuousAt_extChartAt_symm p
    exact h1.comp hηc.continuousAt
  have hA : η ⁻¹' (extChartAt I p).target ∩ σ ⁻¹' {y | ‖(trivializationAt E (TangentSpace I) p).symmL ℝ y ∘L
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p‖ < r} ∈ 𝓝 (0 : ℝ) := by
    refine Filter.inter_mem ?_ ?_
    · refine ((isOpen_extChartAt_target p).preimage hηc).mem_nhds ?_
      simp only [mem_preimage, hη0]
      exact mem_extChartAt_target p
    · refine hσc.preimage_mem_nhds ?_
      rw [hσ0]
      exact hU
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.1 hA
  -- the derivative of `f ∘ σ` at `0` is `D u`
  have hmem0 : extChartAt I p p + (0 : ℝ) • w ∈ (extChartAt I p).target := by
    simp only [zero_smul, add_zero]
    exact mem_extChartAt_target (I := I) p
  obtain ⟨hσd, hσd'⟩ := chartLine_mfderiv (I := I) p w hmem0
  rw [← hσ] at hσd hσd'
  have hsymm0 : (trivializationAt E (TangentSpace I) p).symmL ℝ p w = u := by
    rw [← hw]
    exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
      (FiberBundle.mem_baseSet_trivializationAt' p) u
  have hf0 : MDifferentiableAt I 𝓘(ℝ, ℝ) f (σ 0) := by rw [hσ0]; exact hf
  have hFd : DifferentiableAt ℝ (f ∘ σ) 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hf0.comp 0 hσd)
  have hderiv : deriv (f ∘ σ) 0 = D u := by
    rw [deriv_comp_eq_differential hf0 hσd, hσd', hσ0, hsymm0]
  have hF : HasDerivAt (f ∘ σ) (D u) 0 := hderiv ▸ hFd.hasDerivAt
  have hlo := (hasDerivAt_iff_isLittleO.1 hF).def (c := ε / 4) (by positivity)
  -- pick a small positive time
  obtain ⟨s, hs_lo, hs_pos, hs_a⟩ : ∃ s : ℝ,
      ‖(f ∘ σ) s - (f ∘ σ) 0 - (s - 0) • D u‖ ≤ ε / 4 * ‖s - 0‖ ∧ 0 < s ∧ s < a := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖(f ∘ σ) s - (f ∘ σ) 0 - (s - 0) • D u‖ ≤ ε / 4 * ‖s - 0‖ :=
      nhdsWithin_le_nhds hlo
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < a := Ioo_mem_nhdsGT ha
    obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
    exact ⟨s, hs1, hs2.1, hs2.2⟩
  have hgain : s * (N - ε / 2) ≤ f (σ s) - f p := by
    simp only [Function.comp_apply, hσ0, sub_zero, smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos hs_pos] at hs_lo
    have := (abs_le.1 hs_lo).1
    nlinarith
  -- the length estimate
  have hgood : ∀ t ∈ Icc (0 : ℝ) s, η t ∈ (extChartAt I p).target ∧
      ‖(trivializationAt E (TangentSpace I) p).symmL ℝ (σ t) ∘L
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p‖ < r := by
    intro t ht
    have : t ∈ Metric.ball (0 : ℝ) a := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt hs_a
    exact hball this
  have hσsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 s) := by
    have hηs : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc 0 s) := by
      rw [contMDiffOn_iff_contDiffOn]
      exact (by fun_prop : ContDiff ℝ 1 η).contDiffOn
    exact (contMDiffOn_extChartAt_symm p).comp hηs fun t ht => (hgood t ht).1
  have hlen : pathELength I σ 0 s ≤ ENNReal.ofReal r * ENNReal.ofReal s := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo]
    have hpt : ∀ t ∈ Ioo (0 : ℝ) s, ‖mfderiv 𝓘(ℝ, ℝ) I σ t 1‖ₑ ≤ ENNReal.ofReal r := by
      intro t ht
      have hg := hgood t (Ioo_subset_Icc_self ht)
      rw [(chartLine_mfderiv (I := I) p w hg.1).2]
      have key : ‖(trivializationAt E (TangentSpace I) p).symmL ℝ (σ t) w‖ ≤ r := by
        calc ‖(trivializationAt E (TangentSpace I) p).symmL ℝ (σ t) w‖
            = ‖((trivializationAt E (TangentSpace I) p).symmL ℝ (σ t) ∘L
              (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) u‖ := by
              rw [ContinuousLinearMap.comp_apply, hw]
          _ ≤ ‖(trivializationAt E (TangentSpace I) p).symmL ℝ (σ t) ∘L
              (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p‖ * ‖u‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ r * 1 := by gcongr; exact hg.2.le
          _ = r := mul_one r
      have key' := ENNReal.ofReal_le_ofReal key
      rw [ofReal_norm] at key'
      exact key'
    calc ∫⁻ t in Ioo 0 s, ‖mfderiv 𝓘(ℝ, ℝ) I σ t 1‖ₑ
        ≤ ∫⁻ _t in Ioo 0 s, ENNReal.ofReal r := setLIntegral_mono' measurableSet_Ioo hpt
      _ = ENNReal.ofReal r * ENNReal.ofReal s := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
  have hdist : dist p (σ s) ≤ r * s := by
    have h1 : edist p (σ s) ≤ ENNReal.ofReal (r * s) := by
      rw [edist_eq_riemannianEDist I, ENNReal.ofReal_mul (by linarith)]
      refine le_trans ?_ hlen
      exact riemannianEDist_le_pathELength hσsmooth hσ0 rfl hs_pos.le
    rw [edist_dist] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hgain_pos : 0 < f (σ s) - f p := lt_of_lt_of_le (by nlinarith) hgain
  refine ⟨σ s, ?_, ?_⟩
  · rcases (dist_nonneg : 0 ≤ dist p (σ s)).lt_or_eq with h | h
    · exact h
    · have : p = σ s := dist_eq_zero.1 h.symm
      rw [← this, sub_self] at hgain_pos
      exact absurd hgain_pos (lt_irrefl 0)
  · rw [abs_of_pos hgain_pos]
    calc (N - ε) * dist p (σ s) ≤ (N - ε) * (r * s) := by gcongr
      _ = s * (r * (N - ε)) := by ring
      _ = s * (N - ε / 2) := by rw [hrN]
      _ ≤ f (σ s) - f p := hgain

omit [IsRiemannianManifold I M] in
/-- Local boundedness of `‖df‖` for a `C¹` function: near `x`,
`df_y = d(f ∘ φ_x⁻¹)(φ_x y) ∘ (trivialization at x)_y`, both factors being locally bounded. -/
theorem eventually_norm_differential_le (x : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    ∃ B : ℝ, ∀ᶠ y in 𝓝 x, ‖differential I f y‖ ≤ B := by
  obtain ⟨C, hC, hCev⟩ := eventually_norm_trivializationAt_lt E (fun x : M ↦ TangentSpace I x) x
  set g : E → ℝ := f ∘ (extChartAt I x).symm with hg
  have hgc : ContDiffOn ℝ 1 g (extChartAt I x).target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
  have hgd : ContinuousOn (fun z => fderiv ℝ g z) (extChartAt I x).target :=
    hgc.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target x) le_rfl
  have hcont : ContinuousAt (fun y => fderiv ℝ g (extChartAt I x y)) x :=
    (hgd.continuousAt (extChartAt_target_mem_nhds x)).comp (continuousAt_extChartAt x)
  have hev : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ g (extChartAt I x y)‖ < ‖fderiv ℝ g (extChartAt I x x)‖ + 1 :=
    hcont.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨(‖fderiv ℝ g (extChartAt I x x)‖ + 1) * C, ?_⟩
  filter_upwards [hCev, hev, extChartAt_source_mem_nhds (I := I) x] with y hy1 hy2 hy3
  have hsrc : y ∈ (chartAt H x).source := by rwa [← extChartAt_source I]
  have hbase : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    simpa using hsrc
  have htgt : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy3
  have hinv : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy3
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x y) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := I) htgt
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
  have hfy : MDifferentiableAt I 𝓘(ℝ, ℝ) f y := (hf y).mdifferentiableAt one_ne_zero
  have hcomp : (differential I f y).comp ((trivializationAt E (TangentSpace I) x).symmL ℝ y) =
      fderiv ℝ g (extChartAt I x y) := by
    rw [TangentBundle.symmL_trivializationAt hsrc, I.range_eq_univ, mfderivWithin_univ,
      ← mfderiv_eq_fderiv, hg, mfderiv_comp_of_eq (hinv ▸ hfy) hsymm hinv]
    congr 1
    rw [hinv]
    try rfl
  have hfac : differential I f y = (fderiv ℝ g (extChartAt I x y)).comp
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y) := by
    rw [← hcomp]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hbase v]
  rw [hfac]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul hy2.le hy1.le (norm_nonneg _) (by positivity)

omit [IsRiemannianManifold I M] in
/-- On a compact manifold, `‖df_p‖` is bounded for a `C¹` function `f`, so
`‖∇_g f‖_∞ = ⨆ p, ‖df_p‖` is a genuine supremum. -/
theorem bddAbove_norm_differential [CompactSpace M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    BddAbove (Set.range fun p => ‖differential I f p‖) := by
  classical
  choose B hB using fun x : M => eventually_norm_differential_le (I := I) x hf
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => {y | ‖differential I f y‖ ≤ B x})
    fun x => hB x
  refine ⟨∑ x ∈ t, max (B x) 0, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ ⋃ x ∈ t, {y | ‖differential I f y‖ ≤ B x} := by rw [ht]; trivial
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact hxy.trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun x => max (B x) 0) (fun _ _ => le_max_right _ _) hx))

end Lower

/-! ### Non-vacuity on the Euclidean line -/

section Examples

attribute [local instance] isContinuousRiemannianBundle_vectorSpace

/-- The coordinate function of `ℝ` has differential of norm `1`. -/
theorem norm_differential_id_real (p : ℝ) : ‖differential 𝓘(ℝ, ℝ) (id : ℝ → ℝ) p‖ = 1 := by
  set D := differential 𝓘(ℝ, ℝ) (id : ℝ → ℝ) p with hD
  have hDv : ∀ v : TangentSpace 𝓘(ℝ, ℝ) p, D v = (v : ℝ) := fun v => by
    simp only [hD, differential, mfderiv_id]
    rfl
  have hn : ∀ v : TangentSpace 𝓘(ℝ, ℝ) p, ‖v‖ = ‖letI V : ℝ := v; V‖ := fun v =>
    norm_tangentSpace_vectorSpace
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [hDv, hn, one_mul]
  · obtain ⟨v1, hv1⟩ : ∃ v1 : TangentSpace 𝓘(ℝ, ℝ) p, (v1 : ℝ) = 1 := ⟨(1 : ℝ), rfl⟩
    have h := D.le_opNorm v1
    rw [hDv, hn] at h
    simp only [hv1] at h
    calc (1 : ℝ) = ‖(1 : ℝ)‖ := norm_one.symm
      _ ≤ ‖D‖ * ‖(1 : ℝ)‖ := h
      _ = ‖D‖ := by rw [norm_one, mul_one]

/-- Non-vacuity of the Lipschitz bound: the coordinate function of the Euclidean line (a
Riemannian manifold in Mathlib) is `1`-Lipschitz by `lipschitzWith_of_norm_differential_le`. -/
example : LipschitzWith 1 (id : ℝ → ℝ) :=
  lipschitzWith_of_norm_differential_le (I := 𝓘(ℝ, ℝ)) contMDiff_id
    fun p => (norm_differential_id_real p).le

/-- Non-vacuity of the lower bound (boundaryless model, continuous metric, nonzero
differential): a point `y ≠ 0` with `(1 - 1/2) d(0,y) ≤ |y - 0|`. -/
example : ∃ y : ℝ, 0 < dist (0 : ℝ) y ∧
    (‖differential 𝓘(ℝ, ℝ) (id : ℝ → ℝ) 0‖ - 1 / 2) * dist 0 y ≤ |id y - id 0| :=
  exists_sub_mul_dist_le_abs_sub (I := 𝓘(ℝ, ℝ)) 0 mdifferentiableAt_id (by norm_num)
    (by rw [norm_differential_id_real]; norm_num)

/-- Non-vacuity of the near-geodesic path property on the Euclidean line. -/
example (x y : ℝ) : ∃ γ : ℝ → ℝ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      dist x (γ s) + dist (γ s) (γ t) + dist (γ t) y ≤ dist x y + 1 :=
  exists_nearGeodesic_path 𝓘(ℝ, ℝ) x y 1 one_pos

end Examples

end RenewalGeometry.RiemannianDistanceLipschitz
