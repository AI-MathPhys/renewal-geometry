/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.BosonicStressDefectExact
import RenewalGeometry.Analysis.CovariantGradientCompactness

/-!
# Box-chart instantiation of the bosonic stress-defect records
  (Einstein–SM action closure: `lem:critical-cubic`, `thm:higgs-defect`,
  `thm:zero-defect-characterization`, `cor:independent-bosonic-certificates`)

Box rendering of the bounded four-dimensional chart, as for `prop:orlicz` and
`prop:covariant-higgs-endpoint` (`SobolevBoxCompactness.lean`, `CovariantGradientCompactness.lean`):
`Q = box a b = Π_i (a_i, b_i) ⊂ ℝ⁴` with Lebesgue measure, the standard Sobolev space
`H¹(Q) = W^{1,2}(Q)` (`MemW12`, `w12Norm`), Higgs fields with `m` complex components.  The
compact domain including its boundary is the closed box `Q̄ = Icc a b`; Radon measures on `Q̄` are
functionals on `C(Q̄)`, and the reference measure on `Q̄` is Lebesgue measure on `Q` pulled back along
the inclusion (`V0 a b`, so that `∫_{Q̄} f ∘ ι dV0 = ∫_Q f`).

The paper's `eq:critical-Higgs` (`H_h ⇀ H` in `H¹(Q)`, `H_h → H` a.e.) is encoded by weak `H¹(Q)`
convergence componentwise — `H_h, H ∈ W^{1,2}(Q)`, a uniform `W^{1,2}(Q)` bound, and weak `L²(Q)`
convergence of the components and of their weak partial derivatives — and a.e. convergence.  The
uniform `L⁴(Q)` bound is **derived** from the critical Sobolev embedding
`SobolevOpen.exists_sobolev_L4_box` (`H¹(Q) ↪ L⁴(Q)` through the reflection extension).

## Results

* `critical_cubic_box` (`lem:critical-cubic`), `exists_L4_bound_box`.
* `higgs_defect_box`, `higgs_defect_box_einstein`, `higgs_defect_box_conserved`
  (`thm:higgs-defect`).
* `zero_defect_characterization_box` (`thm:zero-defect-characterization`).
* `independent_bosonic_certificates_box` (`cor:independent-bosonic-certificates`), composed with
  `SobolevOpen.covariant_higgs_endpoint_box_of_L2` (`prop:covariant-higgs-endpoint`) and
  `SobolevOpen.tendsto_L2_box_of_weak` (Rellich), including the `H¹(Q)` clause.
* Transfer infrastructure: `weakL2_comp`, `strongL2_comp_iff`, `integral_comp` (pull-back along
  `Q̄ ↪ ℝ⁴`), `Hvec`/`tendsto_inner_Hvec` (`ℂ^m`-valued fields from components), `Aop`/`AopF`
  (`ρ_H(A_μ)` as operator fields), `covD_Hvec`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false

namespace RenewalGeometry

namespace BosonicStressDefectBox

open BosonicStress QuadraticPacketDefect SignedMeasureWeakCompactness BosonicStressDefect

/-! ## Transfer along a measure-preserving embedding -/

section Transfer

variable {K X : Type*} [MeasurableSpace K] [MeasurableSpace X] {e : K → X}
  {V₀ : Measure K} {ν : Measure X}

theorem memLp_comp_iff (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {E : Type*}
    [NormedAddCommGroup E] {f : X → E} {p : ℝ≥0∞} : MemLp (f ∘ e) p V₀ ↔ MemLp f p ν := by
  rw [← hmap, he.memLp_map_measure_iff]

theorem eLpNorm_comp (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {E : Type*}
    [NormedAddCommGroup E] (f : X → E) (p : ℝ≥0∞) : eLpNorm (f ∘ e) p V₀ = eLpNorm f p ν := by
  rw [← hmap, he.eLpNorm_map_measure]

theorem integral_comp (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : X → E) : ∫ y, f (e y) ∂V₀ = ∫ x, f x ∂ν := by
  rw [← hmap, he.integral_map]

theorem ae_comp (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {P : X → Prop}
    (h : ∀ᵐ x ∂ν, P x) : ∀ᵐ y ∂V₀, P (e y) := by
  rw [← hmap] at h
  exact he.ae_map_iff.1 h

theorem aestronglyMeasurable_comp (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {E : Type*}
    [TopologicalSpace E] {f : X → E} (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (f ∘ e) V₀ := by
  rw [← hmap] at hf
  exact he.aestronglyMeasurable_map_iff.1 hf

variable [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure V₀]

/-- **Weak `L²` convergence transfers to the pulled-back packet** (tests on `K` extend by zero). -/
theorem weakL2_comp (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {ι : Type*}
    {Y : ℕ → ι → X → ℝ} {Y₀ : ι → X → ℝ} (hY : ∀ h i, MemLp (Y h i) 2 ν)
    (hY₀ : ∀ i, MemLp (Y₀ i) 2 ν)
    (hw : ∀ i (v : X → ℝ), MemLp v 2 ν →
      Tendsto (fun h => ∫ x, v x * Y h i x ∂ν) atTop (𝓝 (∫ x, v x * Y₀ i x ∂ν))) :
    WeakL2 V₀ (fun h i => Y h i ∘ e) (fun i => Y₀ i ∘ e) := by
  refine ⟨fun h i => (memLp_comp_iff he hmap).2 (hY h i), fun i => (memLp_comp_iff he hmap).2 (hY₀ i),
    fun i v hv => ?_⟩
  set v' : X → ℝ := Function.extend e v 0
  have hv' : v' ∘ e = v := funext fun y => he.injective.extend_apply v 0 y
  have hv'm : MemLp v' 2 ν := (memLp_comp_iff he hmap).1 (hv' ▸ hv)
  have e1 : ∀ G : X → ℝ, ∫ x, v' x * G x ∂ν = ∫ y, v y * (G ∘ e) y ∂V₀ := by
    intro G
    rw [← integral_comp he hmap (fun x => v' x * G x)]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      simp only [Function.comp_apply, ← hv'])
  have := hw i v' hv'm
  simp only [e1] at this
  exact this

/-- Strong `L²` convergence of the pulled-back packet is strong `L²(ν)` convergence. -/
theorem strongL2_comp_iff (he : MeasurableEmbedding e) (hmap : V₀.map e = ν) {ι : Type*}
    {Y : ℕ → ι → X → ℝ} {Y₀ : ι → X → ℝ} :
    StrongL2 V₀ (fun h i => Y h i ∘ e) (fun i => Y₀ i ∘ e) ↔
      ∀ i, Tendsto (fun h => ∫ x, (Y h i x - Y₀ i x) ^ 2 ∂ν) atTop (𝓝 0) := by
  unfold StrongL2
  have e1 : ∀ h i, ∫ y, ((Y h i ∘ e) y - (Y₀ i ∘ e) y) ^ 2 ∂V₀ =
      ∫ x, (Y h i x - Y₀ i x) ^ 2 ∂ν := fun h i =>
    integral_comp he hmap (fun x => (Y h i x - Y₀ i x) ^ 2)
  simp only [e1]

end Transfer

/-! ## The box chart -/

section BoxChart

variable (a b : Fin 4 → ℝ)

/-- Lebesgue measure on the open box `Q`. -/
noncomputable abbrev boxμ : Measure (Fin 4 → ℝ) := volume.restrict (SobolevOpen.box a b)

instance : IsFiniteMeasure (boxμ a b) :=
  isFiniteMeasure_restrict.mpr (SobolevOpen.volume_box_ne_top a b)

/-- The reference measure on the closed box `Q̄`: Lebesgue measure on `Q` pulled back. -/
noncomputable def V0 : Measure (Icc a b) := (boxμ a b).comap Subtype.val

theorem emb : MeasurableEmbedding (Subtype.val : Icc a b → Fin 4 → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

theorem map_V0 : (V0 a b).map Subtype.val = boxμ a b := by
  rw [V0, map_comap_subtype_coe measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_right.2 (SobolevOpen.box_subset_Icc a b)]

instance : IsFiniteMeasure (V0 a b) := by
  constructor
  have h := map_V0 a b
  have h2 : (V0 a b).map Subtype.val univ = V0 a b univ := by
    rw [Measure.map_apply (emb a b).measurable MeasurableSet.univ, preimage_univ]
  rw [← h2, h]
  exact measure_lt_top _ _

end BoxChart


/-! ## Higgs fields with `m` complex components as `ℂ^m`-valued fields -/

section HiggsVec

variable {m : ℕ}

/-- The realified Higgs fibre `ℂ^m` (Hermitian norm; real inner product `Re⟨·,·⟩`). -/
abbrev HE (m : ℕ) := EuclideanSpace ℂ (Fin m)

/-- Assemble complex components into a vector of `ℂ^m`. -/
def toE (f : Fin m → ℂ) : HE m := WithLp.toLp 2 f

@[simp] theorem toE_ofLp (f : Fin m → ℂ) (c : Fin m) : (toE f).ofLp c = f c := rfl

theorem continuous_toE : Continuous (toE (m := m)) := PiLp.continuous_toLp 2 _

theorem norm_toE_sq (f : Fin m → ℂ) : ‖toE f‖ ^ 2 = ∑ c, ‖f c‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

theorem sum_sq_le_sq_sum {s : Finset (Fin m)} {a : Fin m → ℝ} (ha : ∀ c, 0 ≤ a c) :
    ∑ c ∈ s, a c ^ 2 ≤ (∑ c ∈ s, a c) ^ 2 := by
  rw [sq (∑ c ∈ s, a c), Finset.sum_mul]
  refine Finset.sum_le_sum fun c hc => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun d _ => ha d) hc) (ha c)

theorem norm_toE_le (f : Fin m → ℂ) : ‖toE f‖ ≤ ∑ c, ‖f c‖ := by
  have h1 : ‖toE f‖ ^ 2 ≤ (∑ c, ‖f c‖) ^ 2 := by
    rw [norm_toE_sq]; exact sum_sq_le_sq_sum fun c => norm_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

theorem norm_ofLp_le (v : HE m) (c : Fin m) : ‖v.ofLp c‖ ≤ ‖v‖ := by
  have h := norm_toE_sq v.ofLp
  have h2 : ‖v.ofLp c‖ ^ 2 ≤ ∑ d, ‖v.ofLp d‖ ^ 2 :=
    Finset.single_le_sum (f := fun d => ‖v.ofLp d‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have e : toE v.ofLp = v := rfl
  rw [e] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h ▸ h2)

/-- The vector field `x ↦ (H^c(x))_c`. -/
def Hvec {X : Type*} (H : Fin m → X → ℂ) (x : X) : HE m := toE fun c => H c x

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem aestronglyMeasurable_Hvec {H : Fin m → X → ℂ} {p : ℝ≥0∞} (hH : ∀ c, MemLp (H c) p ν) :
    AEStronglyMeasurable (Hvec H) ν :=
  continuous_toE.comp_aestronglyMeasurable (MemLp.of_eval (f := fun x c => H c x) hH).1

theorem memLp_Hvec {H : Fin m → X → ℂ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hH : ∀ c, MemLp (H c) p ν) :
    MemLp (Hvec H) p ν := by
  have hs : MemLp (fun x => ∑ c, ‖H c x‖) p ν :=
    memLp_finsetSum _ fun c _ => (hH c).norm
  refine hs.of_le (aestronglyMeasurable_Hvec hH) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_toE_le _

theorem eLpNorm_Hvec_le {H : Fin m → X → ℂ} (hH : ∀ c, AEStronglyMeasurable (H c) ν) {p : ℝ≥0∞}
    (hp : 1 ≤ p) : eLpNorm (Hvec H) p ν ≤ ∑ c, eLpNorm (H c) p ν := by
  calc eLpNorm (Hvec H) p ν ≤ eLpNorm (∑ c, fun x => ‖H c x‖) p ν := by
        refine eLpNorm_mono fun x => ?_
        rw [Finset.sum_apply, Real.norm_of_nonneg (by positivity)]
        exact norm_toE_le _
    _ ≤ ∑ c, eLpNorm (fun x => ‖H c x‖) p ν :=
        eLpNorm_sum_le (fun c _ => (hH c).norm) hp
    _ = ∑ c, eLpNorm (H c) p ν := by simp only [eLpNorm_norm]

theorem ae_tendsto_Hvec {H : ℕ → Fin m → X → ℂ} {H₀ : Fin m → X → ℂ}
    (hae : ∀ᵐ x ∂ν, ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x))) :
    ∀ᵐ x ∂ν, Tendsto (fun h => Hvec (H h) x) atTop (𝓝 (Hvec H₀ x)) :=
  hae.mono fun x hx => (continuous_toE.tendsto _).comp (tendsto_pi_nhds.2 hx)

theorem inner_toE (v : HE m) (g : Fin m → ℂ) :
    ⟪v, toE g⟫ = ∑ c, ((starRingEnd ℂ) (v.ofLp c) * g c).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.inner, mul_comm]
  rfl

/-- **Componentwise weak `L²` convergence gives weak `L²` convergence of the `ℂ^m`-valued
field** (real pairing `Re⟨·,·⟩`). -/
theorem tendsto_inner_Hvec [IsFiniteMeasure ν] {G : ℕ → Fin m → X → ℂ} {G₀ : Fin m → X → ℂ}
    (hG : ∀ h c, MemLp (G h c) 2 ν) (hG₀ : ∀ c, MemLp (G₀ c) 2 ν)
    (hw : ∀ c (w : X → ℂ), MemLp w 2 ν →
      Tendsto (fun h => ∫ x, w x * G h c x ∂ν) atTop (𝓝 (∫ x, w x * G₀ c x ∂ν)))
    {v : X → HE m} (hv : MemLp v 2 ν) :
    Tendsto (fun h => ∫ x, ⟪v x, Hvec (G h) x⟫ ∂ν) atTop (𝓝 (∫ x, ⟪v x, Hvec G₀ x⟫ ∂ν)) := by
  set w : Fin m → X → ℂ := fun c x => (starRingEnd ℂ) ((v x).ofLp c)
  have hwm : ∀ c, MemLp (w c) 2 ν := by
    intro c
    refine hv.of_le ?_ (Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_conj.comp ((continuous_apply c).comp (PiLp.continuous_ofLp 2 _))).comp_aestronglyMeasurable hv.1
    · simp only [w, Complex.norm_conj]
      exact norm_ofLp_le _ _
  have hint : ∀ c {g : X → ℂ}, MemLp g 2 ν → Integrable (fun x => w c x * g x) ν :=
    fun c g hg => (hwm c).integrable_mul hg
  have e : ∀ g : Fin m → X → ℂ, (∀ c, MemLp (g c) 2 ν) →
      ∫ x, ⟪v x, Hvec g x⟫ ∂ν = ∑ c, (∫ x, w c x * g c x ∂ν).re := by
    intro g hg
    simp only [Hvec, inner_toE]
    have hi : ∀ c, Integrable (fun x => ((starRingEnd ℂ) ((v x).ofLp c) * g c x).re) ν :=
      fun c => (hint c (hg c)).re
    rw [integral_finsetSum _ fun c _ => hi c]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact integral_re (hint c (hg c))
  rw [e _ hG₀]
  simp only [e _ (hG _)]
  exact tendsto_finsetSum _ fun c _ => (Complex.continuous_re.tendsto _).comp (hw c _ (hwm c))

end HiggsVec

/-! ## The connection as an operator field on `ℂ^m` -/

section Connection

variable {m : ℕ}

/-- The matrix `(A_{ce})` acting on `ℂ^m`, as a real-linear operator. -/
noncomputable def Aop (M : Fin m → Fin m → ℂ) : HE m →L[ℝ] HE m :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of M)).restrictScalars ℝ

theorem Aop_ofLp (M : Fin m → Fin m → ℂ) (w : HE m) (c : Fin m) :
    (Aop M w).ofLp c = ∑ e, M c e * w.ofLp e := by
  have hw : w = toE w.ofLp := rfl
  rw [hw]
  simp only [Aop, ContinuousLinearMap.coe_restrictScalars', toE, Matrix.toEuclideanCLM_toLp,
    PiLp.toLp_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem Aop_toE (M : Fin m → Fin m → ℂ) (f : Fin m → ℂ) :
    Aop M (toE f) = toE fun c => ∑ e, M c e * f e := by
  ext c
  rw [Aop_ofLp]
  rfl

theorem Aop_sub (M M' : Fin m → Fin m → ℂ) : Aop M - Aop M' = Aop (M - M') := by
  ext w c
  simp only [sub_apply, PiLp.sub_apply, Aop_ofLp, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem norm_Aop_le (M : Fin m → Fin m → ℂ) : ‖Aop M‖ ≤ ∑ c, ∑ e, ‖M c e‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw : Aop M w = toE fun c => ∑ e, M c e * w.ofLp e := by
    ext c; rw [Aop_ofLp]; rfl
  rw [hw]
  refine (norm_toE_le _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_ofLp_le w e) (norm_nonneg _)

theorem continuous_Aop : Continuous (Aop (m := m)) := by
  let L : (Fin m → Fin m → ℂ) →ₗ[ℝ] (HE m →L[ℝ] HE m) :=
    { toFun := Aop
      map_add' := fun M M' => by
        ext w c
        simp only [add_apply, PiLp.add_apply, Aop_ofLp, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext w c
        simp only [smul_apply, PiLp.smul_apply, Aop_ofLp, Pi.smul_apply,
          RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [smul_mul_assoc] }
  exact L.continuous_of_finiteDimensional

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The operator field `x ↦ ρ_H(A_μ(x))`. -/
noncomputable def AopF (A : Fin 4 → Fin m → Fin m → X → ℂ) (μ : Fin 4) (x : X) : HE m →L[ℝ] HE m :=
  Aop fun c e => A μ c e x

theorem memLp_AopF {A : Fin 4 → Fin m → Fin m → X → ℂ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hA : ∀ μ c e, MemLp (A μ c e) p ν) (μ : Fin 4) : MemLp (AopF A μ) p ν := by
  have hpi : MemLp (fun x => fun c e => A μ c e x) p ν :=
    MemLp.of_eval fun c => MemLp.of_eval fun e => hA μ c e
  have hs : MemLp (fun x => ∑ c, ∑ e, ‖A μ c e x‖) p ν :=
    memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun e _ => (hA μ c e).norm
  refine hs.of_le (continuous_Aop.comp_aestronglyMeasurable hpi.1)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_Aop_le _

theorem eLpNorm_AopF_sub_le {A A₀ : Fin 4 → Fin m → Fin m → X → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hA : ∀ μ c e, AEStronglyMeasurable (A μ c e - A₀ μ c e) ν) (μ : Fin 4) :
    eLpNorm (fun x => AopF A μ x - AopF A₀ μ x) p ν ≤
      ∑ c, ∑ e, eLpNorm (A μ c e - A₀ μ c e) p ν := by
  calc eLpNorm (fun x => AopF A μ x - AopF A₀ μ x) p ν
      ≤ eLpNorm (∑ c, ∑ e, fun x => ‖(A μ c e - A₀ μ c e) x‖) p ν := by
        refine eLpNorm_mono fun x => ?_
        simp only [Finset.sum_apply]
        rw [Real.norm_of_nonneg (by positivity), AopF, AopF, Aop_sub]
        exact norm_Aop_le _
    _ ≤ ∑ c, eLpNorm (∑ e, fun x => ‖(A μ c e - A₀ μ c e) x‖) p ν :=
        eLpNorm_sum_le (fun c _ => Finset.aestronglyMeasurable_sum _ fun e _ => (hA μ c e).norm) hp
    _ ≤ ∑ c, ∑ e, eLpNorm (fun x => ‖(A μ c e - A₀ μ c e) x‖) p ν :=
        Finset.sum_le_sum fun c _ => eLpNorm_sum_le (fun e _ => (hA μ c e).norm) hp
    _ = ∑ c, ∑ e, eLpNorm (A μ c e - A₀ μ c e) p ν := by simp only [eLpNorm_norm]

/-- The covariant derivative on `ℂ^m`-valued fields is the vector of the component covariant
derivatives `SobolevOpen.covD` of `CovariantGradientCompactness.lean`. -/
theorem covD_Hvec (gH : Fin m → Fin 4 → X → ℂ) (A : Fin 4 → Fin m → Fin m → X → ℂ)
    (H : Fin m → X → ℂ) (μ : Fin 4) (x : X) :
    BosonicStressDefect.covD (fun μ => Hvec fun c => gH c μ) (AopF A) (Hvec H) μ x =
      Hvec (fun c => fun y => gH c μ y + ∑ e, A μ c e y * H e y) x := by
  ext c
  simp only [BosonicStressDefect.covD, Hvec, AopF, Aop_toE, PiLp.add_apply, toE_ofLp]

end Connection

/-! ## The Sobolev `L⁴` bound on the box and `lem:critical-cubic` (box) -/

section CubicBox

variable {m : ℕ} {a b : Fin 4 → ℝ}

/-- **Derived `L⁴(Q)` bound**: a sequence bounded in `W^{1,2}(Q)` is bounded in `L⁴(Q)`
(critical Sobolev embedding `SobolevOpen.exists_sobolev_L4_box`). -/
theorem exists_L4_bound_box (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B) :
    ∃ C : ℝ≥0, ∀ h, eLpNorm (Hvec (H h)) 4 (boxμ a b) ≤ C := by
  obtain ⟨CS, hCS⟩ := SobolevOpen.exists_sobolev_L4_box (ι := Fin 4) (by simp) hab
  refine ⟨m * CS * B.toNNReal, fun h => ?_⟩
  refine (eLpNorm_Hvec_le (fun c => (hW h c).memLp.1) (by norm_num)).trans ?_
  calc ∑ c, eLpNorm (H h c) 4 (boxμ a b) ≤ ∑ _c : Fin m, (CS : ℝ≥0∞) * B :=
        Finset.sum_le_sum fun c _ => (hCS _ _ (hW h c)).trans (by gcongr; exact hB h c)
    _ = ((m * CS * B.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [ENNReal.coe_toNNReal hBt, mul_assoc]

/-- **`lem:critical-cubic`, box rendering.**  On `Q = Π (a_i, b_i) ⊂ ℝ⁴` with Lebesgue measure,
let `H_h ⇀ H` weakly in `H¹(Q; ℂ^m)` (encoded componentwise: `H_h, H ∈ W^{1,2}(Q)`, a uniform
`W^{1,2}(Q)` bound, weak `L²(Q)` convergence of the components and of their weak partials), let
`H_h → H` a.e. (`eq:critical-Higgs`), let `A_h → A` in `L⁴(Q)` (matrix entries of `ρ_H(A_μ)`), and
let continuous metrics `g_h → g` uniformly on `Q̄` with `g` nondegenerate.  Then
`|H_h|²H_h ⇀ |H|²H` in `L^{4/3}(Q)`, `D_{A_h}H_h ⇀ D_AH` in `L²(Q)` (`eq:critical-weak`), and after
extraction there is a nonnegative Radon measure `ν_H` on `Q̄` with
`|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H` and `ν_H = 0 ⟺ H_h → H` in `L⁴(Q)` along the extracted
sequence.  The `L⁴` bound is derived from the Sobolev embedding. -/
theorem critical_cubic_box (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    {gH₀ : Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c))
    (hW₀ : ∀ c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H₀ c) (gH₀ c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (_hweakH : ∀ c (w : (Fin 4 → ℝ) → ℂ), MemLp w 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, w x * H h c x ∂(boxμ a b)) atTop (𝓝 (∫ x, w x * H₀ c x ∂(boxμ a b))))
    (hweakG : ∀ c i (w : (Fin 4 → ℝ) → ℂ), MemLp w 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, w x * gH h c i x ∂(boxμ a b)) atTop
        (𝓝 (∫ x, w x * gH₀ c i x ∂(boxμ a b))))
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {A : ℕ → Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ} {A₀ : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (boxμ a b)) (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (boxμ a b))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4 (boxμ a b)) atTop (𝓝 0))
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0) :
    (∀ v : (Fin 4 → ℝ) → HE m, MemLp v 4 (boxμ a b) →
      Tendsto (fun h => ∫ x, ⟪v x, ‖Hvec (H h) x‖ ^ 2 • Hvec (H h) x⟫ ∂(boxμ a b)) atTop
        (𝓝 (∫ x, ⟪v x, ‖Hvec H₀ x‖ ^ 2 • Hvec H₀ x⟫ ∂(boxμ a b)))) ∧
    (∀ μ (v : (Fin 4 → ℝ) → HE m), MemLp v 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, ⟪v x, Hvec (fun c y => gH h c μ y + ∑ e, A h μ c e y * H h e y) x⟫
          ∂(boxμ a b)) atTop
        (𝓝 (∫ x, ⟪v x, Hvec (fun c y => gH₀ c μ y + ∑ e, A₀ μ c e y * H₀ e y) x⟫ ∂(boxμ a b)))) ∧
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ν : StrongDual ℝ C(Icc a b, ℝ),
      IsQuarticDefect (V0 a b) g g₀ (fun h => Hvec (H h) ∘ Subtype.val) (Hvec H₀ ∘ Subtype.val)
        σ ν ∧ (∀ φ : C(Icc a b, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4 ∂(boxμ a b)) atTop
        (𝓝 0)) := by
  obtain ⟨C, hC⟩ := exists_L4_bound_box hab hW hBt hB
  have hHm : ∀ h, AEStronglyMeasurable (Hvec (H h)) (boxμ a b) := fun h =>
    aestronglyMeasurable_Hvec fun c => (hW h c).memLp
  have hae' := ae_tendsto_Hvec hae
  refine ⟨fun v hv => cubic_weak hHm hae' hC hv, fun μ v hv => ?_, ?_⟩
  · have := covD_weak (dH := fun h μ => Hvec fun c => gH h c μ) (dH₀ := fun μ => Hvec fun c => gH₀ c μ)
      (A := fun h => AopF (A h)) (A₀ := AopF A₀) hHm hae' hC
      (fun h μ => memLp_Hvec fun c => (hW h c).memLp_grad μ)
      (fun μ => memLp_Hvec fun c => (hW₀ c).memLp_grad μ)
      (fun μ v hv => tendsto_inner_Hvec (fun h c => (hW h c).memLp_grad μ)
        (fun c => (hW₀ c).memLp_grad μ) (fun c w hw => hweakG c μ w hw) hv)
      (fun h μ => memLp_AopF (hA h) μ) (fun μ => memLp_AopF hA₀ μ)
      (fun μ => by
        have hs : Tendsto (fun h => ∑ c, ∑ e, eLpNorm (A h μ c e - A₀ μ c e) 4 (boxμ a b)) atTop
            (𝓝 0) := by
          simpa using tendsto_finsetSum _ fun c _ => tendsto_finsetSum _ fun e _ => hAlim μ c e
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
          fun h => eLpNorm_AopF_sub_le (p := 4) (by norm_num)
            (fun μ c e => ((hA h μ c e).sub (hA₀ μ c e)).1) μ)
      μ hv
    simpa only [covD_Hvec] using this
  · have hmap := map_V0 a b
    have he := emb a b
    obtain ⟨σ, hσ, ν, hν, hν0, hνiff⟩ := quartic_defect (V₀ := V0 a b) hg hdet₀
      (H := fun h => Hvec (H h) ∘ Subtype.val) (H₀ := Hvec H₀ ∘ Subtype.val)
      (fun h => aestronglyMeasurable_comp he hmap (hHm h))
      (ae_comp he hmap (P := fun x => Tendsto (fun h => Hvec (H h) x) atTop (𝓝 (Hvec H₀ x))) hae')
      (C := C) (fun h => (eLpNorm_comp he hmap _ _).trans_le (hC h))
    refine ⟨σ, hσ, ν, hν, hν0, ?_⟩
    have e : ∀ h, ∫ y, ‖(Hvec (H (σ h)) ∘ Subtype.val) y - (Hvec H₀ ∘ Subtype.val) y‖ ^ 4 ∂(V0 a b)
        = ∫ x, ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4 ∂(boxμ a b) := fun h =>
      integral_comp he hmap (fun x => ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4)
    simpa only [e] using hνiff

end CubicBox

/-! ## `thm:higgs-defect` (box) -/

section HiggsBox

variable {m : ℕ} {a b : Fin 4 → ℝ}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Pull back of a box packet to the closed box. -/
def pullY (Y : Fin 4 → κ → (Fin 4 → ℝ) → ℝ) : Fin 4 → κ → Icc a b → ℝ :=
  fun μ c => Y μ c ∘ Subtype.val

/-- Pull back of a `ℂ^m`-valued Higgs field to the closed box. -/
def pullH (H : Fin m → (Fin 4 → ℝ) → ℂ) : Icc a b → HE m := Hvec H ∘ Subtype.val

/-- The box form of weak `L²(Q)` convergence of a real packet. -/
def BoxWeakL2 (a b : Fin 4 → ℝ) {ι : Type*} (Y : ℕ → ι → (Fin 4 → ℝ) → ℝ)
    (Y₀ : ι → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ h i, MemLp (Y h i) 2 (boxμ a b)) ∧ (∀ i, MemLp (Y₀ i) 2 (boxμ a b)) ∧
    ∀ i (v : (Fin 4 → ℝ) → ℝ), MemLp v 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, v x * Y h i x ∂(boxμ a b)) atTop (𝓝 (∫ x, v x * Y₀ i x ∂(boxμ a b)))

theorem BoxWeakL2.pull {ι : Type*} {Y : ℕ → ι → (Fin 4 → ℝ) → ℝ} {Y₀ : ι → (Fin 4 → ℝ) → ℝ}
    (hY : BoxWeakL2 a b Y Y₀) :
    WeakL2 (V0 a b) (fun h i => Y h i ∘ Subtype.val) (fun i => Y₀ i ∘ Subtype.val) :=
  weakL2_comp (emb a b) (map_V0 a b) hY.1 hY.2.1 hY.2.2

/-- Common box hypotheses yield the pulled-back Higgs hypotheses: measurability, a.e.
convergence, and the **derived** `L⁴` bound. -/
theorem higgs_pull (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x))) :
    (∀ h, AEStronglyMeasurable (pullH (a := a) (b := b) (H h)) (V0 a b)) ∧
    (∀ᵐ y ∂(V0 a b), Tendsto (fun h => pullH (H h) y) atTop (𝓝 (pullH H₀ y))) ∧
    ∃ C : ℝ≥0, ∀ h, eLpNorm (pullH (a := a) (b := b) (H h)) 4 (V0 a b) ≤ C := by
  obtain ⟨C, hC⟩ := exists_L4_bound_box hab hW hBt hB
  refine ⟨fun h => aestronglyMeasurable_comp (emb a b) (map_V0 a b)
      (aestronglyMeasurable_Hvec fun c => (hW h c).memLp),
    ae_comp (emb a b) (map_V0 a b) (P := fun x => Tendsto (fun h => Hvec (H h) x) atTop
      (𝓝 (Hvec H₀ x))) (ae_tendsto_Hvec hae),
    C, fun h => (eLpNorm_comp (emb a b) (map_V0 a b) _ _).trans_le (hC h)⟩

/-- **`thm:higgs-defect`, box rendering, `eq:H-defect`**: on `Q ⊂ ℝ⁴` (measures on `Q̄`), with
`H_h` bounded in `W^{1,2}(Q)` and `H_h → H` a.e. (implied by `eq:critical-Higgs`; the `L⁴` bound is
derived), an identified weak gradient limit `D_{A_h}H_h ⇀ D_AH` in `L²(Q)` (realified components
`Y`), continuous metrics `g_h → g` uniformly on `Q̄` (nondegenerate) and convergent parameters:
after extraction `𝔎_H`, `ν_H ≥ 0` exist and `T^H_h dV_{g_h} ⇀* T^H dV_g + 𝔎_H - λ g ν_H`. -/
theorem higgs_defect_box (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {Y : ℕ → Fin 4 → κ → (Fin 4 → ℝ) → ℝ} {Y₀ : Fin 4 → κ → (Fin 4 → ℝ) → ℝ}
    (hY : BoxWeakL2 a b (fun h => Yp (Y h)) (Yp Y₀))
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ (KH : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ))
      (ν : StrongDual ℝ C(Icc a b, ℝ)),
      IsKinDefect (V0 a b) g g₀ (fun h => pullY (Y h)) (pullY Y₀) σ KH ∧
      IsQuarticDefect (V0 a b) g g₀ (fun h => pullH (H h)) (pullH H₀) σ ν ∧
      (∀ φ : C(Icc a b, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      IsHiggsDefect (V0 a b) g g₀ lam vH lam₀ vH₀ (fun h => pullY (Y h)) (pullY Y₀)
        (fun h => pullH (H h)) (pullH H₀) σ (fun μ ν' => KH μ ν' - potDefect lam₀ g₀ ν μ ν') := by
  obtain ⟨hHm, hae', C, hC⟩ := higgs_pull hab hW hBt hB hae
  exact higgs_defect hg hdet hdet₀ hHm hae' hC hY.pull hlam hvH

/-- **`thm:higgs-defect`, box rendering, Einstein clause `eq:defect-Einstein`.** -/
theorem higgs_defect_box_einstein (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {Y : ℕ → Fin 4 → κ → (Fin 4 → ℝ) → ℝ} {Y₀ : Fin 4 → κ → (Fin 4 → ℝ) → ℝ}
    (hY : BoxWeakL2 a b (fun h => Yp (Y h)) (Yp Y₀))
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SH : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ),
      IsHiggsDefect (V0 a b) g g₀ lam vH lam₀ vH₀ (fun h => pullY (Y h)) (pullY Y₀)
        (fun h => pullH (H h)) (pullH H₀) σ SH ∧
      ∀ (κE : ℝ) (Grav : ℕ → (Fin 4 → Fin 4 → C(Icc a b, ℝ)) → ℝ)
        (Ein : (Fin 4 → Fin 4 → C(Icc a b, ℝ)) → ℝ)
        (Rest : ℕ → (Fin 4 → Fin 4 → C(Icc a b, ℝ)) → ℝ)
        (RestLim : (Fin 4 → Fin 4 → C(Icc a b, ℝ)) → ℝ),
        0 < κE → (∀ k, Tendsto (fun h => Grav h k) atTop (𝓝 (Ein k))) →
        (∀ k, Tendsto (fun h => Rest h k) atTop (𝓝 (RestLim k))) →
        (∀ k, Tendsto (fun h => Grav h k / (2 * κE) - (1 / 2) * (∑ μ, ∑ ν, ∫ x, k μ ν x *
          (higgsStress (g h x) (lam h) (vH h) (Yval (pullY (Y h)) x) (‖pullH (H h) x‖ ^ 2) μ ν *
            vol (g h x)) ∂(V0 a b) + Rest h k)) atTop (𝓝 0)) →
        ∀ k, Ein k = κE * ((∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀
          (Yval (pullY Y₀) x) (‖pullH H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂(V0 a b)) +
          RestLim k + pairT SH k) := by
  obtain ⟨σ, hσ, KH, ν, -, -, -, hSH⟩ := higgs_defect_box hab hW hBt hB hae hY hg hdet hdet₀
    hlam hvH
  exact ⟨σ, hσ, _, hSH, fun κE Grav Ein Rest RestLim hκ hGrav hRest hres k =>
    higgs_defect_einstein hσ hSH hκ Grav Ein hGrav Rest RestLim hRest hres k⟩

/-- **`thm:higgs-defect`, box rendering, conservation clause** (`C¹` metric convergence on the
chart, total stress bounded with remaining contributions converging to their regular limits,
vanishing tested divergence; Noether identity of the regular stress gives `∇^μ 𝔖_{H,μν} = 0`). -/
theorem higgs_defect_box_conserved (hab : ∀ i, a i < b i) {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ}
    {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {Y : ℕ → Fin 4 → κ → (Fin 4 → ℝ) → ℝ} {Y₀ : Fin 4 → κ → (Fin 4 → ℝ) → ℝ}
    (hY : BoxWeakL2 a b (fun h => Yp (Y h)) (Yp Y₀))
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SH : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ),
      IsHiggsDefect (V0 a b) g g₀ lam vH lam₀ vH₀ (fun h => pullY (Y h)) (pullY Y₀)
        (fun h => pullH (H h)) (pullH H₀) σ SH ∧
      ∀ (gf : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
        (gf₀ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ),
        (∀ h i j, ContDiff ℝ 1 fun x => gf h x i j) → (∀ i j, ContDiff ℝ 1 fun x => gf₀ x i j) →
        (∀ x ∈ Icc a b, (gf₀ x).det ≠ 0) →
        (∀ i j, TendstoUniformlyOn (fun h x => gf h x i j) (fun x => gf₀ x i j) atTop (Icc a b)) →
        (∀ k i j, TendstoUniformlyOn (fun h => DefectConservationTransport.pd k fun x => gf h x i j)
          (DefectConservationTransport.pd k fun x => gf₀ x i j) atTop (Icc a b)) →
        ∀ (R : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ))
          (Rlim : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ)),
        (∀ μ ν φ, Tendsto (fun h => R h μ ν φ) atTop (𝓝 (Rlim μ ν φ))) →
        ∀ (T : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ)),
        (∀ h μ ν φ, T h μ ν φ = ∫ x, φ x * (higgsStress (g h x) (lam h) (vH h)
          (Yval (pullY (Y h)) x) (‖pullH (H h) x‖ ^ 2) μ ν * vol (g h x)) ∂(V0 a b) +
            R h μ ν φ) →
        ∀ {CT : ℝ}, (∀ h μ ν, ‖T h μ ν‖ ≤ CT) → ∀ (X : (Fin 4 → ℝ) → Fin 4 → ℝ),
        Tendsto (fun h => ∑ μ, ∑ ν, T h μ ν (DefectConservationTransport.covSym (Icc a b) (gf h)
          X μ ν)) atTop (𝓝 0) →
        (∑ μ, ∑ ν, (densityCLM (V0 a b) (fun x => higgsStress (g₀ x) lam₀ vH₀
            (Yval (pullY Y₀) x) (‖pullH H₀ x‖ ^ 2) μ ν * vol (g₀ x)) + Rlim μ ν + SH μ ν)
          (DefectConservationTransport.covSym (Icc a b) gf₀ X μ ν) = 0) ∧
        (∑ μ, ∑ ν, (densityCLM (V0 a b) (fun x => higgsStress (g₀ x) lam₀ vH₀
            (Yval (pullY Y₀) x) (‖pullH H₀ x‖ ^ 2) μ ν * vol (g₀ x)) + Rlim μ ν)
          (DefectConservationTransport.covSym (Icc a b) gf₀ X μ ν) = 0 →
          ∑ μ, ∑ ν, SH μ ν (DefectConservationTransport.covSym (Icc a b) gf₀ X μ ν) = 0) := by
  obtain ⟨σ, hσ, KH, ν, -, -, -, hSH⟩ := higgs_defect_box hab hW hBt hB hae hY hg hdet hdet₀
    hlam hvH
  obtain ⟨hHm, hae', C, hC⟩ := higgs_pull hab hW hBt hB hae
  have hH₀ : MemLp (pullH (a := a) (b := b) H₀) 4 (V0 a b) := (memLp_of_ae_tendsto hHm hae' hC).1
  refine ⟨σ, hσ, _, hSH, fun gf gf₀ hgf hgf₀ hdetf hC0 hC1 R Rlim hR T hTdef CT hT X htest => ?_⟩
  exact higgs_defect_conserved gf gf₀ hgf hgf₀ hdetf hC0 hC1 hdet₀ hH₀ hY.pull.memLp_lim hσ hSH
    R Rlim hR T hTdef hT X htest

end HiggsBox

/-! ## `thm:zero-defect-characterization` (box) -/

section ZeroBox

variable {m : ℕ} {a b : Fin 4 → ℝ}
variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Pull back of a box curvature packet to the closed box. -/
def pullF (F : Fin 4 → Fin 4 → κG → (Fin 4 → ℝ) → ℝ) : Fin 4 → Fin 4 → κG → Icc a b → ℝ :=
  fun α β c => F α β c ∘ Subtype.val

/-- **`thm:zero-defect-characterization`, box rendering.**  Hypotheses as in `higgs_defect_box`
(`H_h` bounded in `W^{1,2}(Q)` with `H_h → H` a.e.; the `L⁴` bound is derived), curvatures
`F_{A_h} ⇀ F_A` weakly in `L²(Q)` (antisymmetric two-forms, realified components), positive
limiting gauge weights and `λ_H > 0`, continuous metrics `g_h → g` uniformly on `Q̄` with Lorentzian
limit `g = Pᵀ η P` and a continuous unit timelike field `n` (`g(n,n) = -1`).  After extraction:
the stress defects, trace defects and `ν_H` (measures on `Q̄`), the two-sided timelike coercivity,
and the equivalences of `eq:complete-zero-defect-equivalence`, the strong convergences being
`F_{A_h} → F_A`, `D_{A_h}H_h → D_AH` in `L²(Q)` and `H_h → H` in `L⁴(Q)`. -/
theorem zero_defect_characterization_box (hab : ∀ i, a i < b i)
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(Icc a b, Fin 4 → ℝ)}
    (hsig : ∀ x, ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      mat (g₀ x) = Matrix.transpose P * eta * P)
    (hunit : ∀ x, gnn (g₀ x) (n x) = -1)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hw₀ : ∀ a, 0 < w₀ a)
    {F : ℕ → Fin 4 → Fin 4 → κG → (Fin 4 → ℝ) → ℝ} {F₀ : Fin 4 → Fin 4 → κG → (Fin 4 → ℝ) → ℝ}
    (hF : BoxWeakL2 a b (fun h => Fp (F h)) (Fp F₀))
    (hFa : ∀ h α β c x, F h β α c x = -F h α β c x) (hFa₀ : ∀ α β c x, F₀ β α c x = -F₀ α β c x)
    {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ} {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    {H₀ : Fin m → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {Y : ℕ → Fin 4 → κ → (Fin 4 → ℝ) → ℝ} {Y₀ : Fin 4 → κ → (Fin 4 → ℝ) → ℝ}
    (hY : BoxWeakL2 a b (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) (hlam₀ : 0 < lam₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ (SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ))
      (μYM μH ν : StrongDual ℝ C(Icc a b, ℝ)),
      IsYMDefect (V0 a b) g g₀ w w₀ (fun h => pullF (F h)) (pullF F₀) σ SYM ∧
      IsHiggsDefect (V0 a b) g g₀ lam vH lam₀ vH₀ (fun h => pullY (Y h)) (pullY Y₀)
        (fun h => pullH (H h)) (pullH H₀) σ SH ∧
      (∀ φ : C(Icc a b, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Fp (pullF (F (σ h))) p x ^ 2
        ∂(V0 a b)) atTop (𝓝 (∫ x, φ x * ∑ p, Fp (pullF F₀) p x ^ 2 ∂(V0 a b) + μYM φ))) ∧
      (∀ φ : C(Icc a b, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Yp (pullY (Y (σ h))) p x ^ 2
        ∂(V0 a b)) atTop (𝓝 (∫ x, φ x * ∑ p, Yp (pullY Y₀) p x ^ 2 ∂(V0 a b) + μH φ))) ∧
      IsQuarticDefect (V0 a b) g g₀ (fun h => pullH (H h)) (pullH H₀) σ ν ∧
      (∃ c > 0, ∃ C' > 0, ∀ φ : C(Icc a b, ℝ), (∀ x, 0 ≤ φ x) →
        c * (μYM φ + μH φ + ν φ) ≤ nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ∧
        nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ≤ C' * (μYM φ + μH φ + ν φ)) ∧
      ((∀ μ ν', SYM μ ν' + SH μ ν' = 0) ↔ nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0) ∧
      (nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0 ↔ μYM = 0 ∧ μH = 0 ∧ ν = 0) ∧
      (μYM = 0 ∧ μH = 0 ∧ ν = 0 ↔
        (∀ p, Tendsto (fun h => ∫ x, (Fp (F (σ h)) p x - Fp F₀ p x) ^ 2 ∂(boxμ a b)) atTop
          (𝓝 0)) ∧
        (∀ p, Tendsto (fun h => ∫ x, (Yp (Y (σ h)) p x - Yp Y₀ p x) ^ 2 ∂(boxμ a b)) atTop
          (𝓝 0)) ∧
        Tendsto (fun h => ∫ x, ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4 ∂(boxμ a b)) atTop (𝓝 0)) ∧
      (μYM = 0 ↔ ∀ p, Tendsto (fun h => ∫ x, (Fp (F (σ h)) p x - Fp F₀ p x) ^ 2 ∂(boxμ a b))
        atTop (𝓝 0)) ∧
      (μH = 0 ↔ ∀ p, Tendsto (fun h => ∫ x, (Yp (Y (σ h)) p x - Yp Y₀ p x) ^ 2 ∂(boxμ a b))
        atTop (𝓝 0)) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4 ∂(boxμ a b)) atTop
        (𝓝 0)) := by
  obtain ⟨hHm, hae', C, hC⟩ := higgs_pull hab hW hBt hB hae
  have he := emb a b
  have hmap := map_V0 a b
  obtain ⟨σ, hσ, SYM, SH, μYM, μH, ν, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    zero_defect_characterization (V₀ := V0 a b) (F := fun h => pullF (F h)) (F₀ := pullF F₀)
      (Y := fun h => pullY (Y h)) (Y₀ := pullY Y₀) hg hdet hdet₀ hsig hunit hw hw₀ hF.pull
      (fun h α β c x => hFa h α β c x) (fun α β c x => hFa₀ α β c x) hHm hae' hC hY.pull hlam hvH
      hlam₀
  have sF : StrongL2 (V0 a b) (fun h => Fp (pullF (F (σ h)))) (Fp (pullF F₀)) ↔
      ∀ p, Tendsto (fun h => ∫ x, (Fp (F (σ h)) p x - Fp F₀ p x) ^ 2 ∂(boxμ a b)) atTop (𝓝 0) :=
    strongL2_comp_iff he hmap (Y := fun h => Fp (F (σ h))) (Y₀ := Fp F₀)
  have sY : StrongL2 (V0 a b) (fun h => Yp (pullY (Y (σ h)))) (Yp (pullY Y₀)) ↔
      ∀ p, Tendsto (fun h => ∫ x, (Yp (Y (σ h)) p x - Yp Y₀ p x) ^ 2 ∂(boxμ a b)) atTop (𝓝 0) :=
    strongL2_comp_iff he hmap (Y := fun h => Yp (Y (σ h))) (Y₀ := Yp Y₀)
  have e4 : ∀ h, ∫ y, ‖pullH (a := a) (b := b) (H (σ h)) y - pullH H₀ y‖ ^ 4 ∂(V0 a b) =
      ∫ x, ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4 ∂(boxμ a b) := fun h =>
    integral_comp he hmap (fun x => ‖Hvec (H (σ h)) x - Hvec H₀ x‖ ^ 4)
  simp only [e4] at h9 h12
  rw [sF, sY] at h9
  rw [sF] at h10
  rw [sY] at h11
  exact ⟨σ, hσ, SYM, SH, μYM, μH, ν, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end ZeroBox

/-! ## `cor:independent-bosonic-certificates` (box), composed with
`prop:covariant-higgs-endpoint` (`SobolevOpen.covariant_higgs_endpoint_box_of_L2`) -/

section CorBox

variable {m : ℕ} {a b : Fin 4 → ℝ}
variable {κG : Type*} [Fintype κG] [DecidableEq κG]

/-- Realification `(Re, Im)` of a family of complex fields `G_{cμ}`. -/
def reY {X : Type*} (G : Fin m → Fin 4 → X → ℂ) : Fin 4 → (Fin m × Fin 2) → X → ℝ :=
  fun μ p x => if p.2 = 0 then (G p.1 μ x).re else (G p.1 μ x).im

theorem tendsto_eLpNorm_two_of_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : ℕ → X → ℂ} (hf : ∀ h, MemLp (f h) 2 ν)
    (hlim : Tendsto (fun h => ∫ x, ‖f h x‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun h => eLpNorm (f h) 2 ν) atTop (𝓝 0) := by
  have e : ∀ h, eLpNorm (f h) 2 ν = ENNReal.ofReal ((∫ x, ‖f h x‖ ^ 2 ∂ν) ^ (2 : ℝ)⁻¹) := by
    intro h
    rw [(hf h).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e]
  have h1 : Tendsto (fun h => (∫ x, ‖f h x‖ ^ 2 ∂ν) ^ (2 : ℝ)⁻¹) atTop (𝓝 ((0 : ℝ) ^ (2 : ℝ)⁻¹)) :=
    hlim.rpow_const (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h1
  have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
  rw [ENNReal.ofReal_zero] at h2
  exact h2

theorem tendsto_eLpNorm_of_reY {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {G : ℕ → Fin m → Fin 4 → X → ℂ} {G₀ : Fin m → Fin 4 → X → ℂ}
    (hG : ∀ h c μ, MemLp (G h c μ) 2 ν) (hG₀ : ∀ c μ, MemLp (G₀ c μ) 2 ν)
    (hs : ∀ p, Tendsto (fun h => ∫ x, (Yp (reY (G h)) p x - Yp (reY G₀) p x) ^ 2 ∂ν) atTop (𝓝 0))
    (c : Fin m) (μ : Fin 4) :
    Tendsto (fun h => eLpNorm (G h c μ - G₀ c μ) 2 ν) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_integral (fun h => (hG h c μ).sub (hG₀ c μ)) ?_
  have hre : Tendsto (fun h => ∫ x, ((G h c μ x).re - (G₀ c μ x).re) ^ 2 ∂ν) atTop (𝓝 0) :=
    hs (μ, (c, 0))
  have him : Tendsto (fun h => ∫ x, ((G h c μ x).im - (G₀ c μ x).im) ^ 2 ∂ν) atTop (𝓝 0) :=
    hs (μ, (c, 1))
  have := hre.add him
  rw [add_zero] at this
  refine this.congr fun h => ?_
  have i0 : Integrable (fun x => ((G h c μ x).re - (G₀ c μ x).re) ^ 2) ν :=
    ((hG h c μ).re.sub (hG₀ c μ).re).integrable_sq
  have i1 : Integrable (fun x => ((G h c μ x).im - (G₀ c μ x).im) ^ 2) ν :=
    ((hG h c μ).im.sub (hG₀ c μ).im).integrable_sq
  rw [← integral_add i0 i1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem tendsto_integral_Hvec_pow_four {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {H : ℕ → Fin m → X → ℂ} {H₀ : Fin m → X → ℂ} (hH : ∀ h c, MemLp (H h c) 4 ν)
    (hH₀ : ∀ c, MemLp (H₀ c) 4 ν)
    (hlim : ∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 4 ν) atTop (𝓝 0)) :
    Tendsto (fun h => ∫ x, ‖Hvec (H h) x - Hvec H₀ x‖ ^ 4 ∂ν) atTop (𝓝 0) := by
  have hd : ∀ h c, MemLp (H h c - H₀ c) 4 ν := fun h c => (hH h c).sub (hH₀ c)
  have hc : ∀ c, Tendsto (fun h => ∫ x, ‖(H h c - H₀ c) x‖ ^ 4 ∂ν) atTop (𝓝 0) := by
    intro c
    simp only [integral_norm_pow_four_eq (hd _ c)]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim c)
    simpa using this.pow 4
  have hpt : ∀ h x, ‖Hvec (H h) x - Hvec H₀ x‖ ^ 4 ≤ m * ∑ c, ‖(H h c - H₀ c) x‖ ^ 4 := by
    intro h x
    have e : Hvec (H h) x - Hvec H₀ x = toE fun c => (H h c - H₀ c) x := by
      ext c; simp [Hvec]
    rw [e, show ‖toE fun c => (H h c - H₀ c) x‖ ^ 4 = (‖toE fun c => (H h c - H₀ c) x‖ ^ 2) ^ 2 by
      ring, norm_toE_sq]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c => ‖(H h c - H₀ c) x‖ ^ 2)
    simpa [Finset.card_univ, ← pow_mul] using this
  have hsum : Tendsto (fun h => (m : ℝ) * ∑ c, ∫ x, ‖(H h c - H₀ c) x‖ ^ 4 ∂ν) atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum _ fun c _ => hc c).const_mul (m : ℝ)
  refine squeeze_zero (fun h => integral_nonneg fun x => by positivity) (fun h => ?_) hsum
  rw [← integral_finsetSum _ fun c _ => integrable_norm_pow_four (hd h c), ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
    ((integrable_finsetSum _ fun c _ => integrable_norm_pow_four (hd h c)).const_mul _)
    (Eventually.of_forall (hpt h))

/-- Weak `L²(Q)` convergence of the components gives convergence of all test pairings (the form
used by `SobolevOpen.tendsto_L2_box_of_weak`). -/
theorem test_pairing_of_weak {H : ℕ → (Fin 4 → ℝ) → ℂ} {H₀ : (Fin 4 → ℝ) → ℂ}
    (hw : ∀ w : (Fin 4 → ℝ) → ℂ, MemLp w 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, w x * H h x ∂(boxμ a b)) atTop (𝓝 (∫ x, w x * H₀ x ∂(boxμ a b))))
    (φ : (Fin 4 → ℝ) → ℝ) (hφ : SobolevOpen.IsTest (SobolevOpen.box a b) φ) :
    Tendsto (fun h => ∫ x, ((φ x : ℝ) : ℂ) * H h x) atTop (𝓝 (∫ x, ((φ x : ℝ) : ℂ) * H₀ x)) := by
  obtain ⟨Cφ, hCφ⟩ := hφ.continuous.bounded_above_of_compact_support hφ.compact
  have hm : MemLp (fun x => ((φ x : ℝ) : ℂ)) 2 (boxμ a b) :=
    MemLp.of_bound (Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable Cφ
      (Eventually.of_forall fun x => by simpa using hCφ x)
  have e : ∀ G : (Fin 4 → ℝ) → ℂ, ∫ x, ((φ x : ℝ) : ℂ) * G x =
      ∫ x, ((φ x : ℝ) : ℂ) * G x ∂(boxμ a b) := by
    intro G
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφ.subset h)
    simp [this]
  simp only [e]
  exact hw _ hm

/-- **`cor:independent-bosonic-certificates`, box rendering, composed with the proved
`prop:covariant-higgs-endpoint`.**  Under the hypotheses of `zero_defect_characterization_box`,
with the covariant gradient `D_{A_h}H_h` itself as the realified gradient packet (identified weak
limit `D_AH`), `H_h ⇀ H` weakly in `H¹(Q)` (componentwise) and `A_h → A` in `L⁴(Q)`: along the
extracted sequence `μ_{∇H} = 0` implies `H_h → H` in `H¹(Q)` (components and weak partials in
`L²(Q)`) and in `L⁴(Q)`, hence `ν_H = 0`; and `μ_{YM} = μ_{∇H} = 0` is necessary and sufficient
for the zero-defect branch `𝔖_{YM} + 𝔖_H = 0`. -/
theorem independent_bosonic_certificates_box (hab : ∀ i, a i < b i)
    {g : ℕ → MetricField (Icc a b)} {g₀ : MetricField (Icc a b)} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(Icc a b, Fin 4 → ℝ)}
    (hsig : ∀ x, ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      mat (g₀ x) = Matrix.transpose P * eta * P)
    (hunit : ∀ x, gnn (g₀ x) (n x) = -1)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hw₀ : ∀ a, 0 < w₀ a)
    {F : ℕ → Fin 4 → Fin 4 → κG → (Fin 4 → ℝ) → ℝ} {F₀ : Fin 4 → Fin 4 → κG → (Fin 4 → ℝ) → ℝ}
    (hF : BoxWeakL2 a b (fun h => Fp (F h)) (Fp F₀))
    (hFa : ∀ h α β c x, F h β α c x = -F h α β c x) (hFa₀ : ∀ α β c x, F₀ β α c x = -F₀ α β c x)
    {H : ℕ → Fin m → (Fin 4 → ℝ) → ℂ} {gH : ℕ → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    {H₀ : Fin m → (Fin 4 → ℝ) → ℂ} {gH₀ : Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hW : ∀ h c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H h c) (gH h c))
    (hW₀ : ∀ c, SobolevOpen.MemW12 (SobolevOpen.box a b) (H₀ c) (gH₀ c)) {B : ℝ≥0∞}
    (hBt : B ≠ ⊤) (hB : ∀ h c, SobolevOpen.w12Norm (SobolevOpen.box a b) (H h c) (gH h c) ≤ B)
    (hweakH : ∀ c (w : (Fin 4 → ℝ) → ℂ), MemLp w 2 (boxμ a b) →
      Tendsto (fun h => ∫ x, w x * H h c x ∂(boxμ a b)) atTop (𝓝 (∫ x, w x * H₀ c x ∂(boxμ a b))))
    (hae : ∀ᵐ x ∂(boxμ a b), ∀ c, Tendsto (fun h => H h c x) atTop (𝓝 (H₀ c x)))
    {A : ℕ → Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ} {A₀ : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (hA : ∀ h μ c e, MemLp (A h μ c e) 4 (boxμ a b)) (hA₀ : ∀ μ c e, MemLp (A₀ μ c e) 4 (boxμ a b))
    (hAlim : ∀ μ c e, Tendsto (fun h => eLpNorm (A h μ c e - A₀ μ c e) 4 (boxμ a b)) atTop (𝓝 0))
    (hY : BoxWeakL2 a b
      (fun h => Yp (reY fun c μ => SobolevOpen.covD (gH h) (A h) (H h) c μ))
      (Yp (reY fun c μ => SobolevOpen.covD gH₀ A₀ H₀ c μ)))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) (hlam₀ : 0 < lam₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ (SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Icc a b, ℝ))
      (μYM μH ν : StrongDual ℝ C(Icc a b, ℝ)),
      IsYMDefect (V0 a b) g g₀ w w₀ (fun h => pullF (F h)) (pullF F₀) σ SYM ∧
      IsHiggsDefect (V0 a b) g g₀ lam vH lam₀ vH₀
        (fun h => pullY (reY fun c μ => SobolevOpen.covD (gH h) (A h) (H h) c μ))
        (pullY (reY fun c μ => SobolevOpen.covD gH₀ A₀ H₀ c μ))
        (fun h => pullH (H h)) (pullH H₀) σ SH ∧
      (∀ φ : C(Icc a b, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Fp (pullF (F (σ h))) p x ^ 2
        ∂(V0 a b)) atTop (𝓝 (∫ x, φ x * ∑ p, Fp (pullF F₀) p x ^ 2 ∂(V0 a b) + μYM φ))) ∧
      (∀ φ : C(Icc a b, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p,
        Yp (pullY (reY fun c μ => SobolevOpen.covD (gH (σ h)) (A (σ h)) (H (σ h)) c μ)) p x ^ 2
        ∂(V0 a b)) atTop (𝓝 (∫ x, φ x * ∑ p,
          Yp (pullY (reY fun c μ => SobolevOpen.covD gH₀ A₀ H₀ c μ)) p x ^ 2 ∂(V0 a b) + μH φ))) ∧
      IsQuarticDefect (V0 a b) g g₀ (fun h => pullH (H h)) (pullH H₀) σ ν ∧
      (μH = 0 →
        (∀ c, Tendsto (fun h => eLpNorm (H (σ h) c - H₀ c) 2 (boxμ a b)) atTop (𝓝 0)) ∧
        (∀ c i, Tendsto (fun h => eLpNorm (gH (σ h) c i - gH₀ c i) 2 (boxμ a b)) atTop (𝓝 0)) ∧
        (∀ c, Tendsto (fun h => eLpNorm (H (σ h) c - H₀ c) 4 (boxμ a b)) atTop (𝓝 0)) ∧
        ν = 0) ∧
      (μYM = 0 ∧ μH = 0 ↔ ∀ μ ν', SYM μ ν' + SH μ ν' = 0) := by
  obtain ⟨σ, hσ, SYM, SH, μYM, μH, ν, h1, h2, h3, h4, h5, -, hAB, hBC, -, -, hμH, hνiff⟩ :=
    zero_defect_characterization_box hab hg hdet hdet₀ hsig hunit hw hw₀ hF hFa hFa₀ hW hBt hB hae
      hY hlam hvH hlam₀
  have hσt := hσ.tendsto_atTop
  -- the covariant gradients are `L²` fields
  have hcov : ∀ h c μ, MemLp (SobolevOpen.covD (gH h) (A h) (H h) c μ) 2 (boxμ a b) := by
    intro h c μ
    have hre : MemLp (fun x => (SobolevOpen.covD (gH h) (A h) (H h) c μ x).re) 2 (boxμ a b) :=
      hY.1 h (μ, (c, 0))
    have him : MemLp (fun x => (SobolevOpen.covD (gH h) (A h) (H h) c μ x).im) 2 (boxμ a b) :=
      hY.1 h (μ, (c, 1))
    refine (hre.norm.add him.norm).of_le ?_ (Eventually.of_forall fun x => ?_)
    · exact SobolevOpen.aestronglyMeasurable_covD (fun c μ => ((hW h c).memLp_grad μ).1)
        (fun μ c e => (hA h μ c e).1) (fun e => (hW h e).memLp.1) c μ
    · simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact Complex.norm_le_abs_re_add_abs_im _
  have hcov₀ : ∀ c μ, MemLp (SobolevOpen.covD gH₀ A₀ H₀ c μ) 2 (boxμ a b) := by
    intro c μ
    have hre : MemLp (fun x => (SobolevOpen.covD gH₀ A₀ H₀ c μ x).re) 2 (boxμ a b) :=
      hY.2.1 (μ, (c, 0))
    have him : MemLp (fun x => (SobolevOpen.covD gH₀ A₀ H₀ c μ x).im) 2 (boxμ a b) :=
      hY.2.1 (μ, (c, 1))
    refine (hre.norm.add him.norm).of_le ?_ (Eventually.of_forall fun x => ?_)
    · exact SobolevOpen.aestronglyMeasurable_covD (fun c μ => ((hW₀ c).memLp_grad μ).1)
        (fun μ c e => (hA₀ μ c e).1) (fun e => (hW₀ e).memLp.1) c μ
    · simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact Complex.norm_le_abs_re_add_abs_im _
  have hL2full : ∀ c, Tendsto (fun h => eLpNorm (H h c - H₀ c) 2 (boxμ a b)) atTop (𝓝 0) :=
    fun c => SobolevOpen.tendsto_L2_box_of_weak hab (fun h => H h c) (fun h => gH h c) (H₀ c)
      (fun h => hW h c) hBt (fun h => hB h c) (hW₀ c).memLp (test_pairing_of_weak (hweakH c))
  have hcert : μH = 0 →
      (∀ c, Tendsto (fun h => eLpNorm (H (σ h) c - H₀ c) 2 (boxμ a b)) atTop (𝓝 0)) ∧
      (∀ c i, Tendsto (fun h => eLpNorm (gH (σ h) c i - gH₀ c i) 2 (boxμ a b)) atTop (𝓝 0)) ∧
      (∀ c, Tendsto (fun h => eLpNorm (H (σ h) c - H₀ c) 4 (boxμ a b)) atTop (𝓝 0)) ∧
      ν = 0 := by
    intro h0
    have hs := hμH.1 h0
    have hYlim : ∀ c μ, Tendsto (fun h => eLpNorm (SobolevOpen.covD (gH (σ h)) (A (σ h)) (H (σ h)) c μ
        - SobolevOpen.covD gH₀ A₀ H₀ c μ) 2 (boxμ a b)) atTop (𝓝 0) :=
      tendsto_eLpNorm_of_reY (G := fun h c μ => SobolevOpen.covD (gH (σ h)) (A (σ h)) (H (σ h)) c μ)
        (fun h => hcov (σ h)) hcov₀ hs
    obtain ⟨-, hgrad, hL4⟩ := SobolevOpen.covariant_higgs_endpoint_box_of_L2 (ι := Fin 4)
      (by simp) hab (fun h => H (σ h)) (fun h => gH (σ h)) (fun h => A (σ h)) A₀
      (fun c μ => SobolevOpen.covD gH₀ A₀ H₀ c μ) (fun h => hW (σ h)) (fun h => hA (σ h)) hA₀
      (fun μ c e => (hAlim μ c e).comp hσt) hBt
      (fun h c => (le_self_add).trans (hB (σ h) c)) hcov₀ hYlim H₀ (fun c => (hW₀ c).memLp)
      (fun c => (hL2full c).comp hσt)
    have hcg : ∀ c μ, SobolevOpen.covGrad (fun c μ => SobolevOpen.covD gH₀ A₀ H₀ c μ) A₀ H₀ c μ =
        gH₀ c μ := by
      intro c μ; funext x; simp [SobolevOpen.covGrad, SobolevOpen.covD]
    simp only [hcg] at hgrad
    refine ⟨fun c => (hL2full c).comp hσt, hgrad, hL4, hνiff.2 ?_⟩
    obtain ⟨CS, hCS⟩ := SobolevOpen.exists_sobolev_L4_box (ι := Fin 4) (by simp) hab
    have hH4 : ∀ h c, MemLp (H h c) 4 (boxμ a b) := fun h c =>
      ⟨(hW h c).memLp.1, (hCS _ _ (hW h c)).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
        ((hB h c).trans_lt hBt.lt_top))⟩
    have hH₀4 : ∀ c, MemLp (H₀ c) 4 (boxμ a b) := fun c =>
      ⟨(hW₀ c).memLp.1, (hCS _ _ (hW₀ c)).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
        (by
          simp only [SobolevOpen.w12Norm]
          exact ENNReal.add_lt_top.2 ⟨(hW₀ c).memLp.2,
            ENNReal.sum_lt_top.2 fun i _ => ((hW₀ c).memLp_grad i).2⟩))⟩
    exact tendsto_integral_Hvec_pow_four (fun h => hH4 (σ h)) hH₀4 hL4
  refine ⟨σ, hσ, SYM, SH, μYM, μH, ν, h1, h2, h3, h4, h5, hcert, ?_, ?_⟩
  · rintro ⟨e1, e2⟩
    exact hAB.2 (hBC.2 ⟨e1, e2, (hcert e2).2.2.2⟩)
  · intro hA'
    obtain ⟨e1, e2, -⟩ := hBC.1 (hAB.1 hA')
    exact ⟨e1, e2⟩

end CorBox
end BosonicStressDefectBox

end RenewalGeometry
