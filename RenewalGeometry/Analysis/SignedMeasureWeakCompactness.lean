/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorMeasureWeakCompactness

/-!
# Weak-* compactness of bounded signed and vector-valued measures, density measures,
  and weak/strong `Lᵖ` identification of their limits

Generic measure theory (no renewal notions), built for the measure-valued stress defects of the
Einstein–Standard-Model action-closure manuscript (`lem:critical-cubic`, `thm:higgs-defect`,
`prop:YM-defect`, `thm:zero-defect-characterization`).

## Signed and vector measures as functionals

On a compact metric space `K` (a compact chart with its boundary, or `𝕋^d`) a finite signed Radon
measure is encoded, through the Riesz–Markov identification, as a continuous linear functional on
`C(K, ℝ)`, and a finite tensor-valued measure as a finite family of these.  This is the encoding of
`PositivePacketDefectExact.lean` and `DefectConservationTransportExact.lean`.

* `exists_subseq_weakStar_tendsto_family`: **sequential Banach–Alaoglu** for finitely many
  uniformly bounded sequences of functionals on a separable normed space (one common subsequence).
* `densityCLM V₀ f`: the measure `f dV₀` (`φ ↦ ∫ φ f dV₀`), of norm `≤ ∫ |f| dV₀`.
* `exists_subseq_density_tendsto_family`: uniformly `L¹`-bounded densities `f_{h,i} dV₀` have a
  common weak-* convergent subsequence (vector/tensor-valued measures componentwise).
* `tendsto_density_of_tendsto_L1`: if `f_h → f` in `L¹` the weak-* limit is `f dV₀`.
* `tendsto_density_mul_of_tendsto`: weak-* convergence with bounded mass survives multiplication
  by uniformly convergent continuous coefficients `c_h → c` (the limit is `c · Λ`).

## Signed measures through the Jordan decomposition

* `exists_subseq_tendsto_jordan_family`: on a compact metrizable space, finitely many sequences of
  signed measures with uniformly bounded positive and negative parts have a common subsequence
  along which both Jordan parts converge weakly, hence `∫ φ ds_h → ∫ φ dμ⁺ - ∫ φ dμ⁻` for every
  bounded continuous `φ` (positive-measure compactness `exists_subseq_tendsto_family` of
  `OperatorMeasureWeakCompactness.lean` applied to the Jordan parts).

## Identification of weak limits through almost-everywhere convergence

* `memLp_of_ae_tendsto` (Fatou): an a.e. limit of an `Lᵖ`-bounded sequence is in `Lᵖ`.
* `tendsto_integral_inner_of_ae` (**weak `Lᵖ` identification**, `1 < p < ∞`): an `Lᵖ`-bounded,
  a.e. convergent sequence converges weakly in `Lᵖ` to its a.e. limit: `∫ ⟪v, u_h⟫ → ∫ ⟪v, u⟫` for
  every `v ∈ L^q`, `1/p + 1/q = 1` (Hölder + Vitali; `unifIntegrable_inner`);
  `tendsto_integral_mul_of_ae` is the scalar form.

## Radon–Riesz in `L⁴` (uniform convexity)

* `norm_add_pow_four_add_norm_sub_pow_four_le` (Clarkson, `p = 4`):
  `‖a + b‖⁴ + ‖a - b‖⁴ ≤ 8(‖a‖⁴ + ‖b‖⁴)`; `four_mul_inner_le` (convexity at `b`):
  `4‖b‖²⟪b, a⟫ ≤ ‖a‖⁴ + 3‖b‖⁴`; together `norm_sub_pow_four_le`:
  `‖a - b‖⁴ ≤ 8‖a‖⁴ - 32‖b‖²⟪b, a⟫ + 24‖b‖⁴`.
* `tendsto_integral_weighted_norm_sub_pow_four`: for a weight `ω ≥ 0`, weak convergence tested on
  `ω ‖u‖² u` plus convergence of `∫ ω ‖u_h‖⁴` give `∫ ω ‖u_h - u‖⁴ → 0`.
* `tendsto_integral_norm_sub_pow_four_of_weak` (**Radon–Riesz in `L⁴`**): weak `L⁴` convergence
  (tested on `L^{4/3}`) plus convergence of the `L⁴` norms gives strong `L⁴` convergence
  (`holderConjugate_four`, `memLp_weight_norm_sq_smul`: `‖u‖² u ∈ L^{4/3}`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace RenewalGeometry

namespace SignedMeasureWeakCompactness

/-! ## Sequential Banach–Alaoglu for finite families -/

section BanachAlaoglu

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace.SeparableSpace F]

/-- **Sequential Banach–Alaoglu**: a uniformly bounded sequence of functionals on a separable
normed space has a weak-* convergent subsequence. -/
theorem exists_subseq_weakStar_tendsto (Λ : ℕ → StrongDual ℝ F) {C : ℝ}
    (hC : ∀ h, ‖Λ h‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ L : StrongDual ℝ F,
      ∀ e, Tendsto (fun h => Λ (σ h) e) atTop (𝓝 (L e)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set ρ : ℝ := 1 / (C + 1)
  have hρ : 0 < ρ := by positivity
  let ℓ : ℕ → WeakDual ℝ F := fun h => StrongDual.toWeakDual (Λ h)
  have hmem : ∀ h, ℓ h ∈ WeakDual.polar ℝ (Metric.ball (0 : F) ρ) := by
    intro h
    rw [WeakDual.polar_def]
    intro e he
    rw [mem_ball_zero_iff] at he
    change ‖Λ h e‖ ≤ 1
    calc ‖Λ h e‖ ≤ ‖Λ h‖ * ‖e‖ := (Λ h).le_opNorm e
      _ ≤ C * ρ := by gcongr; exact hC h
      _ ≤ (C + 1) * ρ := by gcongr; linarith
      _ = 1 := by simp only [ρ]; field_simp
  obtain ⟨L, -, σ, hσ, hlim⟩ :=
    WeakDual.isSeqCompact_polar ℝ F (Metric.ball_mem_nhds (0 : F) hρ) hmem
  exact ⟨σ, hσ, WeakDual.toStrongDual L, fun e =>
    ((WeakDual.eval_continuous e).tendsto L).comp hlim⟩

/-- **Sequential Banach–Alaoglu for finite families**: finitely many uniformly bounded sequences of
functionals have one common weak-* convergent subsequence. -/
theorem exists_subseq_weakStar_tendsto_family {ι : Type*} [Fintype ι]
    (Λ : ℕ → ι → StrongDual ℝ F) {C : ℝ} (hC : ∀ h i, ‖Λ h i‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ L : ι → StrongDual ℝ F,
      ∀ i e, Tendsto (fun h => Λ (σ h) i e) atTop (𝓝 (L i e)) := by
  classical
  -- combine the family into one functional on `ι → F`
  let T : ℕ → StrongDual ℝ (ι → F) := fun h =>
    ∑ i, (Λ h i).comp (ContinuousLinearMap.proj i)
  have hT : ∀ h, ‖T h‖ ≤ ∑ _i : ι, C := by
    intro h
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine ((Λ h i).opNorm_comp_le _).trans ?_
    calc ‖Λ h i‖ * ‖(ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)‖ ≤ C * 1 := by
          gcongr
          · exact (norm_nonneg _).trans (hC h i)
          · exact hC h i
          · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
              simpa using norm_le_pi_norm x i
      _ = C := mul_one C
  obtain ⟨σ, hσ, L, hL⟩ := exists_subseq_weakStar_tendsto T hT
  refine ⟨σ, hσ, fun i => L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => F) i),
    fun i e => ?_⟩
  have key : ∀ h, T (σ h) (Pi.single i e) = Λ (σ h) i e := by
    intro h
    simp only [T, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  simp_rw [← key]
  exact hL _

end BanachAlaoglu

/-! ## Density measures `f dV₀` on a compact metric space -/

section Density

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable (V₀ : Measure K)

theorem integrable_mul_density (φ : C(K, ℝ)) {f : K → ℝ} (hf : Integrable f V₀) :
    Integrable (fun x => φ x * f x) V₀ :=
  hf.bdd_mul φ.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => φ.norm_coe_le_norm x)

theorem abs_integral_mul_le (φ : C(K, ℝ)) {f : K → ℝ} (hf : Integrable f V₀) :
    |∫ x, φ x * f x ∂V₀| ≤ ‖φ‖ * ∫ x, |f x| ∂V₀ := by
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.abs.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs (f x)]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (abs_nonneg _)

/-- The finite signed measure `f dV₀` as a functional `φ ↦ ∫ φ f dV₀` on `C(K, ℝ)` (zero if `f`
is not integrable). -/
noncomputable def densityCLM (f : K → ℝ) : StrongDual ℝ C(K, ℝ) := by
  classical
  exact if hf : Integrable f V₀ then
    LinearMap.mkContinuous
      { toFun := fun φ => ∫ x, φ x * f x ∂V₀
        map_add' := fun φ ψ => by
          simp only [ContinuousMap.add_apply, add_mul]
          exact integral_add (integrable_mul_density V₀ φ hf) (integrable_mul_density V₀ ψ hf)
        map_smul' := fun c φ => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
          exact integral_const_mul c _ }
      (∫ x, |f x| ∂V₀) fun φ => by
        rw [Real.norm_eq_abs, mul_comm]
        exact abs_integral_mul_le V₀ φ hf
  else 0

theorem densityCLM_apply {f : K → ℝ} (hf : Integrable f V₀) (φ : C(K, ℝ)) :
    densityCLM V₀ f φ = ∫ x, φ x * f x ∂V₀ := by
  simp [densityCLM, hf]

theorem norm_densityCLM_le {f : K → ℝ} (hf : Integrable f V₀) :
    ‖densityCLM V₀ f‖ ≤ ∫ x, |f x| ∂V₀ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => abs_nonneg _) fun φ => ?_
  rw [densityCLM_apply V₀ hf, Real.norm_eq_abs, mul_comm]
  exact abs_integral_mul_le V₀ φ hf

/-- **Weak-* compactness of uniformly `L¹`-bounded density measures** (finite families, i.e.
vector- or tensor-valued measures componentwise): if `∫ |f_{h,i}| dV₀ ≤ M`, a common subsequence
and finite signed Radon measures `Λ_i` exist with `f_{σ h, i} dV₀ ⇀* Λ_i`. -/
theorem exists_subseq_density_tendsto_family {ι : Type*} [Fintype ι] (f : ℕ → ι → K → ℝ)
    (hf : ∀ h i, Integrable (f h i) V₀) {M : ℝ} (hM : ∀ h i, ∫ x, |f h i x| ∂V₀ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Λ : ι → StrongDual ℝ C(K, ℝ),
      ∀ i (φ : C(K, ℝ)), Tendsto (fun h => ∫ x, φ x * f (σ h) i x ∂V₀) atTop (𝓝 (Λ i φ)) := by
  obtain ⟨σ, hσ, Λ, hΛ⟩ := exists_subseq_weakStar_tendsto_family
    (fun h i => densityCLM V₀ (f h i)) (fun h i => (norm_densityCLM_le V₀ (hf h i)).trans (hM h i))
  refine ⟨σ, hσ, Λ, fun i φ => ?_⟩
  simpa only [densityCLM_apply V₀ (hf _ _)] using hΛ i φ

/-- Single-sequence form of `exists_subseq_density_tendsto_family`. -/
theorem exists_subseq_density_tendsto (f : ℕ → K → ℝ)
    (hf : ∀ h, Integrable (f h) V₀) {M : ℝ} (hM : ∀ h, ∫ x, |f h x| ∂V₀ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Λ : StrongDual ℝ C(K, ℝ),
      ∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * f (σ h) x ∂V₀) atTop (𝓝 (Λ φ)) := by
  obtain ⟨σ, hσ, Λ, hΛ⟩ := exists_subseq_density_tendsto_family V₀ (fun h (_ : Unit) => f h)
    (fun h _ => hf h) (fun h _ => hM h)
  exact ⟨σ, hσ, Λ (), fun φ => hΛ () φ⟩

/-- **Identification under strong `L¹` convergence**: if `∫ |f_h - f| dV₀ → 0`, then
`f_h dV₀ ⇀* f dV₀`. -/
theorem tendsto_density_of_tendsto_L1 {f : ℕ → K → ℝ} {f₀ : K → ℝ}
    (hf : ∀ h, Integrable (f h) V₀) (hf₀ : Integrable f₀ V₀)
    (hL1 : Tendsto (fun h => ∫ x, |f h x - f₀ x| ∂V₀) atTop (𝓝 0)) (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * f h x ∂V₀) atTop (𝓝 (∫ x, φ x * f₀ x ∂V₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) (by simpa using hL1.const_mul ‖φ‖)
  rw [← integral_sub (integrable_mul_density V₀ φ (hf h)) (integrable_mul_density V₀ φ hf₀),
    Real.norm_eq_abs]
  have := abs_integral_mul_le V₀ φ ((hf h).sub hf₀)
  simp only [Pi.sub_apply, mul_sub] at this
  exact this

/-- **Coefficient replacement**: weak-* convergence `f_h dV₀ ⇀* Λ` with bounded mass survives
multiplication by uniformly convergent continuous coefficients: `c_h f_h dV₀ ⇀* c Λ`. -/
theorem tendsto_density_mul_of_tendsto {f : ℕ → K → ℝ} (hf : ∀ h, Integrable (f h) V₀)
    {M : ℝ} (hM : ∀ h, ∫ x, |f h x| ∂V₀ ≤ M) {Λ : StrongDual ℝ C(K, ℝ)}
    (hΛ : ∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * f h x ∂V₀) atTop (𝓝 (Λ φ)))
    {c : ℕ → C(K, ℝ)} {c₀ : C(K, ℝ)} (hc : Tendsto c atTop (𝓝 c₀)) (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * (c h x * f h x) ∂V₀) atTop (𝓝 (Λ (φ * c₀))) := by
  have hsmall : Tendsto (fun h => ∫ x, (φ * (c h - c₀)) x * f h x ∂V₀) atTop (𝓝 0) := by
    have hd : Tendsto (fun h => ‖φ * (c h - c₀)‖) atTop (𝓝 0) := by
      have : Tendsto (fun h => φ * (c h - c₀)) atTop (𝓝 (φ * (c₀ - c₀))) :=
        tendsto_const_nhds.mul (hc.sub tendsto_const_nhds)
      rw [sub_self, mul_zero] at this
      simpa using this.norm
    refine squeeze_zero_norm (fun h => ?_) (by simpa using hd.mul_const M)
    rw [Real.norm_eq_abs]
    exact (abs_integral_mul_le V₀ _ (hf h)).trans
      (mul_le_mul_of_nonneg_left (hM h) (norm_nonneg _))
  have hsum := hsmall.add (hΛ (φ * c₀))
  rw [zero_add] at hsum
  refine hsum.congr fun h => ?_
  rw [← integral_add (integrable_mul_density V₀ _ (hf h)) (integrable_mul_density V₀ _ (hf h))]
  congr 1
  funext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply]
  ring

end Density

/-! ## Signed measures on a compact metrizable space via the Jordan decomposition -/

section Jordan

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [TopologicalSpace.SeparableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X]

/-- **Sequential weak-* compactness of bounded signed (and, componentwise, vector- or
tensor-valued) measures** on a compact metrizable space: if the total variations
`|s_{h,i}|(X) ≤ M` are uniformly bounded, a common subsequence and finite measures `μ⁺_i, μ⁻_i`
exist with `s_{σ h, i}⁺ ⇀ μ⁺_i`, `s_{σ h, i}⁻ ⇀ μ⁻_i` weakly; in particular
`∫ φ ds_{σ h, i} = ∫ φ ds⁺ - ∫ φ ds⁻ → ∫ φ dμ⁺_i - ∫ φ dμ⁻_i` for every bounded continuous `φ`,
i.e. `s_{σ h, i} ⇀* μ⁺_i - μ⁻_i`.  Proof: the positive-measure compactness
`OperatorMeasureL2.exists_subseq_tendsto_family` applied to the Jordan parts. -/
theorem exists_subseq_tendsto_jordan_family {ι : Type*} [Fintype ι]
    (s : ℕ → ι → SignedMeasure X) {M : ℝ≥0}
    (hM : ∀ h i, (s h i).totalVariation univ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ μp μn : ι → FiniteMeasure X,
      ∀ i (φ : X →ᵇ ℝ),
        Tendsto (fun h => ∫ x, φ x ∂(s (σ h) i).toJordanDecomposition.posPart) atTop
          (𝓝 (∫ x, φ x ∂(μp i : Measure X))) ∧
        Tendsto (fun h => ∫ x, φ x ∂(s (σ h) i).toJordanDecomposition.negPart) atTop
          (𝓝 (∫ x, φ x ∂(μn i : Measure X))) ∧
        Tendsto (fun h => ∫ x, φ x ∂(s (σ h) i).toJordanDecomposition.posPart -
            ∫ x, φ x ∂(s (σ h) i).toJordanDecomposition.negPart) atTop
          (𝓝 (∫ x, φ x ∂(μp i : Measure X) - ∫ x, φ x ∂(μn i : Measure X))) := by
  let m : ℕ → ι × Bool → FiniteMeasure X := fun h ib =>
    if ib.2 then ⟨(s h ib.1).toJordanDecomposition.posPart, inferInstance⟩
    else ⟨(s h ib.1).toJordanDecomposition.negPart, inferInstance⟩
  have hmass : ∀ h ib, (m h ib).mass ≤ M := by
    intro h ⟨i, b⟩
    have htv : (s h i).totalVariation univ =
        (s h i).toJordanDecomposition.posPart univ +
          (s h i).toJordanDecomposition.negPart univ := rfl
    have hle : (m h (i, b) : Measure X) univ ≤ M := by
      refine le_trans ?_ (hM h i)
      rw [htv]
      cases b
      · exact le_add_self
      · exact le_self_add
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hle
  obtain ⟨σ, hσ, mlim, hlim⟩ := OperatorMeasureL2.exists_subseq_tendsto_family m hmass
  refine ⟨σ, hσ, fun i => mlim (i, true), fun i => mlim (i, false), fun i φ => ?_⟩
  have hp := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hlim (i, true))) φ
  have hn := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hlim (i, false))) φ
  simp only [m, Bool.false_eq_true, ↓reduceIte] at hp hn
  exact ⟨hp, hn, hp.sub hn⟩

end Jordan

/-! ## Weak `Lᵖ` identification through almost-everywhere convergence -/

section WeakLp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Fatou for `Lᵖ` norms**: the a.e. limit of a sequence bounded in `Lᵖ` lies in `Lᵖ`, with the
same bound. -/
theorem memLp_of_ae_tendsto {p : ℝ≥0∞} {u : ℕ → α → E} {u₀ : α → E}
    (hu : ∀ h, AEStronglyMeasurable (u h) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun h => u h x) atTop (𝓝 (u₀ x)))
    {C : ℝ≥0} (hC : ∀ h, eLpNorm (u h) p μ ≤ C) : MemLp u₀ p μ ∧ eLpNorm u₀ p μ ≤ C := by
  have hm : AEStronglyMeasurable u₀ μ := aestronglyMeasurable_of_tendsto_ae atTop hu hae
  have hb : eLpNorm u₀ p μ ≤ C := (Lp.eLpNorm_lim_le_liminf_eLpNorm hu u₀ hae).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall hC))
  exact ⟨⟨hm, hb.trans_lt ENNReal.coe_lt_top⟩, hb⟩

/-- Hölder for the pointwise inner product: `‖⟪v, u⟫‖_{L¹} ≤ ‖v‖_{L^q} ‖u‖_{L^p}`. -/
theorem eLpNorm_inner_le {p q : ℝ≥0∞} [hpq : p.HolderConjugate q] {v u : α → E}
    (hv : AEStronglyMeasurable v μ) (hu : AEStronglyMeasurable u μ) :
    eLpNorm (fun x => ⟪v x, u x⟫) 1 μ ≤ eLpNorm v q μ * eLpNorm u p μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := q) (q := p) (r := 1) hv hu
    (fun a b => ⟪a, b⟫) 1 (Eventually.of_forall fun x => by
      simpa using nnnorm_inner_le_nnnorm (v x) (u x))
  simpa using this

/-- An `Lᵖ`-bounded sequence paired with a fixed `L^q` function is uniformly integrable. -/
theorem unifIntegrable_inner {p q : ℝ≥0∞} [hpq : p.HolderConjugate q] (hq : q ≠ ∞)
    {u : ℕ → α → E} (hu : ∀ h, AEStronglyMeasurable (u h) μ) {C : ℝ≥0}
    (hC : ∀ h, eLpNorm (u h) p μ ≤ C) {v : α → E} (hv : MemLp v q μ) :
    UnifIntegrable (fun h x => ⟪v x, u h x⟫) 1 μ := by
  intro ε hε
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  have hε' : 0 < ε / ((C : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδv⟩ := unifIntegrable_const (ι := Unit) hq1 hq hv hε'
  refine ⟨δ, hδ, fun h s hs hμs => ?_⟩
  have h1 : (s.indicator fun x => ⟪v x, u h x⟫) = fun x => ⟪s.indicator v x, u h x⟫ := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  rw [h1]
  calc eLpNorm (fun x => ⟪s.indicator v x, u h x⟫) 1 μ
      ≤ eLpNorm (s.indicator v) q μ * eLpNorm (u h) p μ :=
        eLpNorm_inner_le (hv.1.indicator hs) (hu h)
    _ ≤ ENNReal.ofReal (ε / ((C : ℝ) + 1)) * ENNReal.ofReal ((C : ℝ) + 1) := by
        gcongr
        · exact hδv () s hs hμs
        · refine (hC h).trans ?_
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hε'.le, div_mul_cancel₀ _ (by positivity)]

/-- **Weak `Lᵖ` identification** (`1 < p < ∞`): on a finite measure space, a sequence bounded in
`Lᵖ` that converges almost everywhere converges weakly in `Lᵖ` to its a.e. limit:
`∫ ⟪v, u_h⟫ → ∫ ⟪v, u⟫` for every `v ∈ L^q`, `1/p + 1/q = 1` (Hölder and Vitali). -/
theorem tendsto_integral_inner_of_ae [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [hpq : p.HolderConjugate q] (hp1 : 1 < p) {u : ℕ → α → E} {u₀ : α → E}
    (hu : ∀ h, AEStronglyMeasurable (u h) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun h => u h x) atTop (𝓝 (u₀ x)))
    {C : ℝ≥0} (hC : ∀ h, eLpNorm (u h) p μ ≤ C) {v : α → E} (hv : MemLp v q μ) :
    Tendsto (fun h => ∫ x, ⟪v x, u h x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪v x, u₀ x⟫ ∂μ)) := by
  have hq : q ≠ ∞ := fun hq => by
    rw [ENNReal.HolderConjugate.eq_top_iff_eq_one q p] at hq
    exact hp1.ne' hq
  obtain ⟨hu₀, -⟩ := memLp_of_ae_tendsto hu hae hC
  have hw : ∀ h, MemLp (fun x => ⟪v x, u h x⟫) 1 μ := fun h =>
    ⟨hv.1.inner (hu h), (eLpNorm_inner_le hv.1 (hu h)).trans_lt
      (ENNReal.mul_lt_top hv.2 ((hC h).trans_lt ENNReal.coe_lt_top))⟩
  have hw₀ : MemLp (fun x => ⟪v x, u₀ x⟫) 1 μ :=
    ⟨hv.1.inner hu₀.1, (eLpNorm_inner_le hv.1 hu₀.1).trans_lt (ENNReal.mul_lt_top hv.2 hu₀.2)⟩
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun h => (hw h).1) hw₀ (unifIntegrable_inner hq hu hC hv)
    (hae.mono fun x hx => (tendsto_const_nhds.inner hx))
  exact tendsto_integral_of_L1' _ hw₀.1
    (Eventually.of_forall fun h => memLp_one_iff_integrable.1 (hw h)) hL1

/-- Scalar form of `tendsto_integral_inner_of_ae`: `∫ ψ f_h → ∫ ψ f` for `ψ ∈ L^q`. -/
theorem tendsto_integral_mul_of_ae [IsFiniteMeasure μ] {p q : ℝ≥0∞}
    [hpq : p.HolderConjugate q] (hp1 : 1 < p) {f : ℕ → α → ℝ} {f₀ : α → ℝ}
    (hf : ∀ h, AEStronglyMeasurable (f h) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun h => f h x) atTop (𝓝 (f₀ x)))
    {C : ℝ≥0} (hC : ∀ h, eLpNorm (f h) p μ ≤ C) {ψ : α → ℝ} (hψ : MemLp ψ q μ) :
    Tendsto (fun h => ∫ x, ψ x * f h x ∂μ) atTop (𝓝 (∫ x, ψ x * f₀ x ∂μ)) := by
  have := tendsto_integral_inner_of_ae hp1 hf hae hC hψ
  simpa [mul_comm] using this

end WeakLp

/-! ## Radon–Riesz in `L⁴` (uniform convexity) -/

section RadonRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Clarkson's inequality for `p = 4` (pointwise): `‖a + b‖⁴ + ‖a - b‖⁴ ≤ 8(‖a‖⁴ + ‖b‖⁴)`. -/
theorem norm_add_pow_four_add_norm_sub_pow_four_le (a b : E) :
    ‖a + b‖ ^ 4 + ‖a - b‖ ^ 4 ≤ 8 * (‖a‖ ^ 4 + ‖b‖ ^ 4) := by
  have h1 : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_add_sq_real a b
  have h2 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_sub_sq_real a b
  have h3 : |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have h4 : ⟪a, b⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have e1 : ‖a + b‖ ^ 4 = (‖a + b‖ ^ 2) ^ 2 := by ring
  have e2 : ‖a - b‖ ^ 4 = (‖a - b‖ ^ 2) ^ 2 := by ring
  rw [e1, e2, h1, h2]
  nlinarith [sq_nonneg (‖a‖ ^ 2 - ‖b‖ ^ 2)]

/-- Convexity (Young) lower bound: `4 ‖b‖² ⟪b, a⟫ ≤ ‖a‖⁴ + 3 ‖b‖⁴`. -/
theorem four_mul_inner_le (a b : E) :
    4 * (‖b‖ ^ 2 * ⟪b, a⟫) ≤ ‖a‖ ^ 4 + 3 * ‖b‖ ^ 4 := by
  have h3 : ⟪b, a⟫ ≤ ‖b‖ * ‖a‖ := real_inner_le_norm b a
  have hb := norm_nonneg b
  have ha := norm_nonneg a
  have : 4 * (‖b‖ ^ 2 * (‖b‖ * ‖a‖)) ≤ ‖a‖ ^ 4 + 3 * ‖b‖ ^ 4 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ + ‖b‖), mul_nonneg ha hb,
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖a‖ - ‖b‖)),
      mul_nonneg (sq_nonneg (‖a‖ - ‖b‖)) (sq_nonneg (‖a‖ + ‖b‖)),
      mul_nonneg (sq_nonneg (‖a‖ - ‖b‖)) (add_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖))]
  have h5 : ‖b‖ ^ 2 * ⟪b, a⟫ ≤ ‖b‖ ^ 2 * (‖b‖ * ‖a‖) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  linarith

/-- **Uniform convexity of `L⁴`, pointwise form**:
`‖a - b‖⁴ ≤ 8‖a‖⁴ - 32 ‖b‖² ⟪b, a⟫ + 24 ‖b‖⁴` (Clarkson plus the convexity bound at
`(a + b)/2`). -/
theorem norm_sub_pow_four_le (a b : E) :
    ‖a - b‖ ^ 4 ≤ 8 * ‖a‖ ^ 4 - 32 * (‖b‖ ^ 2 * ⟪b, a⟫) + 24 * ‖b‖ ^ 4 := by
  have hC := norm_add_pow_four_add_norm_sub_pow_four_le a b
  have hY := four_mul_inner_le ((1 / 2 : ℝ) • (a + b)) b
  have e1 : ‖(1 / 2 : ℝ) • (a + b)‖ ^ 4 = ‖a + b‖ ^ 4 / 16 := by
    rw [norm_smul, mul_pow]; norm_num; ring
  have e2 : ⟪b, (1 / 2 : ℝ) • (a + b)⟫ = (⟪b, a⟫ + ‖b‖ ^ 2) / 2 := by
    rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]; ring
  rw [e1, e2] at hY
  nlinarith

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Radon–Riesz in weighted `L⁴`**: for a weight `ω ≥ 0`, if
`∫ ω ‖u₀‖² ⟪u₀, u_h⟫ → ∫ ω ‖u₀‖⁴` (weak convergence tested on `ω ‖u₀‖² u₀`) and
`∫ ω ‖u_h‖⁴ → ∫ ω ‖u₀‖⁴` (convergence of norms), then `∫ ω ‖u_h - u₀‖⁴ → 0`. -/
theorem tendsto_integral_weighted_norm_sub_pow_four {ω : α → ℝ} (hω0 : ∀ x, 0 ≤ ω x)
    {u : ℕ → α → E} {u₀ : α → E}
    (h1 : ∀ h, Integrable (fun x => ω x * ‖u h x‖ ^ 4) μ)
    (h2 : ∀ h, Integrable (fun x => ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫)) μ)
    (h3 : Integrable (fun x => ω x * ‖u₀ x‖ ^ 4) μ)
    (hweak : Tendsto (fun h => ∫ x, ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫) ∂μ) atTop
      (𝓝 (∫ x, ω x * ‖u₀ x‖ ^ 4 ∂μ)))
    (hnorm : Tendsto (fun h => ∫ x, ω x * ‖u h x‖ ^ 4 ∂μ) atTop
      (𝓝 (∫ x, ω x * ‖u₀ x‖ ^ 4 ∂μ))) :
    Tendsto (fun h => ∫ x, ω x * ‖u h x - u₀ x‖ ^ 4 ∂μ) atTop (𝓝 0) := by
  set N := ∫ x, ω x * ‖u₀ x‖ ^ 4 ∂μ
  have hbound : ∀ h, ∫ x, ω x * ‖u h x - u₀ x‖ ^ 4 ∂μ ≤
      8 * ∫ x, ω x * ‖u h x‖ ^ 4 ∂μ - 32 * ∫ x, ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫) ∂μ +
        24 * N := by
    intro h
    have hg : Integrable (fun x => 8 * (ω x * ‖u h x‖ ^ 4) -
        32 * (ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫)) + 24 * (ω x * ‖u₀ x‖ ^ 4)) μ :=
      (((h1 h).const_mul 8).sub ((h2 h).const_mul 32)).add (h3.const_mul 24)
    calc ∫ x, ω x * ‖u h x - u₀ x‖ ^ 4 ∂μ
        ≤ ∫ x, (8 * (ω x * ‖u h x‖ ^ 4) - 32 * (ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫)) +
            24 * (ω x * ‖u₀ x‖ ^ 4)) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) hg
            (Eventually.of_forall fun x => ?_)
          · exact mul_nonneg (hω0 x) (by positivity)
          · have := mul_le_mul_of_nonneg_left (norm_sub_pow_four_le (u h x) (u₀ x)) (hω0 x)
            simp only
            nlinarith
      _ = _ := by
          have e1 := integral_add (((h1 h).const_mul 8).sub ((h2 h).const_mul 32))
            (h3.const_mul 24)
          have e2 := integral_sub ((h1 h).const_mul 8) ((h2 h).const_mul 32)
          simp only [Pi.sub_apply] at e1
          rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  have hlim : Tendsto (fun h => 8 * ∫ x, ω x * ‖u h x‖ ^ 4 ∂μ -
      32 * ∫ x, ω x * (‖u₀ x‖ ^ 2 * ⟪u₀ x, u h x⟫) ∂μ + 24 * N) atTop (𝓝 0) := by
    have := ((hnorm.const_mul 8).sub (hweak.const_mul 32)).add_const (24 * N)
    convert this using 2
    ring
  exact squeeze_zero (fun h => integral_nonneg fun x => mul_nonneg (hω0 x) (by positivity))
    hbound hlim

/-- The exponents `4` and `4/3` are Hölder conjugate. -/
instance holderConjugate_four : (4 : ℝ≥0∞).HolderConjugate (4 / 3) := by
  rw [ENNReal.holderConjugate_iff, ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [ENNReal.div_eq_inv_mul]
  calc (4 : ℝ≥0∞)⁻¹ + 4⁻¹ * 3 = 4⁻¹ * (1 + 3) := by ring
    _ = 1 := by norm_num; exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The cubic `‖u‖² u` of an `L⁴` field lies in `L^{4/3}` (also after multiplication by a bounded
measurable weight). -/
theorem memLp_weight_norm_sq_smul {u : α → E} (hu : MemLp u 4 μ) {ω : α → ℝ}
    (hω : AEStronglyMeasurable ω μ) {c : ℝ} (hωc : ∀ x, |ω x| ≤ c) :
    MemLp (fun x => ω x • (‖u x‖ ^ 2 • u x)) (4 / 3) μ := by
  have h3 : MemLp (fun x => ‖u x‖ ^ ((3 : ℝ≥0∞).toReal)) (4 / 3) μ := hu.norm_rpow_div 3
  have h3' : MemLp (fun x => c * ‖u x‖ ^ ((3 : ℝ≥0∞).toReal)) (4 / 3) μ := h3.const_mul c
  refine h3'.of_le (hω.smul ((hu.1.norm.pow 2).smul hu.1)) (Eventually.of_forall fun x => ?_)
  have hc : 0 ≤ c := (abs_nonneg _).trans (hωc x)
  have e : ‖u x‖ ^ ((3 : ℝ≥0∞).toReal) = ‖u x‖ ^ 3 := by
    rw [show ((3 : ℝ≥0∞).toReal) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e, norm_smul, norm_smul, Real.norm_eq_abs, norm_pow, norm_norm, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ c * ‖u x‖ ^ 3)]
  calc |ω x| * (‖u x‖ ^ 2 * ‖u x‖) = |ω x| * ‖u x‖ ^ 3 := by ring
    _ ≤ c * ‖u x‖ ^ 3 := mul_le_mul_of_nonneg_right (hωc x) (by positivity)

/-- **Radon–Riesz in `L⁴`** (`lem:critical-cubic`, uniform convexity step): if `u_h ⇀ u₀` weakly in
`L⁴` (tested on `L^{4/3}`) and `‖u_h‖_{L⁴} → ‖u₀‖_{L⁴}`, then `u_h → u₀` strongly in `L⁴`. -/
theorem tendsto_integral_norm_sub_pow_four_of_weak {u : ℕ → α → E} {u₀ : α → E}
    (hu : ∀ h, MemLp (u h) 4 μ) (hu₀ : MemLp u₀ 4 μ)
    (hweak : ∀ v : α → E, MemLp v (4 / 3) μ →
      Tendsto (fun h => ∫ x, ⟪v x, u h x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪v x, u₀ x⟫ ∂μ)))
    (hnorm : Tendsto (fun h => ∫ x, ‖u h x‖ ^ 4 ∂μ) atTop (𝓝 (∫ x, ‖u₀ x‖ ^ 4 ∂μ))) :
    Tendsto (fun h => ∫ x, ‖u h x - u₀ x‖ ^ 4 ∂μ) atTop (𝓝 0) := by
  have hv : MemLp (fun x => (1 : ℝ) • (‖u₀ x‖ ^ 2 • u₀ x)) (4 / 3) μ :=
    memLp_weight_norm_sq_smul hu₀ aestronglyMeasurable_const (c := 1) fun _ => by simp
  have hcross : ∀ w : α → E, MemLp w 4 μ →
      Integrable (fun x => ⟪(1 : ℝ) • (‖u₀ x‖ ^ 2 • u₀ x), w x⟫) μ := by
    intro w hw
    refine memLp_one_iff_integrable.1 ⟨hv.1.inner hw.1, ?_⟩
    exact (eLpNorm_inner_le (p := 4) (q := 4 / 3) hv.1 hw.1).trans_lt
      (ENNReal.mul_lt_top hv.2 hw.2)
  have e0 : ∀ x, ⟪(1 : ℝ) • (‖u₀ x‖ ^ 2 • u₀ x), u₀ x⟫ = ‖u₀ x‖ ^ 4 := by
    intro x
    rw [one_smul, real_inner_smul_left, real_inner_self_eq_norm_sq]; ring
  have h4 : ∀ w : α → E, MemLp w 4 μ → Integrable (fun x => ‖w x‖ ^ 4) μ := fun w hw =>
    hw.integrable_norm_pow (p := 4) (by norm_num)
  have := tendsto_integral_weighted_norm_sub_pow_four (ω := fun _ => (1 : ℝ)) (μ := μ)
    (fun _ => zero_le_one) (u := u) (u₀ := u₀)
    (fun h => by simpa using h4 _ (hu h))
    (fun h => by
      have := hcross _ (hu h)
      simpa [one_smul, real_inner_smul_left] using this)
    (by simpa using h4 _ hu₀)
    (by
      have := hweak _ hv
      simp only [e0] at this
      simpa [one_smul, real_inner_smul_left] using this)
    (by simpa using hnorm)
  simpa using this

end RadonRiesz

end SignedMeasureWeakCompactness

end RenewalGeometry
