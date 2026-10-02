/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `L^p` convergence of mollifiers, Young's inequality for probability kernels, and a strong
  `L^p` convergence calculus

Infrastructure for the mollification arguments of the emergent-spacetime manuscript (first
Bianchi identity at limit regularity in `thm:supp-renewal-palatini`); none of it refers to
renewal notions.

On a finite-dimensional real normed space `G` with an additive Haar measure `μ`, for a kernel
`ρ ≥ 0` with `∫ ρ = 1` and `f : G → E`:

* `lintegral_ofReal_mul_rpow_le`: Jensen's inequality
  `(∫⁻ ρ g)^q ≤ ∫⁻ ρ g^q` (`q ≥ 1`) for a probability density `ρ` (any measure space);
* `eLpNorm_convolution_le`: **Young's inequality for probability kernels**,
  `‖ρ ⋆ f‖_{L^p} ≤ ‖f‖_{L^p}` for `1 ≤ p < ∞`;
* `tendsto_eLpNorm_convolution_sub`: **`L^p` convergence of mollifiers** — if `ρ_i` are
  continuous probability kernels supported in balls `B(0, r_i)` with `r_i → 0`, then
  `‖ρ_i ⋆ f - f‖_{L^p} → 0` for every `f ∈ L^p`, `1 ≤ p < ∞` (proved via density of continuous
  compactly supported functions, uniform continuity and Young's inequality);
* `tendsto_eLpNorm_normed_bump_convolution_sub`: the same for normalized `ContDiffBump`s;
* `fderiv_convolution_apply`: `D(ρ ⋆ g)(x) v = ∫ Dρ(t) v • g(x - t)` for a `C¹` compactly
  supported kernel and a locally integrable `g`.

The second part is a small calculus of strong `L^p` convergence (`LpTendsto`): sums,
differences, almost-everywhere congruence, exponent lowering on finite measures, the Hölder
product passage for continuous bilinear maps (`LpTendsto.bilin`, any Hölder triple
`1/p + 1/q = 1/r`), and passage of integrals from `L¹` convergence; `holderTriple_ofReal`
produces the needed Hölder triples from real exponents.
-/

open MeasureTheory Filter Topology ENNReal Set Metric
open scoped Convolution NNReal Pointwise

noncomputable section

namespace RenewalGeometry

set_option linter.unusedSectionVars false

namespace Mollifier

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Jensen's inequality for a probability density**: if `∫⁻ ρ = 1`, `g ≥ 0` is measurable and
`q ≥ 1`, then `(∫⁻ ρ g)^q ≤ ∫⁻ ρ g^q`. -/
theorem lintegral_ofReal_mul_rpow_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ : X → ℝ}
    (hρm : Measurable ρ)
    (hρ1 : ∫⁻ t, ENNReal.ofReal (ρ t) ∂μ = 1) {g : X → ℝ≥0∞} (hg : Measurable g)
    {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ t, ENNReal.ofReal (ρ t) * g t ∂μ) ^ q ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * g t ^ q ∂μ := by
  set ν := μ.withDensity fun t => ENNReal.ofReal (ρ t)
  have hρm' : Measurable fun t => ENNReal.ofReal (ρ t) := ENNReal.measurable_ofReal.comp hρm
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν]; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hρ1]⟩
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 : ∫⁻ t, ENNReal.ofReal (ρ t) * g t ∂μ = ∫⁻ t, g t ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hρm' hg]; rfl
  have h2 : ∫⁻ t, ENNReal.ofReal (ρ t) * g t ^ q ∂μ = ∫⁻ t, g t ^ q ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hρm' (hg.pow_const q)]; rfl
  rw [h1, h2]
  have hcmp := eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (p := 1) (q := ENNReal.ofReal q)
    (by simpa using hq) (f := g) hg.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith)
    ofReal_ne_top, toReal_ofReal hq0.le] at hcmp
  simp only [enorm_eq_self] at hcmp
  calc (∫⁻ t, g t ∂ν) ^ q ≤ ((∫⁻ t, g t ^ q ∂ν) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow hcmp hq0.le
    _ = ∫⁻ t, g t ^ q ∂ν := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

/-- Young's inequality for a probability kernel, strongly measurable version. -/
theorem eLpNorm_convolution_le_of_stronglyMeasurable {ρ : G → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫⁻ t, ENNReal.ofReal (ρ t) ∂μ = 1) {f : G → E}
    (hf : StronglyMeasurable f) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) p μ ≤ eLpNorm f p μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  set q := p.toReal with hq
  have hq1 : 1 ≤ q := by
    rw [hq]; simpa using ENNReal.toReal_mono hp hp1
  have hq0 : 0 < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hfm : Measurable fun y => ‖f y‖ₑ := hf.enorm
  have hfs : ∀ t, Measurable fun x => ‖f (x - t)‖ₑ ^ q := fun t =>
    ((hf.comp_measurable (measurable_id.sub measurable_const)).enorm).pow_const q
  have hρm' : Measurable fun t => ENNReal.ofReal (ρ t) := ENNReal.measurable_ofReal.comp hρm
  -- pointwise bound
  have hpt : ∀ x, ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x‖ₑ ^ q ≤
      ∫⁻ t, ENNReal.ofReal (ρ t) * ‖f (x - t)‖ₑ ^ q ∂μ := by
    intro x
    have h1 : ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x‖ₑ ≤
        ∫⁻ t, ENNReal.ofReal (ρ t) * ‖f (x - t)‖ₑ ∂μ := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t => ?_
      rw [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_of_nonneg (hρ0 t)]
    refine (ENNReal.rpow_le_rpow h1 hq0.le).trans ?_
    exact lintegral_ofReal_mul_rpow_le hρm hρ1
      ((hf.comp_measurable (measurable_const.sub measurable_id)).enorm) hq1
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have hmeas : Measurable (Function.uncurry fun x t => ENNReal.ofReal (ρ t) * ‖f (x - t)‖ₑ ^ q) :=
    (hρm'.comp measurable_snd).mul
      ((hf.comp_measurable (measurable_fst.sub measurable_snd)).enorm.pow_const q)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have : ∀ t, ∫⁻ x, ENNReal.ofReal (ρ t) * ‖f (x - t)‖ₑ ^ q ∂μ =
      ENNReal.ofReal (ρ t) * ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
    intro t
    rw [lintegral_const_mul _ (hfs t)]
    congr 1
    exact lintegral_sub_right_eq_self (fun y => ‖f y‖ₑ ^ q) t
  simp only [this]
  rw [lintegral_mul_const _ hρm', hρ1, one_mul]

/-- **Young's inequality for a probability kernel**: for a measurable kernel `ρ ≥ 0` with
`∫ ρ = 1` and `1 ≤ p < ∞`, `‖ρ ⋆ f‖_{L^p} ≤ ‖f‖_{L^p}`. -/
theorem eLpNorm_convolution_le {ρ : G → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ t, ρ t ∂μ = 1) {f : G → E}
    (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) p μ ≤ eLpNorm f p μ := by
  have hρi : Integrable ρ μ := integrable_of_integral_eq_one hρ1
  have hρ1' : ∫⁻ t, ENNReal.ofReal (ρ t) ∂μ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1,
      ENNReal.ofReal_one]
  rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ ρ) hf.ae_eq_mk,
    eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_convolution_le_of_stronglyMeasurable hρm hρ0 hρ1' hf.stronglyMeasurable_mk hp1 hp

/-- Convolution is subtractive where both convolutions exist. -/
theorem convolution_sub_apply {ρ : G → ℝ} {f g : G → E} {x : G}
    (hf : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul ℝ ℝ) μ)
    (hg : ConvolutionExistsAt ρ g x (ContinuousLinearMap.lsmul ℝ ℝ) μ) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) x =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x := by
  simp only [convolution_def, Pi.sub_apply, map_sub]
  exact integral_sub hf hg

/-- A kernel supported in a ball has compact support. -/
theorem hasCompactSupport_of_support_subset_ball {ρ : G → ℝ} {r : ℝ}
    (h : Function.support ρ ⊆ ball (0 : G) r) : HasCompactSupport ρ :=
  HasCompactSupport.intro (isCompact_closedBall 0 r) fun x hx => by
    by_contra hne
    exact hx (ball_subset_closedBall (h hne))

/-- **`L^p` convergence of mollifiers.**  If the continuous probability kernels `ρ_i ≥ 0`
(`∫ ρ_i = 1`) are supported in `B(0, r_i)` with `r_i → 0`, then `ρ_i ⋆ f → f` in `L^p` for every
`f ∈ L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_convolution_sub {ι : Type*} {l : Filter ι} {ρ : ι → G → ℝ}
    {r : ι → ℝ} (hr : Tendsto r l (𝓝 0)) (hρc : ∀ i, Continuous (ρ i))
    (hρ0 : ∀ i x, 0 ≤ ρ i x) (hρ1 : ∀ i, ∫ t, ρ i t ∂μ = 1)
    (hρs : ∀ i, Function.support (ρ i) ⊆ ball (0 : G) (r i)) {f : G → E} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm ((ρ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) - f) p μ) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ofNat_ne_top).ne'
  obtain ⟨g, hgc, hfg, hgcont, hgLp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε3
  have hfloc : LocallyIntegrable f μ := hf.locallyIntegrable hp1
  have hgloc : LocallyIntegrable g μ := hgLp.locallyIntegrable hp1
  have hcs : ∀ i, HasCompactSupport (ρ i) := fun i => hasCompactSupport_of_support_subset_ball (hρs i)
  -- the compact set carrying the supports
  set K1 := closedBall (0 : G) 1 + tsupport g with hK1
  have hK1c : IsCompact K1 := (isCompact_closedBall 0 1).add hgc
  set C := μ K1 ^ p.toReal⁻¹ with hC
  have hCne : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK1c.measure_lt_top.ne
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.exists_nnreal_pos_mul_lt hCne hε3
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuous_iff.mp
    (hgc.uniformContinuous_of_continuous hgcont) (δ : ℝ) (by exact_mod_cast hδ0)
  filter_upwards [hr.eventually (gt_mem_nhds (lt_min hη0 one_pos))] with i hi
  have hri : r i < η := hi.trans_le (min_le_left _ _)
  have hri1 : r i < 1 := hi.trans_le (min_le_right _ _)
  set ρi := ρ i
  -- (1) Young on f - g
  have h1 : eLpNorm (ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) p μ ≤ ε / 3 :=
    (eLpNorm_convolution_le (hρc i).measurable (hρ0 i) (hρ1 i)
      (hf.aestronglyMeasurable.sub hgLp.aestronglyMeasurable) hp1 hp).trans hfg
  -- (2) uniform approximation of g
  have h2 : eLpNorm ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) p μ ≤ ε / 3 := by
    have hsupp : Function.support ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) ⊆ K1 := by
      refine (Function.support_sub _ _).trans (Set.union_subset ?_ ?_)
      · refine (support_convolution_subset _).trans (Set.add_subset_add ?_ (subset_tsupport g))
        exact (hρs i).trans ((ball_subset_closedBall).trans (closedBall_subset_closedBall hri1.le))
      · intro x hx
        exact ⟨0, mem_closedBall_self zero_le_one, x, subset_tsupport g hx, zero_add x⟩
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    have hb : ∀ x, ‖((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) x‖ ≤ (δ : ℝ) := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      refine dist_convolution_le (by positivity) (hρs i) (hρ0 i) (hρ1 i)
        hgcont.aestronglyMeasurable fun y hy => ?_
      exact (hη (lt_trans (mem_ball.mp hy) hri)).le
    refine (eLpNorm_le_of_ae_bound (Eventually.of_forall hb)).trans ?_
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal, mul_comm]
    exact hδ.le
  -- (3) assemble
  have hex : ∀ (u : G → E), LocallyIntegrable u μ → ∀ x,
      ConvolutionExistsAt ρi u x (ContinuousLinearMap.lsmul ℝ ℝ) μ := fun u hu x =>
    (hcs i).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρc i) hu x
  have hdec : (ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) - f =
      (ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) +
        ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) + (g - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [convolution_sub_apply (hex f hfloc x) (hex g hgloc x)]
    abel
  have hc1 : AEStronglyMeasurable (ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) μ :=
    ((hcs i).continuous_convolution_left _ (hρc i) (hfloc.sub hgloc)).aestronglyMeasurable
  have hc2 : AEStronglyMeasurable ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) μ :=
    (((hcs i).continuous_convolution_left _ (hρc i) hgloc).sub hgcont).aestronglyMeasurable
  have hc3 : AEStronglyMeasurable (g - f) μ := hgLp.aestronglyMeasurable.sub hf.aestronglyMeasurable
  rw [hdec]
  calc eLpNorm ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) +
        ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) + (g - f)) p μ
      ≤ eLpNorm ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) +
        ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g)) p μ + eLpNorm (g - f) p μ :=
        eLpNorm_add_le (hc1.add hc2) hc3 hp1
    _ ≤ eLpNorm (ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f - g)) p μ +
        eLpNorm ((ρi ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) - g) p μ + eLpNorm (g - f) p μ := by
        gcongr; exact eLpNorm_add_le hc1 hc2 hp1
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        rw [eLpNorm_sub_comm]; exact hfg
    _ = ε := ENNReal.add_thirds ε

/-- Derivative of a mollification: `D(ρ ⋆ g)(x) v = ∫ Dρ(t) v • g(x - t)` for a `C¹`
compactly supported kernel and a locally integrable `g`. -/
theorem fderiv_convolution_apply {ρ : G → ℝ} (hρ : ContDiff ℝ 1 ρ) (hcs : HasCompactSupport ρ)
    {g : G → E} (hg : LocallyIntegrable g μ) (x v : G) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x v =
      ∫ t, fderiv ℝ ρ t v • g (x - t) ∂μ := by
  rw [(hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hg x).fderiv,
    convolution_def]
  have hex := (hcs.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).precompL G)
    (hρ.continuous_fderiv one_ne_zero) hg x
  rw [ContinuousLinearMap.integral_apply hex]
  simp

/-- `L^p` convergence for normalized `ContDiffBump` mollifiers with shrinking outer radius. -/
theorem tendsto_eLpNorm_normed_bump_convolution_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : G)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) {f : G → E}
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm (((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) - f) p μ)
      l (𝓝 0) :=
  tendsto_eLpNorm_convolution_sub hφ (fun i => (φ i).continuous_normed)
    (fun i x => (φ i).nonneg_normed x) (fun i => (φ i).integral_normed)
    (fun i => ((φ i).support_normed_eq (μ := μ)).subset) hp1 hp hf

end Mollifier

/-! ### A calculus of strong `L^p` convergence -/

section LpTendstoCalculus

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Hölder triples from real exponents: `1/p + 1/q = 1/r` gives
`HolderTriple (ofReal p) (ofReal q) (ofReal r)`. -/
theorem holderTriple_ofReal {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p⁻¹ + q⁻¹ = r⁻¹) :
    HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_add (by positivity) (by positivity), h]

/-- Strong `L^p(ν)` convergence `u n → u'` of `L^p` functions. -/
structure LpTendsto (ν : Measure X) (p : ℝ≥0∞) (u : ℕ → X → E) (u' : X → E) : Prop where
  memLp : ∀ n, MemLp (u n) p ν
  memLp_lim : MemLp u' p ν
  tendsto : Tendsto (fun n => eLpNorm (u n - u') p ν) atTop (𝓝 0)

namespace LpTendsto

/-- Sums of strongly convergent sequences converge strongly. -/
theorem add {p : ℝ≥0∞} [Fact (1 ≤ p)] {u v : ℕ → X → E} {u' v' : X → E}
    (hu : LpTendsto ν p u u') (hv : LpTendsto ν p v v') :
    LpTendsto ν p (fun n => u n + v n) (u' + v') := by
  refine ⟨fun n => (hu.memLp n).add (hv.memLp n), hu.memLp_lim.add hv.memLp_lim, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hu.tendsto.add hv.tendsto) (fun n => bot_le) fun n => ?_
  have : u n + v n - (u' + v') = (u n - u') + (v n - v') := by abel
  simp only [this]
  exact eLpNorm_add_le ((hu.memLp n).1.sub hu.memLp_lim.1) ((hv.memLp n).1.sub hv.memLp_lim.1)
    Fact.out

/-- Negation preserves strong convergence. -/
theorem neg {p : ℝ≥0∞} {u : ℕ → X → E} {u' : X → E} (hu : LpTendsto ν p u u') :
    LpTendsto ν p (fun n => -u n) (-u') := by
  refine ⟨fun n => (hu.memLp n).neg, hu.memLp_lim.neg, ?_⟩
  refine hu.tendsto.congr fun n => ?_
  rw [← eLpNorm_neg]; congr 1; abel

/-- Differences of strongly convergent sequences converge strongly. -/
theorem sub {p : ℝ≥0∞} [Fact (1 ≤ p)] {u v : ℕ → X → E} {u' v' : X → E}
    (hu : LpTendsto ν p u u') (hv : LpTendsto ν p v v') :
    LpTendsto ν p (fun n => u n - v n) (u' - v') := by
  have := hu.add hv.neg
  simpa [sub_eq_add_neg] using this

/-- Strong convergence is invariant under almost-everywhere modification. -/
theorem congr {p : ℝ≥0∞} {u v : ℕ → X → E} {u' v' : X → E} (hu : LpTendsto ν p u u')
    (h : ∀ n, u n =ᵐ[ν] v n) (h' : u' =ᵐ[ν] v') : LpTendsto ν p v v' := by
  refine ⟨fun n => (hu.memLp n).ae_eq (h n), hu.memLp_lim.ae_eq h', ?_⟩
  refine hu.tendsto.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [h n, h'] with x h1 h2
  simp [h1, h2]

/-- Exponent lowering on a finite measure: strong `L^q` convergence implies strong `L^p`
convergence for `0 < p ≤ q`. -/
theorem mono [IsFiniteMeasure ν] {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpq : p ≤ q) {u : ℕ → X → E}
    {u' : X → E}
    (hu : LpTendsto ν q u u') : LpTendsto ν p u u' := by
  refine ⟨fun n => (hu.memLp n).mono_exponent hpq, hu.memLp_lim.mono_exponent hpq, ?_⟩
  have hb : ∀ n, eLpNorm (u n - u') p ν ≤
      eLpNorm (u n - u') q ν * ν univ ^ (1 / p.toReal - 1 / q.toReal) := fun n =>
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq ((hu.memLp n).1.sub hu.memLp_lim.1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
  have hexp : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne q ∞ with rfl | hq
    · simp
    · have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
      have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hp' (ENNReal.toReal_mono hq hpq)
  have : ν univ ^ (1 / p.toReal - 1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top ν univ)
  simpa using ENNReal.Tendsto.mul_const hu.tendsto (Or.inr this)

/-- **Hölder product passage**: if `u n → u'` in `L^p`, `v n → v'` in `L^q` and
`1/p + 1/q = 1/r`, then `B(u n, v n) → B(u', v')` in `L^r` for every continuous bilinear `B`. -/
theorem bilin {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [HolderTriple p q r] (B : E →L[ℝ] F →L[ℝ] W) {u : ℕ → X → E} {u' : X → E}
    {v : ℕ → X → F} {v' : X → F} (hu : LpTendsto ν p u u') (hv : LpTendsto ν q v v') :
    LpTendsto ν r (fun n x => B (u n x) (v n x)) (fun x => B (u' x) (v' x)) := by
  set H := ContinuousLinearMap.holderL ν p q r B
  have hU : Tendsto (fun n => (hu.memLp n).toLp (u n)) atTop (𝓝 (hu.memLp_lim.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hu.tendsto
  have hV : Tendsto (fun n => (hv.memLp n).toLp (v n)) atTop (𝓝 (hv.memLp_lim.toLp v')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hv.tendsto
  have hW := (H.continuous₂.tendsto (hu.memLp_lim.toLp u', hv.memLp_lim.toLp v')).comp
    (hU.prodMk_nhds hV)
  have heq : ∀ (a : X → E) (b : X → F) (ha : MemLp a p ν) (hb : MemLp b q ν),
      (H (ha.toLp a) (hb.toLp b) : X → W) =ᵐ[ν] fun x => B (a x) (b x) := by
    intro a b ha hb
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp,
      ContinuousLinearMap.coeFn_holder (r := r) B (ha.toLp a) (hb.toLp b)] with x h1 h2 h3
    simp only [H, ContinuousLinearMap.holderL_apply_apply] at *
    rw [h3, h1, h2]
  have hm : ∀ (a : X → E) (b : X → F) (ha : MemLp a p ν) (hb : MemLp b q ν),
      MemLp (fun x => B (a x) (b x)) r ν := fun a b ha hb =>
    (Lp.memLp (H (ha.toLp a) (hb.toLp b))).ae_eq (heq a b ha hb)
  refine ⟨fun n => hm _ _ (hu.memLp n) (hv.memLp n), hm _ _ hu.memLp_lim hv.memLp_lim, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (f := fun n => H ((hu.memLp n).toLp (u n))
    ((hv.memLp n).toLp (v n))) (f_lim := H (hu.memLp_lim.toLp u') (hv.memLp_lim.toLp v'))).1 hW
  refine this.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [heq _ _ (hu.memLp n) (hv.memLp n), heq _ _ hu.memLp_lim hv.memLp_lim]
    with x h1 h2
  simp only [Pi.sub_apply, h1, h2]

/-- Integrals pass to the limit under strong `L¹` convergence. -/
theorem tendsto_integral [CompleteSpace E] {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν 1 u u') : Tendsto (fun n => ∫ x, u n x ∂ν) atTop (𝓝 (∫ x, u' x ∂ν)) :=
  tendsto_integral_of_L1' u' hu.memLp_lim.1 (Eventually.of_forall fun n =>
    memLp_one_iff_integrable.1 (hu.memLp n)) hu.tendsto

/-- Strong convergence on `ν` implies strong convergence on every restriction of `ν`. -/
theorem restrict {p : ℝ≥0∞} {u : ℕ → X → E} {u' : X → E} (hu : LpTendsto ν p u u')
    (s : Set X) : LpTendsto (ν.restrict s) p u u' := by
  refine ⟨fun n => (hu.memLp n).restrict s, hu.memLp_lim.restrict s, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu.tendsto
    (fun n => bot_le) fun n => eLpNorm_mono_measure _ Measure.restrict_le_self

/-- A constant sequence converges strongly. -/
theorem const {p : ℝ≥0∞} {u : X → E} (hu : MemLp u p ν) : LpTendsto ν p (fun _ => u) u :=
  ⟨fun _ => hu, hu, by simp⟩

/-- **Uniform bounds pass to strong limits**: if `u n → u'` in `L^p` (`p ≠ 0`) and
`‖u n‖_{L^q} ≤ M` for all `n`, then `‖u'‖_{L^q} ≤ M` (Fatou along an a.e. convergent
subsequence).  This is how a uniform regulator bound (e.g. the `L⁶` coframe bound, or an `L³`/`L⁴`
bound on spatial connection coefficients) is inherited by the strong limit. -/
theorem eLpNorm_le_of_bound {p q : ℝ≥0∞} (hp0 : p ≠ 0) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') {M : ℝ≥0∞} (hM : ∀ n, eLpNorm (u n) q ν ≤ M) :
    eLpNorm u' q ν ≤ M := by
  have hm : TendstoInMeasure ν u atTop u' :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 (fun n => (hu.memLp n).1) hu.memLp_lim.1 hu.tendsto
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hu.memLp (ns n)).1) u' hae).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall fun n => hM (ns n))

/-- A strong `L^p` limit of a sequence bounded in `L^q` lies in `L^q`. -/
theorem memLp_of_bound {p q : ℝ≥0∞} (hp0 : p ≠ 0) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') {M : ℝ≥0∞} (hMt : M ≠ ∞) (hM : ∀ n, eLpNorm (u n) q ν ≤ M) :
    MemLp u' q ν :=
  ⟨hu.memLp_lim.1, (hu.eLpNorm_le_of_bound hp0 hM).trans_lt hMt.lt_top⟩

end LpTendsto

end LpTendstoCalculus

end RenewalGeometry
