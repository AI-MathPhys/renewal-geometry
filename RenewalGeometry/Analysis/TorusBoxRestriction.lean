/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevTorusBridge
import RenewalGeometry.Analysis.TorusCurvatureConvergence
import RenewalGeometry.Analysis.CovariantGradientCompactness
import RenewalGeometry.Analysis.GaugeCovariantDerivative
import RenewalGeometry.Analysis.TorusSobolevL4

/-!
# Restricting torus Sobolev functions to a box

Generic infrastructure (no renewal notions): the fractional Sobolev spaces `H^s(Q)` of a bounded box
`Q ⊂ ℝ^ι` rendered as **restriction spaces** — `u ∈ H^s(Q)` with `‖u‖_{H^s(Q)} ≤ R` iff `u`
agrees a.e. on `Q` with the pull-back of a periodic `H^s` function of `H^s`-norm `≤ R` on a torus
`ℝ^ι / Lℤ^ι` whose fundamental cube `c + L(0,1]^ι` contains `Q` (the classical restriction
definition `H^s(Ω) = H^s(ℝ^ι)|_Ω`, localised; for bounded Lipschitz regions it is equivalent to the
intrinsic Sobolev–Slobodeckij norm).

* `chart c L x = (x - c)/L mod ℤ^ι` and the pull-back `U ∘ chart`.
* `lintegral_chart_le`, `eLpNorm_chart_le` (**restriction inequality**):
  `‖V ∘ chart‖_{L^p(Q)} ≤ L^{d/p} ‖V‖_{L^p(𝕋^ι)}`.
* `pd_trigPoly_chart`: the classical derivative of a pulled-back trigonometric polynomial.
* `hasWeakPartial_chart` (**weak derivatives restrict**): for `U ∈ H¹(𝕋^ι)`, the pull-back of the
  Fourier-multiplier derivative `L⁻¹ (∂_i U) ∘ chart` is the weak `i`-th partial derivative of
  `U ∘ chart` on every open `Ω` of finite measure (`Ω ⊆ c + L(0,1]^ι`); hence `memW12_chart`:
  `U ∘ chart ∈ W^{1,2}(Q)`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal ContDiff Real

noncomputable section

namespace RenewalGeometry.SobolevOpen
namespace TorusChart

open TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The chart and the restriction inequality -/

/-- The chart `x ↦ (x - c)/L mod ℤ^ι`. -/
def chart (c : ι → ℝ) (L : ℝ) (x : ι → ℝ) : UnitAddTorus ι :=
  fun i => (((x i - c i) / L : ℝ) : UnitAddCircle)

theorem chart_affine (c : ι → ℝ) {L : ℝ} (hL : L ≠ 0) (y : ι → ℝ) :
    chart c L (c + L • y) = fun i => (y i : UnitAddCircle) := by
  funext i
  simp only [chart, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  rw [mul_div_cancel_left₀ _ hL]

theorem continuous_chart (c : ι → ℝ) (L : ℝ) : Continuous (chart c L) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun x : ι → ℝ => (x i - c i) / L := by fun_prop
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp h

theorem measurable_chart (c : ι → ℝ) (L : ℝ) : Measurable (chart c L) :=
  (continuous_chart c L).measurable

/-- The cube `c + L (0,1]^ι`. -/
def cubeAt (c : ι → ℝ) (L : ℝ) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (c i) (c i + L)}

theorem affine_preimage_cubeAt (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    (fun y : ι → ℝ => c + L • y) ⁻¹' cubeAt c L = unitCube := by
  ext y
  simp only [cubeAt, unitCube, mem_preimage, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mem_Ioc]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem measurableEmbedding_affine (c : ι → ℝ) {L : ℝ} (hL : L ≠ 0) :
    MeasurableEmbedding (fun y : ι → ℝ => c + L • y) := by
  have he : (fun y : ι → ℝ => c + L • y) = ⇑((Homeomorph.smulOfNeZero L hL).trans
      (Homeomorph.addLeft c)) := by
    funext y; simp
  rw [he]
  exact ((Homeomorph.smulOfNeZero L hL).trans (Homeomorph.addLeft c)).measurableEmbedding

/-- Change of variables onto the cube. -/
theorem lintegral_cubeAt (c : ι → ℝ) {L : ℝ} (hL : 0 < L) (g : (ι → ℝ) → ℝ≥0∞) :
    ∫⁻ x in cubeAt c L, g x =
      ENNReal.ofReal (L ^ Fintype.card ι) * ∫⁻ y in unitCube, g (c + L • y) := by
  have hmp := measurePreserving_affine c hL
  have h := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_affine c hL.ne') g
    (cubeAt c L)
  rw [affine_preimage_cubeAt c hL] at h
  rw [h, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

/-- **Restriction inequality** (integrals): for `Q ⊆ c + L(0,1]^ι`,
`∫_Q g(chart x) dx ≤ L^d ∫_{𝕋^ι} g`. -/
theorem lintegral_chart_le {Q : Set (ι → ℝ)} {c : ι → ℝ} {L : ℝ} (hL : 0 < L)
    (hQ : Q ⊆ cubeAt c L) (g : UnitAddTorus ι → ℝ≥0∞) :
    ∫⁻ x in Q, g (chart c L x) ≤ ENNReal.ofReal (L ^ Fintype.card ι) * ∫⁻ t, g t := by
  refine (lintegral_mono_set hQ).trans (le_of_eq ?_)
  rw [lintegral_cubeAt c hL, lintegral_torus_eq_unitCube]
  congr 1
  refine setLIntegral_congr_fun measurableSet_unitCube fun y _ => ?_
  rw [chart_affine c hL.ne']

/-- **Restriction inequality** (`L^p`, `0 < p < ∞`):
`‖V ∘ chart‖_{L^p(Q)} ≤ L^{d/p} ‖V‖_{L^p(𝕋^ι)}`. -/
theorem eLpNorm_chart_le {E : Type*} [NormedAddCommGroup E] {Q : Set (ι → ℝ)} {c : ι → ℝ}
    {L : ℝ} (hL : 0 < L) (hQ : Q ⊆ cubeAt c L) (V : UnitAddTorus ι → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => V (chart c L x)) (ENNReal.ofReal p) (volume.restrict Q) ≤
      ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / p)) * eLpNorm V (ENNReal.ofReal p) volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  have h := lintegral_chart_le hL hQ (fun t => ‖V t‖ₑ ^ p)
  calc (∫⁻ x in Q, ‖V (chart c L x)‖ₑ ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal (L ^ Fintype.card ι) * ∫⁻ t, ‖V t‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / p)) * (∫⁻ t, ‖V t‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_rpow_of_pos
          (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
        congr 3
        ring

/-- Pull-backs of a.e.-equal functions are a.e. equal on `Q`. -/
theorem ae_chart_of_ae {E : Type*} {Q : Set (ι → ℝ)} {c : ι → ℝ} {L : ℝ} (hL : 0 < L)
    (hQ : Q ⊆ cubeAt c L) {V W : UnitAddTorus ι → E} (h : V =ᵐ[volume] W) :
    (fun x => V (chart c L x)) =ᵐ[volume.restrict Q] fun x => W (chart c L x) := by
  have hnull : volume {t | V t ≠ W t} = 0 := ae_iff.mp h
  set M := toMeasurable volume {t | V t ≠ W t}
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM0 : volume M = 0 := by rw [measure_toMeasurable]; exact hnull
  have hle := lintegral_chart_le hL hQ (M.indicator 1)
  rw [lintegral_indicator_one hM, hM0, mul_zero, nonpos_iff_eq_zero] at hle
  have hpre : ∫⁻ x in Q, M.indicator 1 (chart c L x) = (volume.restrict Q) (chart c L ⁻¹' M) := by
    rw [← lintegral_indicator_one ((measurable_chart c L) hM)]
    rfl
  rw [hpre] at hle
  rw [EventuallyEq, ae_iff]
  exact measure_mono_null (t := chart c L ⁻¹' M)
    (fun x hx => subset_toMeasurable volume {t | V t ≠ W t} hx) hle

/-! ### Pulled-back trigonometric polynomials -/

theorem mFourier_chart (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) (x : ι → ℝ) :
    mFourier n (chart c L x) = charS (-n) c L x := by
  have h := mFourier_neg_mk (-n) (L⁻¹ • (x - c))
  rw [neg_neg] at h
  have e : chart c L x = fun i => (((L⁻¹ • (x - c)) i : ℝ) : UnitAddCircle) := by
    funext i
    simp only [chart, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    congr 1
    ring
  rw [e, h]
  rfl

theorem trigPoly_chart (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) (c : ι → ℝ) (L : ℝ) :
    (fun x => trigPoly S a (chart c L x)) = fun x => ∑ n ∈ S, a n * charS (-n) c L x := by
  funext x
  simp only [trigPoly, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, mFourier_chart]

theorem contDiff_trigPoly_chart (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) (c : ι → ℝ) (L : ℝ) :
    ContDiff ℝ ∞ (fun x => trigPoly S a (chart c L x)) := by
  rw [trigPoly_chart]
  exact ContDiff.sum fun n _ => contDiff_const.mul (contDiff_charS (-n) c L)

theorem pd_const_mul_charS (b : ℂ) (m : ι → ℤ) (c : ι → ℝ) (L : ℝ) (i : ι) (x : ι → ℝ) :
    pd (fun x => b * charS m c L x) i x = b * pd (charS m c L) i x := by
  unfold pd
  rw [fderiv_const_mul ((contDiff_charS m c L).differentiable (by simp) x)]
  rfl

/-- The classical derivative of a pulled-back trigonometric polynomial:
`∂_i (P ∘ chart) = L⁻¹ (∂_i P) ∘ chart`, `∂_i P` having coefficients `2π i n_i a_n`. -/
theorem pd_trigPoly_chart (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) (c : ι → ℝ) {L : ℝ} (i : ι)
    (x : ι → ℝ) :
    pd (fun x => trigPoly S a (chart c L x)) i x =
      (L⁻¹ : ℂ) * trigPoly S (fun n => 2 * π * Complex.I * (n i : ℂ) * a n) (chart c L x) := by
  rw [trigPoly_chart, pd_sum_complex (fun n _ =>
    ((contDiff_const.mul (contDiff_charS (-n) c L)).differentiable (by simp)) x)]
  have e := congrFun (trigPoly_chart S (fun n => 2 * π * Complex.I * (n i : ℂ) * a n) c L) x
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pd_const_mul_charS, pd_charS]
  simp only [Pi.neg_apply, Int.cast_neg]
  push_cast
  ring

/-! ### Weak derivatives restrict -/

theorem continuous_trigPoly_chart (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) (c : ι → ℝ) (L : ℝ) :
    Continuous fun x => trigPoly S a (chart c L x) :=
  (trigPoly S a).continuous.comp (continuous_chart c L)

theorem memLp_continuousMap_chart {Ω : Set (ι → ℝ)} (hΩf : volume Ω ≠ ⊤) (P : C(UnitAddTorus ι, ℂ))
    (c : ι → ℝ) (L : ℝ) : MemLp (fun x => P (chart c L x)) 2 (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩf
  refine MemLp.of_bound (P.continuous.comp (continuous_chart c L)).aestronglyMeasurable ‖P‖
    (Eventually.of_forall fun x => P.norm_coe_le_norm _)

theorem memLp_chart {Ω : Set (ι → ℝ)} {c : ι → ℝ} {L : ℝ} (hL : 0 < L) (hΩ : Ω ⊆ cubeAt c L)
    (V : L²(UnitAddTorus ι)) : MemLp (fun x => V (chart c L x)) 2 (volume.restrict Ω) := by
  have hV := Lp.memLp V
  obtain ⟨V', hV'm, hVV'⟩ := hV.1
  have hae := ae_chart_of_ae hL hΩ hVV'
  refine ⟨(hV'm.comp_measurable (measurable_chart c L)).aestronglyMeasurable.congr hae.symm, ?_⟩
  have h := eLpNorm_chart_le hL hΩ (⇑V) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_ofNat] at h
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV.2)

theorem tendsto_chart_of_tendsto_L2 {Ω : Set (ι → ℝ)} {c : ι → ℝ} {L : ℝ} (hL : 0 < L)
    (hΩ : Ω ⊆ cubeAt c L) {P : ℕ → C(UnitAddTorus ι, ℂ)} {V : L²(UnitAddTorus ι)}
    (h : Tendsto (fun N => (P N).toLp 2 volume ℂ) atTop (𝓝 V)) :
    Tendsto (fun N => eLpNorm ((fun x => P N (chart c L x)) - fun x => V (chart c L x)) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ V).mp h
  have h2 : Tendsto (fun N => ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / 2)) *
      eLpNorm (⇑((P N).toLp 2 volume ℂ) - ⇑V) 2 volume) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / 2))) h1
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun N => zero_le)
    fun N => ?_
  have hb := eLpNorm_chart_le hL hΩ (⇑((P N).toLp 2 volume ℂ) - ⇑V) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_ofNat] at hb
  refine le_trans (le_of_eq ?_) hb
  refine eLpNorm_congr_ae ?_
  have hae := ae_chart_of_ae hL hΩ (ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
    (P N))
  filter_upwards [hae] with x hx
  simp only [Pi.sub_apply, hx]

/-- **Weak derivatives restrict**: for `U ∈ H¹(𝕋^ι)` and an open (measurable) `Ω ⊆ c + L(0,1]^ι`
of finite measure, `L⁻¹ (∂_i U) ∘ chart` (Fourier-multiplier derivative) is the weak `i`-th partial
derivative of `U ∘ chart` on `Ω`. -/
theorem hasWeakPartial_chart {Ω : Set (ι → ℝ)} (hΩm : MeasurableSet Ω) (hΩf : volume Ω ≠ ⊤)
    {c : ι → ℝ} {L : ℝ} (hL : 0 < L) (hΩ : Ω ⊆ cubeAt c L) {U : L²(UnitAddTorus ι)}
    (hU : MemH 1 U) (i : ι) :
    HasWeakPartial Ω i (fun x => U (chart c L x))
      (fun x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)) := by
  set u : ℕ → (ι → ℝ) → ℂ := fun N x => fourierTrunc N U (chart c L x)
  set g : ℕ → (ι → ℝ) → ℂ := fun N x => (L⁻¹ : ℂ) * fourierTrunc N (weakDeriv i U) (chart c L x)
  have hcoef : ∀ N, fourierTrunc N (weakDeriv i U) =
      trigPoly (TorusSobolev.box N) (fun n => 2 * π * Complex.I * (n i : ℂ) * mFourierCoeff U n) := by
    intro N
    unfold fourierTrunc
    congr 1
    funext n
    rw [mFourierCoeff_weakDeriv hU]
  have hw : ∀ N, HasWeakPartial Ω i (u N) (g N) := by
    intro N
    have h := hasWeakPartial_of_contDiff Ω ((contDiff_trigPoly_chart (TorusSobolev.box N) (mFourierCoeff U)
      c L).of_le (by simp)) i
    have he : pd (fun x => trigPoly (TorusSobolev.box N) (mFourierCoeff U) (chart c L x)) i = g N := by
      funext x
      rw [pd_trigPoly_chart]
      simp only [g, hcoef]
    rw [he] at h
    exact h
  have hu : ∀ N, MemLp (u N) 2 (volume.restrict Ω) := fun N =>
    memLp_continuousMap_chart hΩf _ c L
  have hg : ∀ N, MemLp (g N) 2 (volume.restrict Ω) := fun N =>
    (memLp_continuousMap_chart hΩf _ c L).const_mul _
  have hU' := memLp_chart hL hΩ U
  have hdU' : MemLp (fun x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)) 2 (volume.restrict Ω) :=
    (memLp_chart hL hΩ (weakDeriv i U)).const_mul _
  have hul := tendsto_chart_of_tendsto_L2 hL hΩ (tendsto_fourierTrunc U)
  have hgl : Tendsto (fun N => eLpNorm (g N - fun x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    have h1 := tendsto_chart_of_tendsto_L2 hL hΩ (tendsto_fourierTrunc (weakDeriv i U))
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.coe_ne_top (r := ‖(L⁻¹ : ℂ)‖₊)))
    simp only [mul_zero] at h2
    refine h2.congr fun N => ?_
    have : (g N - fun x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)) =
        (L⁻¹ : ℂ) • ((fun x => fourierTrunc N (weakDeriv i U) (chart c L x)) -
          fun x => weakDeriv i U (chart c L x)) := by
      funext x; simp only [g, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [this, eLpNorm_const_smul]
    rfl
  exact hasWeakPartial_of_tendsto hΩm hΩf hw hu hg hU' hdU' hul hgl

/-- `U ∘ chart ∈ W^{1,2}(Ω)` for `U ∈ H¹(𝕋^ι)`, with weak gradient `L⁻¹ (∇U) ∘ chart`. -/
theorem memW12_chart {Ω : Set (ι → ℝ)} (hΩm : MeasurableSet Ω) (hΩf : volume Ω ≠ ⊤)
    {c : ι → ℝ} {L : ℝ} (hL : 0 < L) (hΩ : Ω ⊆ cubeAt c L) {U : L²(UnitAddTorus ι)}
    (hU : MemH 1 U) :
    MemW12 Ω (fun x => U (chart c L x)) (fun i x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)) :=
  ⟨memLp_chart hL hΩ U, fun i => (memLp_chart hL hΩ (weakDeriv i U)).const_mul _,
    fun i => hasWeakPartial_chart hΩm hΩf hL hΩ hU i⟩

end TorusChart
end RenewalGeometry.SobolevOpen
