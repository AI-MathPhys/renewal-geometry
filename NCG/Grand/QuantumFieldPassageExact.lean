/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniformly integrable passage of correlations under weak convergence

Machinery for `thm:SMST-quantum-tightness` (QRP.9): if field laws `μ̂_j ⇒ μ` weakly, the family is
tight, continuous writers `F_j → F` locally uniformly, and `sup_j ∫ |F_j|^{1+δ} dμ̂_j < ∞`, then
`∫ F_j dμ̂_j → ∫ F dμ`.

This file contains the truncation toolkit:

* `clamp L t = max (-L) (min L t)`: bounded by `L`, `1`-Lipschitz, and
  `|t - clamp L t| ≤ |t|^{1+δ} / L^δ` (`abs_sub_clamp_le`);
* `integrable_of_moment`, `integrable_rpow_of_moment`: a `(1+δ)`-moment bound gives
  integrability of `f` and of `|f|^{1+δ}` on a probability space, with the real moment bound
  `integral_rpow_le_of_moment`;
* `abs_integral_sub_clamp_le`: the truncation error `|∫ f - ∫ clamp L ∘ f| ≤ C / L^δ`.
-/

open MeasureTheory Filter Topology Set

namespace NCG
namespace QuantumFieldPassage

set_option linter.unusedSectionVars false

/-! ### The clamp -/

/-- The clamp of a real number to `[-L, L]`. -/
def clamp (L t : ℝ) : ℝ := max (-L) (min L t)

theorem abs_clamp_le {L : ℝ} (hL : 0 ≤ L) (t : ℝ) : |clamp L t| ≤ L := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clamp_of_abs_le {L t : ℝ} (h : |t| ≤ L) : clamp L t = t := by
  unfold clamp
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The clamp is `1`-Lipschitz. -/
theorem abs_clamp_sub_clamp_le (L a b : ℝ) : |clamp L a - clamp L b| ≤ |a - b| := by
  unfold clamp
  calc |max (-L) (min L a) - max (-L) (min L b)|
      ≤ max |(-L) - (-L)| |min L a - min L b| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ |a - b| := by
        refine max_le (by simp) ?_
        calc |min L a - min L b| ≤ max |L - L| |a - b| := abs_min_sub_min_le_max _ _ _ _
          _ ≤ |a - b| := max_le (by simp) le_rfl

/-- The truncation defect is controlled by the `(1+δ)`-moment:
`|t - clamp L t| ≤ |t|^{1+δ} / L^δ`. -/
theorem abs_sub_clamp_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (t : ℝ) :
    |t - clamp L t| ≤ |t| ^ (1 + δ) / L ^ δ := by
  by_cases h : |t| ≤ L
  · rw [clamp_of_abs_le h, sub_self, abs_zero]
    positivity
  · have h := not_le.mp h
    have ht : 0 < |t| := lt_trans hL h
    have hpow : |t| ^ (1 + δ) = |t| * |t| ^ δ := by
      rw [Real.rpow_add ht, Real.rpow_one]
    have hLt : L ^ δ ≤ |t| ^ δ := Real.rpow_le_rpow hL.le h.le hδ
    have hLδ : 0 < L ^ δ := Real.rpow_pos_of_pos hL δ
    calc |t - clamp L t| ≤ |t| := by
          unfold clamp
          rcases le_or_gt 0 t with ht0 | ht0
          · rw [abs_of_nonneg ht0] at h ⊢
            rw [min_eq_left h.le, max_eq_right (by linarith), abs_le]
            constructor <;> linarith
          · rw [abs_of_neg ht0] at h ⊢
            rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_le]
            constructor <;> linarith
      _ = |t| ^ (1 + δ) / |t| ^ δ := by
          rw [hpow, mul_div_assoc, div_self (Real.rpow_pos_of_pos ht δ).ne', mul_one]
      _ ≤ |t| ^ (1 + δ) / L ^ δ := by
          gcongr

/-! ### Integrability from a moment bound -/

variable {E : Type*} [MeasurableSpace E]

/-- A finite `(1+δ)`-moment gives membership in `L^{1+δ}`. -/
theorem memLp_of_moment {ν : Measure E} {f : E → ℝ} (hf : AEStronglyMeasurable f ν) {δ : ℝ}
    (hδ : 0 ≤ δ) {C : ENNReal} (hC : C ≠ ⊤) (hmom : ∫⁻ x, ‖f x‖ₑ ^ (1 + δ) ∂ν ≤ C) :
    MemLp f (ENNReal.ofReal (1 + δ)) ν := by
  refine ⟨hf, ?_⟩
  have hp0 : ENNReal.ofReal (1 + δ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_top_of_le_ne_top hC hmom)

theorem integrable_of_moment {ν : Measure E} [IsProbabilityMeasure ν] {f : E → ℝ}
    (hf : AEStronglyMeasurable f ν) {δ : ℝ} (hδ : 0 ≤ δ) {C : ENNReal} (hC : C ≠ ⊤)
    (hmom : ∫⁻ x, ‖f x‖ₑ ^ (1 + δ) ∂ν ≤ C) : Integrable f ν := by
  have h := memLp_of_moment hf hδ hC hmom
  exact memLp_one_iff_integrable.mp (h.mono_exponent (by
    rw [ENNReal.one_le_ofReal]; linarith))

theorem integrable_rpow_of_moment {ν : Measure E} [IsProbabilityMeasure ν] {f : E → ℝ}
    (hf : AEStronglyMeasurable f ν) {δ : ℝ} (hδ : 0 ≤ δ) {C : ENNReal} (hC : C ≠ ⊤)
    (hmom : ∫⁻ x, ‖f x‖ₑ ^ (1 + δ) ∂ν ≤ C) : Integrable (fun x => |f x| ^ (1 + δ)) ν := by
  have h := (memLp_of_moment hf hδ hC hmom).integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal (by linarith)] at h
  simpa [Real.norm_eq_abs] using h

/-- The real `(1+δ)`-moment is bounded by `C.toReal`. -/
theorem integral_rpow_le_of_moment {ν : Measure E} [IsProbabilityMeasure ν] {f : E → ℝ}
    (hf : AEStronglyMeasurable f ν) {δ : ℝ} (hδ : 0 ≤ δ) {C : ENNReal} (hC : C ≠ ⊤)
    (hmom : ∫⁻ x, ‖f x‖ₑ ^ (1 + δ) ∂ν ≤ C) :
    ∫ x, |f x| ^ (1 + δ) ∂ν ≤ C.toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => |f x| ^ (1 + δ))
    (Eventually.of_forall fun x => by positivity)
    ((hf.norm.aemeasurable.pow_const _).aestronglyMeasurable)]
  refine ENNReal.toReal_mono hC (le_trans (le_of_eq ?_) hmom)
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith), ← Real.norm_eq_abs,
    ofReal_norm]

/-! ### The truncation error -/

/-- **Truncation error**: `|∫ f dν - ∫ clamp L (f x) dν| ≤ C.toReal / L^δ`. -/
theorem abs_integral_sub_clamp_le {ν : Measure E} [IsProbabilityMeasure ν] {f : E → ℝ}
    (hf : AEStronglyMeasurable f ν) {δ : ℝ} (hδ : 0 ≤ δ) {C : ENNReal} (hC : C ≠ ⊤)
    (hmom : ∫⁻ x, ‖f x‖ₑ ^ (1 + δ) ∂ν ≤ C) {L : ℝ} (hL : 0 < L) :
    |∫ x, f x ∂ν - ∫ x, clamp L (f x) ∂ν| ≤ C.toReal / L ^ δ := by
  have hint : Integrable f ν := integrable_of_moment hf hδ hC hmom
  have hclamp : Integrable (fun x => clamp L (f x)) ν := by
    refine Integrable.of_bound ?_ L (Eventually.of_forall fun x => ?_)
    · exact (continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hf
    · rw [Real.norm_eq_abs]
      exact abs_clamp_le hL.le _
  have hrpow : Integrable (fun x => |f x| ^ (1 + δ) / L ^ δ) ν :=
    (integrable_rpow_of_moment hf hδ hC hmom).div_const _
  rw [← integral_sub hint hclamp]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |f x - clamp L (f x)| ∂ν
      ≤ ∫ x, |f x| ^ (1 + δ) / L ^ δ ∂ν :=
        integral_mono (hint.sub hclamp).abs hrpow fun x => abs_sub_clamp_le hL hδ (f x)
    _ = (∫ x, |f x| ^ (1 + δ) ∂ν) / L ^ δ := integral_div _ _
    _ ≤ C.toReal / L ^ δ := by
        gcongr
        exact integral_rpow_le_of_moment hf hδ hC hmom

/-! ### Uniform comparison on compacts -/

section Topological

variable [TopologicalSpace E] [T2Space E] [BorelSpace E]

/-- Post-composing a locally uniformly convergent sequence with a continuous function keeps it
uniformly close on every compact. -/
theorem eventually_abs_comp_sub_le {F : E → ℝ} (hF : Continuous F) {Fs : ℕ → E → ℝ}
    {K : Set E} (hK : IsCompact K) (hunif : TendstoUniformlyOn Fs F atTop K) {g : ℝ → ℝ}
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ K, |g (Fs j x) - g (F x)| ≤ ε := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := F) hF.continuousOn
  have hUC : UniformContinuousOn g (Icc (-(R + 1)) (R + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨θ, hθ, hθg⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
  have hev := Metric.tendstoUniformlyOn_iff.1 hunif (min θ 1) (lt_min hθ one_pos)
  filter_upwards [hev] with j hj
  intro x hx
  have hd := hj x hx
  rw [Real.dist_eq] at hd
  have hFx : F x ∈ Icc (-(R + 1)) (R + 1) := by
    have := hR x hx
    rw [Real.norm_eq_abs, abs_le] at this
    constructor <;> linarith
  have hFjx : Fs j x ∈ Icc (-(R + 1)) (R + 1) := by
    have h1 := hR x hx
    rw [Real.norm_eq_abs, abs_le] at h1
    have h2 : |F x - Fs j x| < 1 := lt_of_lt_of_le hd (min_le_right _ _)
    rw [abs_lt] at h2
    constructor <;> linarith
  have := hθg (Fs j x) hFjx (F x) hFx (by
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_lt_of_le hd (min_le_left _ _))
  rw [Real.dist_eq] at this
  exact this.le

/-- Splitting an integral of a bounded function over a compact and its complement. -/
theorem abs_integral_sub_le_of_compact {ν : Measure E} [IsProbabilityMeasure ν]
    {u v : E → ℝ} (hu : AEStronglyMeasurable u ν) (hv : AEStronglyMeasurable v ν) {B : ℝ}
    (hBu : ∀ x, |u x| ≤ B) (hBv : ∀ x, |v x| ≤ B) {K : Set E} (hK : IsCompact K) {ω : ℝ}
    (hω : 0 ≤ ω) (hωK : ∀ x ∈ K, |u x - v x| ≤ ω) :
    |∫ x, u x ∂ν - ∫ x, v x ∂ν| ≤ ω + 2 * B * (ν Kᶜ).toReal := by
  have hui : Integrable u ν :=
    Integrable.of_bound hu B (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBu x)
  have hvi : Integrable v ν :=
    Integrable.of_bound hv B (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBv x)
  have hsub : Integrable (fun x => u x - v x) ν := hui.sub hvi
  rw [← integral_sub hui hvi, ← integral_add_compl hK.measurableSet hsub]
  have h1 : ‖∫ x in K, (u x - v x) ∂ν‖ ≤ ω * (ν K).toReal :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun x hx => by
      rw [Real.norm_eq_abs]; exact hωK x hx
  have h2 : ‖∫ x in Kᶜ, (u x - v x) ∂ν‖ ≤ (2 * B) * (ν Kᶜ).toReal :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun x _ => by
      rw [Real.norm_eq_abs]
      calc |u x - v x| ≤ |u x| + |v x| := abs_sub _ _
        _ ≤ B + B := add_le_add (hBu x) (hBv x)
        _ = 2 * B := by ring
  have hK1 : (ν K).toReal ≤ 1 := by
    have := prob_le_one (μ := ν) (s := K)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  calc |∫ x in K, (u x - v x) ∂ν + ∫ x in Kᶜ, (u x - v x) ∂ν|
      ≤ |∫ x in K, (u x - v x) ∂ν| + |∫ x in Kᶜ, (u x - v x) ∂ν| := abs_add_le _ _
    _ ≤ ω * (ν K).toReal + 2 * B * (ν Kᶜ).toReal := add_le_add h1 h2
    _ ≤ ω * 1 + 2 * B * (ν Kᶜ).toReal := by gcongr
    _ = ω + 2 * B * (ν Kᶜ).toReal := by ring

end Topological

/-! ### Moment transfer and the passage theorem -/

section Passage

variable [TopologicalSpace E] [T2Space E] [BorelSpace E] [HasOuterApproxClosed E]

/-- The truncated moment function `t ↦ min (|t|^{1+δ}) N`. -/
noncomputable def truncMoment (δ : ℝ) (N : ℕ) (t : ℝ) : ℝ := min (|t| ^ (1 + δ)) N

theorem continuous_truncMoment {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) : Continuous (truncMoment δ N) :=
  (continuous_abs.rpow_const fun _ => Or.inr (by linarith)).min continuous_const

theorem truncMoment_nonneg (δ : ℝ) (N : ℕ) (t : ℝ) : 0 ≤ truncMoment δ N t :=
  le_min (by positivity) (Nat.cast_nonneg N)

theorem truncMoment_le (δ : ℝ) (N : ℕ) (t : ℝ) : truncMoment δ N t ≤ N := min_le_right _ _

theorem abs_truncMoment_le (δ : ℝ) (N : ℕ) (t : ℝ) : |truncMoment δ N t| ≤ N := by
  rw [abs_of_nonneg (truncMoment_nonneg δ N t)]
  exact truncMoment_le δ N t

/-- A bounded continuous composite as a bounded continuous function. -/
noncomputable def boundedComp {F : E → ℝ} (hF : Continuous F) {g : ℝ → ℝ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ t, |g t| ≤ B) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => g (F x), hg.comp hF⟩ (2 * B) fun x y => by
    rw [Real.dist_eq]
    calc |g (F x) - g (F y)| ≤ |g (F x)| + |g (F y)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring

theorem boundedComp_apply {F : E → ℝ} (hF : Continuous F) {g : ℝ → ℝ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ t, |g t| ≤ B) (x : E) : boundedComp hF hg hB x = g (F x) := rfl

/-- **Moment transfer**: under weak convergence, tightness and local uniform convergence, the
`(1+δ)`-moment bound passes to the limit law. -/
theorem moment_limit_le {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (htight : ∀ η : ENNReal, 0 < η → ∃ K : Set E, IsCompact K ∧ ∀ j, (μs j : Measure E) Kᶜ ≤ η)
    {F : E → ℝ} (hF : Continuous F) {Fs : ℕ → E → ℝ} (hFs : ∀ j, Continuous (Fs j))
    (hunif : ∀ K : Set E, IsCompact K → TendstoUniformlyOn Fs F atTop K) {δ : ℝ} (hδ : 0 ≤ δ)
    {C : ENNReal} (hC : C ≠ ⊤) (hmom : ∀ j, ∫⁻ x, ‖Fs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) :
    ∫⁻ x, ‖F x‖ₑ ^ (1 + δ) ∂(μ : Measure E) ≤ C := by
  -- the truncated moments of the limit are bounded by `C.toReal`
  have hN : ∀ N : ℕ, ∫ x, truncMoment δ N (F x) ∂(μ : Measure E) ≤ C.toReal := by
    intro N
    refine le_of_forall_pos_le_add fun θ hθ => ?_
    -- tightness at scale `θ / (4 (N+1))`
    have hη : (0 : ENNReal) < ENNReal.ofReal (θ / (4 * ((N : ℝ) + 1))) := by
      rw [ENNReal.ofReal_pos]; positivity
    obtain ⟨K, hK, hKμ⟩ := htight _ hη
    have hKreal : ∀ j, 2 * (N : ℝ) * ((μs j : Measure E) Kᶜ).toReal ≤ θ / 2 := by
      intro j
      have h1 : ((μs j : Measure E) Kᶜ).toReal ≤ θ / (4 * ((N : ℝ) + 1)) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hKμ j)
      have hfrac : 2 * (N : ℝ) / (4 * ((N : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      calc 2 * (N : ℝ) * ((μs j : Measure E) Kᶜ).toReal
          ≤ 2 * (N : ℝ) * (θ / (4 * ((N : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = θ * (2 * (N : ℝ) / (4 * ((N : ℝ) + 1))) := by ring
        _ ≤ θ * (1 / 2) := mul_le_mul_of_nonneg_left hfrac hθ.le
        _ = θ / 2 := by ring
    -- uniform closeness of the truncated moments on `K`
    have hev := eventually_abs_comp_sub_le hF hK (hunif K hK) (continuous_truncMoment hδ N)
      (half_pos hθ)
    -- weak convergence of the bounded continuous test
    set φ := boundedComp hF (continuous_truncMoment hδ N) (abs_truncMoment_le δ N) with hφ
    have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ φ
    refine le_of_tendsto hconv ?_
    filter_upwards [hev] with j hj
    have hbound : ∫ x, truncMoment δ N (Fs j x) ∂(μs j : Measure E) ≤ C.toReal := by
      calc ∫ x, truncMoment δ N (Fs j x) ∂(μs j : Measure E)
          ≤ ∫ x, |Fs j x| ^ (1 + δ) ∂(μs j : Measure E) := by
            refine integral_mono ?_ (integrable_rpow_of_moment (hFs j).aestronglyMeasurable hδ hC
              (hmom j)) fun x => min_le_left _ _
            exact Integrable.of_bound
              ((continuous_truncMoment hδ N).comp (hFs j)).aestronglyMeasurable
              N (Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs]; exact abs_truncMoment_le δ N _)
        _ ≤ C.toReal := integral_rpow_le_of_moment (hFs j).aestronglyMeasurable hδ hC (hmom j)
    have hsplit := abs_integral_sub_le_of_compact (ν := (μs j : Measure E))
      ((continuous_truncMoment hδ N).comp hF).aestronglyMeasurable
      ((continuous_truncMoment hδ N).comp (hFs j)).aestronglyMeasurable
      (fun x => abs_truncMoment_le δ N (F x)) (fun x => abs_truncMoment_le δ N (Fs j x)) hK
      (half_pos hθ).le (fun x hx => by rw [abs_sub_comm]; exact hj x hx)
    have : ∫ x, φ x ∂(μs j : Measure E) = ∫ x, truncMoment δ N (F x) ∂(μs j : Measure E) := rfl
    rw [this]
    have hle := (abs_le.mp hsplit).2
    simp only [Function.comp_apply] at hle
    linarith [hKreal j]
  -- monotone convergence in `N`
  have hmono' : ∀ x, Monotone fun N : ℕ => ENNReal.ofReal (truncMoment δ N (F x)) := by
    intro x N M hNM
    refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
    exact_mod_cast hNM
  have hlim : ∀ x, Tendsto (fun N : ℕ => ENNReal.ofReal (truncMoment δ N (F x))) atTop
      (𝓝 (‖F x‖ₑ ^ (1 + δ))) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|F x| ^ (1 + δ)⌉₊] with N hN
    have hle : |F x| ^ (1 + δ) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [truncMoment, min_eq_left hle,
      ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (F x)) (by linarith : (0 : ℝ) ≤ 1 + δ),
      ← Real.norm_eq_abs, ofReal_norm]
  have hmeas : ∀ N : ℕ, Measurable fun x => ENNReal.ofReal (truncMoment δ N (F x)) := fun N =>
    ENNReal.measurable_ofReal.comp ((continuous_truncMoment hδ N).comp hF).measurable
  have htend := lintegral_tendsto_of_tendsto_of_monotone (μ := (μ : Measure E))
    (fun N => (hmeas N).aemeasurable) (Eventually.of_forall fun x => hmono' x)
    (Eventually.of_forall hlim)
  refine le_of_tendsto' htend fun N => ?_
  have hfin : ∫⁻ x, ENNReal.ofReal (truncMoment δ N (F x)) ∂(μ : Measure E) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) ?_
    calc ∫⁻ x, ENNReal.ofReal (truncMoment δ N (F x)) ∂(μ : Measure E)
        ≤ ∫⁻ _, (N : ENNReal) ∂(μ : Measure E) := lintegral_mono fun x => by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (truncMoment_le δ N _)
      _ = N := by simp
  have h := hN N
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => truncMoment_nonneg δ N (F x))
    ((continuous_truncMoment hδ N).comp hF).aestronglyMeasurable] at h
  exact (ENNReal.toReal_le_toReal hfin hC).mp h


/-- A truncation level with `C.toReal / L^δ < ε`. -/
theorem exists_truncation_level {δ : ℝ} (hδ : 0 < δ) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ c / L ^ δ < ε := by
  have h1 : Tendsto (fun L : ℝ => c / L ^ δ) atTop (𝓝 0) := by
    have := ((tendsto_rpow_atTop hδ).inv_tendsto_atTop).const_mul c
    rw [mul_zero] at this
    refine this.congr fun L => ?_
    rw [div_eq_mul_inv, Pi.inv_apply]
  obtain ⟨L, hL⟩ := ((h1.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)).exists
  exact ⟨L, hL.2, hL.1⟩

/-- **(QRP.9)**: uniformly integrable passage of correlations under weak convergence. -/
theorem tendsto_integral_of_locally_uniform {μs : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ))
    (htight : ∀ η : ENNReal, 0 < η → ∃ K : Set E, IsCompact K ∧ ∀ j, (μs j : Measure E) Kᶜ ≤ η)
    {F : E → ℝ} (hF : Continuous F) {Fs : ℕ → E → ℝ} (hFs : ∀ j, Continuous (Fs j))
    (hunif : ∀ K : Set E, IsCompact K → TendstoUniformlyOn Fs F atTop K) {δ : ℝ} (hδ : 0 < δ)
    {C : ENNReal} (hC : C ≠ ⊤) (hmom : ∀ j, ∫⁻ x, ‖Fs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) :
    Tendsto (fun j => ∫ x, Fs j x ∂(μs j : Measure E)) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure E))) := by
  have hmomμ := moment_limit_le hμ htight hF hFs hunif hδ.le hC hmom
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL1, hLε⟩ := exists_truncation_level hδ C.toReal (by positivity : (0 : ℝ) < ε / 8)
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  -- tightness at scale `ε / (16 (L+1))`
  have hη : (0 : ENNReal) < ENNReal.ofReal (ε / (16 * (L + 1))) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨K, hK, hKμ⟩ := htight _ hη
  have hKreal : ∀ j, 2 * L * ((μs j : Measure E) Kᶜ).toReal ≤ ε / 8 := by
    intro j
    have h1 : ((μs j : Measure E) Kᶜ).toReal ≤ ε / (16 * (L + 1)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hKμ j)
    have hfrac : 2 * L / (16 * (L + 1)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 2 * L * ((μs j : Measure E) Kᶜ).toReal ≤ 2 * L * (ε / (16 * (L + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε * (2 * L / (16 * (L + 1))) := by ring
      _ ≤ ε * (1 / 8) := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε / 8 := by ring
  have hclamp : Continuous (clamp L) := continuous_const.max (continuous_const.min continuous_id)
  have hev := eventually_abs_comp_sub_le hF hK (hunif K hK) hclamp (by positivity : (0 : ℝ) < ε / 8)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  set φ := boundedComp hF hclamp (abs_clamp_le hL0.le) with hφ
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ φ
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hconv (ε / 8) (by positivity)
  refine ⟨max N1 N2, fun j hj => ?_⟩
  have hj1 : ∀ x ∈ K, |clamp L (Fs j x) - clamp L (F x)| ≤ ε / 8 :=
    hN1 j (le_trans (le_max_left _ _) hj)
  have hj2 := hN2 j (le_trans (le_max_right _ _) hj)
  have hφj : ∫ x, φ x ∂(μs j : Measure E) = ∫ x, clamp L (F x) ∂(μs j : Measure E) := rfl
  have hφμ : ∫ x, φ x ∂(μ : Measure E) = ∫ x, clamp L (F x) ∂(μ : Measure E) := rfl
  rw [Real.dist_eq, hφj, hφμ] at hj2
  -- the four pieces
  have hA := abs_integral_sub_clamp_le (hFs j).aestronglyMeasurable hδ.le hC (hmom j) hL0
  have hB := abs_integral_sub_le_of_compact (ν := (μs j : Measure E))
    (hclamp.comp (hFs j)).aestronglyMeasurable (hclamp.comp hF).aestronglyMeasurable
    (fun x => abs_clamp_le hL0.le _) (fun x => abs_clamp_le hL0.le _) hK
    (by positivity : (0 : ℝ) ≤ ε / 8) hj1
  simp only [Function.comp_apply] at hB
  have hD := abs_integral_sub_clamp_le hF.aestronglyMeasurable hδ.le hC hmomμ hL0
  have hKj := hKreal j
  rw [Real.dist_eq]
  calc |∫ x, Fs j x ∂(μs j : Measure E) - ∫ x, F x ∂(μ : Measure E)|
      ≤ |∫ x, Fs j x ∂(μs j : Measure E) - ∫ x, clamp L (Fs j x) ∂(μs j : Measure E)|
        + |∫ x, clamp L (Fs j x) ∂(μs j : Measure E) - ∫ x, F x ∂(μ : Measure E)| :=
        abs_sub_le _ _ _
    _ ≤ |∫ x, Fs j x ∂(μs j : Measure E) - ∫ x, clamp L (Fs j x) ∂(μs j : Measure E)|
        + (|∫ x, clamp L (Fs j x) ∂(μs j : Measure E) - ∫ x, clamp L (F x) ∂(μs j : Measure E)|
          + |∫ x, clamp L (F x) ∂(μs j : Measure E) - ∫ x, F x ∂(μ : Measure E)|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ ≤ |∫ x, Fs j x ∂(μs j : Measure E) - ∫ x, clamp L (Fs j x) ∂(μs j : Measure E)|
        + (|∫ x, clamp L (Fs j x) ∂(μs j : Measure E) - ∫ x, clamp L (F x) ∂(μs j : Measure E)|
          + (|∫ x, clamp L (F x) ∂(μs j : Measure E) - ∫ x, clamp L (F x) ∂(μ : Measure E)|
            + |∫ x, clamp L (F x) ∂(μ : Measure E) - ∫ x, F x ∂(μ : Measure E)|)) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε := by
        rw [abs_sub_comm (∫ x, clamp L (F x) ∂(μ : Measure E))]
        linarith

/-- **Nontriviality**: if the variances of the approximating observables are bounded below by
`v > 0` and both `O_j` and `O_j²` satisfy the uniformly integrable passage hypotheses, the
limiting variance is at least `v`. -/
theorem variance_limit_ge {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (htight : ∀ η : ENNReal, 0 < η → ∃ K : Set E, IsCompact K ∧ ∀ j, (μs j : Measure E) Kᶜ ≤ η)
    {O : E → ℝ} (hO : Continuous O) {Os : ℕ → E → ℝ} (hOs : ∀ j, Continuous (Os j))
    (hunif : ∀ K : Set E, IsCompact K → TendstoUniformlyOn Os O atTop K) {δ : ℝ} (hδ : 0 < δ)
    {C : ENNReal} (hC : C ≠ ⊤) (hmom1 : ∀ j, ∫⁻ x, ‖Os j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C)
    (hmom2 : ∀ j, ∫⁻ x, ‖Os j x ^ 2‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) {v : ℝ}
    (hvar : ∀ j, v ≤ ∫ x, Os j x ^ 2 ∂(μs j : Measure E) - (∫ x, Os j x ∂(μs j : Measure E)) ^ 2) :
    v ≤ ∫ x, O x ^ 2 ∂(μ : Measure E) - (∫ x, O x ∂(μ : Measure E)) ^ 2 := by
  have h1 := tendsto_integral_of_locally_uniform hμ htight hO hOs hunif hδ hC hmom1
  have hunif2 : ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun j x => Os j x ^ 2) (fun x => O x ^ 2) atTop K := by
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have := eventually_abs_comp_sub_le hO hK (hunif K hK) (continuous_pow 2) (half_pos hε)
    filter_upwards [this] with j hj
    intro x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hj x hx) (half_lt_self hε)
  have h2 := tendsto_integral_of_locally_uniform hμ htight (hO.pow 2) (fun j => (hOs j).pow 2)
    hunif2 hδ hC hmom2
  exact ge_of_tendsto' (h2.sub (h1.pow 2)) hvar

end Passage

end QuantumFieldPassage
end NCG
