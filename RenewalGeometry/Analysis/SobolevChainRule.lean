/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevCriticalEmbedding
import RenewalGeometry.Analysis.SobolevLocalRellich
import RenewalGeometry.Analysis.LpProductContinuity

/-!
# The chain rule for weak derivatives on open sets

Generic infrastructure (no renewal notions) for the chart-composition clause
`eq:bounded-chart-composition` of `lem:products` (Einstein–Standard-Model action-closure
manuscript): if the components `u_c` (`c ∈ κ`, a finite index set) of a real vector-valued
function lie in `W^{1,2}(Ω)` with weak gradients `g_c`, and `Φ : ℝ^κ → ℝ` is `C¹`, then `Φ ∘ u`
has the weak partial derivatives

  `∂_i (Φ ∘ u) = Σ_c ∂_cΦ(u) · Re g_{c,i}`

(the real part only removes the imaginary part of the complex-valued gradient data of the real
functions `u_c`, which vanishes a.e.).

* `pd_comp`: the classical chain rule for partial derivatives;
* `integral_pd_mul_eq_neg_real`: integration by parts for real `C¹` functions against tests;
* `hasWeakPartial_comp` (**weak chain rule**, global form): `Φ ∈ C¹(ℝ^κ)` with bounded
  derivative.  Proof by mollification: for a test `φ ∈ C_c^∞(Ω)` the components are cut off
  (`χ u_c ∈ W^{1,2}(ℝ^ι)`, `χ = 1` near `supp φ`, `MemW12.mul_test`), mollified
  (`∂_i(ρ_k ⋆ χu_c) = ρ_k ⋆ ∂_i(χu_c)`, `pd_convolution_eq`), the classical chain rule and
  integration by parts are applied to `Φ(Re(ρ_k ⋆ χu))`, and the identity passes to the limit
  (`L²` convergence of mollifiers, Lipschitz bound on `Φ`, dominated convergence for the
  coefficients `∂_cΦ` along an a.e. convergent subsequence);
* `MemW12.comp`: the `W^{1,2}(Ω)` version on a set of finite measure;
* `hasWeakPartial_comp_of_mem_compact`, `MemW12.comp_of_mem_compact` (**chart version**): `Φ`
  only `C¹` on an open set `U` containing a compact set `K_c` in which `u` takes its values
  a.e. on `Ω` (e.g. a smooth algebraic coefficient `F(e, e⁻¹)` on a compact subset of a
  nondegenerate coframe chart); `Φ` is replaced by `χ Φ` with a cutoff `χ = 1` near `K_c`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Convolution

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Classical calculus -/

/-- A linear form on `ℝ^κ` is determined by its values on the coordinate vectors. -/
theorem clm_apply_eq_sum (Lf : (κ → ℝ) →L[ℝ] ℝ) (v : κ → ℝ) :
    Lf v = ∑ c, v c * Lf (Pi.single c 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, smul_eq_mul]

theorem norm_clm_single_le (Lf : (κ → ℝ) →L[ℝ] ℝ) (c : κ) :
    ‖Lf (Pi.single c 1)‖ ≤ ‖Lf‖ := by
  refine (Lf.le_opNorm _).trans ?_
  have : ‖(Pi.single c (1 : ℝ) : κ → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    by_cases h : j = c
    · subst h; simp
    · simp [Pi.single_apply, h]
  calc ‖Lf‖ * ‖(Pi.single c (1 : ℝ) : κ → ℝ)‖ ≤ ‖Lf‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖Lf‖ := mul_one _

/-- **Classical chain rule for partial derivatives.** -/
theorem pd_comp {Φ : (κ → ℝ) → ℝ} {V : κ → (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hΦ : DifferentiableAt ℝ Φ (fun c => V c x)) (hV : ∀ c, DifferentiableAt ℝ (V c) x) (i : ι) :
    pd (fun y => Φ (fun c => V c y)) i x =
      ∑ c, fderiv ℝ Φ (fun c => V c x) (Pi.single c 1) * pd (V c) i x := by
  have hVd : DifferentiableAt ℝ (fun y c => V c y) x := differentiableAt_pi.mpr hV
  unfold pd
  rw [show (fun y => Φ (fun c => V c y)) = Φ ∘ fun y c => V c y from rfl,
    fderiv_comp x hΦ hVd, fderiv_pi hV, ContinuousLinearMap.comp_apply,
    clm_apply_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

/-- Integration by parts for a real `C¹` function against a real test function:
`∫ ∂_iφ · f = -∫ φ · ∂_i f`. -/
theorem integral_pd_mul_eq_neg_real {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : ι) :
    ∫ x, pd φ i x * f x = -∫ x, φ x * pd f i x := by
  have hfc : ContDiff ℝ 1 (fun y => ((f y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have h := hasWeakPartial_of_contDiff univ hfc i φ ⟨hφ, hφc, subset_univ _⟩
  simp only [pd_ofReal hf] at h
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * ((f x : ℝ) : ℂ)) =
      fun x => (((pd φ i x * f x) : ℝ) : ℂ) := by funext x; push_cast; ring
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * ((pd f i x : ℝ) : ℂ)) =
      fun x => (((φ x * pd f i x) : ℝ) : ℂ) := by funext x; push_cast; ring
  rw [e1, e2, integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

/-! ### Limits of integrals -/

/-- If `|F_k - F| ≤ |ψ| G_k` with `ψ ∈ L²` and `G_k → 0` in `L²`, then `∫ F_k → ∫ F`. -/
theorem tendsto_integral_of_le_mul_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {F₀ : X → ℝ} (hF : ∀ k, Integrable (F k) μ)
    (hF₀ : AEStronglyMeasurable F₀ μ) {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) {G : ℕ → X → ℝ}
    (hG : ∀ k, AEStronglyMeasurable (G k) μ)
    (hGt : Tendsto (fun k => eLpNorm (G k) 2 μ) atTop (𝓝 0))
    (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x - F₀ x‖ ≤ ‖ψ x‖ * ‖G k x‖) :
    Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 (∫ x, F₀ x ∂μ)) := by
  refine tendsto_integral_of_L1' F₀ hF₀ (Eventually.of_forall hF) ?_
  have hb : ∀ k, eLpNorm (F k - F₀) 1 μ ≤ 1 * eLpNorm ψ 2 μ * eLpNorm (G k) 2 μ := by
    intro k
    refine (eLpNorm_mono_ae (g := fun x => ψ x * G k x) ?_).trans ?_
    · filter_upwards [hle k] with x hx
      rw [Pi.sub_apply, norm_mul]; exact hx
    · exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hψ.1 (hG k) (· * ·) 1
        (Eventually.of_forall fun x => by simp [nnnorm_mul])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
  have := ENNReal.Tendsto.const_mul hGt (a := 1 * eLpNorm ψ 2 μ)
    (Or.inr (by simpa using hψ.eLpNorm_ne_top))
  simpa using this

/-! ### The weak chain rule -/

/-- **Weak chain rule** (global `C¹` form).  Let `Ω ⊂ ℝ^ι` be open, `u_c ∈ W^{1,2}(Ω)` real
(`c ∈ κ`) with weak gradients `g_c`, and `Φ ∈ C¹(ℝ^κ)` with `‖DΦ‖ ≤ L`.  Then `Φ ∘ u` has the weak
partial derivatives `Σ_c ∂_cΦ(u) · Re g_{c,i}` on `Ω`. -/
theorem hasWeakPartial_comp {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {u : κ → (ι → ℝ) → ℝ}
    {g : κ → ι → (ι → ℝ) → ℂ} (hW : ∀ c, MemW12 Ω (fun x => ((u c x : ℝ) : ℂ)) (g c))
    {Φ : (κ → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) {L : ℝ≥0} (hL : ∀ y, ‖fderiv ℝ Φ y‖ ≤ L)
    (i : ι) :
    HasWeakPartial Ω i (fun x => ((Φ (fun c => u c x) : ℝ) : ℂ))
      (fun x => ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) : ℂ)) := by
  intro φ hφ
  -- reduce to a real identity
  suffices hreal : ∫ x, pd φ i x * Φ (fun c => u c x) =
      -∫ x, φ x * ∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re by
    have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * ((Φ (fun c => u c x) : ℝ) : ℂ)) =
        fun x => (((pd φ i x * Φ (fun c => u c x)) : ℝ) : ℂ) := by funext x; push_cast; ring
    have e2 : (fun x => ((φ x : ℝ) : ℂ) *
        ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) : ℂ)) =
        fun x => (((φ x * ∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re) :
          ℝ) : ℂ) := by funext x; push_cast; ring
    rw [e1, e2, integral_complex_ofReal, integral_complex_ofReal, hreal]
    push_cast; ring
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  -- the cutoff
  obtain ⟨χ, hχ, hχ1, -⟩ := exists_cutoff hΩ hφ.compact hφ.subset
  obtain ⟨M, hM⟩ := hχ.exists_bound
  obtain ⟨M', hM'⟩ := hχ.exists_bound_pd
  have hχ1x : ∀ x ∈ tsupport φ, χ x = 1 := fun x hx => hχ1.self_of_nhdsSet x hx
  have hpdχ : ∀ x ∈ tsupport φ, ∀ j, pd χ j x = 0 := by
    intro x hx j
    have hev : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hχ1.filter_mono (nhds_le_nhdsSet hx)
    unfold pd
    rw [hev.fderiv_eq]
    simp
  set w : κ → (ι → ℝ) → ℂ := fun c x => ((χ x : ℝ) : ℂ) * ((u c x : ℝ) : ℂ) with hwdef
  set G : κ → ι → (ι → ℝ) → ℂ := fun c j x =>
    ((χ x : ℝ) : ℂ) * g c j x + ((pd χ j x : ℝ) : ℂ) * ((u c x : ℝ) : ℂ) with hGdef
  have hwW : ∀ c, MemW12 univ (w c) (G c) := fun c => ((hW c).mul_test hΩ hχ hM hM').1
  have hw2 : ∀ c, MemLp (w c) 2 volume := fun c => by simpa using (hwW c).memLp
  have hG2 : ∀ c j, MemLp (G c j) 2 volume := fun c j => by simpa using (hwW c).memLp_grad j
  have hloc : ∀ c, LocallyIntegrable (w c) volume := fun c => (hw2 c).locallyIntegrable
    (by norm_num)
  -- mollifiers
  let φk : ℕ → ContDiffBump (0 : ι → ℝ) := fun k =>
    ⟨1 / ((k : ℝ) + 2), 2 / ((k : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  have hr : Tendsto (fun k => (φk k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 2)) atTop (𝓝 0)
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    simpa using this.const_div_atTop 2
  set ρ : ℕ → (ι → ℝ) → ℝ := fun k => (φk k).normed volume
  have hρs : ∀ k, ContDiff ℝ ∞ (ρ k) := fun k => (φk k).contDiff_normed
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k => (φk k).hasCompactSupport_normed
  set m : κ → ℕ → (ι → ℝ) → ℂ := fun c k => ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w c
  have hm : ∀ c k, ContDiff ℝ ∞ (m c k) := fun c k =>
    (hρc k).contDiff_convolution_left _ (hρs k) (hloc c)
  have hm1 : ∀ c k, ContDiff ℝ 1 (m c k) := fun c k => (hm c k).of_le (by simp)
  have hpdm : ∀ c k j x, pd (m c k) j x =
      (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c j) x := fun c k j x =>
    pd_convolution_eq (hρs k) (hρc k) ((hwW c).weak j) (hloc c) x
  have hmL2 : ∀ c, Tendsto (fun k => eLpNorm (m c k - w c) 2 volume) atTop (𝓝 0) := fun c =>
    Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub (μ := volume) hr (by norm_num)
      (by norm_num) (hw2 c)
  have hGL2 : ∀ c j, Tendsto (fun k => eLpNorm
      ((ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c j) - G c j) 2 volume) atTop (𝓝 0) :=
    fun c j => Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub (μ := volume) hr
      (by norm_num) (by norm_num) (hG2 c j)
  -- the real mollified fields and their limit
  set W : ℕ → (ι → ℝ) → κ → ℝ := fun k x c => (m c k x).re
  set w₀ : (ι → ℝ) → κ → ℝ := fun x c => (w c x).re
  have hw₀ : ∀ x, w₀ x = fun c => χ x * u c x := fun x => by
    funext c; simp [w₀, w]
  have hWd : ∀ k c, ContDiff ℝ 1 (fun x => W k x c) := fun k c =>
    Complex.reCLM.contDiff.comp (hm1 c k)
  have hWc : ∀ k, ContDiff ℝ 1 (W k) := fun k => contDiff_pi.mpr (hWd k)
  have hw₀m : AEStronglyMeasurable w₀ volume := by
    refine (aemeasurable_pi_lambda _ fun c => ?_).aestronglyMeasurable
    exact (Complex.continuous_re.comp_aestronglyMeasurable (hw2 c).1).aemeasurable
  have hWm : ∀ k, AEStronglyMeasurable (W k) volume := fun k => (hWc k).continuous.aestronglyMeasurable
  -- pointwise bound `‖W_k - w₀‖ ≤ Σ_c ‖m_{c,k} - w_c‖`
  have hWdist : ∀ k x, ‖W k x - w₀ x‖ ≤ ∑ c, ‖(m c k - w c) x‖ := by
    intro k x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
      fun c => ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun c => ‖(m c k - w c) x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ c))
    simp only [Pi.sub_apply, W, w₀, Real.norm_eq_abs, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have hsumL2 : Tendsto (fun k => eLpNorm (fun x => ∑ c, ‖(m c k - w c) x‖) 2 volume) atTop
      (𝓝 0) := by
    have hb : ∀ k, eLpNorm (fun x => ∑ c, ‖(m c k - w c) x‖) 2 volume ≤
        ∑ c, eLpNorm (m c k - w c) 2 volume := by
      intro k
      have := eLpNorm_sum_le (f := fun c x => ‖(m c k - w c) x‖) (s := Finset.univ)
        (fun c _ => ((hm c k).continuous.aestronglyMeasurable.sub (hw2 c).1).norm)
        (p := 2) (by norm_num)
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
      · congr 1; funext x; simp
      · refine Finset.sum_congr rfl fun c _ => eLpNorm_norm _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
    have := tendsto_finsetSum (Finset.univ : Finset κ) fun c _ => hmL2 c
    simpa using this
  have hWL2 : Tendsto (fun k => eLpNorm (W k - w₀) 2 volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumL2 (fun k => zero_le)
      fun k => eLpNorm_mono fun x => ?_
    refine (hWdist k x).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hWm hw₀m
    hWL2).exists_seq_tendsto_ae
  -- notation for the coefficient `∂_cΦ`
  set D : (κ → ℝ) → κ → ℝ := fun y c => fderiv ℝ Φ y (Pi.single c 1)
  have hDb : ∀ y c, ‖D y c‖ ≤ L := fun y c => (norm_clm_single_le _ c).trans (hL y)
  have hDc : ∀ c, Continuous fun y => D y c := fun c =>
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hΦL : LipschitzWith L Φ := lipschitzWith_of_nnnorm_fderiv_le
    (hΦ.differentiable one_ne_zero) (fun y => by
      have := hL y; rw [← NNReal.coe_le_coe]; simpa using this)
  -- the identity at level `k`
  have hk : ∀ k, ∫ x, pd φ i x * Φ (W k x) =
      -∫ x, φ x * ∑ c, D (W k x) c *
        ((ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) x).re := by
    intro k
    rw [integral_pd_mul_eq_neg_real (f := fun x => Φ (W k x)) (hΦ.comp (hWc k)) hφ.smooth hφ.compact i]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show φ x * pd (fun y => Φ (fun c => W k y c)) i x = _
    rw [pd_comp ((hΦ.differentiable one_ne_zero) _)
      (fun c => (hWd k c).differentiable one_ne_zero x) i]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    show pd (fun y => (m c k y).re) i x = _
    rw [pd_re (hm1 c k), hpdm]
  -- limit of the left side
  have hψ : MemLp (pd φ i) 2 volume :=
    (continuous_pd hφ1 i).memLp_of_hasCompactSupport (hasCompactSupport_pd hφ.compact i)
  have hLHS : Tendsto (fun k => ∫ x, pd φ i x * Φ (W k x)) atTop
      (𝓝 (∫ x, pd φ i x * Φ (w₀ x))) := by
    refine tendsto_integral_of_le_mul_L2 (G := fun k x => L * ∑ c, ‖(m c k - w c) x‖)
      (fun k => ?_) ?_ hψ (fun k => ?_) ?_ (fun k => Eventually.of_forall fun x => ?_)
    · exact ((continuous_pd hφ1 i).mul (hΦ.continuous.comp (hWc k).continuous))
        |>.integrable_of_hasCompactSupport (hasCompactSupport_pd hφ.compact i).mul_right
    · exact (continuous_pd hφ1 i).aestronglyMeasurable.mul
        (hΦ.continuous.comp_aestronglyMeasurable hw₀m)
    · exact aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
        ((hm c k).continuous.aestronglyMeasurable.sub (hw2 c).1).norm)
    · have := ENNReal.Tendsto.const_mul hsumL2 (a := (L : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
      simp only [mul_zero] at this
      refine this.congr fun k => ?_
      have hsm : (fun x => (L : ℝ) * ∑ c, ‖(m c k - w c) x‖) =
          (L : ℝ) • fun x => ∑ c, ‖(m c k - w c) x‖ := rfl
      rw [hsm, eLpNorm_const_smul]; simp
    · rw [← mul_sub, norm_mul]
      gcongr
      refine (hΦL.dist_le_mul _ _).trans ?_
      rw [dist_eq_norm, Real.norm_eq_abs, abs_mul, NNReal.abs_eq,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hWdist k x) L.coe_nonneg
  -- limit of the right side (along the subsequence)
  have hRHS : Tendsto (fun k => ∫ x, φ x * ∑ c, D (W (ns k) x) c *
        ((ρ (ns k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) x).re) atTop
      (𝓝 (∫ x, φ x * ∑ c, D (w₀ x) c * (G c i x).re)) := by
    set F : ℕ → (ι → ℝ) → ℝ := fun k x => φ x * ∑ c, D (W (ns k) x) c *
        ((ρ (ns k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) x).re
    set F₀ : (ι → ℝ) → ℝ := fun x => φ x * ∑ c, D (w₀ x) c * (G c i x).re
    have hφb : ∃ C, ∀ x, ‖φ x‖ ≤ C := hφ.continuous.bounded_above_of_compact_support hφ.compact
    obtain ⟨Cφ, hCφ⟩ := hφb
    have hφL2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφ.compact
    have hDm : ∀ c, AEStronglyMeasurable (fun x => D (w₀ x) c) volume := fun c =>
      (hDc c).comp_aestronglyMeasurable hw₀m
    have hGre : ∀ c, AEStronglyMeasurable (fun x => (G c i x).re) volume := fun c =>
      Complex.continuous_re.comp_aestronglyMeasurable (hG2 c i).1
    have hconvG : ∀ k c, Continuous (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) :=
      fun k c => ((hρc k).contDiff_convolution_left _ (hρs k)
        ((hG2 c i).locallyIntegrable (by norm_num))).continuous
    have hF₀m : AEStronglyMeasurable F₀ volume :=
      hφ.continuous.aestronglyMeasurable.mul (Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
        (hDm c).mul (hGre c))
    have hFint : ∀ k, Integrable (F k) volume := by
      intro k
      refine Continuous.integrable_of_hasCompactSupport ?_ hφ.compact.mul_right
      refine hφ.continuous.mul (continuous_finsetSum _ fun c _ => ?_)
      exact ((hDc c).comp (hWc (ns k)).continuous).mul
        (Complex.continuous_re.comp (hconvG (ns k) c))
    refine tendsto_integral_of_L1' F₀ hF₀m (Eventually.of_forall hFint) ?_
    -- split into the mollification error and the coefficient error
    set P : ℕ → (ι → ℝ) → ℝ := fun k x => ‖φ x‖ * (L *
      ∑ c, ‖((ρ (ns k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) - G c i) x‖)
    set Q : ℕ → (ι → ℝ) → ℝ := fun k x => ∑ c, ‖φ x‖ * ‖D (W (ns k) x) c - D (w₀ x) c‖ *
      ‖G c i x‖
    have hle : ∀ k x, ‖F k x - F₀ x‖ ≤ P k x + Q k x := by
      intro k x
      set R : κ → (ι → ℝ) → ℂ := fun c => ρ (ns k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i
      have hc : ∀ c, ‖D (W (ns k) x) c * (R c x).re - D (w₀ x) c * (G c i x).re‖ ≤
          L * ‖(R c - G c i) x‖ + ‖D (W (ns k) x) c - D (w₀ x) c‖ * ‖G c i x‖ := by
        intro c
        have hsplit : D (W (ns k) x) c * (R c x).re - D (w₀ x) c * (G c i x).re =
            D (W (ns k) x) c * ((R c - G c i) x).re + (D (W (ns k) x) c - D (w₀ x) c) *
              (G c i x).re := by
          simp only [Pi.sub_apply, Complex.sub_re]; ring
        have hre : ∀ z : ℂ, ‖z.re‖ ≤ ‖z‖ := fun z => by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
        rw [hsplit]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul (hDb _ c) (hre _) (norm_nonneg _) L.coe_nonneg
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hre _) (norm_nonneg _)
      calc ‖F k x - F₀ x‖ = ‖φ x‖ * ‖∑ c, (D (W (ns k) x) c * (R c x).re -
            D (w₀ x) c * (G c i x).re)‖ := by
            simp only [F, F₀, R]; rw [← mul_sub, norm_mul, ← Finset.sum_sub_distrib]
        _ ≤ ‖φ x‖ * ∑ c, (L * ‖(R c - G c i) x‖ +
            ‖D (W (ns k) x) c - D (w₀ x) c‖ * ‖G c i x‖) := by
            gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hc c)
        _ = P k x + Q k x := by
            simp only [P, Q, R]
            rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum]
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by ring
    have hPm : ∀ k, AEStronglyMeasurable (P k) volume := fun k =>
      hφ.continuous.norm.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul
        (Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
          ((hconvG (ns k) c).aestronglyMeasurable.sub (hG2 c i).1).norm))
    have hQm : ∀ k, AEStronglyMeasurable (Q k) volume := fun k =>
      Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
        (hφ.continuous.norm.aestronglyMeasurable.mul
          ((((hDc c).comp (hWc (ns k)).continuous).aestronglyMeasurable.sub (hDm c)).norm)).mul
          (hG2 c i).1.norm
    have hP : Tendsto (fun k => eLpNorm (P k) 1 volume) atTop (𝓝 0) := by
      have hb : ∀ k, eLpNorm (P k) 1 volume ≤ 1 * eLpNorm φ 2 volume *
          eLpNorm (fun x => L * ∑ c, ‖((ρ (ns k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            G c i) - G c i) x‖) 2 volume := by
        intro k
        refine le_trans (le_of_eq ?_) (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (r := 1) hφL2.1
          (aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
            ((hconvG (ns k) c).aestronglyMeasurable.sub (hG2 c i).1).norm))
          (fun a b => ‖a‖ * b) 1 (Eventually.of_forall fun x => ?_))
        · rfl
        · simp [nnnorm_mul]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
      have hs : Tendsto (fun k => eLpNorm (fun x => L * ∑ c, ‖((ρ k ⋆[ContinuousLinearMap.lsmul
          ℝ ℝ, volume] G c i) - G c i) x‖) 2 volume) atTop (𝓝 0) := by
        have hb2 : ∀ k, eLpNorm (fun x => L * ∑ c, ‖((ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            volume] G c i) - G c i) x‖) 2 volume ≤ L * ∑ c, eLpNorm ((ρ k ⋆[ContinuousLinearMap.lsmul
              ℝ ℝ, volume] G c i) - G c i) 2 volume := by
          intro k
          rw [show (fun x => (L : ℝ) * ∑ c, ‖((ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              G c i) - G c i) x‖) = (L : ℝ) • fun x => ∑ c, ‖((ρ k ⋆[ContinuousLinearMap.lsmul ℝ
              ℝ, volume] G c i) - G c i) x‖ from rfl, eLpNorm_const_smul]
          have h3 : ‖(L : ℝ)‖ₑ = (L : ℝ≥0∞) := by simp
          rw [h3]
          gcongr
          refine le_trans (le_of_eq ?_) ((eLpNorm_sum_le (s := Finset.univ)
            (f := fun c x => ‖((ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G c i) -
              G c i) x‖) (fun c _ => ((hconvG k c).aestronglyMeasurable.sub (hG2 c i).1).norm)
            (p := 2) (by norm_num)).trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
              eLpNorm_norm _)))
          congr 1; funext x; simp
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le)
          hb2
        have := ENNReal.Tendsto.const_mul (tendsto_finsetSum (Finset.univ : Finset κ)
          fun c _ => hGL2 c i) (a := (L : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
        simpa using this
      have := ENNReal.Tendsto.const_mul (hs.comp hns.tendsto_atTop)
        (a := 1 * eLpNorm φ 2 volume) (Or.inr (by simpa using hφL2.eLpNorm_ne_top))
      simpa using this
    have hQ : Tendsto (fun k => eLpNorm (Q k) 1 volume) atTop (𝓝 0) := by
      refine LpProductContinuity.tendsto_eLpNorm_of_dominated_ae (by norm_num) (by norm_num)
        hQm (g := fun x => ∑ c, ‖φ x‖ * (2 * L) * ‖G c i x‖) ?_ (fun k => ?_) ?_
      · refine memLp_finsetSum _ fun c _ => ?_
        have hφG : MemLp (fun x => φ x * ‖G c i x‖) 1 volume := by
          exact (hG2 c i).norm.mul' (r := 1) hφL2
        have := (hφG.norm).const_mul (2 * L)
        refine this.ae_eq (Eventually.of_forall fun x => ?_)
        simp only [norm_mul, Real.norm_eq_abs, abs_norm]; ring
      · refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
        refine Finset.sum_le_sum fun c _ => ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        linarith [hDb (W (ns k) x) c, hDb (w₀ x) c]
      · filter_upwards [hae] with x hx
        have : Tendsto (fun k => Q k x)
            atTop (𝓝 (∑ c : κ, ‖φ x‖ * ‖D (w₀ x) c - D (w₀ x) c‖ * ‖G c i x‖)) := by
          refine tendsto_finsetSum _ fun c _ => ?_
          refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds)
          exact ((((hDc c).tendsto _).comp hx).sub tendsto_const_nhds).norm
        rwa [show (∑ c : κ, ‖φ x‖ * ‖D (w₀ x) c - D (w₀ x) c‖ * ‖G c i x‖) = 0 by simp] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hP.add hQ) (fun k => zero_le) fun k => ?_
    refine (eLpNorm_mono_real (g := fun x => P k x + Q k x) fun x => ?_).trans
      (eLpNorm_add_le (hPm k) (hQm k) le_rfl)
    exact hle k x
  -- pass to the limit in the identity
  have h1 : Tendsto (fun k => ∫ x, pd φ i x * Φ (W (ns k) x)) atTop
      (𝓝 (∫ x, pd φ i x * Φ (w₀ x))) := hLHS.comp hns.tendsto_atTop
  have h2 : Tendsto (fun k => ∫ x, pd φ i x * Φ (W (ns k) x)) atTop
      (𝓝 (-∫ x, φ x * ∑ c, D (w₀ x) c * (G c i x).re)) := by
    simp only [hk]; exact hRHS.neg
  have hlim := tendsto_nhds_unique h1 h2
  -- identify the limit on the support of the test function
  have eL : ∫ x, pd φ i x * Φ (w₀ x) = ∫ x, pd φ i x * Φ (fun c => u c x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only [hw₀, hχ1x x hx, one_mul]
    · have : pd φ i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (tsupport_pd_subset φ i h))
      simp [this]
  have eR : ∫ x, φ x * ∑ c, D (w₀ x) c * (G c i x).re =
      ∫ x, φ x * ∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only [D, hw₀, hχ1x x hx, one_mul, G, hpdχ x hx]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← eL, ← eR]
  simpa using hlim

/-- **Weak chain rule in `W^{1,2}(Ω)`** (`Ω` open of finite measure, `Φ ∈ C¹` with bounded
derivative): `Φ ∘ u ∈ W^{1,2}(Ω)` with weak gradient `Σ_c ∂_cΦ(u) Re g_c`. -/
theorem MemW12.comp {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) (hΩf : volume Ω ≠ ⊤)
    {u : κ → (ι → ℝ) → ℝ} {g : κ → ι → (ι → ℝ) → ℂ}
    (hW : ∀ c, MemW12 Ω (fun x => ((u c x : ℝ) : ℂ)) (g c))
    {Φ : (κ → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) {L : ℝ≥0} (hL : ∀ y, ‖fderiv ℝ Φ y‖ ≤ L) :
    MemW12 Ω (fun x => ((Φ (fun c => u c x) : ℝ) : ℂ))
      (fun i x => ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) :
        ℂ)) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩf
  have hum : ∀ c, AEStronglyMeasurable (u c) (volume.restrict Ω) := fun c => by
    have := Complex.continuous_re.comp_aestronglyMeasurable (hW c).memLp.1
    simpa using this
  have hUm : AEStronglyMeasurable (fun x c => u c x) (volume.restrict Ω) :=
    (aemeasurable_pi_lambda _ fun c => (hum c).aemeasurable).aestronglyMeasurable
  have hu2 : ∀ c, MemLp (u c) 2 (volume.restrict Ω) := fun c =>
    (hW c).memLp.norm.of_le (hum c) (Eventually.of_forall fun x => by simp)
  have hΦL : LipschitzWith L Φ := lipschitzWith_of_nnnorm_fderiv_le
    (hΦ.differentiable one_ne_zero) (fun y => by
      have := hL y; rw [← NNReal.coe_le_coe]; simpa using this)
  refine ⟨?_, fun i => ?_, fun i => hasWeakPartial_comp hΩ hW hΦ hL i⟩
  · -- `|Φ(u)| ≤ |Φ 0| + L Σ_c |u_c|`
    have hs : MemLp (fun x => ∑ c, ‖u c x‖) 2 (volume.restrict Ω) :=
      memLp_finsetSum _ fun c _ => (hu2 c).norm
    have hs' : MemLp (fun x => (L : ℝ) * ∑ c, ‖u c x‖) 2 (volume.restrict Ω) := hs.const_mul _
    have hbd : MemLp (fun x => ‖Φ 0‖ + L * ∑ c, ‖u c x‖) 2 (volume.restrict Ω) :=
      (memLp_const ‖Φ 0‖).add hs'
    refine hbd.of_le ((Complex.continuous_ofReal.comp hΦ.continuous).comp_aestronglyMeasurable
      hUm) (Eventually.of_forall fun x => ?_)
    change ‖((Φ (fun c => u c x) : ℝ) : ℂ)‖ ≤ ‖‖Φ 0‖ + (L : ℝ) * ∑ c, ‖u c x‖‖
    rw [Complex.norm_real]
    have h1 : ‖Φ (fun c => u c x)‖ ≤ ‖Φ 0‖ + L * ‖(fun c => u c x)‖ := by
      have := hΦL.dist_le_mul (fun c => u c x) 0
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at this
      linarith [norm_sub_norm_le (Φ (fun c => u c x)) (Φ 0)]
    have h2 : ‖(fun c => u c x)‖ ≤ ∑ c, ‖u c x‖ := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
        fun c => Finset.single_le_sum (f := fun c => ‖u c x‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ c)
    have h3 : (0 : ℝ) ≤ ‖Φ 0‖ + L * ∑ c, ‖u c x‖ := by positivity
    calc ‖Φ (fun c => u c x)‖ ≤ ‖Φ 0‖ + L * ‖(fun c => u c x)‖ := h1
      _ ≤ ‖Φ 0‖ + L * ∑ c, ‖u c x‖ := by gcongr
      _ ≤ ‖‖Φ 0‖ + (L : ℝ) * ∑ c, ‖u c x‖‖ := (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
  · -- bounded coefficients times `L²` gradients
    have hterm : ∀ c, MemLp (fun x => fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) *
        (g c i x).re) 2 (volume.restrict Ω) := by
      intro c
      have hD : AEStronglyMeasurable (fun x => fderiv ℝ Φ (fun c => u c x) (Pi.single c 1))
          (volume.restrict Ω) :=
        ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp_aestronglyMeasurable
          hUm
      have hg : MemLp (fun x => (g c i x).re) 2 (volume.restrict Ω) :=
        ((hW c).memLp_grad i).re
      refine (hg.const_mul L).of_le (hD.mul hg.1) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (L : ℝ), NNReal.abs_eq]
      exact mul_le_mul_of_nonneg_right ((norm_clm_single_le _ c).trans (hL _)) (norm_nonneg _)
    have hsum : MemLp (fun x => ∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) *
        (g c i x).re) 2 (volume.restrict Ω) := memLp_finsetSum _ fun c _ => hterm c
    refine (hsum.norm.of_le ?_ (Eventually.of_forall fun x => ?_))
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hsum.1
    · change ‖((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, norm_norm]

/-! ### The chart version -/

/-- A `C¹` function on an open set `U ⊇ K_c` (`K_c` compact) agrees near `K_c` with a globally
`C¹` function of compact support, in particular with bounded derivative. -/
theorem exists_contDiff_extension {U Kc : Set (κ → ℝ)} (hU : IsOpen U) (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) {Φ : (κ → ℝ) → ℝ} (hΦ : ContDiffOn ℝ 1 Φ U) :
    ∃ Ψ : (κ → ℝ) → ℝ, ContDiff ℝ 1 Ψ ∧ (∃ L : ℝ≥0, ∀ y, ‖fderiv ℝ Ψ y‖ ≤ L) ∧
      ∀ y ∈ Kc, Ψ =ᶠ[𝓝 y] Φ := by
  obtain ⟨χ, hχ, hχ1, -⟩ := exists_cutoff hU hKc hKU
  set Ψ : (κ → ℝ) → ℝ := fun y => χ y * Φ y
  have hΨ : ContDiff ℝ 1 Ψ := by
    refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ U
    · exact (hχ.smooth.of_le (by simp)).contDiffAt.mul (hΦ.contDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hχ.subset h)
      have h0 : χ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with z hz
      simp [Ψ, hz]
  have hcs : HasCompactSupport Ψ := hχ.compact.mul_right
  obtain ⟨C, hC⟩ := (hΨ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hcs.fderiv (𝕜 := ℝ))
  refine ⟨Ψ, hΨ, ⟨C.toNNReal, fun y => (hC y).trans (Real.le_coe_toNNReal C)⟩, fun y hy => ?_⟩
  have h1 : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := hχ1.filter_mono (nhds_le_nhdsSet hy)
  filter_upwards [h1] with z hz
  simp [Ψ, hz]

/-- **Weak chain rule, chart version.**  If `u ∈ W^{1,2}(Ω)` takes its values a.e. on `Ω` in a
compact set `K_c` and `Φ` is `C¹` on an open `U ⊇ K_c`, then `Φ ∘ u` has the weak partials
`Σ_c ∂_cΦ(u) Re g_{c,i}` on `Ω`. -/
theorem hasWeakPartial_comp_of_mem_compact {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω)
    {u : κ → (ι → ℝ) → ℝ} {g : κ → ι → (ι → ℝ) → ℂ}
    (hW : ∀ c, MemW12 Ω (fun x => ((u c x : ℝ) : ℂ)) (g c))
    {U Kc : Set (κ → ℝ)} (hU : IsOpen U) (hKc : IsCompact Kc) (hKU : Kc ⊆ U)
    (hmem : ∀ᵐ x ∂(volume.restrict Ω), (fun c => u c x) ∈ Kc)
    {Φ : (κ → ℝ) → ℝ} (hΦ : ContDiffOn ℝ 1 Φ U) (i : ι) :
    HasWeakPartial Ω i (fun x => ((Φ (fun c => u c x) : ℝ) : ℂ))
      (fun x => ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) :
        ℂ)) := by
  obtain ⟨Ψ, hΨ, ⟨L, hL⟩, hΨΦ⟩ := exists_contDiff_extension hU hKc hKU hΦ
  have h := hasWeakPartial_comp hΩ hW hΨ hL i
  intro φ hφ
  have hmem' : ∀ᵐ x, x ∈ Ω → (fun c => u c x) ∈ Kc :=
    (ae_restrict_iff' hΩ.measurableSet).mp hmem
  have e1 : ∫ x, ((pd φ i x : ℝ) : ℂ) * ((Φ (fun c => u c x) : ℝ) : ℂ) =
      ∫ x, ((pd φ i x : ℝ) : ℂ) * ((Ψ (fun c => u c x) : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [hmem'] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [(hΨΦ _ (hx hxΩ)).eq_of_nhds]
    · have : pd φ i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hxΩ (hφ.subset (tsupport_pd_subset φ i h)))
      simp [this]
  have e2 : ∫ x, ((φ x : ℝ) : ℂ) *
        ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) : ℂ) =
      ∫ x, ((φ x : ℝ) : ℂ) *
        ((∑ c, fderiv ℝ Ψ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [hmem'] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [(hΨΦ _ (hx hxΩ)).fderiv_eq]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxΩ (hφ.subset h))
      simp [this]
  rw [e1, e2]
  exact h φ hφ

/-- **Weak chain rule in `W^{1,2}(Ω)`, chart version** (`Ω` open of finite measure). -/
theorem MemW12.comp_of_mem_compact {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) (hΩf : volume Ω ≠ ⊤)
    {u : κ → (ι → ℝ) → ℝ} {g : κ → ι → (ι → ℝ) → ℂ}
    (hW : ∀ c, MemW12 Ω (fun x => ((u c x : ℝ) : ℂ)) (g c))
    {U Kc : Set (κ → ℝ)} (hU : IsOpen U) (hKc : IsCompact Kc) (hKU : Kc ⊆ U)
    (hmem : ∀ᵐ x ∂(volume.restrict Ω), (fun c => u c x) ∈ Kc)
    {Φ : (κ → ℝ) → ℝ} (hΦ : ContDiffOn ℝ 1 Φ U) :
    MemW12 Ω (fun x => ((Φ (fun c => u c x) : ℝ) : ℂ))
      (fun i x => ((∑ c, fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * (g c i x).re : ℝ) :
        ℂ)) := by
  obtain ⟨Ψ, hΨ, ⟨L, hL⟩, hΨΦ⟩ := exists_contDiff_extension hU hKc hKU hΦ
  have hM := MemW12.comp hΩ hΩf hW hΨ hL
  refine ⟨hM.memLp.ae_eq ?_, fun i => (hM.memLp_grad i).ae_eq ?_,
    fun i => hasWeakPartial_comp_of_mem_compact hΩ hW hU hKc hKU hmem hΦ i⟩
  · filter_upwards [hmem] with x hx
    rw [(hΨΦ _ hx).eq_of_nhds]
  · filter_upwards [hmem] with x hx
    rw [(hΨΦ _ hx).fderiv_eq]

end RenewalGeometry.SobolevOpen
