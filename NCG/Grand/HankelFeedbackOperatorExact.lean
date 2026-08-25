/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ApproximationNumbersExact

/-!
# The feedback Hankel operator on `L²(ℝ₊; H₀)`

Machinery for `thm:feedback-Hankel-Weyl`: the Hankel operator
`(ℌ f)(t) = ∫₀^∞ M(t+s) f(s) ds` with memory kernel `M(t) = B e^{-tH} C` on the loaded carrier,
built as observability ∘ controllability.

This file (pass A) provides the analytic ingredients on the half line:

* `eLpNorm_expDecay`: the `L²(0,∞)` norm of `t ↦ e^{-Rt}` is `(1/(2R))^{1/2}`;
* `integral_expDecay_mul_norm_le`: the Cauchy–Schwarz pairing bound
  `∫₀^∞ e^{-Rs} ‖f s‖ ds ≤ (1/(2R))^{1/2} ‖f‖_{L²}`;
* `ctrl`: the controllability map `f ↦ ∫₀^∞ S(s) P C f(s) ds` and its bound
  `‖ctrl f‖ ≤ c (1/(2R))^{1/2} ‖f‖` under the screen `‖S(s) P‖ ≤ e^{-Rs}`;
* `obs`: the observability map `h ↦ (t ↦ B S(t) P h) ∈ L²` and its bound
  `‖obs h‖ ≤ b (1/(2R))^{1/2} ‖h‖`.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace NCG
namespace HankelFeedback

set_option linter.unusedSectionVars false

/-- The half-line Lebesgue measure. -/
noncomputable abbrev halfLine : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-! ### The exponential weight in `L²(0,∞)` -/

/-- The exponential weight `t ↦ e^{-Rt}`. -/
noncomputable def expDecay (R t : ℝ) : ℝ := Real.exp (-(R * t))

theorem integrableOn_expDecay {R : ℝ} (hR : 0 < R) : IntegrableOn (expDecay R) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) 0 hR).mpr
    (by rw [mul_zero]; exact integrableOn_exp_neg_Ioi 0)
  exact h

theorem memLp_expDecay {R : ℝ} (hR : 0 < R) : MemLp (expDecay R) 2 halfLine := by
  rw [memLp_two_iff_integrable_sq (Continuous.aestronglyMeasurable (by unfold expDecay; fun_prop))]
  have h := integrableOn_expDecay (R := 2 * R) (by positivity)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold expDecay
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The square integral `∫₀^∞ e^{-2Rt} dt = 1/(2R)`. -/
theorem integral_expDecay_sq {R : ℝ} (hR : 0 < R) :
    ∫ t in Ioi (0 : ℝ), expDecay R t ^ 2 = 1 / (2 * R) := by
  have h := exp_tail_integral (2 * R) (by positivity)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  unfold expDecay
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The `L²(0,∞)` norm of the exponential weight. -/
theorem eLpNorm_expDecay {R : ℝ} (hR : 0 < R) :
    eLpNorm (expDecay R) 2 halfLine = ENNReal.ofReal ((1 / (2 * R)) ^ ((1 : ℝ) / 2)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hint : Integrable (fun t => expDecay R t ^ 2) halfLine := by
    have := (memLp_expDecay hR).integrable_norm_rpow (by norm_num) (by norm_num)
    rw [ENNReal.toReal_ofNat] at this
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  have hlint : ∫⁻ t, ‖expDecay R t‖ₑ ^ (2 : ℝ) ∂halfLine = ENNReal.ofReal (1 / (2 * R)) := by
    rw [← integral_expDecay_sq hR,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [← ofReal_norm]
    try rw [ENNReal.rpow_two]
    rw [← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [hlint, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

theorem norm_toLp_expDecay {R : ℝ} (hR : 0 < R) :
    ‖(memLp_expDecay hR).toLp (expDecay R)‖ = (1 / (2 * R)) ^ ((1 : ℝ) / 2) := by
  rw [Lp.norm_toLp, eLpNorm_expDecay hR, ENNReal.toReal_ofReal (by positivity)]

/-! ### The Cauchy–Schwarz pairing on the half line -/

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [MeasurableSpace H₀] [BorelSpace H₀] [SecondCountableTopology H₀]

/-- **Cauchy–Schwarz on the half line**: `∫₀^∞ e^{-Rs} ‖f s‖ ds ≤ (1/(2R))^{1/2} ‖f‖_{L²}`. -/
theorem integral_expDecay_mul_norm_le {R : ℝ} (hR : 0 < R) (f : Lp H₀ 2 halfLine) :
    ∫ s, expDecay R s * ‖f s‖ ∂halfLine ≤ (1 / (2 * R)) ^ ((1 : ℝ) / 2) * ‖f‖ := by
  have hfn : MemLp (fun s => ‖f s‖) 2 halfLine := (Lp.memLp f).norm
  have hg := memLp_expDecay hR
  -- the pairing is an inner product in `L²(0,∞)`
  have hpair : ∫ s, expDecay R s * ‖f s‖ ∂halfLine
      = ⟪hg.toLp (expDecay R), hfn.toLp fun s => ‖f s‖⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hfn.coeFn_toLp] with s h1 h2
    rw [h1, h2]
    simp [mul_comm]
  rw [hpair]
  refine (real_inner_le_norm _ _).trans ?_
  rw [norm_toLp_expDecay hR, Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]

/-! ### Controllability and observability -/

/-- The memory data: a semigroup `S`, couplings `B C`, and a screen `P` with
`‖S(t) P‖ ≤ e^{-Rt}` on the half line. -/
structure Screen (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] where
  /-- the semigroup `e^{-tH}` -/
  S : ℝ → H₀ →L[ℝ] H₀
  /-- the screened range -/
  P : H₀ →L[ℝ] H₀
  /-- the couplings -/
  B : H₀ →L[ℝ] H₀
  C : H₀ →L[ℝ] H₀
  R : ℝ
  b : ℝ
  c : ℝ
  R_pos : 0 < R
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  S_cont : Continuous S
  screen : ∀ t, 0 ≤ t → ‖S t * P‖ ≤ expDecay R t
  B_le : ‖B‖ ≤ b
  C_le : ‖C‖ ≤ c

variable (M : Screen H₀)

/-- The controllability integrand `s ↦ S(s) P C f(s)`. -/
noncomputable def ctrlIntegrand (f : ℝ → H₀) (s : ℝ) : H₀ := M.S s (M.P (M.C (f s)))

theorem ctrlIntegrand_aestronglyMeasurable {f : ℝ → H₀} (hf : AEStronglyMeasurable f halfLine) :
    AEStronglyMeasurable (ctrlIntegrand M f) halfLine := by
  unfold ctrlIntegrand
  have hc : Continuous fun p : (H₀ →L[ℝ] H₀) × H₀ => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  exact hc.comp_aestronglyMeasurable₂ M.S_cont.aestronglyMeasurable
    ((M.P.comp M.C).continuous.comp_aestronglyMeasurable hf)

theorem norm_ctrlIntegrand_le (f : ℝ → H₀) (s : ℝ) (hs : 0 ≤ s) :
    ‖ctrlIntegrand M f s‖ ≤ M.c * (expDecay M.R s * ‖f s‖) := by
  unfold ctrlIntegrand
  calc ‖M.S s (M.P (M.C (f s)))‖ = ‖(M.S s * M.P) (M.C (f s))‖ := rfl
    _ ≤ ‖M.S s * M.P‖ * ‖M.C (f s)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ expDecay M.R s * (‖M.C‖ * ‖f s‖) :=
        mul_le_mul (M.screen s hs) (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          (by unfold expDecay; positivity)
    _ ≤ expDecay M.R s * (M.c * ‖f s‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right M.C_le (norm_nonneg _))
          (by unfold expDecay; positivity)
    _ = M.c * (expDecay M.R s * ‖f s‖) := by ring

theorem integrable_ctrlIntegrand (f : Lp H₀ 2 halfLine) :
    Integrable (ctrlIntegrand M f) halfLine := by
  have hfn : MemLp (fun s => ‖f s‖) 2 halfLine := (Lp.memLp f).norm
  have hprod : Integrable (fun s => expDecay M.R s * ‖f s‖) halfLine :=
    (memLp_expDecay M.R_pos).integrable_mul hfn
  refine (hprod.const_mul M.c).mono' (ctrlIntegrand_aestronglyMeasurable M (Lp.memLp f).1) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun s hs => norm_ctrlIntegrand_le M f s (le_of_lt hs)

/-- The controllability map `f ↦ ∫₀^∞ S(s) P C f(s) ds`. -/
noncomputable def ctrl (f : Lp H₀ 2 halfLine) : H₀ := ∫ s, ctrlIntegrand M f s ∂halfLine

/-- **Controllability bound**: `‖ctrl f‖ ≤ c (1/(2R))^{1/2} ‖f‖`. -/
theorem norm_ctrl_le (f : Lp H₀ 2 halfLine) :
    ‖ctrl M f‖ ≤ M.c * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * ‖f‖ := by
  unfold ctrl
  have hfn : MemLp (fun s => ‖f s‖) 2 halfLine := (Lp.memLp f).norm
  have hprod : Integrable (fun s => M.c * (expDecay M.R s * ‖f s‖)) halfLine :=
    ((memLp_expDecay M.R_pos).integrable_mul hfn).const_mul M.c
  calc ‖∫ s, ctrlIntegrand M f s ∂halfLine‖
      ≤ ∫ s, M.c * (expDecay M.R s * ‖f s‖) ∂halfLine := by
        refine norm_integral_le_of_norm_le hprod ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun s hs => norm_ctrlIntegrand_le M f s (le_of_lt hs)
    _ = M.c * ∫ s, expDecay M.R s * ‖f s‖ ∂halfLine := integral_const_mul _ _
    _ ≤ M.c * ((1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (integral_expDecay_mul_norm_le M.R_pos f) M.c_nonneg
    _ = M.c * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * ‖f‖ := by ring

/-- The observability path `t ↦ B S(t) P h`. -/
noncomputable def obsFun (h : H₀) (t : ℝ) : H₀ := M.B (M.S t (M.P h))

theorem continuous_obsFun (h : H₀) : Continuous (obsFun M h) := by
  unfold obsFun
  exact M.B.continuous.comp ((ContinuousLinearMap.apply ℝ H₀ (M.P h)).continuous.comp M.S_cont)

theorem norm_obsFun_le (h : H₀) (t : ℝ) (ht : 0 ≤ t) :
    ‖obsFun M h t‖ ≤ M.b * ‖h‖ * expDecay M.R t := by
  unfold obsFun
  calc ‖M.B (M.S t (M.P h))‖ ≤ ‖M.B‖ * ‖(M.S t * M.P) h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M.b * (‖M.S t * M.P‖ * ‖h‖) :=
        mul_le_mul M.B_le (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) M.b_nonneg
    _ ≤ M.b * (expDecay M.R t * ‖h‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (M.screen t ht) (norm_nonneg _))
          M.b_nonneg
    _ = M.b * ‖h‖ * expDecay M.R t := by ring

theorem memLp_obsFun (h : H₀) : MemLp (obsFun M h) 2 halfLine := by
  refine MemLp.of_le ((memLp_expDecay M.R_pos).const_mul (M.b * ‖h‖))
    (continuous_obsFun M h).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg M.b_nonneg (norm_nonneg _))
    (by unfold expDecay; positivity))]
  exact norm_obsFun_le M h t (le_of_lt ht)

/-- The observability map `h ↦ (t ↦ B S(t) P h) ∈ L²(0,∞; H₀)`. -/
noncomputable def obs (h : H₀) : Lp H₀ 2 halfLine := (memLp_obsFun M h).toLp (obsFun M h)

/-- **Observability bound**: `‖obs h‖ ≤ b (1/(2R))^{1/2} ‖h‖`. -/
theorem norm_obs_le (h : H₀) : ‖obs M h‖ ≤ M.b * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * ‖h‖ := by
  unfold obs
  rw [Lp.norm_toLp]
  have hmono : eLpNorm (obsFun M h) 2 halfLine
      ≤ eLpNorm (fun t => M.b * ‖h‖ * expDecay M.R t) 2 halfLine := by
    refine eLpNorm_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg M.b_nonneg (norm_nonneg _))
      (by unfold expDecay; positivity))]
    exact norm_obsFun_le M h t (le_of_lt ht)
  have hconst : eLpNorm (fun t => M.b * ‖h‖ * expDecay M.R t) 2 halfLine
      = ‖M.b * ‖h‖‖ₑ * eLpNorm (expDecay M.R) 2 halfLine := by
    rw [← eLpNorm_const_smul]
    rfl
  have hfin : ‖M.b * ‖h‖‖ₑ * eLpNorm (expDecay M.R) 2 halfLine ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (memLp_expDecay M.R_pos).eLpNorm_ne_top
  calc (eLpNorm (obsFun M h) 2 halfLine).toReal
      ≤ (‖M.b * ‖h‖‖ₑ * eLpNorm (expDecay M.R) 2 halfLine).toReal :=
        ENNReal.toReal_mono hfin (hconst ▸ hmono)
    _ = M.b * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * ‖h‖ := by
        rw [ENNReal.toReal_mul, eLpNorm_expDecay M.R_pos,
          ENNReal.toReal_ofReal (Real.rpow_nonneg (by have := M.R_pos; positivity) _),
          toReal_enorm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg M.b_nonneg (norm_nonneg _))]
        ring

/-! ### Linear structure and bounded operators -/

theorem ctrl_add (f g : Lp H₀ 2 halfLine) : ctrl M (f + g) = ctrl M f + ctrl M g := by
  unfold ctrl
  rw [← integral_add (integrable_ctrlIntegrand M f) (integrable_ctrlIntegrand M g)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with s hs
  simp only [ctrlIntegrand, hs, Pi.add_apply, map_add]

theorem ctrl_smul (r : ℝ) (f : Lp H₀ 2 halfLine) : ctrl M (r • f) = r • ctrl M f := by
  unfold ctrl
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul r f] with s hs
  simp only [ctrlIntegrand, hs, Pi.smul_apply, map_smul]

/-- The controllability operator as a bounded linear map `L²(0,∞; H₀) → H₀`. -/
noncomputable def ctrlL : Lp H₀ 2 halfLine →L[ℝ] H₀ :=
  LinearMap.mkContinuous
    { toFun := ctrl M
      map_add' := ctrl_add M
      map_smul' := ctrl_smul M }
    (M.c * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)) (norm_ctrl_le M)

theorem ctrlL_apply (f : Lp H₀ 2 halfLine) : ctrlL M f = ctrl M f := rfl

theorem norm_ctrlL_le : ‖ctrlL M‖ ≤ M.c * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg M.c_nonneg (Real.rpow_nonneg (by have := M.R_pos; positivity) _)) _

theorem obs_add (h k : H₀) : obs M (h + k) = obs M h + obs M k := by
  unfold obs
  rw [← MemLp.toLp_add]
  congr 1
  funext t
  simp [obsFun]

theorem obs_smul (r : ℝ) (h : H₀) : obs M (r • h) = r • obs M h := by
  unfold obs
  rw [← MemLp.toLp_const_smul]
  congr 1
  funext t
  simp [obsFun]

/-- The observability operator as a bounded linear map `H₀ → L²(0,∞; H₀)`. -/
noncomputable def obsL : H₀ →L[ℝ] Lp H₀ 2 halfLine :=
  LinearMap.mkContinuous
    { toFun := obs M
      map_add' := obs_add M
      map_smul' := obs_smul M }
    (M.b * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)) (norm_obs_le M)

theorem obsL_apply (h : H₀) : obsL M h = obs M h := rfl

theorem norm_obsL_le : ‖obsL M‖ ≤ M.b * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg M.b_nonneg (Real.rpow_nonneg (by have := M.R_pos; positivity) _)) _

/-- The screened Hankel operator `obs ∘ ctrl`. -/
noncomputable def hankel : Lp H₀ 2 halfLine →L[ℝ] Lp H₀ 2 halfLine := (obsL M).comp (ctrlL M)

/-- **Norm bound**: `‖ℌ_M‖ ≤ b c / (2R)` for the screened Hankel operator. -/
theorem norm_hankel_le : ‖hankel M‖ ≤ M.b * M.c / (2 * M.R) := by
  have hR := M.R_pos
  have hsq : (1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)
      = 1 / (2 * M.R) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  calc ‖hankel M‖ ≤ ‖obsL M‖ * ‖ctrlL M‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M.b * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)) * (M.c * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul (norm_obsL_le M) (norm_ctrlL_le M) (norm_nonneg (ctrlL M))
          (mul_nonneg M.b_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = M.b * M.c * ((1 / (2 * M.R)) ^ ((1 : ℝ) / 2) * (1 / (2 * M.R)) ^ ((1 : ℝ) / 2)) := by
        ring
    _ = M.b * M.c / (2 * M.R) := by rw [hsq]; ring

/-- For an idempotent screen commuting with the semigroup, the controllability map lands in the
range of the screen. -/
theorem ctrl_mem_range (hcomm : ∀ t, M.S t * M.P = M.P * M.S t) (hidem : M.P * M.P = M.P)
    (f : Lp H₀ 2 halfLine) : ctrl M f ∈ LinearMap.range M.P.toLinearMap := by
  refine ⟨ctrl M f, ?_⟩
  change M.P (ctrl M f) = ctrl M f
  unfold ctrl
  rw [← ContinuousLinearMap.integral_comp_comm M.P (integrable_ctrlIntegrand M f)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [ctrlIntegrand]
  change (M.P * M.S s) (M.P (M.C (f s))) = M.S s (M.P (M.C (f s)))
  rw [← hcomm s]
  change M.S s ((M.P * M.P) (M.C (f s))) = M.S s (M.P (M.C (f s)))
  rw [hidem]

/-- **Finite rank**: the screened Hankel operator has rank at most the rank of the screen. -/
theorem finrank_range_hankel_le [FiniteDimensional ℝ H₀]
    (hcomm : ∀ t, M.S t * M.P = M.P * M.S t) (hidem : M.P * M.P = M.P) :
    Module.finrank ℝ (LinearMap.range (hankel M).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range M.P.toLinearMap) := by
  have hsub : LinearMap.range (hankel M).toLinearMap ≤
      LinearMap.range ((obsL M).toLinearMap.comp (LinearMap.range M.P.toLinearMap).subtype) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨ctrl M f, ctrl_mem_range M hcomm hidem f⟩, rfl⟩
  exact (Submodule.finrank_mono hsub).trans (LinearMap.finrank_range_le _)

/-- **Compactness**: the Hankel operator factors through the finite-dimensional carrier. -/
theorem isCompactOperator_hankel [FiniteDimensional ℝ H₀] : IsCompactOperator (hankel M) :=
  (isCompactOperator_of_locallyCompactSpace_dom (ctrlL M)).clm_comp (obsL M)

/-! ### Low/high splitting of the memory -/

/-- Loaded-transient memory data with a spectral splitting `1 = P + Q` into low and high modes:
`‖S(t)‖, ‖S(t) P‖ ≤ e^{-λt}` (transient floor) and `‖S(t) Q‖ ≤ e^{-Rt}` (screen). -/
structure Splitting (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] where
  S : ℝ → H₀ →L[ℝ] H₀
  B : H₀ →L[ℝ] H₀
  C : H₀ →L[ℝ] H₀
  P : H₀ →L[ℝ] H₀
  Q : H₀ →L[ℝ] H₀
  lam : ℝ
  R : ℝ
  b : ℝ
  c : ℝ
  lam_pos : 0 < lam
  R_pos : 0 < R
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  S_cont : Continuous S
  full : ∀ t, 0 ≤ t → ‖S t‖ ≤ expDecay lam t
  low : ∀ t, 0 ≤ t → ‖S t * P‖ ≤ expDecay lam t
  high : ∀ t, 0 ≤ t → ‖S t * Q‖ ≤ expDecay R t
  B_le : ‖B‖ ≤ b
  C_le : ‖C‖ ≤ c
  PQ : P + Q = 1
  PmulQ : P * Q = 0
  QmulP : Q * P = 0
  Pidem : P * P = P
  Qidem : Q * Q = Q
  commP : ∀ t, S t * P = P * S t
  commQ : ∀ t, S t * Q = Q * S t

variable (W : Splitting H₀)

/-- The full memory as a screen (`Π = 1`). -/
noncomputable def Splitting.fullScreen : Screen H₀ where
  S := W.S
  P := 1
  B := W.B
  C := W.C
  R := W.lam
  b := W.b
  c := W.c
  R_pos := W.lam_pos
  b_nonneg := W.b_nonneg
  c_nonneg := W.c_nonneg
  S_cont := W.S_cont
  screen := fun t ht => by rw [mul_one]; exact W.full t ht
  B_le := W.B_le
  C_le := W.C_le

/-- The low-energy screen. -/
noncomputable def Splitting.lowScreen : Screen H₀ where
  S := W.S
  P := W.P
  B := W.B
  C := W.C
  R := W.lam
  b := W.b
  c := W.c
  R_pos := W.lam_pos
  b_nonneg := W.b_nonneg
  c_nonneg := W.c_nonneg
  S_cont := W.S_cont
  screen := W.low
  B_le := W.B_le
  C_le := W.C_le

/-- The high-energy screen. -/
noncomputable def Splitting.highScreen : Screen H₀ where
  S := W.S
  P := W.Q
  B := W.B
  C := W.C
  R := W.R
  b := W.b
  c := W.c
  R_pos := W.R_pos
  b_nonneg := W.b_nonneg
  c_nonneg := W.c_nonneg
  S_cont := W.S_cont
  screen := W.high
  B_le := W.B_le
  C_le := W.C_le

theorem Splitting.one_apply (h : H₀) : h = W.P h + W.Q h := by
  have := congrArg (fun L : H₀ →L[ℝ] H₀ => L h) W.PQ
  simpa using this.symm

/-- The observability map splits. -/
theorem obs_full_eq (h : H₀) :
    obs W.fullScreen h = obs W.lowScreen h + obs W.highScreen h := by
  unfold obs
  rw [← MemLp.toLp_add]
  congr 1
  funext t
  simp only [obsFun, Splitting.fullScreen, Splitting.lowScreen, Splitting.highScreen,
    one_apply_eq_self, Pi.add_apply]
  rw [← map_add, ← map_add, ← W.one_apply h]

/-- The controllability map splits. -/
theorem ctrl_full_eq (f : Lp H₀ 2 halfLine) :
    ctrl W.fullScreen f = ctrl W.lowScreen f + ctrl W.highScreen f := by
  unfold ctrl
  rw [← integral_add (integrable_ctrlIntegrand _ f) (integrable_ctrlIntegrand _ f)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [ctrlIntegrand, Splitting.fullScreen, Splitting.lowScreen, Splitting.highScreen,
    one_apply_eq_self]
  rw [← map_add, ← W.one_apply]

/-- The low observability map kills the range of `Q`. -/
theorem obs_low_Q (y : H₀) : obs W.lowScreen (W.Q y) = 0 := by
  unfold obs
  have : obsFun W.lowScreen (W.Q y) = fun _ => 0 := by
    funext t
    simp only [obsFun, Splitting.lowScreen]
    change W.B (W.S t ((W.P * W.Q) y)) = 0
    rw [W.PmulQ]
    simp
  refine Lp.ext ?_
  filter_upwards [(memLp_obsFun W.lowScreen (W.Q y)).coeFn_toLp,
    Lp.coeFn_zero (E := H₀) (p := 2) (μ := halfLine)] with t h1 h2
  rw [h1, h2, this]
  rfl

/-- The high observability map kills the range of `P`. -/
theorem obs_high_P (y : H₀) : obs W.highScreen (W.P y) = 0 := by
  unfold obs
  have : obsFun W.highScreen (W.P y) = fun _ => 0 := by
    funext t
    simp only [obsFun, Splitting.highScreen]
    change W.B (W.S t ((W.Q * W.P) y)) = 0
    rw [W.QmulP]
    simp
  refine Lp.ext ?_
  filter_upwards [(memLp_obsFun W.highScreen (W.P y)).coeFn_toLp,
    Lp.coeFn_zero (E := H₀) (p := 2) (μ := halfLine)] with t h1 h2
  rw [h1, h2, this]
  rfl

theorem obsL_full_eq : obsL W.fullScreen = obsL W.lowScreen + obsL W.highScreen :=
  ContinuousLinearMap.ext fun h => by
    simp only [add_apply, obsL_apply]
    exact obs_full_eq W h

theorem ctrlL_full_eq : ctrlL W.fullScreen = ctrlL W.lowScreen + ctrlL W.highScreen :=
  ContinuousLinearMap.ext fun f => by
    simp only [add_apply, ctrlL_apply]
    exact ctrl_full_eq W f

theorem obsL_low_comp_ctrlL_high : (obsL W.lowScreen).comp (ctrlL W.highScreen) = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, zero_apply, obsL_apply,
    ctrlL_apply]
  obtain ⟨y, hy⟩ := ctrl_mem_range W.highScreen W.commQ W.Qidem f
  have hy' : ctrl W.highScreen f = W.Q y := hy.symm
  rw [hy']
  exact obs_low_Q W y

theorem obsL_high_comp_ctrlL_low : (obsL W.highScreen).comp (ctrlL W.lowScreen) = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, zero_apply, obsL_apply,
    ctrlL_apply]
  obtain ⟨y, hy⟩ := ctrl_mem_range W.lowScreen W.commP W.Pidem f
  have hy' : ctrl W.lowScreen f = W.P y := hy.symm
  rw [hy']
  exact obs_high_P W y

/-- **Splitting of the Hankel operator**: `ℌ = ℌ_{≤R} + ℌ_{>R}`. -/
theorem hankel_full_eq : hankel W.fullScreen = hankel W.lowScreen + hankel W.highScreen := by
  unfold hankel
  rw [obsL_full_eq, ctrlL_full_eq, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add, obsL_low_comp_ctrlL_high, obsL_high_comp_ctrlL_low]
  abel

/-- **Hankel truncation**: `‖ℌ - ℌ_{≤R}‖ ≤ b c/(2R)`, `rank ℌ_{≤R} ≤ rank P_R`, and `ℌ` is
compact. -/
theorem hankel_truncation [FiniteDimensional ℝ H₀] :
    ‖hankel W.fullScreen - hankel W.lowScreen‖ ≤ W.b * W.c / (2 * W.R) ∧
      Module.finrank ℝ (LinearMap.range (hankel W.lowScreen).toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range W.P.toLinearMap) ∧
      IsCompactOperator (hankel W.fullScreen) := by
  refine ⟨?_, finrank_range_hankel_le W.lowScreen W.commP W.Pidem, isCompactOperator_hankel _⟩
  rw [hankel_full_eq, add_sub_cancel_left]
  exact norm_hankel_le W.highScreen

/-- **The dimension-three decay law** for a family of splittings sharing the full memory `T`:
if `rank P_R ≤ C_W R^{3/2}`, then `a_{n+1}(T) ≤ (b c C_W^{2/3}/2) n^{-2/3}`. -/
theorem hankel_approxNumber_decay [FiniteDimensional ℝ H₀] (W : ℝ → Splitting H₀)
    (T : Lp H₀ 2 halfLine →L[ℝ] Lp H₀ 2 halfLine) (hT : ∀ R, 0 < R → hankel (W R).fullScreen = T)
    {b c CW : ℝ} (hbc : 0 < b * c) (hCW : 0 < CW)
    (hR : ∀ R, 0 < R → (W R).R = R) (hb : ∀ R, 0 < R → (W R).b = b) (hc : ∀ R, 0 < R → (W R).c = c)
    (hrank : ∀ R, 0 < R →
      (Module.finrank ℝ (LinearMap.range (W R).P.toLinearMap) : ℝ) ≤ CW * R ^ ((3 : ℝ) / 2))
    (n : ℕ) (hn : 0 < n) :
    ApproximationNumbers.approxNumber T (n + 1)
      ≤ (b * c * CW ^ ((2 : ℝ) / 3) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 3)) := by
  refine ApproximationNumbers.approxNumber_le_decay T hbc hCW (fun R => hankel (W R).lowScreen)
    (fun R hRpos => ?_) (fun R hRpos => ?_) n hn
  · have h1 := (hankel_truncation (W R)).2.1
    exact (Nat.cast_le.mpr h1).trans (hrank R hRpos)
  · have h1 := (hankel_truncation (W R)).1
    rw [hT R hRpos, hR R hRpos, hb R hRpos, hc R hRpos] at h1
    exact h1

/-- **Field count**: at `R = (Z b c/ε)^{1/2}` the rank envelope reads
`C_W (1 + (Z b c/ε)^{3/4})` and the Feshbach remainder `|z| b c / R²` is at most `ε` on the
window `|z| ≤ Z`. -/
theorem field_count {CW Z b c ε : ℝ} (_hCW : 0 ≤ CW) (hZ : 0 < Z) (hb : 0 < b) (hc : 0 < c)
    (hε : 0 < ε) :
    CW * (1 + ((Z * b * c / ε) ^ ((1 : ℝ) / 2)) ^ ((3 : ℝ) / 2))
        = CW * (1 + (Z * b * c / ε) ^ ((3 : ℝ) / 4)) ∧
      ∀ z : ℝ, |z| ≤ Z → |z| * b * c / ((Z * b * c / ε) ^ ((1 : ℝ) / 2)) ^ 2 ≤ ε := by
  have hx : 0 < Z * b * c / ε := by positivity
  constructor
  · rw [← Real.rpow_mul hx.le]
    norm_num
  · intro z hz
    have hsq : ((Z * b * c / ε) ^ ((1 : ℝ) / 2)) ^ 2 = Z * b * c / ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    rw [hsq, div_le_iff₀ hx]
    have : ε * (Z * b * c / ε) = Z * b * c := by field_simp
    rw [this]
    gcongr

end HankelFeedback
end NCG
