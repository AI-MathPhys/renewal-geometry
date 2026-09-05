/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HypocoerciveFlowExact

/-!
# Lyapunov solution, exponential decay, and the hypocoercive memory alternative

Machinery for `thm:GT-hypocoercive-memory`, Lyapunov part, and the bundled theorem.

* `norm_flow_one_lt_one`: (H4) and (FC.10) give the strict sampled contraction `‖e^{K}‖ < 1`
  (through the norm bridge for positive operators);
* `exists_decay`: a strict sampled contraction gives exponential decay `‖e^{tK}‖ ≤ C e^{-εt}`;
* `lyapunovSol K = ∫₀^∞ e^{tK*} e^{tK} dt` solves `K* P + P K = -I`, is positive definite, and is
  the unique solution (`lyapunov_eq`, `lyapunovSol_pos`, `lyapunov_unique`);
* `eigenvaluesNeg_of_lyapunov`: a positive definite Lyapunov solution forces every eigenvalue of
  `K` into the open left half-plane;
* `hypocoercive_memory`: the bundled statement (FC.9), (H1) ⟺ (H2) ⟺ (H3) ⟺ (H4) ⟺ (H5), (FC.10).
-/

open ContinuousLinearMap Finset Module NormedSpace Set Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace NCG
namespace HypocoerciveMemory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K S : E →L[ℂ] E)

/-! ### The strict sampled contraction -/

/-- (H4) and (FC.10) give `‖e^{K}‖ < 1`. -/
theorem norm_flow_one_lt_one [FiniteDimensional ℂ E] {A : E →L[ℂ] E} (hK : K = A - S)
    (hA : star A = -A) (hS : star S = S) (h : PosDefSampled K S) : ‖flow K 1‖ < 1 := by
  have hpos : (star (flow K 1) * flow K 1).IsPositive := by
    rw [star_eq_adjoint]
    exact isPositive_adjoint_comp_self (flow K 1)
  have hlt : ‖star (flow K 1) * flow K 1‖ < 1 := by
    rw [PositiveNormBridge.opNorm_lt_one_iff_of_isPositive hpos]
    intro x hx
    have hW := h 1 one_pos x hx
    rw [gramFlow_eq K S hK hA hS 1, sub_apply, one_apply_eq_self, smul_apply,
      inner_sub_left, inner_smul_left, map_sub, inner_self_eq_norm_sq (𝕜 := ℂ), map_ofNat, two_mul,
      map_add]
    linarith
  have hC : ‖star (flow K 1) * flow K 1‖ = ‖flow K 1‖ * ‖flow K 1‖ := CStarRing.norm_star_mul_self
  rw [hC] at hlt
  nlinarith [norm_nonneg (flow K 1)]

/-! ### Exponential decay from a strict sampled contraction -/

theorem flow_natCast (n : ℕ) : flow K (n : ℝ) = flow K 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, flow_add, ih, pow_succ]

theorem norm_flow_le_pow : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
    ‖flow K t‖ ≤ C * ‖flow K 1‖ ^ ⌊t⌋₊ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_flow K).continuousOn
  refine ⟨max C 1, by positivity, fun t ht => ?_⟩
  set n := ⌊t⌋₊ with hn
  have hn1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t < n + 1 := Nat.lt_floor_add_one t
  have hsplit : flow K t = flow K (t - n) * flow K n := by rw [← flow_add, sub_add_cancel]
  have hs : ‖flow K (t - n)‖ ≤ max C 1 :=
    (hC _ ⟨by linarith, by linarith⟩).trans (le_max_left _ _)
  rw [hsplit, flow_natCast]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero, mul_one, pow_zero, mul_one]
    rw [h0] at hs
    exact hs
  · calc ‖flow K (t - n) * flow K 1 ^ n‖ ≤ ‖flow K (t - n)‖ * ‖flow K 1 ^ n‖ := norm_mul_le _ _
      _ ≤ max C 1 * ‖flow K 1‖ ^ n :=
        mul_le_mul hs (norm_pow_le' _ hpos) (norm_nonneg _) (by positivity)

/-- A strict sampled contraction gives exponential decay of the flow. -/
theorem exists_decay (hq : ‖flow K 1‖ < 1) : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
    ∀ t : ℝ, 0 ≤ t → ‖flow K t‖ ≤ C * Real.exp (-ε * t) := by
  obtain ⟨C, hC0, hC⟩ := norm_flow_le_pow K
  set q : ℝ := max ‖flow K 1‖ (1 / 2) with hq_def
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq1 : q < 1 := max_lt hq (by norm_num)
  have hle : ‖flow K 1‖ ≤ q := le_max_left _ _
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  refine ⟨C / q, -Real.log q, by positivity, by linarith, fun t ht => ?_⟩
  have hn1 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht
  have hn2 : t < (⌊t⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one t
  calc ‖flow K t‖ ≤ C * ‖flow K 1‖ ^ ⌊t⌋₊ := hC t ht
    _ ≤ C * q ^ ⌊t⌋₊ := by gcongr
    _ = C * Real.exp (Real.log q * ⌊t⌋₊) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0]
    _ ≤ C * Real.exp (Real.log q * (t - 1)) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by linarith) hlog.le)) hC0.le
    _ = C / q * Real.exp (-(-Real.log q) * t) := by
      rw [neg_neg, mul_sub, mul_one, Real.exp_sub, Real.exp_log hq0]
      ring

theorem tendsto_flow_zero {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖flow K t‖ ≤ C * Real.exp (-ε * t)) :
    Tendsto (flow K) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-ε * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => ε * t) atTop atTop := tendsto_id.const_mul_atTop hε
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.const_mul C
    rw [mul_zero] at h3
    refine h3.congr fun t => ?_
    simp [neg_mul]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hb t ht

/-! ### Integrability of the Gram integrand on the half line -/

theorem integrableOn_gramFlow {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖flow K t‖ ≤ C * Real.exp (-ε * t)) :
    IntegrableOn (fun t => star (flow K t) * flow K t) (Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (fun t : ℝ => C ^ 2 * Real.exp (-(2 * ε) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul (C ^ 2)
  refine Integrable.mono' hg ?_ ?_
  · exact (((continuous_flow K).star).mul (continuous_flow K)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht' : 0 ≤ t := le_of_lt ht
    have h1 : ‖star (flow K t) * flow K t‖ ≤ ‖flow K t‖ * ‖flow K t‖ := by
      calc ‖star (flow K t) * flow K t‖ ≤ ‖star (flow K t)‖ * ‖flow K t‖ := norm_mul_le _ _
        _ = ‖flow K t‖ * ‖flow K t‖ := by rw [norm_star]
    have h2 : ‖flow K t‖ * ‖flow K t‖ ≤ (C * Real.exp (-ε * t)) * (C * Real.exp (-ε * t)) :=
      mul_le_mul (hb t ht') (hb t ht') (norm_nonneg _)
        (le_trans (norm_nonneg _) (hb t ht'))
    have h3 : (C * Real.exp (-ε * t)) * (C * Real.exp (-ε * t))
        = C ^ 2 * Real.exp (-(2 * ε) * t) := by
      rw [show -(2 * ε) * t = -ε * t + -ε * t by ring, Real.exp_add]
      ring
    linarith

/-! ### The Lyapunov solution `P = ∫₀^∞ e^{tK*} e^{tK} dt` -/

/-- The Lyapunov solution `∫₀^∞ e^{tK*} e^{tK} dt`. -/
noncomputable def lyapunovSol : E →L[ℂ] E := ∫ t in Ioi (0 : ℝ), star (flow K t) * flow K t

/-- The Lyapunov operator `M ↦ K* M + M K` as a continuous real-linear map. -/
noncomputable def lyapunovOp : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
  ContinuousLinearMap.mul ℝ (E →L[ℂ] E) (star K) + (ContinuousLinearMap.mul ℝ (E →L[ℂ] E)).flip K

theorem lyapunovOp_apply (M : E →L[ℂ] E) : lyapunovOp K M = star K * M + M * K := by
  simp [lyapunovOp, ContinuousLinearMap.mul_apply', flip_apply]

/-- **The Lyapunov equation** `K* P + P K = -I`. -/
theorem lyapunov_eq (hG : IntegrableOn (fun t => star (flow K t) * flow K t) (Ioi (0 : ℝ)))
    (hdec : Tendsto (flow K) atTop (𝓝 0)) :
    star K * lyapunovSol K + lyapunovSol K * K = -1 := by
  rw [← lyapunovOp_apply, lyapunovSol, ← (lyapunovOp K).integral_comp_comm hG]
  have hint : IntegrableOn (fun t => lyapunovOp K (star (flow K t) * flow K t)) (Ioi (0 : ℝ)) :=
    (lyapunovOp K).integrable_comp hG
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have h2 : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, lyapunovOp K (star (flow K t) * flow K t)
      = star (flow K T) * flow K T - 1 := by
    intro T
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) T,
        HasDerivAt (fun s => star (flow K s) * flow K s)
          (lyapunovOp K (star (flow K s) * flow K s)) s := fun s _ => by
      rw [lyapunovOp_apply]
      exact hasDerivAt_gramFlow K s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (((lyapunovOp K).continuous.comp
        (((continuous_flow K).star).mul (continuous_flow K))).intervalIntegrable 0 T)]
    simp [flow_zero]
  have h3 : Tendsto (fun T : ℝ => star (flow K T) * flow K T - 1) atTop (𝓝 (star 0 * 0 - 1)) :=
    ((hdec.star).mul hdec).sub_const 1
  simp only [h2, id] at h1
  have := tendsto_nhds_unique h1 h3
  rw [this]
  simp

theorem isSelfAdjoint_lyapunovSol
    (hG : IntegrableOn (fun t => star (flow K t) * flow K t) (Ioi (0 : ℝ))) :
    IsSelfAdjoint (lyapunovSol K) := by
  have hstar : ∀ t : ℝ, star (star (flow K t) * flow K t) = star (flow K t) * flow K t := by
    intro t
    rw [star_mul, star_star]
  change star (lyapunovSol K) = lyapunovSol K
  have h := ((starL' ℝ : (E →L[ℂ] E) ≃L[ℝ] (E →L[ℂ] E)) :
    (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)).integral_comp_comm hG
  rw [lyapunovSol]
  have e1 : star (∫ t in Ioi (0 : ℝ), star (flow K t) * flow K t)
      = ((starL' ℝ : (E →L[ℂ] E) ≃L[ℝ] (E →L[ℂ] E)) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (∫ t in Ioi (0 : ℝ), star (flow K t) * flow K t) := rfl
  rw [e1, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change star (star (flow K t) * flow K t) = _
  rw [hstar]

theorem re_inner_lyapunovSol
    (hG : IntegrableOn (fun t => star (flow K t) * flow K t) (Ioi (0 : ℝ))) (x : E) :
    RCLike.re ⟪lyapunovSol K x, x⟫_ℂ = ∫ t in Ioi (0 : ℝ), ‖flow K t x‖ ^ 2 := by
  have hGx : IntegrableOn (fun t => (star (flow K t) * flow K t) x) (Ioi (0 : ℝ)) :=
    (ContinuousLinearMap.apply ℂ E x).integrable_comp hG
  have hGxx : IntegrableOn (fun t => ⟪x, (star (flow K t) * flow K t) x⟫_ℂ) (Ioi (0 : ℝ)) :=
    (innerSL ℂ x).integrable_comp hGx
  rw [lyapunovSol, ContinuousLinearMap.integral_apply hG x, re_inner_comm]
  have e1 : ⟪x, ∫ t in Ioi (0 : ℝ), (star (flow K t) * flow K t) x⟫_ℂ
      = ∫ t in Ioi (0 : ℝ), ⟪x, (star (flow K t) * flow K t) x⟫_ℂ := by
    rw [← innerSL_apply_apply (𝕜 := ℂ) x, ← (innerSL ℂ x).integral_comp_comm hGx]
    rfl
  have e2 : RCLike.re (∫ t in Ioi (0 : ℝ), ⟪x, (star (flow K t) * flow K t) x⟫_ℂ)
      = ∫ t in Ioi (0 : ℝ), RCLike.re ⟪x, (star (flow K t) * flow K t) x⟫_ℂ := by
    rw [← RCLike.reCLM_apply (K := ℂ), ← RCLike.reCLM.integral_comp_comm hGxx]
  rw [e1, e2]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change RCLike.re ⟪x, star (flow K t) (flow K t x)⟫_ℂ = _
  rw [star_eq_adjoint, adjoint_inner_right, inner_self_eq_norm_sq]

/-- **Positive definiteness of the Lyapunov solution.** -/
theorem lyapunovSol_pos {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖flow K t‖ ≤ C * Real.exp (-ε * t)) {x : E} (hx : x ≠ 0) :
    0 < RCLike.re ⟪lyapunovSol K x, x⟫_ℂ := by
  have hG := integrableOn_gramFlow K hε hb
  rw [re_inner_lyapunovSol K hG x]
  have hcont : Continuous fun t => ‖flow K t x‖ ^ 2 :=
    ((continuous_flow_apply K x).norm).pow 2
  have hint : IntegrableOn (fun t => ‖flow K t x‖ ^ 2) (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn (fun t : ℝ => (C ^ 2 * Real.exp (-(2 * ε) * t)) * ‖x‖ ^ 2) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul (C ^ 2)).mul_const (‖x‖ ^ 2)
    refine Integrable.mono' hg hcont.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht' : 0 ≤ t := le_of_lt ht
    have h1 : ‖flow K t x‖ ≤ ‖flow K t‖ * ‖x‖ := (flow K t).le_opNorm x
    have h2 : ‖flow K t‖ ≤ C * Real.exp (-ε * t) := hb t ht'
    have h3 : (C * Real.exp (-ε * t)) * (C * Real.exp (-ε * t))
        = C ^ 2 * Real.exp (-(2 * ε) * t) := by
      rw [show -(2 * ε) * t = -ε * t + -ε * t by ring, Real.exp_add]
      ring
    rw [Real.norm_of_nonneg (sq_nonneg _), ← h3]
    calc ‖flow K t x‖ ^ 2 ≤ (‖flow K t‖ * ‖x‖) ^ 2 := by gcongr
      _ ≤ ((C * Real.exp (-ε * t)) * ‖x‖) ^ 2 := by gcongr
      _ = (C * Real.exp (-ε * t)) * (C * Real.exp (-ε * t)) * ‖x‖ ^ 2 := by ring
  calc (0 : ℝ) < ∫ t in (0 : ℝ)..1, ‖flow K t x‖ ^ 2 :=
        intervalIntegral.integral_pos one_pos hcont.continuousOn (fun t _ => sq_nonneg _)
          ⟨0, ⟨le_rfl, zero_le_one⟩, by
            simp only [flow_zero, one_apply_eq_self]
            positivity⟩
    _ = ∫ t in Ioc (0 : ℝ) 1, ‖flow K t x‖ ^ 2 := intervalIntegral.integral_of_le zero_le_one
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖flow K t x‖ ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun t => sq_nonneg _)
          (Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht)

/-- **Uniqueness of the Lyapunov solution.** -/
theorem lyapunov_unique (hG : IntegrableOn (fun t => star (flow K t) * flow K t) (Ioi (0 : ℝ)))
    (hdec : Tendsto (flow K) atTop (𝓝 0)) {P' : E →L[ℂ] E}
    (hP' : star K * P' + P' * K = -1) : P' = lyapunovSol K := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => star (flow K s) * P' * flow K s)
      (-(star (flow K t) * flow K t)) t := by
    intro t
    have h := ((hasDerivAt_star_flow K t).mul (hasDerivAt_const t P')).mul (hasDerivAt_flow K t)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, mul_zero, add_zero]
    rw [star_flow_mul_star, flow_mul_comm]
    have e : star (flow K t) * star K * P' * flow K t + star (flow K t) * P' * (K * flow K t)
        = star (flow K t) * (star K * P' + P' * K) * flow K t := by
      simp only [mul_add, add_mul, mul_assoc]
    rw [e, hP', mul_neg, mul_one, neg_mul]
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hG tendsto_id
  have h2 : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, star (flow K t) * flow K t
      = P' - star (flow K T) * P' * flow K T := by
    intro T
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      ((((continuous_flow K).star).mul (continuous_flow K)).neg.intervalIntegrable 0 T)
    rw [intervalIntegral.integral_neg] at hFTC
    simp only [flow_zero, star_one, mul_one, one_mul] at hFTC
    have := congrArg Neg.neg hFTC
    rw [neg_neg] at this
    rw [this]
    abel
  have h3 : Tendsto (fun T : ℝ => P' - star (flow K T) * P' * flow K T) atTop
      (𝓝 (P' - star 0 * P' * 0)) :=
    tendsto_const_nhds.sub (((hdec.star).mul tendsto_const_nhds).mul hdec)
  simp only [h2, id] at h1
  have := tendsto_nhds_unique h1 h3
  rw [lyapunovSol, this]
  simp

/-! ### (H5) ⟹ (H3) -/

/-- A positive definite Lyapunov solution forces the spectrum into the open left half-plane. -/
theorem eigenvaluesNeg_of_lyapunov {P : E →L[ℂ] E}
    (hPpos : ∀ x : E, x ≠ 0 → 0 < RCLike.re ⟪P x, x⟫_ℂ) (hP : star K * P + P * K = -1) :
    EigenvaluesNeg K := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hKv : K v = μ • v := hv.apply_eq_smul
  have h := congrArg (fun M : E →L[ℂ] E => ⟪M v, v⟫_ℂ) hP
  simp only [add_apply, neg_apply, one_apply_eq_self, inner_add_left,
    inner_neg_left] at h
  have h1 : ⟪(star K * P) v, v⟫_ℂ = μ * ⟪P v, v⟫_ℂ := by
    change ⟪star K (P v), v⟫_ℂ = _
    rw [star_eq_adjoint, adjoint_inner_left, hKv, inner_smul_right]
  have h2 : ⟪(P * K) v, v⟫_ℂ = (starRingEnd ℂ) μ * ⟪P v, v⟫_ℂ := by
    change ⟪P (K v), v⟫_ℂ = _
    rw [hKv, map_smul, inner_smul_left]
  rw [h1, h2] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.neg_re] at hre
  have hp := hPpos v hv0
  have hvv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [hvv] at hre
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  have hp' : 0 < (⟪P v, v⟫_ℂ).re := hp
  nlinarith

/-! ### The bundled theorem -/

/-- The Lyapunov clause (H5): a positive definite solution of `K* P + P K = -I`. -/
def HasLyapunov (K : E →L[ℂ] E) : Prop :=
  ∃ P : E →L[ℂ] E, P.IsPositive ∧ (∀ x : E, x ≠ 0 → 0 < RCLike.re ⟪P x, x⟫_ℂ) ∧
    star K * P + P * K = -1 ∧ ∀ P' : E →L[ℂ] E, star K * P' + P' * K = -1 → P' = P

/-- **(H4) ⟹ (H5)**. -/
theorem hasLyapunov_of_posDefSampled [FiniteDimensional ℂ E] {A : E →L[ℂ] E} (hK : K = A - S)
    (hA : star A = -A) (hS : star S = S) (h : PosDefSampled K S) : HasLyapunov K := by
  obtain ⟨C, ε, hC, hε, hb⟩ := exists_decay K (norm_flow_one_lt_one K S hK hA hS h)
  have hG := integrableOn_gramFlow K hε hb
  have hdec := tendsto_flow_zero K hε hb
  refine ⟨lyapunovSol K, ⟨(isSelfAdjoint_lyapunovSol K hG).isSymmetric, fun x => ?_⟩,
    fun x hx => lyapunovSol_pos K hε hb hx, lyapunov_eq K hG hdec,
    fun P' hP' => lyapunov_unique K hG hdec hP'⟩
  rw [reApplyInnerSelf_apply]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (lyapunovSol_pos K hε hb hx).le

/-- **`thm:GT-hypocoercive-memory`** on a finite-dimensional complex Hilbert space, for
`K = -S + A` with `S ≥ 0` and `A` skew-adjoint: (FC.9) the kernel of `O_{d-1}` is the largest
`A`-invariant subspace of `ker S`; the clauses (H1)–(H5) are equivalent; and (FC.10)
`e^{TK*} e^{TK} = I - 2 W_K(T)`. -/
theorem hypocoercive_memory [FiniteDimensional ℂ E] {A S : E →L[ℂ] E} (hA : star A = -A)
    (hS : S.IsPositive) :
    (LinearMap.ker ((obsGram A S (finrank ℂ E - 1) : E →L[ℂ] E) : E →ₗ[ℂ] E)
        = unobservable A S ∧
      IsInvariantIn A S (unobservable A S) ∧
      ∀ W : Submodule ℂ E, IsInvariantIn A S W → W ≤ unobservable A S) ∧
    (PosDefGram A S (finrank ℂ E - 1) ↔ NoInvariant A S) ∧
    (NoInvariant A S ↔ EigenvaluesNeg (A - S)) ∧
    (NoInvariant A S ↔ PosDefSampled (A - S) S) ∧
    (PosDefSampled (A - S) S ↔ HasLyapunov (A - S)) ∧
    (HasLyapunov (A - S) ↔ EigenvaluesNeg (A - S)) ∧
    ∀ T : ℝ, star (flow (A - S) T) * flow (A - S) T = 1 - (2 : ℂ) • sampledGram (A - S) S T := by
  have hr : finrank ℂ E ≤ finrank ℂ E - 1 + 1 := by omega
  have hSsa : star S = S := hS.isSelfAdjoint
  have h12 := posDefGram_iff_noInvariant A hS hr
  have h23 := noInvariant_iff_eigenvaluesNeg hA hS
  have h24 : NoInvariant A S ↔ PosDefSampled (A - S) S :=
    ⟨posDefSampled_of_noInvariant (A - S) S rfl hS, noInvariant_of_posDefSampled (A - S) S rfl⟩
  have h45 : PosDefSampled (A - S) S ↔ HasLyapunov (A - S) := by
    constructor
    · exact hasLyapunov_of_posDefSampled (A - S) S rfl hA hSsa
    · rintro ⟨P, -, hPpos, hP, -⟩
      exact h24.mp (h23.mpr (eigenvaluesNeg_of_lyapunov (A - S) hPpos hP))
  have h53 : HasLyapunov (A - S) ↔ EigenvaluesNeg (A - S) := by
    constructor
    · rintro ⟨P, -, hPpos, hP, -⟩
      exact eigenvaluesNeg_of_lyapunov (A - S) hPpos hP
    · intro h
      exact h45.mp (h24.mp (h23.mpr h))
  exact ⟨⟨ker_obsGram_eq_unobservable A hS hr, unobservable_isInvariantIn A S,
    fun W hW => le_unobservable_of_isInvariantIn A S hW⟩, h12, h23, h24, h45, h53,
    fun T => gramFlow_eq (A - S) S rfl hA hSsa T⟩

end HypocoerciveMemory
end NCG
