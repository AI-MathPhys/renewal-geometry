/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hypocoercive screens: Lyapunov decay, sampled loss, circulation screen

Exact proofs, in the quadratic-form (Rayleigh) formulation on a real Hilbert
space `E`, of

* `thm:GT-approx-Lyapunov` (FC.13 ⇒ FC.14): if
  `R_P = K^* P + P K + I` has `‖R_P‖ ≤ ε < 1` and `P ⪯ p₊ I`, then along
  `u(t) = e^{tK} u₀` the `P`-energy decays like
  `exp(-(1-ε) t / p₊)` (`approx_lyapunov`), i.e.
  `‖e^{tK}‖_P ≤ exp(-(1-ε) t / (2 p₊))` (`approx_lyapunov_norm`);
* `cor:GT-hypocoercive-decay`: (FC.12) an exact Lyapunov solution
  `K^* P + P K = -I` with `p₋ I ⪯ P ⪯ p₊ I` gives
  `‖e^{tK}‖ ≤ √(p₊/p₋) e^{-t/(2p₊)}` (`hypocoercive_decay_opNorm`); (FC.10/
  FC.11) for `K = A - S` with `A` skew, the sampled loss
  `w_K(T,x) = ∫₀ᵀ ⟪S e^{tK}x, e^{tK}x⟫ dt` (the Rayleigh form of `W_K(T)`)
  satisfies `‖e^{TK}x‖² = ‖x‖² - 2 w_K(T,x)` (`normSq_flow_eq`), hence a
  lower Rayleigh bound `ω` on `W_K(T)` gives `‖e^{TK}‖ ≤ √(1 - 2ω)`
  (`sampled_contraction`) with positive hypocoercive rate
  `g_T = -log(1-2ω)/(2T)` (`hypocoercive_rate_pos`), and `2ω < 1`
  automatically on a nontrivial space (`two_omega_lt_one`);
* `thm:GT-circulation-screen` (FC.15/FC.16): with `M = ‖S‖`,
  `w_K(T,x) ≥ w_A(T,x) - M² T² ‖x‖²` (`circulation_screen`), via the
  Duhamel/dissipativity bound `‖e^{tK}x - e^{tA}x‖ ≤ t M ‖x‖`
  (`flow_sub_flow_norm_le`); consequently a lower Rayleigh bound `ω_A` on
  `W_A(T)` with `η_T = ω_A - M²T² > 0` gives `‖e^{TK}‖ ≤ √(1 - 2η_T) < 1`
  (`circulation_screen_contraction`).

The operator inequalities of the manuscript are stated through their
quadratic forms `x ↦ ⟪x, W x⟫`, which determine the (self-adjoint) operators;
`λ_min(W_K(T))` is represented by the best lower Rayleigh bound `ω`.
-/

open NormedSpace Set
open scoped RealInnerProductSpace

namespace NCG
namespace HypocoerciveScreens

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The flow `e^{tK} x`. -/
noncomputable def flow (K : E →L[ℝ] E) (t : ℝ) (x : E) : E := exp (t • K) x

omit [CompleteSpace E] in
@[simp] theorem flow_zero (K : E →L[ℝ] E) (x : E) : flow K 0 x = x := by
  simp [flow]

theorem hasDerivAt_flow (K : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s => flow K s x) (K (flow K t x)) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) K t).clm_apply (hasDerivAt_const t x)
  rw [map_zero, add_zero] at h
  exact h

theorem continuous_flow (K : E →L[ℝ] E) (x : E) : Continuous (fun s => flow K s x) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_flow K x t).continuousAt

theorem hasDerivAt_quad (K P : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s => ⟪flow K s x, P (flow K s x)⟫)
      (⟪flow K t x, P (K (flow K t x))⟫ + ⟪K (flow K t x), P (flow K t x)⟫) t := by
  have hf := hasDerivAt_flow K x t
  have hg : HasDerivAt (fun s => P (flow K s x)) (P (K (flow K t x))) t := by
    have := (hasDerivAt_const t P).clm_apply hf
    simpa using this
  exact hf.inner ℝ hg

/-- **Gronwall in quadratic form**: if `⟪u, PKu⟫ + ⟪Ku, Pu⟫ ≤ -λ ⟪u, Pu⟫` then
the `P`-energy of the flow decays like `exp(-λ t)`. -/
theorem quad_decay (K P : E →L[ℝ] E) (x : E) (lam : ℝ)
    (hdiss : ∀ u, ⟪u, P (K u)⟫ + ⟪K u, P u⟫ ≤ -lam * ⟪u, P u⟫)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪flow K t x, P (flow K t x)⟫ ≤ Real.exp (-lam * t) * ⟪x, P x⟫ := by
  have hψd : ∀ s, HasDerivAt (fun s => Real.exp (lam * s) * ⟪flow K s x, P (flow K s x)⟫)
      (Real.exp (lam * s) * lam * ⟪flow K s x, P (flow K s x)⟫
        + Real.exp (lam * s) *
          (⟪flow K s x, P (K (flow K s x))⟫ + ⟪K (flow K s x), P (flow K s x)⟫)) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s := by
      have h1 : HasDerivAt (fun s : ℝ => lam * s) lam s := by
        simpa using (hasDerivAt_id s).const_mul lam
      exact (Real.hasDerivAt_exp _).comp s h1
    exact he.mul (hasDerivAt_quad K P x s)
  have hanti : AntitoneOn (fun s => Real.exp (lam * s) * ⟪flow K s x, P (flow K s x)⟫)
      (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact fun s _ => (hψd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hψd s).differentiableAt.differentiableWithinAt
    · intro s _
      rw [(hψd s).deriv]
      have h1 := hdiss (flow K s x)
      have h2 : 0 < Real.exp (lam * s) := Real.exp_pos _
      have key : Real.exp (lam * s) *
          (⟪flow K s x, P (K (flow K s x))⟫ + ⟪K (flow K s x), P (flow K s x)⟫)
          ≤ Real.exp (lam * s) * (-lam * ⟪flow K s x, P (flow K s x)⟫) :=
        mul_le_mul_of_nonneg_left h1 h2.le
      have : Real.exp (lam * s) * lam * ⟪flow K s x, P (flow K s x)⟫
          + Real.exp (lam * s) * (-lam * ⟪flow K s x, P (flow K s x)⟫) = 0 := by ring
      linarith
  have hle := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul, flow_zero] at hle
  calc ⟪flow K t x, P (flow K t x)⟫
      = Real.exp (-lam * t) * (Real.exp (lam * t) * ⟪flow K t x, P (flow K t x)⟫) := by
        rw [← mul_assoc, ← Real.exp_add, show -lam * t + lam * t = 0 by ring, Real.exp_zero,
          one_mul]
    _ ≤ Real.exp (-lam * t) * ⟪x, P x⟫ := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-! ### `thm:GT-approx-Lyapunov` -/

/-- The approximate Lyapunov residual `R_P = K^* P + P K + I`. -/
noncomputable def lyapunovResidual (K P : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.adjoint K * P + P * K + 1

theorem quad_residual (K P : E →L[ℝ] E) (u : E) :
    ⟪u, P (K u)⟫ + ⟪K u, P u⟫ = ⟪u, lyapunovResidual K P u⟫ - ‖u‖ ^ 2 := by
  change ⟪u, P (K u)⟫ + ⟪K u, P u⟫
    = ⟪u, (ContinuousLinearMap.adjoint K) (P u) + P (K u) + u⟫ - ‖u‖ ^ 2
  rw [inner_add_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
  ring

/-- **(FC.13 ⇒ FC.14)**: `‖R_P‖ ≤ ε ≤ 1` and `P ⪯ p₊ I` give the decay
`⟪u(t), P u(t)⟫ ≤ exp(-(1-ε) t / p₊) ⟪u₀, P u₀⟫`. -/
theorem approx_lyapunov (K P : E →L[ℝ] E) (pplus eps : ℝ) (hpplus : 0 < pplus)
    (heps : eps ≤ 1) (hP : ∀ u, ⟪u, P u⟫ ≤ pplus * ‖u‖ ^ 2)
    (hR : ‖lyapunovResidual K P‖ ≤ eps) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ⟪flow K t x, P (flow K t x)⟫
      ≤ Real.exp (-((1 - eps) / pplus) * t) * ⟪x, P x⟫ := by
  refine quad_decay K P x ((1 - eps) / pplus) (fun u => ?_) ht
  rw [quad_residual]
  have hR' : ⟪u, lyapunovResidual K P u⟫ ≤ eps * ‖u‖ ^ 2 := by
    calc ⟪u, lyapunovResidual K P u⟫ ≤ ‖u‖ * ‖lyapunovResidual K P u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖lyapunovResidual K P‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left ((lyapunovResidual K P).le_opNorm u) (norm_nonneg _)
      _ ≤ ‖u‖ * (eps * ‖u‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
            (norm_nonneg _)
      _ = eps * ‖u‖ ^ 2 := by ring
  have h2 : (1 - eps) / pplus * ⟪u, P u⟫ ≤ (1 - eps) / pplus * (pplus * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (hP u) (div_nonneg (by linarith) hpplus.le)
  have h3 : (1 - eps) / pplus * (pplus * ‖u‖ ^ 2) = (1 - eps) * ‖u‖ ^ 2 := by
    field_simp
  linarith

/-- **(FC.14)** in `P`-norm form: `‖u(t)‖_P ≤ exp(-(1-ε) t / (2p₊)) ‖u₀‖_P`. -/
theorem approx_lyapunov_norm (K P : E →L[ℝ] E) (pplus eps : ℝ) (hpplus : 0 < pplus)
    (heps : eps ≤ 1) (hP : ∀ u, ⟪u, P u⟫ ≤ pplus * ‖u‖ ^ 2)
    (hR : ‖lyapunovResidual K P‖ ≤ eps) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt ⟪flow K t x, P (flow K t x)⟫
      ≤ Real.exp (-((1 - eps) / (2 * pplus)) * t) * Real.sqrt ⟪x, P x⟫ := by
  have h := approx_lyapunov K P pplus eps hpplus heps hP hR x ht
  calc Real.sqrt ⟪flow K t x, P (flow K t x)⟫
      ≤ Real.sqrt (Real.exp (-((1 - eps) / pplus) * t) * ⟪x, P x⟫) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Real.exp (-((1 - eps) / pplus) * t)) * Real.sqrt ⟪x, P x⟫ :=
        Real.sqrt_mul (Real.exp_pos _).le _
    _ = Real.exp (-((1 - eps) / (2 * pplus)) * t) * Real.sqrt ⟪x, P x⟫ := by
        congr 1
        rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
        congr 1
        field_simp
        ring

/-! ### `cor:GT-hypocoercive-decay` (FC.12) -/

/-- **(FC.12)**: an exact Lyapunov solution `K^* P + P K = -I` with
`p₋ I ⪯ P ⪯ p₊ I` gives `‖e^{tK} x‖² ≤ (p₊/p₋) e^{-t/p₊} ‖x‖²`. -/
theorem hypocoercive_decay (K P : E →L[ℝ] E) (pminus pplus : ℝ) (hpminus : 0 < pminus)
    (hpplus : 0 < pplus)
    (hlyap : ContinuousLinearMap.adjoint K * P + P * K = -1)
    (hPlow : ∀ u, pminus * ‖u‖ ^ 2 ≤ ⟪u, P u⟫) (hPhigh : ∀ u, ⟪u, P u⟫ ≤ pplus * ‖u‖ ^ 2)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow K t x‖ ^ 2 ≤ pplus / pminus * Real.exp (-t / pplus) * ‖x‖ ^ 2 := by
  have hR : ‖lyapunovResidual K P‖ ≤ 0 := by
    have : lyapunovResidual K P = 0 := by
      unfold lyapunovResidual
      rw [hlyap]; abel
    rw [this, norm_zero]
  have h := approx_lyapunov K P pplus 0 hpplus (by norm_num) hPhigh hR x ht
  have h1 := hPlow (flow K t x)
  have h2 := hPhigh x
  have hexp : -((1 - 0) / pplus) * t = -t / pplus := by ring
  rw [hexp] at h
  have hpos := Real.exp_pos (-t / pplus)
  have h3 : pminus * ‖flow K t x‖ ^ 2 ≤ Real.exp (-t / pplus) * (pplus * ‖x‖ ^ 2) :=
    le_trans h1 (le_trans h (mul_le_mul_of_nonneg_left h2 hpos.le))
  have hdiv : pplus / pminus * Real.exp (-t / pplus) * ‖x‖ ^ 2
      = (Real.exp (-t / pplus) * (pplus * ‖x‖ ^ 2)) / pminus := by
    rw [eq_div_iff hpminus.ne', div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_mul_cancel₀ _ hpminus.ne']
    ring
  rw [hdiv, le_div_iff₀ hpminus]
  linarith

/-- **(FC.12)** as an operator-norm bound:
`‖e^{tK}‖ ≤ √(p₊/p₋) e^{-t/(2p₊)}`. -/
theorem hypocoercive_decay_opNorm (K P : E →L[ℝ] E) (pminus pplus : ℝ) (hpminus : 0 < pminus)
    (hpplus : 0 < pplus)
    (hlyap : ContinuousLinearMap.adjoint K * P + P * K = -1)
    (hPlow : ∀ u, pminus * ‖u‖ ^ 2 ≤ ⟪u, P u⟫) (hPhigh : ∀ u, ⟪u, P u⟫ ≤ pplus * ‖u‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • K)‖ ≤ Real.sqrt (pplus / pminus) * Real.exp (-t / (2 * pplus)) := by
  have hc : 0 ≤ Real.sqrt (pplus / pminus) * Real.exp (-t / (2 * pplus)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have h := hypocoercive_decay K P pminus pplus hpminus hpplus hlyap hPlow hPhigh x ht
  have hsq : (Real.sqrt (pplus / pminus) * Real.exp (-t / (2 * pplus)) * ‖x‖) ^ 2
      = pplus / pminus * Real.exp (-t / pplus) * ‖x‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hpplus.le hpminus.le), sq, ← Real.exp_add]
    congr 2
    field_simp
    ring_nf
  have : ‖flow K t x‖ ^ 2
      ≤ (Real.sqrt (pplus / pminus) * Real.exp (-t / (2 * pplus)) * ‖x‖) ^ 2 := by
    rw [hsq]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).mp this

/-! ### Sampled loss (FC.10, FC.11) -/

/-- The sampled loss `w_K(T,x) = ∫₀ᵀ ⟪S e^{tK}x, e^{tK}x⟫ dt`, the Rayleigh form
of the sampled loss Gram `W_K(T)`. -/
noncomputable def sampledLoss (K S : E →L[ℝ] E) (T : ℝ) (x : E) : ℝ :=
  ∫ t in (0 : ℝ)..T, ⟪S (flow K t x), flow K t x⟫

theorem hasDerivAt_normSq_flow (K : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s => ‖flow K s x‖ ^ 2) (2 * ⟪K (flow K t x), flow K t x⟫) t := by
  have h := (hasDerivAt_flow K x t).inner ℝ (hasDerivAt_flow K x t)
  have hfun : (fun s => ‖flow K s x‖ ^ 2) = fun s => ⟪flow K s x, flow K s x⟫ := by
    funext s; rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [real_inner_comm (K (flow K t x)) (flow K t x)]
  ring

theorem continuous_sampled_integrand (K S : E →L[ℝ] E) (x : E) :
    Continuous (fun s => ⟪S (flow K s x), flow K s x⟫) :=
  (S.continuous.comp (continuous_flow K x)).inner (continuous_flow K x)

/-- **(FC.10)** in quadratic form: for `K = A - S` with `A` skew,
`‖e^{TK} x‖² = ‖x‖² - 2 w_K(T,x)`. -/
theorem normSq_flow_eq (K A S : E →L[ℝ] E) (hKAS : K = A - S) (hA : ∀ u, ⟪A u, u⟫ = 0)
    (x : E) (T : ℝ) :
    ‖flow K T x‖ ^ 2 = ‖x‖ ^ 2 - 2 * sampledLoss K S T x := by
  have hsub : ∀ u, ⟪K u, u⟫ = -⟪S u, u⟫ := by
    intro u
    rw [hKAS]
    change ⟪A u - S u, u⟫ = _
    rw [inner_sub_left, hA u]
    ring
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun s => ‖flow K s x‖ ^ 2) (-2 * ⟪S (flow K s x), flow K s x⟫) s := by
    intro s _
    refine (hasDerivAt_normSq_flow K x s).congr_deriv ?_
    rw [hsub]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((continuous_sampled_integrand K S x).const_mul (-2)).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul, flow_zero] at hint
  unfold sampledLoss
  linarith

/-- **(FC.11)**: a lower Rayleigh bound `ω` on `W_K(T)` gives the sampled
contraction `‖e^{TK}‖ ≤ √(1 - 2ω)`. -/
theorem sampled_contraction (K A S : E →L[ℝ] E) (hKAS : K = A - S) (hA : ∀ u, ⟪A u, u⟫ = 0)
    (T ω : ℝ) (hω : ∀ x, ω * ‖x‖ ^ 2 ≤ sampledLoss K S T x) :
    (∀ x, ‖flow K T x‖ ^ 2 ≤ (1 - 2 * ω) * ‖x‖ ^ 2) ∧
      ‖exp (T • K)‖ ≤ Real.sqrt (1 - 2 * ω) := by
  have hpt : ∀ x, ‖flow K T x‖ ^ 2 ≤ (1 - 2 * ω) * ‖x‖ ^ 2 := by
    intro x
    rw [normSq_flow_eq K A S hKAS hA x T]
    linarith [hω x]
  refine ⟨hpt, ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_⟩
  have h := hpt x
  have hsq : (Real.sqrt (1 - 2 * ω) * ‖x‖) ^ 2 = Real.sqrt (1 - 2 * ω) ^ 2 * ‖x‖ ^ 2 := by ring
  rcases le_or_gt 0 (1 - 2 * ω) with h0 | h0
  · have : ‖flow K T x‖ ^ 2 ≤ (Real.sqrt (1 - 2 * ω) * ‖x‖) ^ 2 := by
      rw [hsq, Real.sq_sqrt h0]; exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp this
  · -- `1 - 2ω < 0`: the flow must vanish
    have hneg : (1 - 2 * ω) * ‖x‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
    have : ‖flow K T x‖ ^ 2 ≤ 0 := le_trans h hneg
    have hz : ‖flow K T x‖ = 0 := by nlinarith [norm_nonneg (flow K T x)]
    change ‖flow K T x‖ ≤ _
    rw [hz]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The flow is injective (`e^{-TK} e^{TK} = I`), so `‖e^{TK} x‖ > 0` for `x ≠ 0`. -/
theorem flow_ne_zero (K : E →L[ℝ] E) (T : ℝ) (x : E) (hx : x ≠ 0) : flow K T x ≠ 0 := by
  intro h
  have hcomm : Commute ((-T) • K) (T • K) := ((Commute.refl K).smul_left (-T)).smul_right T
  have hball : ∀ z : E →L[ℝ] E,
      z ∈ Metric.eball (0 : E →L[ℝ] E) (expSeries ℝ (E →L[ℝ] E)).radius := fun z =>
    (expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _
  have hexp : exp ((-T) • K) * exp (T • K) = 1 := by
    rw [← exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm (hball _) (hball _),
      show (-T) • K + T • K = 0 by rw [← add_smul]; simp, exp_zero]
  have : x = exp ((-T) • K) (exp (T • K) x) := by
    change x = (exp ((-T) • K) * exp (T • K)) x
    rw [hexp]
    rfl
  apply hx
  rw [this]
  change exp ((-T) • K) (flow K T x) = 0
  rw [h, map_zero]

/-- On a nontrivial space, a lower Rayleigh bound `ω` on `W_K(T)` satisfies `2ω < 1`. -/
theorem two_omega_lt_one [Nontrivial E] (K A S : E →L[ℝ] E) (hKAS : K = A - S)
    (hA : ∀ u, ⟪A u, u⟫ = 0) (T ω : ℝ) (hω : ∀ x, ω * ‖x‖ ^ 2 ≤ sampledLoss K S T x) :
    2 * ω < 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h := (sampled_contraction K A S hKAS hA T ω hω).1 x
  have hpos : 0 < ‖flow K T x‖ ^ 2 := by
    have := norm_pos_iff.mpr (flow_ne_zero K T x hx)
    positivity
  have hx2 : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.mpr hx
    positivity
  by_contra hcon
  push Not at hcon
  have : (1 - 2 * ω) * ‖x‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hx2.le
  linarith

/-- **(FC.11)** hypocoercive rate `g_T = -log(1 - 2ω) / (2T) > 0`. -/
theorem hypocoercive_rate_pos (T ω : ℝ) (hT : 0 < T) (hω : 0 < ω) (h1 : 2 * ω < 1) :
    0 < -Real.log (1 - 2 * ω) / (2 * T) := by
  have : Real.log (1 - 2 * ω) < 0 := Real.log_neg (by linarith) (by linarith)
  have : 0 < -Real.log (1 - 2 * ω) := by linarith
  positivity

/-! ### `thm:GT-circulation-screen` (FC.15, FC.16) -/

/-- Dissipative flows are contractions for `t ≥ 0`. -/
theorem norm_flow_le (K : E →L[ℝ] E) (hK : ∀ u, ⟪K u, u⟫ ≤ 0) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow K t x‖ ≤ ‖x‖ := by
  have hanti : AntitoneOn (fun s => ‖flow K s x‖ ^ 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact fun s _ => (hasDerivAt_normSq_flow K x s).continuousAt.continuousWithinAt
    · exact fun s _ => (hasDerivAt_normSq_flow K x s).differentiableAt.differentiableWithinAt
    · intro s _
      rw [(hasDerivAt_normSq_flow K x s).deriv]
      linarith [hK (flow K s x)]
  have hle := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [flow_zero] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- **Duhamel bound**: for `K = A - S` with `K, A` dissipative,
`‖e^{tK} x - e^{tA} x‖ ≤ t ‖S‖ ‖x‖` for `t ≥ 0`. -/
theorem flow_sub_flow_norm_le (K A S : E →L[ℝ] E) (hKAS : K = A - S)
    (hK : ∀ u, ⟪K u, u⟫ ≤ 0) (hA : ∀ u, ⟪A u, u⟫ ≤ 0) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow K t x - flow A t x‖ ≤ t * ‖S‖ * ‖x‖ := by
  let g : ℝ → E := fun s => exp ((t - s) • K) (flow A s x)
  have hg : ∀ s, HasDerivAt g (exp ((t - s) • K) (S (flow A s x))) s := by
    intro s
    have h1 : HasDerivAt (fun s => exp ((t - s) • K)) ((-1 : ℝ) • (exp ((t - s) • K) * K)) s := by
      have hh : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub t
      have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) K (t - s)).scomp s hh
      simpa [Function.comp_def] using this
    have h2 := h1.clm_apply (hasDerivAt_flow A x s)
    refine h2.congr_deriv ?_
    change (-1 : ℝ) • exp ((t - s) • K) (K (flow A s x)) + exp ((t - s) • K) (A (flow A s x))
      = exp ((t - s) • K) (S (flow A s x))
    rw [neg_one_smul, ← sub_eq_neg_add, ← map_sub]
    congr 1
    rw [hKAS]
    change A (flow A s x) - (A (flow A s x) - S (flow A s x)) = S (flow A s x)
    abel
  have hbound : ∀ s ∈ Icc (0 : ℝ) t, ‖exp ((t - s) • K) (S (flow A s x))‖ ≤ ‖S‖ * ‖x‖ := by
    intro s hs
    calc ‖exp ((t - s) • K) (S (flow A s x))‖ = ‖flow K (t - s) (S (flow A s x))‖ := rfl
      _ ≤ ‖S (flow A s x)‖ := norm_flow_le K hK _ (by linarith [hs.2])
      _ ≤ ‖S‖ * ‖flow A s x‖ := S.le_opNorm _
      _ ≤ ‖S‖ * ‖x‖ :=
          mul_le_mul_of_nonneg_left (norm_flow_le A hA x hs.1) (norm_nonneg _)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun s => exp ((t - s) • K) (S (flow A s x))) (C := ‖S‖ * ‖x‖)
    (s := Icc (0 : ℝ) t) (fun s _ => (hg s).hasDerivWithinAt) hbound (convex_Icc 0 t)
    (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  have hgt : g t = flow A t x := by simp [g]
  have hg0 : g 0 = flow K t x := by simp [g, flow]
  rw [hgt, hg0, norm_sub_rev, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] at hmv
  linarith [hmv]

omit [CompleteSpace E] in
theorem quad_diff_bound (S : E →L[ℝ] E) (y z : E) :
    ⟪S z, z⟫ - ‖S‖ * ‖y - z‖ * (‖y‖ + ‖z‖) ≤ ⟪S y, y⟫ := by
  have hid : ⟪S y, y⟫ - ⟪S z, z⟫ = ⟪S (y - z), y⟫ + ⟪S z, y - z⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right]; ring
  have h1 : -(‖S‖ * ‖y - z‖ * ‖y‖) ≤ ⟪S (y - z), y⟫ := by
    have := abs_real_inner_le_norm (S (y - z)) y
    have h' := S.le_opNorm (y - z)
    have : |⟪S (y - z), y⟫| ≤ ‖S‖ * ‖y - z‖ * ‖y‖ :=
      le_trans this (mul_le_mul_of_nonneg_right h' (norm_nonneg _))
    linarith [neg_abs_le ⟪S (y - z), y⟫]
  have h2 : -(‖S‖ * ‖z‖ * ‖y - z‖) ≤ ⟪S z, y - z⟫ := by
    have := abs_real_inner_le_norm (S z) (y - z)
    have h' := S.le_opNorm z
    have : |⟪S z, y - z⟫| ≤ ‖S‖ * ‖z‖ * ‖y - z‖ :=
      le_trans this (mul_le_mul_of_nonneg_right h' (norm_nonneg _))
    linarith [neg_abs_le ⟪S z, y - z⟫]
  nlinarith [hid, h1, h2]

/-- **(FC.15)** in quadratic form: `w_K(T,x) ≥ w_A(T,x) - M² T² ‖x‖²` with
`M = ‖S‖`, for `K = A - S`, `A` skew and `S ⪰ 0`. -/
theorem circulation_screen (K A S : E →L[ℝ] E) (hKAS : K = A - S) (hA : ∀ u, ⟪A u, u⟫ = 0)
    (hS : ∀ u, 0 ≤ ⟪S u, u⟫) (x : E) {T : ℝ} (hT : 0 ≤ T) :
    sampledLoss A S T x - ‖S‖ ^ 2 * T ^ 2 * ‖x‖ ^ 2 ≤ sampledLoss K S T x := by
  have hK : ∀ u, ⟪K u, u⟫ ≤ 0 := by
    intro u
    rw [hKAS]
    change ⟪A u - S u, u⟫ ≤ 0
    rw [inner_sub_left, hA]
    linarith [hS u]
  have hA' : ∀ u, ⟪A u, u⟫ ≤ 0 := fun u => (hA u).le
  have hpt : ∀ s ∈ Icc (0 : ℝ) T,
      ⟪S (flow A s x), flow A s x⟫ - 2 * s * ‖S‖ ^ 2 * ‖x‖ ^ 2
        ≤ ⟪S (flow K s x), flow K s x⟫ := by
    intro s hs
    have h1 := quad_diff_bound S (flow K s x) (flow A s x)
    have h2 := flow_sub_flow_norm_le K A S hKAS hK hA' x hs.1
    have h3 := norm_flow_le K hK x hs.1
    have h4 := norm_flow_le A hA' x hs.1
    have hs0 : 0 ≤ s := hs.1
    have h5 : ‖S‖ * ‖flow K s x - flow A s x‖ * (‖flow K s x‖ + ‖flow A s x‖)
        ≤ ‖S‖ * (s * ‖S‖ * ‖x‖) * (‖x‖ + ‖x‖) := by
      gcongr
    nlinarith [h1, h5]
  have hc2 : Continuous fun s : ℝ => 2 * s * ‖S‖ ^ 2 * ‖x‖ ^ 2 := by fun_prop
  have hint : ∫ s in (0 : ℝ)..T,
      (⟪S (flow A s x), flow A s x⟫ - 2 * s * ‖S‖ ^ 2 * ‖x‖ ^ 2)
      ≤ ∫ s in (0 : ℝ)..T, ⟪S (flow K s x), flow K s x⟫ :=
    intervalIntegral.integral_mono_on hT
      (((continuous_sampled_integrand A S x).sub hc2).intervalIntegrable 0 T)
      ((continuous_sampled_integrand K S x).intervalIntegrable 0 T) hpt
  have hsplit : ∫ s in (0 : ℝ)..T,
      (⟪S (flow A s x), flow A s x⟫ - 2 * s * ‖S‖ ^ 2 * ‖x‖ ^ 2)
      = sampledLoss A S T x - ‖S‖ ^ 2 * T ^ 2 * ‖x‖ ^ 2 := by
    unfold sampledLoss
    rw [intervalIntegral.integral_sub ((continuous_sampled_integrand A S x).intervalIntegrable 0 T)
      (hc2.intervalIntegrable 0 T)]
    congr 1
    have : (fun s : ℝ => 2 * s * ‖S‖ ^ 2 * ‖x‖ ^ 2) = fun s => (2 * ‖S‖ ^ 2 * ‖x‖ ^ 2) * s := by
      funext s; ring
    rw [this, intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hsplit] at hint
  exact hint

/-- **(FC.16)**: a lower Rayleigh bound `ω_A` on `W_A(T)` with
`η_T = ω_A - M²T² > 0` gives `‖e^{TK}‖ ≤ √(1 - 2η_T) < 1`. -/
theorem circulation_screen_contraction (K A S : E →L[ℝ] E) (hKAS : K = A - S)
    (hA : ∀ u, ⟪A u, u⟫ = 0) (hS : ∀ u, 0 ≤ ⟪S u, u⟫) (T ωA : ℝ) (hT : 0 ≤ T)
    (hωA : ∀ x, ωA * ‖x‖ ^ 2 ≤ sampledLoss A S T x) :
    ‖exp (T • K)‖ ≤ Real.sqrt (1 - 2 * (ωA - ‖S‖ ^ 2 * T ^ 2)) ∧
      (0 < ωA - ‖S‖ ^ 2 * T ^ 2 → ‖exp (T • K)‖ < 1) := by
  have hω : ∀ x, (ωA - ‖S‖ ^ 2 * T ^ 2) * ‖x‖ ^ 2 ≤ sampledLoss K S T x := by
    intro x
    have := circulation_screen K A S hKAS hA hS x hT
    have := hωA x
    nlinarith
  have hc := (sampled_contraction K A S hKAS (fun u => hA u) T _ hω).2
  refine ⟨hc, fun hη => lt_of_le_of_lt hc ?_⟩
  rw [Real.sqrt_lt' one_pos]
  linarith

end HypocoerciveScreens
end NCG
