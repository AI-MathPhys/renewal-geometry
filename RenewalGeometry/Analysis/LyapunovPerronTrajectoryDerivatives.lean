/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovPerronGraphSecondOrder

/-!
# First and second derivatives of the forward weighted trajectories at every time

Fifth layer of the forward invariant-graph construction (`lem:supp-exact-graph-criterion`,
emergent-spacetime manuscript), on top of `Analysis/LyapunovPerronGraphSecondOrder.lean`.

The `C¹` and `C²` layers only differentiated the graph `h(n₀) = u(0)`.  Here the same
quadratic-defect machinery is applied to the value maps `n₀ ↦ y_*(n₀)(t)` at **every** time
`t ≥ 0` (`trajAt`, clamped to `max t 0` so that everything is defined and continuous on `ℝ`):

* `trajAt_quadDefect`, `traj1`: `n₀ ↦ y_*(n₀)(t)` has uniform quadratic three-point defects with
  constant `K₁ e^{2νt}` (`traj_first`), hence a derivative `Y₁(t, n₀)` with
  `‖Y₁‖ ≤ C₁ e^{νt}`, `‖y_*(n₀+v)(t) - y_*(n₀)(t) - Y₁ v‖ ≤ K₁ e^{2νt}‖v‖²` and Lipschitz constant
  `6K₁e^{2νt}`;
* `second_level_traj_le`, `traj1_quadDefect`, `traj2`: the second-level defect bound of the `C²`
  layer holds at every time (weight `3ν`, `j = 3` inequality), so `n₀ ↦ Y₁(t, n₀)` has a
  derivative `Y₂(t, n₀)` with `‖Y₂‖ ≤ 6K₁e^{2νt}`, Taylor constant `K_d e^{3νt}` and Lipschitz
  constant `6K_d e^{3νt}`;
* `traj1_apply_continuous`, `traj2_apply_continuous`: `t ↦ Y₁(t)d`, `t ↦ Y₂(t)ed` are continuous
  (locally uniform limits of difference quotients, `continuous_of_rate_approx`);
* `traj1_eq`: **the first variational equation** `Y₁(t)d = (0, P_n(t)d) + 𝒮[DN(y_*) Y₁ d](t)`;
* `traj2_eq`: **the second variational equation**
  `Y₂(t)ed = 𝒮[DN(y_*) Y₂ e d + D²N(y_*)(Y₁ e)(Y₁ d)](t)`,

where `𝒮 = srcOp` is the Lyapunov–Perron integral operator.  These identities are obtained
without any limit inside an integral: the difference quotients converge with explicit rates in
the weights `2ν`, `3ν`, and `srcOp_norm_le` transports the rates.  They are the input of the
`C³` layer (`Analysis/LyapunovPerronGraphThirdOrder.lean`).
-/

open Filter Set MeasureTheory intervalIntegral Real
open scoped Topology BoundedContinuousFunction

namespace RenewalGeometry
namespace LyapunovPerron

variable {U Nn : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Generic tools -/

/-- **Continuity from locally uniform approximation with a continuous rate**: if continuous
`F ℓ` satisfy `‖F ℓ r - f r‖ ≤ c(r) ℓ` for every `ℓ > 0`, with `c` continuous, then `f` is
continuous. -/
theorem continuous_of_rate_approx {X : Type*} [NormedAddCommGroup X] {f : ℝ → X}
    {F : ℝ → ℝ → X} (hF : ∀ ℓ, 0 < ℓ → Continuous (F ℓ)) {c : ℝ → ℝ} (hc : Continuous c)
    (hb : ∀ ℓ, 0 < ℓ → ∀ r, ‖F ℓ r - f r‖ ≤ c r * ℓ) : Continuous f := by
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  set C := |c x| + 1 with hCdef
  have hC : 0 < C := by positivity
  have hcx : c x < C := by rw [hCdef]; linarith [le_abs_self (c x)]
  have ht : {y | c y < C} ∈ 𝓝 x := hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hcx)
  have hℓ : 0 < ε / (2 * C) := by positivity
  refine ⟨{y | c y < C}, ht, F (ε / (2 * C)), (hF _ hℓ).continuousAt, fun y hy => hεu ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖F (ε / (2 * C)) y - f y‖ ≤ c y * (ε / (2 * C)) := hb _ hℓ y
    _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_right (le_of_lt hy) hℓ.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem exp_mul_le_exp_mul {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) : exp (a * r) ≤ exp (b * r) :=
  exp_le_exp.2 (mul_le_mul_of_nonneg_right hab hr)

section Src

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M β κ : ℝ}

/-- `srcOp` is subtractive on continuous sources of exponential growth. -/
theorem srcOp_sub' (hPuc : Continuous Pu) (hPnc : Continuous Pn) (hκβ : κ < β) (hM : 0 ≤ M)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)) {S T : ℝ → U × Nn} (hS : Continuous S)
    (hT : Continuous T) {σ τ : ℝ} (hSb : ∀ r, 0 ≤ r → ‖S r‖ ≤ σ * exp (κ * r))
    (hTb : ∀ r, 0 ≤ r → ‖T r‖ ≤ τ * exp (κ * r)) {t : ℝ} (ht : 0 ≤ t) :
    srcOp Pu Pn (S - T) t = srcOp Pu Pn S t - srcOp Pu Pn T t := by
  have hT' : ∀ r, 0 ≤ r → ‖((-1 : ℝ) • T) r‖ ≤ τ * exp (κ * r) := fun r hr => by
    simpa [norm_neg] using hTb r hr
  have e : S - T = S + (-1 : ℝ) • T := by funext r; simp [sub_eq_add_neg]
  rw [e, srcOp_add hPuc hPnc hκβ hM hPu hS (hT.const_smul _) hSb hT' ht, srcOp_smul]
  simp [sub_eq_add_neg]

end Src

/-- Norm of a pair bounded componentwise. -/
theorem norm_prod_le_of_le {a : U} {b : Nn} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) :
    ‖(a, b)‖ ≤ C := by
  rw [Prod.norm_def]; exact max_le ha hb

/-! ### The time-`t` value maps and their first derivative -/

section First

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- The time-`t⁺` value map `n₀ ↦ y_*(n₀)(max t 0)`. -/
def trajAt (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (r : ℝ) : Nn → U × Nn :=
  fun n => yStar h bu bn n (max r 0)

variable {h : GraphHyp Pu Pn M α β ν L Nu Nv} {DNu : U × Nn → (U × Nn) →L[ℝ] U}
  {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}

theorem trajAt_of_nonneg (bu : U) (bn : Nn) {r : ℝ} (hr : 0 ≤ r) (n : Nn) :
    trajAt h bu bn r n = yStar h bu bn n r := by
  simp [trajAt, max_eq_left hr]

theorem C1_nonneg (h : GraphHyp Pu Pn M α β ν L Nu Nv) : 0 ≤ M / (1 - h.q) :=
  div_nonneg h.M_nonneg (sub_pos.2 h.contr).le

/-- The value map at time `t⁺` has uniform quadratic three-point defects with constant
`K₁ e^{2νt⁺}` (`traj_first`). -/
theorem trajAt_quadDefect (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) :
    QuadDefect (trajAt h bu bn r) (hd.K1 * exp (2 * ν * max r 0)) := by
  intro n v₁ v₂ v₃ a₁ a₂ a₃ hsum
  have hsum' : ∑ i, (![a₁, a₂, a₃] : Fin 3 → ℝ) i • (![v₁, v₂, v₃] : Fin 3 → Nn) i = 0 := by
    simpa [Fin.sum_univ_three] using hsum
  have := traj_first hd bu bn n ![a₁, a₂, a₃] ![v₁, v₂, v₃] hsum' (le_max_right r 0)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, trajDiff] at this
  refine this.trans (le_of_eq ?_)
  ring

theorem trajAt_lip (bu : U) (bn : Nn) (r : ℝ) (n n' : Nn) :
    ‖trajAt h bu bn r n - trajAt h bu bn r n'‖ ≤ (M / (1 - h.q) * exp (ν * max r 0)) * ‖n - n'‖ :=
  (norm_yStar_sub_le h bu bn n n' (max r 0)).trans (le_of_eq (by ring))

theorem K1e_nonneg (hd : GraphC1Hyp h DNu DNv L₂) (r : ℝ) : 0 ≤ hd.K1 * exp (2 * ν * max r 0) :=
  mul_nonneg hd.K1_nonneg (exp_pos _).le

/-- **The first derivative of the time-`t` value map**, `Y₁(t, n₀) = D_{n₀} y_*(n₀)(t⁺)`. -/
def traj1 (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n : Nn) :
    Nn →L[ℝ] U × Nn :=
  quadDerivCLM (trajAt_quadDefect hd bu bn r) (K1e_nonneg hd r) (trajAt_lip bu bn r) n

theorem traj1_apply (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n d : Nn) :
    traj1 hd bu bn r n d = quadDeriv (trajAt h bu bn r) n d := rfl

theorem traj1_hasFDerivAt (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n : Nn) :
    HasFDerivAt (trajAt h bu bn r) (traj1 hd bu bn r n) n :=
  quadDeriv_hasFDerivAt _ _ _ n

/-- Taylor bound `‖y(n+v)(t) - y(n)(t) - Y₁ v‖ ≤ K₁ e^{2νt} ‖v‖²`. -/
theorem traj1_taylor (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n v : Nn) :
    ‖trajAt h bu bn r (n + v) - trajAt h bu bn r n - traj1 hd bu bn r n v‖ ≤
      hd.K1 * exp (2 * ν * max r 0) * ‖v‖ ^ 2 :=
  quadDeriv_taylor (trajAt_quadDefect hd bu bn r) (K1e_nonneg hd r) n v

theorem traj1_diffQuot (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n d : Nn)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖diffQuot (trajAt h bu bn r) n d ℓ - traj1 hd bu bn r n d‖ ≤
      hd.K1 * exp (2 * ν * max r 0) * ‖d‖ ^ 2 * ℓ :=
  diffQuot_sub_quadDeriv_le (trajAt_quadDefect hd bu bn r) (K1e_nonneg hd r) n d hℓ

theorem traj1_norm_le (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n : Nn) :
    ‖traj1 hd bu bn r n‖ ≤ M / (1 - h.q) * exp (ν * max r 0) :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (C1_nonneg h) (exp_pos _).le) fun d =>
    quadDeriv_norm_le (trajAt_quadDefect hd bu bn r) (K1e_nonneg hd r) (trajAt_lip bu bn r) n d

/-- `n₀ ↦ Y₁(t, n₀)` is Lipschitz with constant `6K₁e^{2νt}`. -/
theorem traj1_lip (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (r : ℝ) (n n' : Nn) :
    ‖traj1 hd bu bn r n - traj1 hd bu bn r n'‖ ≤
      (6 * (hd.K1 * exp (2 * ν * max r 0))) * ‖n - n'‖ :=
  quadDeriv_lipschitz (trajAt_quadDefect hd bu bn r) (K1e_nonneg hd r) (trajAt_lip bu bn r) n' n

theorem diffQuot_trajAt_eq (bu : U) (bn : Nn) {r : ℝ} (hr : 0 ≤ r) (n d : Nn) (ℓ : ℝ) :
    diffQuot (trajAt h bu bn r) n d ℓ = ℓ⁻¹ • trajDiff h bu bn n (ℓ • d) r := by
  simp [diffQuot, trajAt, trajDiff, max_eq_left hr]

/-- `t ↦ Y₁(t, n₀) d` is continuous. -/
theorem traj1_apply_continuous (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n d : Nn) :
    Continuous fun r => traj1 hd bu bn r n d := by
  have hmax : Continuous fun r : ℝ => max r 0 := continuous_id.max continuous_const
  refine continuous_of_rate_approx (F := fun ℓ r => diffQuot (trajAt h bu bn r) n d ℓ)
    (c := fun r => hd.K1 * exp (2 * ν * max r 0) * ‖d‖ ^ 2) (fun ℓ _ => ?_) ?_
    (fun ℓ hℓ r => traj1_diffQuot hd bu bn r n d hℓ)
  · simp only [diffQuot, trajAt]
    exact (((yStar_continuous h bu bn _).comp hmax).sub
      ((yStar_continuous h bu bn _).comp hmax)).const_smul ℓ⁻¹
  · exact (continuous_const.mul ((continuous_const.mul hmax).rexp)).mul continuous_const

/-! ### The first variational equation -/

/-- **First variational equation** at every time `t ≥ 0`:
`Y₁(t)d = (0, P_n(t) d) + 𝒮[DN(y_*) (Y₁ d)](t)`. -/
theorem traj1_eq (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n d : Nn) {t : ℝ}
    (ht : 0 ≤ t) :
    traj1 hd bu bn t n d = ((0 : U), Pn t d) +
      srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d)) t := by
  have hν := h.ν_pos
  have h2α : α < 2 * ν := by linarith [h.α_lt]
  have h2β := hd.two_lt
  set C1 := M / (1 - h.q) with hC1def
  have hC1 : 0 ≤ C1 := C1_nonneg h
  set c2 := (2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹ with hc2def
  have hc2 : 0 ≤ c2 := by
    have h1 : 0 < 2 * ν - α := by linarith
    have h2 : 0 < β - 2 * ν := by linarith
    positivity
  set Y : ℝ → U × Nn := fun r => traj1 hd bu bn r n d with hYdef
  have hYc : Continuous Y := traj1_apply_continuous hd bu bn n d
  have hYb : ∀ r, 0 ≤ r → ‖Y r‖ ≤ (C1 * ‖d‖) * exp (2 * ν * r) := fun r hr => by
    have h1 := ((traj1 hd bu bn r n).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (traj1_norm_le hd bu bn r n) (norm_nonneg d))
    rw [max_eq_left hr] at h1
    refine h1.trans ?_
    have := exp_mul_le_exp_mul (show ν ≤ 2 * ν by linarith) hr
    calc C1 * exp (ν * r) * ‖d‖ = (C1 * ‖d‖) * exp (ν * r) := by ring
      _ ≤ (C1 * ‖d‖) * exp (2 * ν * r) := mul_le_mul_of_nonneg_left this (by positivity)
  have hlinY : ∀ r, 0 ≤ r → ‖linSrc DNu DNv (yStar h bu bn n) Y r‖ ≤
      (L * (C1 * ‖d‖)) * exp (2 * ν * r) := fun r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hYb r hr) h.L_nonneg)
  set x := traj1 hd bu bn t n d - (((0 : U), Pn t d) +
      srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Y) t) with hxdef
  suffices hx : ‖x‖ ≤ 0 by
    have := sub_eq_zero.1 (norm_le_zero_iff.1 hx)
    exact this
  refine le_of_forall_pos_le_add_mul (C := (hd.K1 * ‖d‖ ^ 2 + M * (L * (hd.K1 * ‖d‖ ^ 2)) * c2 +
    M * (L₂ * (C1 * ‖d‖) ^ 2) * c2) * exp (2 * ν * t)) fun ℓ hℓ => ?_
  set W : ℝ → U × Nn := trajDiff h bu bn n (ℓ • d) with hWdef
  have hWc : Continuous W := trajDiff_continuous bu bn n (ℓ • d)
  have hnl : ‖ℓ • d‖ = ℓ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have hWb : ∀ r, 0 ≤ r → ‖W r‖ ≤ (C1 * (ℓ * ‖d‖)) * exp (2 * ν * r) := fun r hr => by
    have h1 := norm_trajDiff_le (h := h) bu bn n (ℓ • d) r
    rw [hnl] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (exp_mul_le_exp_mul (by linarith) hr)
      (by positivity))
  have hlinW : ∀ r, 0 ≤ r → ‖linSrc DNu DNv (yStar h bu bn n) W r‖ ≤
      (L * (C1 * (ℓ * ‖d‖))) * exp (2 * ν * r) := fun r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hWb r hr) h.L_nonneg)
  -- the quotient error `Q = ℓ⁻¹ W - Y`
  set Q : ℝ → U × Nn := ℓ⁻¹ • W - Y with hQdef
  have hQc : Continuous Q := (hWc.const_smul _).sub hYc
  have hQb : ∀ r, 0 ≤ r → ‖Q r‖ ≤ (hd.K1 * ‖d‖ ^ 2 * ℓ) * exp (2 * ν * r) := fun r hr => by
    have h1 := traj1_diffQuot hd bu bn r n d hℓ
    rw [diffQuot_trajAt_eq bu bn hr, max_eq_left hr] at h1
    simp only [hQdef, Pi.sub_apply, Pi.smul_apply]
    refine h1.trans (le_of_eq ?_)
    ring
  have hlinQ : ∀ r, 0 ≤ r → ‖linSrc DNu DNv (yStar h bu bn n) Q r‖ ≤
      (L * (hd.K1 * ‖d‖ ^ 2 * ℓ)) * exp (2 * ν * r) := fun r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hQb r hr) h.L_nonneg)
  have hlinQeq : linSrc DNu DNv (yStar h bu bn n) Q =
      ℓ⁻¹ • linSrc DNu DNv (yStar h bu bn n) W - linSrc DNu DNv (yStar h bu bn n) Y := by
    funext r
    simp [linSrc, hQdef, map_sub, map_smul]
  have hsrcQ : srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Q) t =
      ℓ⁻¹ • srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) W) t -
        srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Y) t := by
    have hlWc := linSrc_continuous hd bu bn n hWc
    have hlYc := linSrc_continuous hd bu bn n hYc
    have hb' : ∀ r, 0 ≤ r → ‖(ℓ⁻¹ • linSrc DNu DNv (yStar h bu bn n) W) r‖ ≤
        (ℓ⁻¹ * (L * (C1 * (ℓ * ‖d‖)))) * exp (2 * ν * r) := fun r hr => by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hlinW r hr) (by positivity)
    rw [hlinQeq, srcOp_sub' h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound (hlWc.const_smul _)
      hlYc hb' hlinY ht, srcOp_smul]
  have heqW := trajDiff_eq hd bu bn n (ℓ • d) ht
  have hrem := srcOp_norm_le h.Pu_cont h.Pn_cont h2α h2β h.M_nonneg h.Pu_bound h.Pn_bound
    (remSrc_continuous hd bu bn n (ℓ • d)) (fun r _ => by
      have := norm_remSrc_le' hd bu bn n (ℓ • d) r
      rwa [hnl] at this) ht
  have hQt := hQb t ht
  have hsrcQb := srcOp_norm_le h.Pu_cont h.Pn_cont h2α h2β h.M_nonneg h.Pu_bound h.Pn_bound
    (linSrc_continuous hd bu bn n hQc) hlinQ ht
  -- the identity `x = -Q t + 𝒮[DN Q](t) + ℓ⁻¹ 𝒮[R](t)`
  have hx : x = -Q t + srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Q) t +
      ℓ⁻¹ • srcOp Pu Pn (remSrc h bu bn DNu DNv n (ℓ • d)) t := by
    rw [hsrcQ, hxdef]
    have hWt : W t = ((0 : U), Pn t (ℓ • d)) +
        (srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) W) t +
          srcOp Pu Pn (remSrc h bu bn DNu DNv n (ℓ • d)) t) := heqW
    have hQt' : Q t = ℓ⁻¹ • W t - Y t := rfl
    rw [hQt', hWt]
    have hP : ((0 : U), Pn t (ℓ • d)) = ℓ • ((0 : U), Pn t d) := by
      rw [map_smul]; simp
    rw [hP]
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hℓ.ne', one_smul]
    simp only [hYdef]
    abel
  rw [hx]
  have hℓinv : ‖ℓ⁻¹ • srcOp Pu Pn (remSrc h bu bn DNu DNv n (ℓ • d)) t‖ ≤
      (M * (L₂ * (C1 * ‖d‖) ^ 2) * c2 * exp (2 * ν * t)) * ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, inv_mul_le_iff₀ hℓ]
    refine hrem.trans (le_of_eq ?_)
    simp only [hc2def, hC1def]
    ring
  calc ‖-Q t + srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Q) t +
        ℓ⁻¹ • srcOp Pu Pn (remSrc h bu bn DNu DNv n (ℓ • d)) t‖
      ≤ ‖Q t‖ + ‖srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) Q) t‖ +
        ‖ℓ⁻¹ • srcOp Pu Pn (remSrc h bu bn DNu DNv n (ℓ • d)) t‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
        rw [norm_neg]
    _ ≤ (hd.K1 * ‖d‖ ^ 2 * ℓ) * exp (2 * ν * t) +
        M * (L * (hd.K1 * ‖d‖ ^ 2 * ℓ)) * c2 * exp (2 * ν * t) +
        (M * (L₂ * (C1 * ‖d‖) ^ 2) * c2 * exp (2 * ν * t)) * ℓ :=
        add_le_add (add_le_add hQt hsrcQb) hℓinv
    _ = 0 + (hd.K1 * ‖d‖ ^ 2 + M * (L * (hd.K1 * ‖d‖ ^ 2)) * c2 +
        M * (L₂ * (C1 * ‖d‖) ^ 2) * c2) * exp (2 * ν * t) * ℓ := by ring

end First

/-! ### The second derivative of the time-`t` value maps -/

section Second

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}
  {D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)}
  {D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)} {L₃ : ℝ}

/-- **Second-level defect at every time** (the `C²` layer's `second_level_le` at time `t⁺`,
weight `3ν`). -/
theorem second_level_traj_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n₀ d : Nn) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3 → ℝ) (v : Fin 3 → Nn)
    (hsum : ∑ i, a i • v i = 0) :
    ‖∑ i, a i • (diffQuot (trajAt h bu bn r) (n₀ + v i) d ℓ -
        diffQuot (trajAt h bu bn r) n₀ d ℓ)‖ ≤
      hd2.Kc * (L₂ * hd.K1 * (M / (1 - h.q)) * ‖d‖ * (∑ i, |a i| * ‖v i‖ ^ 2) +
        ∑ i, |a i| * (L₂ * (M / (1 - h.q)) * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
          2 * L₂ * (M / (1 - h.q)) ^ 2 * ‖d‖ ^ 2 * ℓ +
          L₃ * (M / (1 - h.q)) ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) * exp (3 * ν * max r 0) := by
  have hν := h.ν_pos
  set c : Fin 3 × Fin 3 → ℝ := fun p => a p.1 / ℓ * (![1, -1, -1] : Fin 3 → ℝ) p.2 with hcdef
  set w : Fin 3 × Fin 3 → Nn := fun p => (![v p.1 + ℓ • d, v p.1, ℓ • d] : Fin 3 → Nn) p.2
    with hwdef
  have hsumF : ∑ p, c p • w p = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [hcdef, hwdef, Fin.sum_univ_three]
    have : ∀ i, (a i / ℓ * 1) • (v i + ℓ • d) + (a i / ℓ * -1) • v i + (a i / ℓ * -1) • (ℓ • d)
        = 0 := fun i => by
      simp only [mul_one, mul_neg, neg_smul, smul_add]; abel
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [this 0, this 1, this 2]
    simp
  have hvalS : ∀ s, (∑ p, c p • remSrc h bu bn DNu DNv n₀ (w p)) s =
      ∑ i, (a i / ℓ) • (remSrc h bu bn DNu DNv n₀ (v i + ℓ • d) s -
        remSrc h bu bn DNu DNv n₀ (v i) s - remSrc h bu bn DNu DNv n₀ (ℓ • d) s) := by
    intro s
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcdef, hwdef, Fin.sum_univ_three, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [mul_one, mul_neg, neg_smul, smul_sub]; abel
  have hσ : 0 ≤ L₂ * hd.K1 * (M / (1 - h.q)) * ‖d‖ * (∑ i, |a i| * ‖v i‖ ^ 2) +
      ∑ i, |a i| * (L₂ * (M / (1 - h.q)) * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
        2 * L₂ * (M / (1 - h.q)) ^ 2 * ‖d‖ ^ 2 * ℓ + L₃ * (M / (1 - h.q)) ^ 3 * ‖v i‖ ^ 2 * ‖d‖) := by
    have hC1 : 0 ≤ M / (1 - h.q) := C1_nonneg h
    have := hd.L₂_nonneg; have := hd2.L₃_nonneg; have := hd.K1_nonneg
    have hK2 : 0 ≤ hd.K2 := by unfold GraphC1Hyp.K2; linarith [hd.K1_nonneg]
    positivity
  have hcomb := comb_le hd bu bn n₀ c w hsumF (by linarith) (by linarith [h.α_lt])
    hd2.three_lt hd2.contr3 hσ
    (fun s hs => by rw [hvalS]; exact second_level_src_le hd hd2 bu bn n₀ d hℓ a v hsum hs)
    (le_max_right r 0)
  have hz0 : (∑ p, c p • trajDiff h bu bn n₀ (w p)) (max r 0) =
      ∑ i, a i • (diffQuot (trajAt h bu bn r) (n₀ + v i) d ℓ -
        diffQuot (trajAt h bu bn r) n₀ d ℓ) := by
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcdef, hwdef, Fin.sum_univ_three, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      trajDiff, diffQuot, trajAt]
    rw [← add_assoc]
    module
  rw [← hz0]
  refine hcomb.trans (le_of_eq ?_)
  simp only [GraphC2Hyp.Kc]
  ring

theorem Kde_nonneg {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (r : ℝ) :
    0 ≤ hd2.Kd * exp (3 * ν * max r 0) :=
  mul_nonneg hd2.Kd_nonneg (exp_pos _).le

/-- **`n₀ ↦ Y₁(t, n₀)` has uniform quadratic three-point defects** (in operator norm), with
constant `K_d e^{3νt⁺}`. -/
theorem traj1_quadDefect (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) :
    QuadDefect (traj1 hd bu bn r) (hd2.Kd * exp (3 * ν * max r 0)) := by
  intro n₀ v₁ v₂ v₃ a₁ a₂ a₃ hsum
  set E3 := exp (3 * ν * max r 0) with hE3
  set K1e := hd.K1 * exp (2 * ν * max r 0) with hK1e
  have hE3p : 0 < E3 := exp_pos _
  have hS0 : 0 ≤ |a₁| * ‖v₁‖ ^ 2 + |a₂| * ‖v₂‖ ^ 2 + |a₃| * ‖v₃‖ ^ 2 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hd2.Kd_nonneg hE3p.le) hS0) fun d => ?_
  set a : Fin 3 → ℝ := ![a₁, a₂, a₃]
  set v : Fin 3 → Nn := ![v₁, v₂, v₃]
  have hsum' : ∑ i, a i • v i = 0 := by simpa [a, v, Fin.sum_univ_three] using hsum
  have hH := trajAt_quadDefect hd bu bn r
  have hK := K1e_nonneg hd r
  have happ : (a₁ • (traj1 hd bu bn r (n₀ + v₁) - traj1 hd bu bn r n₀) +
      a₂ • (traj1 hd bu bn r (n₀ + v₂) - traj1 hd bu bn r n₀) +
      a₃ • (traj1 hd bu bn r (n₀ + v₃) - traj1 hd bu bn r n₀)) d =
      ∑ i, a i • (quadDeriv (trajAt h bu bn r) (n₀ + v i) d -
        quadDeriv (trajAt h bu bn r) n₀ d) := by
    simp only [a, v, Fin.sum_univ_three, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rfl
  rw [happ]
  set C1 := M / (1 - h.q)
  set S := ∑ i, |a i| * ‖v i‖ ^ 2
  have hSeq : S = |a₁| * ‖v₁‖ ^ 2 + |a₂| * ‖v₂‖ ^ 2 + |a₃| * ‖v₃‖ ^ 2 := by
    simp [S, a, v, Fin.sum_univ_three]
  rw [← hSeq]
  refine le_of_forall_pos_le_add_mul (C := hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ *
    ‖d‖ ^ 2 + 2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * E3 + ∑ i, |a i| * (2 * K1e * ‖d‖ ^ 2))
    fun ℓ hℓ => ?_
  have h2 := second_level_traj_le hd hd2 bu bn r n₀ d hℓ a v hsum'
  have hq1 : ∀ n, ‖diffQuot (trajAt h bu bn r) n d ℓ - quadDeriv (trajAt h bu bn r) n d‖ ≤
      K1e * ‖d‖ ^ 2 * ℓ := fun n => diffQuot_sub_quadDeriv_le hH hK n d hℓ
  have hdecomp : ∑ i, a i • (quadDeriv (trajAt h bu bn r) (n₀ + v i) d -
        quadDeriv (trajAt h bu bn r) n₀ d) =
      ∑ i, a i • (diffQuot (trajAt h bu bn r) (n₀ + v i) d ℓ -
        diffQuot (trajAt h bu bn r) n₀ d ℓ) -
      ∑ i, a i • ((diffQuot (trajAt h bu bn r) (n₀ + v i) d ℓ -
          quadDeriv (trajAt h bu bn r) (n₀ + v i) d) -
        (diffQuot (trajAt h bu bn r) n₀ d ℓ - quadDeriv (trajAt h bu bn r) n₀ d)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_sub]; congr 1; abel
  have herr : ‖∑ i, a i • ((diffQuot (trajAt h bu bn r) (n₀ + v i) d ℓ -
          quadDeriv (trajAt h bu bn r) (n₀ + v i) d) -
        (diffQuot (trajAt h bu bn r) n₀ d ℓ - quadDeriv (trajAt h bu bn r) n₀ d))‖ ≤
      (∑ i, |a i| * (2 * K1e * ‖d‖ ^ 2)) * ℓ := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    have := hq1 (n₀ + v i); have := hq1 n₀
    linarith
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  have hsplit : hd2.Kc * (L₂ * hd.K1 * C1 * ‖d‖ * S +
      ∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2 * ℓ + L₃ * C1 ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) * E3 =
      hd2.Kd * E3 * S * ‖d‖ + hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * ‖d‖ ^ 2 +
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * E3 * ℓ := by
    have e1 : hd2.Kc * (L₂ * hd.K1 * C1 * ‖d‖ * S +
        ∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
          2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2 * ℓ + L₃ * C1 ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) =
        hd2.Kd * S * ‖d‖ + hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * ‖d‖ ^ 2 +
          2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * ℓ := by
      simp only [GraphC2Hyp.Kd, S, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e1]; ring
  have := h2.trans (le_of_eq hsplit)
  calc _ ≤ hd2.Kd * E3 * S * ‖d‖ + hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * ‖d‖ ^ 2 +
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * E3 * ℓ + (∑ i, |a i| * (2 * K1e * ‖d‖ ^ 2)) * ℓ :=
        add_le_add this herr
    _ = _ := by ring

/-- **The second derivative of the time-`t` value map**, `Y₂(t, n₀) = D_{n₀} Y₁(t, n₀)`. -/
def traj2 (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (bu : U) (bn : Nn)
    (r : ℝ) (n : Nn) : Nn →L[ℝ] Nn →L[ℝ] U × Nn :=
  quadDerivCLM (traj1_quadDefect hd hd2 bu bn r) (Kde_nonneg hd2 r) (traj1_lip hd bu bn r) n

theorem traj2_hasFDerivAt (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n : Nn) :
    HasFDerivAt (traj1 hd bu bn r) (traj2 hd hd2 bu bn r n) n :=
  quadDeriv_hasFDerivAt _ _ _ n

theorem traj2_taylor (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n v : Nn) :
    ‖traj1 hd bu bn r (n + v) - traj1 hd bu bn r n - traj2 hd hd2 bu bn r n v‖ ≤
      hd2.Kd * exp (3 * ν * max r 0) * ‖v‖ ^ 2 :=
  quadDeriv_taylor (traj1_quadDefect hd hd2 bu bn r) (Kde_nonneg hd2 r) n v

theorem traj2_diffQuot (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n e : Nn) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖diffQuot (traj1 hd bu bn r) n e ℓ - traj2 hd hd2 bu bn r n e‖ ≤
      hd2.Kd * exp (3 * ν * max r 0) * ‖e‖ ^ 2 * ℓ :=
  diffQuot_sub_quadDeriv_le (traj1_quadDefect hd hd2 bu bn r) (Kde_nonneg hd2 r) n e hℓ

theorem traj2_norm_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n : Nn) :
    ‖traj2 hd hd2 bu bn r n‖ ≤ 6 * (hd.K1 * exp (2 * ν * max r 0)) :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := K1e_nonneg hd r; positivity) fun e =>
    quadDeriv_norm_le (traj1_quadDefect hd hd2 bu bn r) (Kde_nonneg hd2 r)
      (traj1_lip hd bu bn r) n e

/-- `n₀ ↦ Y₂(t, n₀)` is Lipschitz with constant `6K_d e^{3νt}`. -/
theorem traj2_lip (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (r : ℝ) (n n' : Nn) :
    ‖traj2 hd hd2 bu bn r n - traj2 hd hd2 bu bn r n'‖ ≤
      (6 * (hd2.Kd * exp (3 * ν * max r 0))) * ‖n - n'‖ :=
  quadDeriv_lipschitz (traj1_quadDefect hd hd2 bu bn r) (Kde_nonneg hd2 r)
    (traj1_lip hd bu bn r) n' n

/-- `t ↦ Y₂(t, n₀) e d` is continuous. -/
theorem traj2_apply_continuous (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) :
    Continuous fun r => traj2 hd hd2 bu bn r n e d := by
  have hmax : Continuous fun r : ℝ => max r 0 := continuous_id.max continuous_const
  refine continuous_of_rate_approx (F := fun ℓ r => diffQuot (traj1 hd bu bn r) n e ℓ d)
    (c := fun r => hd2.Kd * exp (3 * ν * max r 0) * ‖e‖ ^ 2 * ‖d‖) (fun ℓ _ => ?_) ?_
    (fun ℓ hℓ r => ?_)
  · simp only [diffQuot, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
    exact ((traj1_apply_continuous hd bu bn _ d).sub
      (traj1_apply_continuous hd bu bn n d)).const_smul ℓ⁻¹
  · exact ((continuous_const.mul ((continuous_const.mul hmax).rexp)).mul continuous_const).mul
      continuous_const
  · have h1 := traj2_diffQuot hd hd2 bu bn r n e hℓ
    calc ‖diffQuot (traj1 hd bu bn r) n e ℓ d - traj2 hd hd2 bu bn r n e d‖
        = ‖(diffQuot (traj1 hd bu bn r) n e ℓ - traj2 hd hd2 bu bn r n e) d‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖diffQuot (traj1 hd bu bn r) n e ℓ - traj2 hd hd2 bu bn r n e‖ * ‖d‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (hd2.Kd * exp (3 * ν * max r 0) * ‖e‖ ^ 2 * ℓ) * ‖d‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring

/-! ### The second variational equation -/

/-- Pointwise algebra of the second variational equation: for `f = DN`, `Df = D²N`,
`‖ℓ⁻¹(f(y+w) ad' - f(y) ad) - (f(y) b + Df(y) ae ad)‖ = O(ℓ)`. -/
theorem var2_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → E →L[ℝ] G}
    {Df : E → E →L[ℝ] (E →L[ℝ] G)} {L L₂ L₃ : ℝ} (hL₃ : 0 ≤ L₃)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₃ * ‖x - x'‖)
    (hfb : ∀ x, ‖f x‖ ≤ L) (hDfb : ∀ x, ‖Df x‖ ≤ L₂) (y w ae ad ad' b : E) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Wn A1 A2 A3 A4 Bd : ℝ} (hw : ‖w‖ ≤ Wn * ℓ) (h1 : ‖ℓ⁻¹ • w - ae‖ ≤ A1 * ℓ)
    (hae : ‖ae‖ ≤ A2) (h2 : ‖ad' - ad‖ ≤ A3 * ℓ) (had' : ‖ad'‖ ≤ Bd)
    (h3 : ‖ℓ⁻¹ • (ad' - ad) - b‖ ≤ A4 * ℓ) :
    ‖ℓ⁻¹ • (f (y + w) ad' - f y ad) - (f y b + Df y ae ad)‖ ≤
      (L₃ * Wn ^ 2 * Bd + L₂ * A1 * Bd + L₂ * A2 * A3 + L * A4) * ℓ := by
  have hL : 0 ≤ L := (norm_nonneg (f y)).trans (hfb y)
  have hL₂ : 0 ≤ L₂ := (norm_nonneg (Df y)).trans (hDfb y)
  have hBd : 0 ≤ Bd := (norm_nonneg _).trans had'
  have hA2 : 0 ≤ A2 := (norm_nonneg _).trans hae
  have hA1 : 0 ≤ A1 * ℓ := (norm_nonneg _).trans h1
  have hA3 : 0 ≤ A3 * ℓ := (norm_nonneg _).trans h2
  have hA4 : 0 ≤ A4 * ℓ := (norm_nonneg _).trans h3
  have e : ℓ⁻¹ • (f (y + w) ad' - f y ad) - (f y b + Df y ae ad) =
      ℓ⁻¹ • ((f (y + w) - f y - Df y w) ad') + Df y (ℓ⁻¹ • w - ae) ad' +
        Df y ae (ad' - ad) + f y (ℓ⁻¹ • (ad' - ad) - b) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub, map_smul, ContinuousLinearMap.smul_apply]
    module
  rw [e]
  have t1 : ‖ℓ⁻¹ • ((f (y + w) - f y - Df y w) ad')‖ ≤ L₃ * Wn ^ 2 * Bd * ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, inv_mul_le_iff₀ hℓ]
    have hT := GraphC1Hyp.taylor_le hL₃ hf hDf y w
    have hw2 : ‖w‖ ^ 2 ≤ (Wn * ℓ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    calc ‖(f (y + w) - f y - Df y w) ad'‖ ≤ ‖f (y + w) - f y - Df y w‖ * ‖ad'‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L₃ * (Wn * ℓ) ^ 2) * Bd :=
          mul_le_mul (hT.trans (mul_le_mul_of_nonneg_left hw2 hL₃)) had' (norm_nonneg _)
            (by positivity)
      _ = ℓ * (L₃ * Wn ^ 2 * Bd * ℓ) := by ring
  have t2 : ‖Df y (ℓ⁻¹ • w - ae) ad'‖ ≤ L₂ * A1 * Bd * ℓ := by
    calc _ ≤ ‖Df y‖ * ‖ℓ⁻¹ • w - ae‖ * ‖ad'‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ L₂ * (A1 * ℓ) * Bd :=
          mul_le_mul (mul_le_mul (hDfb y) h1 (norm_nonneg _) hL₂) had' (norm_nonneg _)
            (mul_nonneg hL₂ hA1)
      _ = _ := by ring
  have t3 : ‖Df y ae (ad' - ad)‖ ≤ L₂ * A2 * A3 * ℓ := by
    calc _ ≤ ‖Df y‖ * ‖ae‖ * ‖ad' - ad‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ L₂ * A2 * (A3 * ℓ) :=
          mul_le_mul (mul_le_mul (hDfb y) hae (norm_nonneg _) hL₂) h2 (norm_nonneg _)
            (mul_nonneg hL₂ hA2)
      _ = _ := by ring
  have t4 : ‖f y (ℓ⁻¹ • (ad' - ad) - b)‖ ≤ L * A4 * ℓ := by
    calc _ ≤ ‖f y‖ * ‖ℓ⁻¹ • (ad' - ad) - b‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * (A4 * ℓ) := mul_le_mul (hfb y) h3 (norm_nonneg _) hL
      _ = _ := by ring
  calc _ ≤ ‖ℓ⁻¹ • ((f (y + w) - f y - Df y w) ad')‖ + ‖Df y (ℓ⁻¹ • w - ae) ad'‖ +
        ‖Df y ae (ad' - ad)‖ + ‖f y (ℓ⁻¹ • (ad' - ad) - b)‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by nlinarith [t1, t2, t3, t4]

/-- The source of the second variational equation,
`DN(y_*) (Y₂ e d) + D²N(y_*)(Y₁ e)(Y₁ d)`. -/
def var2Src (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (bu : U)
    (bn : Nn) (n e d : Nn) : ℝ → U × Nn := fun r =>
  (DNu (yStar h bu bn n r) (traj2 hd hd2 bu bn r n e d) +
      D2Nu (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d),
    DNv (yStar h bu bn n r) (traj2 hd hd2 bu bn r n e d) +
      D2Nv (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d))

theorem var2Src_continuous (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) : Continuous (var2Src hd hd2 bu bn n e d) := by
  have hy := yStar_continuous h bu bn n
  have hD2u : Continuous D2Nu := GraphHyp.lip_continuous (g := D2Nu) hd2.D2u_lip
  have hD2v : Continuous D2Nv := GraphHyp.lip_continuous (g := D2Nv) hd2.D2v_lip
  have h2 := traj2_apply_continuous hd hd2 bu bn n e d
  have h1e := traj1_apply_continuous hd bu bn n e
  have h1d := traj1_apply_continuous hd bu bn n d
  exact (((hd.continuous_DNu.comp hy).clm_apply h2).add
      (((hD2u.comp hy).clm_apply h1e).clm_apply h1d)).prodMk
    (((hd.continuous_DNv.comp hy).clm_apply h2).add
      (((hD2v.comp hy).clm_apply h1e).clm_apply h1d))

theorem traj1_apply_le (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) {r : ℝ} (hr : 0 ≤ r)
    (n d : Nn) : ‖traj1 hd bu bn r n d‖ ≤ M / (1 - h.q) * exp (ν * r) * ‖d‖ := by
  have h1 := ((traj1 hd bu bn r n).le_opNorm d).trans
    (mul_le_mul_of_nonneg_right (traj1_norm_le hd bu bn r n) (norm_nonneg d))
  rwa [max_eq_left hr] at h1

theorem traj2_apply_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) {r : ℝ} (hr : 0 ≤ r) (n e d : Nn) :
    ‖traj2 hd hd2 bu bn r n e d‖ ≤ 6 * (hd.K1 * exp (2 * ν * r)) * ‖e‖ * ‖d‖ := by
  have h1 := (ContinuousLinearMap.le_opNorm₂ (traj2 hd hd2 bu bn r n) e d).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (traj2_norm_le hd hd2 bu bn r n)
      (norm_nonneg e)) (norm_nonneg d))
  rwa [max_eq_left hr] at h1

theorem var2_key_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {L L₂ C1 K1 E1 E2 E3 : ℝ}
    (A : (U × Nn) →L[ℝ] G) (B : (U × Nn) →L[ℝ] (U × Nn) →L[ℝ] G) (hA : ‖A‖ ≤ L)
    (hB : ‖B‖ ≤ L₂) (x2 x1e x1d : U × Nn) {ne nd : ℝ} (h2 : ‖x2‖ ≤ 6 * (K1 * E2) * ne * nd)
    (h1e : ‖x1e‖ ≤ C1 * E1 * ne) (h1d : ‖x1d‖ ≤ C1 * E1 * nd) (hE : E2 = E1 ^ 2)
    (hE23 : E2 ≤ E3) (hC : 0 ≤ (L * (6 * K1) + L₂ * C1 ^ 2) * ne * nd) :
    ‖A x2 + B x1e x1d‖ ≤ ((L * (6 * K1) + L₂ * C1 ^ 2) * ne * nd) * E3 := by
  have hL : 0 ≤ L := (norm_nonneg A).trans hA
  have hL₂ : 0 ≤ L₂ := (norm_nonneg B).trans hB
  have t1 : ‖A x2‖ ≤ L * (6 * (K1 * E2) * ne * nd) :=
    (A.le_opNorm _).trans (mul_le_mul hA h2 (norm_nonneg _) hL)
  have hb0 : 0 ≤ C1 * E1 * ne := (norm_nonneg _).trans h1e
  have t2 : ‖B x1e x1d‖ ≤ L₂ * (C1 * E1 * ne) * (C1 * E1 * nd) :=
    (B.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul hB h1e (norm_nonneg _) hL₂) h1d
      (norm_nonneg _) (mul_nonneg hL₂ hb0))
  have e2 : L * (6 * (K1 * E2) * ne * nd) + L₂ * (C1 * E1 * ne) * (C1 * E1 * nd) =
      ((L * (6 * K1) + L₂ * C1 ^ 2) * ne * nd) * E2 := by
    rw [hE]; ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := e2
    _ ≤ _ := mul_le_mul_of_nonneg_left hE23 hC

theorem var2Src_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n e d : Nn) {r : ℝ} (hr : 0 ≤ r) :
    ‖var2Src hd hd2 bu bn n e d r‖ ≤
      ((L * (6 * hd.K1) + L₂ * (M / (1 - h.q)) ^ 2) * ‖e‖ * ‖d‖) * exp (3 * ν * r) := by
  have hν := h.ν_pos
  have hC1 := C1_nonneg h
  have hK1 := hd.K1_nonneg
  have hE : exp (2 * ν * r) = exp (ν * r) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hE23 : exp (2 * ν * r) ≤ exp (3 * ν * r) := exp_le_exp.2 (by nlinarith)
  have hC : 0 ≤ (L * (6 * hd.K1) + L₂ * (M / (1 - h.q)) ^ 2) * ‖e‖ * ‖d‖ := by
    have := h.L_nonneg; have := hd.L₂_nonneg; positivity
  have h2 := traj2_apply_le hd hd2 bu bn hr n e d
  have h1e := traj1_apply_le hd bu bn hr n e
  have h1d := traj1_apply_le hd bu bn hr n d
  exact norm_prod_le_of_le
    (var2_key_le _ _ (hd.norm_DNu_le _) (norm_D2_le hd.L₂_nonneg hd.Du_lip hd2.hasDeriv2_u _)
      _ _ _ h2 h1e h1d hE hE23 hC)
    (var2_key_le _ _ (hd.norm_DNv_le _) (norm_D2_le hd.L₂_nonneg hd.Dv_lip hd2.hasDeriv2_v _)
      _ _ _ h2 h1e h1d hE hE23 hC)


/-- **Second variational equation** at every time `t ≥ 0`:
`Y₂(t) e d = 𝒮[DN(y_*)(Y₂ e d) + D²N(y_*)(Y₁ e)(Y₁ d)](t)`. -/
theorem traj2_eq (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) (bu : U)
    (bn : Nn) (n e d : Nn) {t : ℝ} (ht : 0 ≤ t) :
    traj2 hd hd2 bu bn t n e d = srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t := by
  have hν := h.ν_pos
  have h3α : α < 3 * ν := by linarith [h.α_lt]
  have h3β := hd2.three_lt
  have hC1 : 0 ≤ M / (1 - h.q) := C1_nonneg h
  have hc3 : 0 ≤ (3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹ := by
    have h1 : 0 < 3 * ν - α := by linarith
    have h2 : 0 < β - 3 * ν := by linarith
    positivity
  set C1 := M / (1 - h.q) with hC1def
  set Cb := L₃ * (C1 * ‖e‖) ^ 2 * (C1 * ‖d‖) + L₂ * (hd.K1 * ‖e‖ ^ 2) * (C1 * ‖d‖) +
      L₂ * (C1 * ‖e‖) * (6 * hd.K1 * ‖e‖ * ‖d‖) + L * (hd2.Kd * ‖e‖ ^ 2 * ‖d‖) with hCbdef
  have hGc : Continuous (var2Src hd hd2 bu bn n e d) := var2Src_continuous hd hd2 bu bn n e d
  have hGb := fun r (hr : 0 ≤ r) => var2Src_le hd hd2 bu bn n e d hr
  suffices hx : ‖traj2 hd hd2 bu bn t n e d - srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t‖ ≤ 0 from
    sub_eq_zero.1 (norm_le_zero_iff.1 hx)
  refine le_of_forall_pos_le_add_mul (C := (hd2.Kd * ‖e‖ ^ 2 * ‖d‖ +
    M * Cb * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹)) * exp (3 * ν * t)) fun ℓ hℓ => ?_
  have hnl : ‖ℓ • e‖ = ℓ * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  -- the sources of the two first variational equations
  have hS1c : Continuous (linSrc DNu DNv (yStar h bu bn (n + ℓ • e))
      (fun r => traj1 hd bu bn r (n + ℓ • e) d)) :=
    linSrc_continuous hd bu bn _ (traj1_apply_continuous hd bu bn _ d)
  have hS0c : Continuous (linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d)) :=
    linSrc_continuous hd bu bn n (traj1_apply_continuous hd bu bn n d)
  have hlb : ∀ m r, 0 ≤ r →
      ‖linSrc DNu DNv (yStar h bu bn m) (fun r => traj1 hd bu bn r m d) r‖ ≤
        (L * (C1 * ‖d‖)) * exp (3 * ν * r) := fun m r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      have h1 := traj1_apply_le hd bu bn hr m d
      have h2 := exp_mul_le_exp_mul (show ν ≤ 3 * ν by linarith) hr
      have hL := h.L_nonneg
      calc L * ‖traj1 hd bu bn r m d‖ ≤ L * (C1 * exp (ν * r) * ‖d‖) :=
            mul_le_mul_of_nonneg_left h1 hL
        _ = (L * (C1 * ‖d‖)) * exp (ν * r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity))
  have hdiff : traj1 hd bu bn t (n + ℓ • e) d - traj1 hd bu bn t n d =
      srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn (n + ℓ • e))
          (fun r => traj1 hd bu bn r (n + ℓ • e) d)) t -
        srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d)) t := by
    rw [traj1_eq hd bu bn (n + ℓ • e) d ht, traj1_eq hd bu bn n d ht]; abel
  -- the source difference
  set P : ℝ → U × Nn := ℓ⁻¹ • (linSrc DNu DNv (yStar h bu bn (n + ℓ • e))
      (fun r => traj1 hd bu bn r (n + ℓ • e) d) -
        linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d)) -
      var2Src hd hd2 bu bn n e d with hPdef
  have hsrcP : srcOp Pu Pn P t = ℓ⁻¹ • (srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn (n + ℓ • e))
          (fun r => traj1 hd bu bn r (n + ℓ • e) d)) t -
        srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d)) t) -
      srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t := by
    have hbs : ∀ r, 0 ≤ r → ‖(ℓ⁻¹ • (linSrc DNu DNv (yStar h bu bn (n + ℓ • e))
        (fun r => traj1 hd bu bn r (n + ℓ • e) d) -
          linSrc DNu DNv (yStar h bu bn n) (fun r => traj1 hd bu bn r n d))) r‖ ≤
        (ℓ⁻¹ * (L * (C1 * ‖d‖) + L * (C1 * ‖d‖))) * exp (3 * ν * r) := fun r hr => by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [Pi.sub_apply, add_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hlb _ r hr) (hlb n r hr))
    rw [hPdef, srcOp_sub' h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound
      ((hS1c.sub hS0c).const_smul _) hGc hbs hGb ht, srcOp_smul,
      srcOp_sub' h.Pu_cont h.Pn_cont h3β h.M_nonneg h.Pu_bound hS1c hS0c (hlb _) (hlb n) ht]
  have hx : traj2 hd hd2 bu bn t n e d - srcOp Pu Pn (var2Src hd hd2 bu bn n e d) t =
      -(diffQuot (traj1 hd bu bn t) n e ℓ d - traj2 hd hd2 bu bn t n e d) + srcOp Pu Pn P t := by
    rw [hsrcP, ← hdiff]
    simp only [diffQuot, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
    abel
  -- the pointwise bound of the source difference
  have hPb : ∀ r, 0 ≤ r → ‖P r‖ ≤ (Cb * ℓ) * exp (3 * ν * r) := fun r hr => by
    have hE2 : exp (2 * ν * r) = exp (ν * r) ^ 2 := by rw [← exp_nat_mul]; ring_nf
    have hE3 : exp (3 * ν * r) = exp (ν * r) ^ 3 := by rw [← exp_nat_mul]; ring_nf
    have hy' : yStar h bu bn (n + ℓ • e) r =
        yStar h bu bn n r + trajDiff h bu bn n (ℓ • e) r := yStar_add_eq bu bn n (ℓ • e) r
    have hw : ‖trajDiff h bu bn n (ℓ • e) r‖ ≤ (C1 * ‖e‖ * exp (ν * r)) * ℓ := by
      have := norm_trajDiff_le (h := h) bu bn n (ℓ • e) r
      rw [hnl] at this
      exact this.trans (le_of_eq (by ring))
    have h1 : ‖ℓ⁻¹ • trajDiff h bu bn n (ℓ • e) r - traj1 hd bu bn r n e‖ ≤
        (hd.K1 * exp (ν * r) ^ 2 * ‖e‖ ^ 2) * ℓ := by
      have := traj1_diffQuot hd bu bn r n e hℓ
      rw [diffQuot_trajAt_eq bu bn hr, max_eq_left hr, hE2] at this
      exact this.trans (le_of_eq (by ring))
    have hae : ‖traj1 hd bu bn r n e‖ ≤ C1 * exp (ν * r) * ‖e‖ := traj1_apply_le hd bu bn hr n e
    have h2 : ‖traj1 hd bu bn r (n + ℓ • e) d - traj1 hd bu bn r n d‖ ≤
        (6 * hd.K1 * exp (ν * r) ^ 2 * ‖e‖ * ‖d‖) * ℓ := by
      have h0 := traj1_lip hd bu bn r (n + ℓ • e) n
      rw [add_sub_cancel_left, hnl, max_eq_left hr, hE2] at h0
      calc ‖traj1 hd bu bn r (n + ℓ • e) d - traj1 hd bu bn r n d‖
          = ‖(traj1 hd bu bn r (n + ℓ • e) - traj1 hd bu bn r n) d‖ := by
            rw [ContinuousLinearMap.sub_apply]
        _ ≤ ‖traj1 hd bu bn r (n + ℓ • e) - traj1 hd bu bn r n‖ * ‖d‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (6 * (hd.K1 * exp (ν * r) ^ 2)) * (ℓ * ‖e‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
        _ = _ := by ring
    have had' : ‖traj1 hd bu bn r (n + ℓ • e) d‖ ≤ C1 * exp (ν * r) * ‖d‖ :=
      traj1_apply_le hd bu bn hr _ d
    have h3 : ‖ℓ⁻¹ • (traj1 hd bu bn r (n + ℓ • e) d - traj1 hd bu bn r n d) -
        traj2 hd hd2 bu bn r n e d‖ ≤ (hd2.Kd * exp (ν * r) ^ 3 * ‖e‖ ^ 2 * ‖d‖) * ℓ := by
      have h0 := traj2_diffQuot hd hd2 bu bn r n e hℓ
      rw [max_eq_left hr, hE3] at h0
      calc ‖ℓ⁻¹ • (traj1 hd bu bn r (n + ℓ • e) d - traj1 hd bu bn r n d) -
            traj2 hd hd2 bu bn r n e d‖
          = ‖(diffQuot (traj1 hd bu bn r) n e ℓ - traj2 hd hd2 bu bn r n e) d‖ := by
            simp only [diffQuot, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
        _ ≤ ‖diffQuot (traj1 hd bu bn r) n e ℓ - traj2 hd hd2 bu bn r n e‖ * ‖d‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (hd2.Kd * exp (ν * r) ^ 3 * ‖e‖ ^ 2 * ℓ) * ‖d‖ :=
            mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
        _ = _ := by ring
    have hfin : (L₃ * (C1 * ‖e‖ * exp (ν * r)) ^ 2 * (C1 * exp (ν * r) * ‖d‖) +
        L₂ * (hd.K1 * exp (ν * r) ^ 2 * ‖e‖ ^ 2) * (C1 * exp (ν * r) * ‖d‖) +
        L₂ * (C1 * exp (ν * r) * ‖e‖) * (6 * hd.K1 * exp (ν * r) ^ 2 * ‖e‖ * ‖d‖) +
        L * (hd2.Kd * exp (ν * r) ^ 3 * ‖e‖ ^ 2 * ‖d‖)) * ℓ = (Cb * ℓ) * exp (3 * ν * r) := by
      rw [hE3, hCbdef]; ring
    have hPr : P r = (ℓ⁻¹ • (DNu (yStar h bu bn n r + trajDiff h bu bn n (ℓ • e) r)
            (traj1 hd bu bn r (n + ℓ • e) d) - DNu (yStar h bu bn n r) (traj1 hd bu bn r n d)) -
          (DNu (yStar h bu bn n r) (traj2 hd hd2 bu bn r n e d) +
            D2Nu (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d)),
        ℓ⁻¹ • (DNv (yStar h bu bn n r + trajDiff h bu bn n (ℓ • e) r)
            (traj1 hd bu bn r (n + ℓ • e) d) - DNv (yStar h bu bn n r) (traj1 hd bu bn r n d)) -
          (DNv (yStar h bu bn n r) (traj2 hd hd2 bu bn r n e d) +
            D2Nv (yStar h bu bn n r) (traj1 hd bu bn r n e) (traj1 hd bu bn r n d))) := by
      rw [hPdef, ← hy']
      rfl
    rw [hPr]
    refine norm_prod_le_of_le ?_ ?_
    · rw [← hfin]
      exact var2_comp_le hd2.L₃_nonneg hd2.hasDeriv2_u hd2.D2u_lip hd.norm_DNu_le
        (norm_D2_le hd.L₂_nonneg hd.Du_lip hd2.hasDeriv2_u) _ _ _ _ _ _ hℓ hw h1 hae h2 had' h3
    · rw [← hfin]
      exact var2_comp_le hd2.L₃_nonneg hd2.hasDeriv2_v hd2.D2v_lip hd.norm_DNv_le
        (norm_D2_le hd.L₂_nonneg hd.Dv_lip hd2.hasDeriv2_v) _ _ _ _ _ _ hℓ hw h1 hae h2 had' h3
  have hPc : Continuous P := ((hS1c.sub hS0c).const_smul _).sub hGc
  have hsrcPb := srcOp_norm_le h.Pu_cont h.Pn_cont h3α h3β h.M_nonneg h.Pu_bound h.Pn_bound hPc
    hPb ht
  have hq : ‖diffQuot (traj1 hd bu bn t) n e ℓ d - traj2 hd hd2 bu bn t n e d‖ ≤
      (hd2.Kd * ‖e‖ ^ 2 * ‖d‖ * exp (3 * ν * t)) * ℓ := by
    have h0 := traj2_diffQuot hd hd2 bu bn t n e hℓ
    rw [max_eq_left ht] at h0
    calc ‖diffQuot (traj1 hd bu bn t) n e ℓ d - traj2 hd hd2 bu bn t n e d‖
        = ‖(diffQuot (traj1 hd bu bn t) n e ℓ - traj2 hd hd2 bu bn t n e) d‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖diffQuot (traj1 hd bu bn t) n e ℓ - traj2 hd hd2 bu bn t n e‖ * ‖d‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (hd2.Kd * exp (3 * ν * t) * ‖e‖ ^ 2 * ℓ) * ‖d‖ :=
          mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
      _ = _ := by ring
  rw [hx]
  calc ‖-(diffQuot (traj1 hd bu bn t) n e ℓ d - traj2 hd hd2 bu bn t n e d) + srcOp Pu Pn P t‖
      ≤ ‖diffQuot (traj1 hd bu bn t) n e ℓ d - traj2 hd hd2 bu bn t n e d‖ +
        ‖srcOp Pu Pn P t‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ (hd2.Kd * ‖e‖ ^ 2 * ‖d‖ * exp (3 * ν * t)) * ℓ +
        M * (Cb * ℓ) * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) * exp (3 * ν * t) :=
        add_le_add hq hsrcPb
    _ = 0 + (hd2.Kd * ‖e‖ ^ 2 * ‖d‖ + M * Cb * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹)) *
        exp (3 * ν * t) * ℓ := by ring

end Second

end

end LyapunovPerron
end RenewalGeometry
