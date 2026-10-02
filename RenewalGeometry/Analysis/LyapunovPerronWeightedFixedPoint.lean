/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovPerronWeightedKernel

/-!
# The Lyapunov–Perron fixed point in the exponentially weighted space

Second layer of the forward invariant-graph construction (`lem:supp-exact-graph-criterion`,
emergent-spacetime manuscript), on top of `Analysis/LyapunovPerronWeightedKernel.lean`.

Setting (`GraphHyp`): Banach spaces `U`, `Nn`; strongly continuous *groups* of operators
`P_u, P_n : ℝ → End` (`P(s + t) = P(s) P(t)`, as for `P(t) = e^{tA}` in the paper) with
`‖P_u(-s)‖ ≤ M e^{-βs}`, `‖P_n(s)‖ ≤ M e^{αs}` (`s ≥ 0`), `0 < ν`, `α < ν < β`, globally
`L`-Lipschitz nonlinearities `N_u, N_n`, and the `j = 1` contraction condition
`q = M L ((ν-α)⁻¹ + (β-ν)⁻¹) < 1` of `eq:supp-exact-graph-contraction`.

The weighted space is `ℝ →ᵇ U × Nn` with `y(t) = e^{νt} g(t)` (`wt`), i.e. the norm
`sup_{t ≥ 0} e^{-νt} |y(t)|`; the operator `lpOp n₀ g (t) = e^{-νt⁺} (𝒯 y)(t⁺)` (`t⁺ = max t 0`).

* `lpMap_continuousOn`: `t ↦ (𝒯y)(t)` is continuous on `[0, ∞)` (group law + continuity of
  primitives);
* `lpMap_norm_le`: `‖(𝒯y)(t)‖ ≤ (M‖n₀‖ + M c_u/β + M c_n/(ν-α) + qK) e^{νt}`;
* `lpOp_contracting`: `lpOp n₀` is a contraction with constant `q`;
* `yStar_eq_lpMap`: the fixed point gives a continuous trajectory of weighted growth solving the
  Lyapunov–Perron integral equations on `[0, ∞)`;
* `eq_yStar_of_fixed`: **uniqueness** — every continuous solution of weighted growth coincides
  with it on `[0, ∞)`;
* `graphMap` (`h(n₀) = u(0)`) and `graphMap_lipschitz`:
  `‖h(n₀) - h(n₀')‖ ≤ M/(1-q) ‖n₀ - n₀'‖` (the graph `u = h(n)` of the forward weighted
  trajectories is Lipschitz);
* `yStar_shift_fixed`, `yStar_shift_eq`, `yStar_mem_graph`: **time translation preserves the
  equations and the weighted class**, so by uniqueness `y_*(s + τ; n₀) = y_*(s; n(τ))` and the
  graph is forward invariant, `u(τ) = h(n(τ))` for `τ ≥ 0` (the paper's invariance step);
* `yStar_hasDerivAt`, `yStar_hasDerivWithinAt`: if `P_u' = A_u P_u`, `P_n' = A_n P_n` (as for
  `P = e^{tA}`), the forward weighted trajectory solves `eq:supp-exact-graph-field`
  (`graphField`);
* `flow_mem_graph`: **invariance under the flow** — every solution on `[0, T]` starting on the
  graph is the forward weighted trajectory (ODE uniqueness, `graphField_lipschitz`) and stays on
  the graph; `flow_mem_graph_of_local`: the localization clause (solutions of a field agreeing
  with the localized one on a set `O`, staying in `O`, stay on the graph);
* `graphHyp_nonvacuous`: the hypotheses are satisfiable.

Not yet formalized: the `C¹–C³` regularity of `h` (fibre contraction with the weights
`ν, 2ν, 3ν`, using the `j = 2, 3` inequalities of `eq:supp-exact-graph-contraction`).
-/

open Filter Set MeasureTheory intervalIntegral Real
open scoped Topology BoundedContinuousFunction

namespace RenewalGeometry
namespace LyapunovPerron

variable {U Nn : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]

/-- Hypotheses of the quantitative graph criterion (the `j = 1` part). -/
structure GraphHyp (Pu : ℝ → U →L[ℝ] U) (Pn : ℝ → Nn →L[ℝ] Nn) (M α β ν L : ℝ)
    (Nu : U × Nn → U) (Nv : U × Nn → Nn) : Prop where
  Pu_cont : Continuous Pu
  Pn_cont : Continuous Pn
  Pu_add : ∀ s t, Pu (s + t) = (Pu s).comp (Pu t)
  Pn_add : ∀ s t, Pn (s + t) = (Pn s).comp (Pn t)
  Pu_zero : Pu 0 = ContinuousLinearMap.id ℝ U
  Pn_zero : Pn 0 = ContinuousLinearMap.id ℝ Nn
  ν_pos : 0 < ν
  α_lt : α < ν
  lt_β : ν < β
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  Pu_bound : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)
  Pn_bound : ∀ s, 0 ≤ s → ‖Pn s‖ ≤ M * exp (α * s)
  Nu_lip : ∀ x x', ‖Nu x - Nu x'‖ ≤ L * ‖x - x'‖
  Nv_lip : ∀ x x', ‖Nv x - Nv x'‖ ≤ L * ‖x - x'‖
  contr : M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) < 1

namespace GraphHyp

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- The contraction constant `q`. -/
noncomputable def q (_ : GraphHyp Pu Pn M α β ν L Nu Nv) : ℝ := M * L * ((ν - α)⁻¹ + (β - ν)⁻¹)

theorem q_nonneg (h : GraphHyp Pu Pn M α β ν L Nu Nv) : 0 ≤ h.q := by
  have h1 : 0 < ν - α := sub_pos.2 h.α_lt
  have h2 : 0 < β - ν := sub_pos.2 h.lt_β
  unfold q
  have := h.M_nonneg; have := h.L_nonneg
  positivity

theorem lip_continuous {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {L : ℝ} {g : X → Y} (hg : ∀ x x', ‖g x - g x'‖ ≤ L * ‖x - x'‖) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x' => hg x' x) ?_
  have : Tendsto (fun x' => L * ‖x' - x‖) (𝓝 x) (𝓝 (L * ‖x - x‖)) :=
    (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
  simpa using this

end GraphHyp

/-! ### Continuity and growth of `𝒯 y` -/

section Operator

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- **Continuity of `t ↦ (𝒯y)(t)` on `[0, ∞)`** for a continuous trajectory of weighted growth. -/
theorem lpMap_continuousOn (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {y : ℝ → U × Nn} (hy : Continuous y) {K : ℝ} (hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ K * exp (ν * r)) :
    ContinuousOn (lpMap Pu Pn bu bn Nu Nv n₀ y) (Ici 0) := by
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nu_lip x x'
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nv_lip x x'
  set F : ℝ → U := fun r => Pu (-r) (bu + Nu (y r)) with hF
  set G : ℝ → Nn := fun r => Pn (-r) (bn + Nv (y r)) with hG
  have hFc : Continuous F :=
    (h.Pu_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgu).comp hy)
  have hGc : Continuous G :=
    (h.Pn_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgv).comp hy)
  have hFint : IntegrableOn F (Ioi 0) := by
    have := backward_integrable (t := 0) h.Pu_cont h.ν_pos h.lt_β h.M_nonneg h.L_nonneg le_rfl
      h.Pu_bound (fun x => bu + Nu x) hgu hy hyK
    simpa [hF] using this
  have hsplit : ∀ t, 0 ≤ t → lpMap Pu Pn bu bn Nu Nv n₀ y t =
      (-(Pu t) ((∫ r in Ioi 0, F r) - ∫ r in (0 : ℝ)..t, F r),
        Pn t n₀ + Pn t (∫ r in (0 : ℝ)..t, G r)) := by
    intro t ht
    have hFt : IntegrableOn F (Ioi t) := hFint.mono_set (Ioi_subset_Ioi ht)
    have e1 : (∫ r in Ioi t, Pu (t - r) (bu + Nu (y r))) = Pu t (∫ r in Ioi t, F r) := by
      rw [← ContinuousLinearMap.integral_comp_comm _ hFt]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hF, ← ContinuousLinearMap.comp_apply, ← h.Pu_add, sub_eq_add_neg]
    have e2 : (∫ r in Ioi t, F r) = (∫ r in Ioi 0, F r) - ∫ r in (0 : ℝ)..t, F r := by
      rw [← intervalIntegral.integral_interval_add_Ioi hFint hFt]; abel
    have e3 : (∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y r))) =
        Pn t (∫ r in (0 : ℝ)..t, G r) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hGc.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [hG, ← ContinuousLinearMap.comp_apply, ← h.Pn_add, sub_eq_add_neg]
    simp only [lpMap, e1, e2, e3]
  have hcont : Continuous fun t => ((-(Pu t) ((∫ r in Ioi 0, F r) - ∫ r in (0 : ℝ)..t, F r),
      Pn t n₀ + Pn t (∫ r in (0 : ℝ)..t, G r)) : U × Nn) := by
    have hpF : Continuous fun t => ∫ r in (0 : ℝ)..t, F r :=
      intervalIntegral.continuous_primitive (fun a b => hFc.intervalIntegrable a b) 0
    have hpG : Continuous fun t => ∫ r in (0 : ℝ)..t, G r :=
      intervalIntegral.continuous_primitive (fun a b => hGc.intervalIntegrable a b) 0
    refine Continuous.prodMk ?_ ?_
    · exact (h.Pu_cont.clm_apply (continuous_const.sub hpF)).neg
    · exact (h.Pn_cont.clm_apply continuous_const).add (h.Pn_cont.clm_apply hpG)
  exact hcont.continuousOn.congr fun t ht => hsplit t ht

end Operator

/-! ### Growth of `𝒯 y` -/

section Growth

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

theorem norm_prod_le_add' (a : U) (b : Nn) : ‖(a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

/-- **Weighted growth of `𝒯 y`**: for `‖y(r)‖ ≤ K e^{νr}`,
`‖(𝒯y)(t)‖ ≤ (M‖n₀‖ + M‖b_u + N_u 0‖/β + M‖b_n + N_n 0‖/(ν-α) + qK) e^{νt}`. -/
theorem lpMap_norm_le (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {y : ℝ → U × Nn} (hy : Continuous y) {K : ℝ} (hK0 : 0 ≤ K)
    (hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ K * exp (ν * r)) {t : ℝ} (ht : 0 ≤ t) :
    ‖lpMap Pu Pn bu bn Nu Nv n₀ y t‖ ≤
      (M * ‖n₀‖ + M * ‖bu + Nu 0‖ / β + M * ‖bn + Nv 0‖ / (ν - α) + h.q * K) * exp (ν * t) := by
  have hβ : 0 < β := h.ν_pos.trans h.lt_β
  have hc1 : 0 < ν - α := sub_pos.2 h.α_lt
  have hexp1 : 1 ≤ exp (ν * t) := one_le_exp (mul_nonneg h.ν_pos.le ht)
  have h1 := lpMap_sub_le (y₁ := y) (y₂ := fun _ => (0 : U × Nn)) (δ := K) (K := K) h.Pu_cont
    h.Pn_cont h.ν_pos h.α_lt h.lt_β h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound bu bn Nu Nv
    h.Nu_lip h.Nv_lip n₀ hy continuous_const hyK (fun r _ => by simp; positivity)
    (fun r hr => by simpa using hyK r hr) ht
  set cu := ‖bu + Nu 0‖
  set cn := ‖bn + Nv 0‖
  have hB : ‖∫ r in Ioi t, Pu (t - r) (bu + Nu ((fun _ => (0 : U × Nn)) r))‖ ≤ M * cu / β := by
    have hval := backward_kernel_eq (M := M) (K := cu) (ν := 0) (t := t) hβ
    have hval' : M * cu * exp (0 * t) / (β - 0) = M * cu / β := by simp
    calc _ ≤ ∫ r in Ioi t, M * exp (-β * (r - t)) * (cu * exp (0 * r)) := by
          refine norm_integral_le_of_norm_le (backward_kernel_integrable hβ) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
          have hP : ‖Pu (t - r)‖ ≤ M * exp (-β * (r - t)) := by
            have := h.Pu_bound (r - t) (by linarith [hr.out])
            rwa [show -(r - t) = t - r by ring] at this
          rw [zero_mul, exp_zero, mul_one]
          calc ‖Pu (t - r) (bu + Nu 0)‖ ≤ ‖Pu (t - r)‖ * cu := (Pu (t - r)).le_opNorm _
            _ ≤ M * exp (-β * (r - t)) * cu := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = M * cu / β := by rw [hval, hval']
  have hF : ‖∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv ((fun _ => (0 : U × Nn)) r))‖ ≤
      M * cn * exp (ν * t) / (ν - α) := by
    refine (norm_integral_le_of_norm_le ht (f := fun r => Pn (t - r) (bn + Nv 0))
      (g := fun r => M * exp (α * (t - r)) * (cn * exp (ν * r))) ?_ ?_).trans
      (forward_kernel_le h.M_nonneg (norm_nonneg _) h.α_lt ht)
    · refine Eventually.of_forall fun r hr => ?_
      have hP : ‖Pn (t - r)‖ ≤ M * exp (α * (t - r)) := h.Pn_bound (t - r) (by linarith [hr.2])
      have he : 1 ≤ exp (ν * r) := one_le_exp (mul_nonneg h.ν_pos.le hr.1.le)
      calc ‖Pn (t - r) (bn + Nv 0)‖ ≤ ‖Pn (t - r)‖ * cn := (Pn (t - r)).le_opNorm _
        _ ≤ M * exp (α * (t - r)) * cn := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
        _ ≤ M * exp (α * (t - r)) * (cn * exp (ν * r)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by have := h.M_nonneg; positivity)
            nlinarith [norm_nonneg (bn + Nv 0)]
    · have : Continuous fun r : ℝ => M * exp (α * (t - r)) * (cn * exp (ν * r)) := by fun_prop
      exact this.intervalIntegrable _ _
  have hN : ‖Pn t n₀‖ ≤ M * ‖n₀‖ * exp (ν * t) := by
    calc ‖Pn t n₀‖ ≤ ‖Pn t‖ * ‖n₀‖ := (Pn t).le_opNorm _
      _ ≤ M * exp (α * t) * ‖n₀‖ := mul_le_mul_of_nonneg_right (h.Pn_bound t ht) (norm_nonneg _)
      _ ≤ M * exp (ν * t) * ‖n₀‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ h.M_nonneg
          exact exp_le_exp.2 (mul_le_mul_of_nonneg_right h.α_lt.le ht)
      _ = M * ‖n₀‖ * exp (ν * t) := by ring
  have h0 : ‖lpMap Pu Pn bu bn Nu Nv n₀ (fun _ => (0 : U × Nn)) t‖ ≤
      (M * ‖n₀‖ + M * cu / β + M * cn / (ν - α)) * exp (ν * t) := by
    unfold lpMap
    refine (norm_prod_le_add' _ _).trans ?_
    rw [norm_neg]
    have hMcu : 0 ≤ M * cu / β := by have := h.M_nonneg; positivity
    calc _ ≤ M * cu / β + (‖Pn t n₀‖ + M * cn * exp (ν * t) / (ν - α)) :=
          add_le_add hB ((norm_add_le _ _).trans (add_le_add le_rfl hF))
      _ ≤ M * cu / β * exp (ν * t) + (M * ‖n₀‖ * exp (ν * t) + M * cn * exp (ν * t) / (ν - α)) :=
          add_le_add (le_mul_of_one_le_right hMcu hexp1) (add_le_add hN le_rfl)
      _ = _ := by ring
  have hq : h.q = M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) := rfl
  calc ‖lpMap Pu Pn bu bn Nu Nv n₀ y t‖
      ≤ ‖lpMap Pu Pn bu bn Nu Nv n₀ (fun _ => (0 : U × Nn)) t‖ +
        ‖lpMap Pu Pn bu bn Nu Nv n₀ y t - lpMap Pu Pn bu bn Nu Nv n₀ (fun _ => 0) t‖ :=
        norm_le_insert' _ _
    _ ≤ _ := add_le_add h0 h1
    _ = _ := by rw [hq]; ring

end Growth

/-! ### The operator on the weighted space and its fixed point -/

section FixedPoint

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- The weighted trajectory `y(r) = e^{νr} g(r)`. -/
noncomputable def wt (ν : ℝ) (g : ℝ →ᵇ (U × Nn)) : ℝ → U × Nn := fun r => exp (ν * r) • g r

theorem wt_continuous (ν : ℝ) (g : ℝ →ᵇ (U × Nn)) : Continuous (wt ν g) :=
  ((continuous_const.mul continuous_id).rexp).smul g.continuous

theorem norm_wt_le (ν : ℝ) (g : ℝ →ᵇ (U × Nn)) (r : ℝ) : ‖wt ν g r‖ ≤ ‖g‖ * exp (ν * r) := by
  rw [wt, norm_smul, Real.norm_of_nonneg (exp_pos _).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm r) (exp_pos _).le

theorem norm_wt_sub_le (ν : ℝ) (g₁ g₂ : ℝ →ᵇ (U × Nn)) (r : ℝ) :
    ‖wt ν g₁ r - wt ν g₂ r‖ ≤ dist g₁ g₂ * exp (ν * r) := by
  rw [wt, wt, ← smul_sub, norm_smul, Real.norm_of_nonneg (exp_pos _).le, mul_comm, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_right (g₁.dist_coe_le_dist r) (exp_pos _).le

/-- The constant of the growth bound. -/
noncomputable def growthConst (M α β ν : ℝ) (Nu : U × Nn → U) (Nv : U × Nn → Nn) (bu : U)
    (bn : Nn) (n₀ : Nn) : ℝ :=
  M * ‖n₀‖ + M * ‖bu + Nu 0‖ / β + M * ‖bn + Nv 0‖ / (ν - α)

/-- The Lyapunov–Perron operator on the weighted space:
`(lpOp n₀ g)(t) = e^{-νt⁺} (𝒯 (e^{ν·} g))(t⁺)`, `t⁺ = max t 0`. -/
noncomputable def lpOp (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (g : ℝ →ᵇ (U × Nn)) : ℝ →ᵇ (U × Nn) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => exp (-ν * max t 0) • lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g) (max t 0))
    (by
      refine ((continuous_const.mul (continuous_id.max continuous_const)).rexp).smul ?_
      exact (lpMap_continuousOn h bu bn n₀ (wt_continuous ν g)
        (fun r _ => norm_wt_le ν g r)).comp_continuous (continuous_id.max continuous_const)
        (fun t => le_max_right t 0))
    (growthConst M α β ν Nu Nv bu bn n₀ + h.q * ‖g‖)
    (by
      intro t
      have ht : 0 ≤ max t 0 := le_max_right t 0
      have hb := lpMap_norm_le h bu bn n₀ (wt_continuous ν g) (norm_nonneg g)
        (fun r _ => norm_wt_le ν g r) ht
      rw [norm_smul, Real.norm_of_nonneg (exp_pos _).le]
      calc exp (-ν * max t 0) * ‖lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g) (max t 0)‖
          ≤ exp (-ν * max t 0) * ((growthConst M α β ν Nu Nv bu bn n₀ + h.q * ‖g‖) *
              exp (ν * max t 0)) :=
            mul_le_mul_of_nonneg_left hb (exp_pos _).le
        _ = growthConst M α β ν Nu Nv bu bn n₀ + h.q * ‖g‖ := by
            rw [mul_left_comm, ← exp_add, show -ν * max t 0 + ν * max t 0 = 0 by ring, exp_zero,
              mul_one])

theorem lpOp_apply (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (g : ℝ →ᵇ (U × Nn)) (t : ℝ) :
    lpOp h bu bn n₀ g t = exp (-ν * max t 0) • lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g) (max t 0) :=
  rfl

/-- **`lpOp n₀` is a contraction with constant `q`** (the `j = 1` inequality of
`eq:supp-exact-graph-contraction`). -/
theorem lpOp_contracting (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    ContractingWith ⟨h.q, h.q_nonneg⟩ (lpOp h bu bn n₀) := by
  refine ⟨by exact_mod_cast h.contr, LipschitzWith.of_dist_le_mul fun g₁ g₂ => ?_⟩
  refine (BoundedContinuousFunction.dist_le (by have := h.q_nonneg; positivity)).2 fun t => ?_
  have ht : 0 ≤ max t 0 := le_max_right t 0
  rw [lpOp_apply, lpOp_apply, dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (exp_pos _).le]
  have hs := lpMap_sub_le (K := max ‖g₁‖ ‖g₂‖) (δ := dist g₁ g₂) h.Pu_cont h.Pn_cont h.ν_pos
    h.α_lt h.lt_β h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound bu bn Nu Nv h.Nu_lip h.Nv_lip n₀
    (wt_continuous ν g₁) (wt_continuous ν g₂)
    (fun r _ => (norm_wt_le ν g₁ r).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le))
    (fun r _ => (norm_wt_le ν g₂ r).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le))
    (fun r _ => norm_wt_sub_le ν g₁ g₂ r) ht
  calc exp (-ν * max t 0) * ‖lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g₁) (max t 0) -
        lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g₂) (max t 0)‖
      ≤ exp (-ν * max t 0) * (M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) * dist g₁ g₂ *
          exp (ν * max t 0)) := mul_le_mul_of_nonneg_left hs (exp_pos _).le
    _ = h.q * dist g₁ g₂ := by
        unfold GraphHyp.q
        rw [mul_left_comm, ← exp_add, show -ν * max t 0 + ν * max t 0 = 0 by ring, exp_zero,
          mul_one]

/-- The fixed point `g_*` in the weighted space. -/
noncomputable def gStar (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    ℝ →ᵇ (U × Nn) :=
  ContractingWith.fixedPoint (lpOp h bu bn n₀) (lpOp_contracting h bu bn n₀)

/-- The forward weighted trajectory `y_*(t) = e^{νt} g_*(t)` with `n(0) = n₀`. -/
noncomputable def yStar (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    ℝ → U × Nn :=
  wt ν (gStar h bu bn n₀)

/-- **The fixed point solves the Lyapunov–Perron integral equations on `[0, ∞)`.** -/
theorem yStar_eq_lpMap (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {t : ℝ} (ht : 0 ≤ t) :
    yStar h bu bn n₀ t = lpMap Pu Pn bu bn Nu Nv n₀ (yStar h bu bn n₀) t := by
  have hfix := (lpOp_contracting h bu bn n₀).fixedPoint_isFixedPt (f := lpOp h bu bn n₀)
  have := congrArg (fun g : ℝ →ᵇ (U × Nn) => g t) hfix
  simp only [lpOp_apply, max_eq_left ht] at this
  rw [← gStar] at this
  show wt ν (gStar h bu bn n₀) t = lpMap Pu Pn bu bn Nu Nv n₀ (wt ν (gStar h bu bn n₀)) t
  have e : wt ν (gStar h bu bn n₀) t = exp (ν * t) • (gStar h bu bn n₀) t := rfl
  rw [e, ← this, smul_smul, ← exp_add, show ν * t + -ν * t = 0 by ring, exp_zero, one_smul]

theorem yStar_continuous (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    Continuous (yStar h bu bn n₀) := wt_continuous ν _

theorem norm_yStar_le (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (r : ℝ) : ‖yStar h bu bn n₀ r‖ ≤ ‖gStar h bu bn n₀‖ * exp (ν * r) := norm_wt_le ν _ r

/-- **Uniqueness of the forward weighted trajectory**: every continuous solution of the
integral equations on `[0, ∞)` of weighted growth `‖y(r)‖ ≤ K e^{νr}` coincides with `y_*`. -/
theorem eq_yStar_of_fixed (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {y : ℝ → U × Nn} (hy : Continuous y) {K : ℝ} (hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ K * exp (ν * r))
    (hfix : ∀ t, 0 ≤ t → y t = lpMap Pu Pn bu bn Nu Nv n₀ y t) {t : ℝ} (ht : 0 ≤ t) :
    y t = yStar h bu bn n₀ t := by
  set ys := yStar h bu bn n₀
  set G := ‖gStar h bu bn n₀‖
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hyK 0 le_rfl); simpa using this
  set δ₀ := K + G
  have hq0 := h.q_nonneg
  have hys : ∀ r, 0 ≤ r → ys r = lpMap Pu Pn bu bn Nu Nv n₀ ys r :=
    fun r hr => yStar_eq_lpMap h bu bn n₀ hr
  have hiter : ∀ k : ℕ, ∀ r, 0 ≤ r → ‖y r - ys r‖ ≤ h.q ^ k * δ₀ * exp (ν * r) := by
    intro k
    induction k with
    | zero =>
      intro r hr
      simp only [pow_zero, one_mul]
      calc ‖y r - ys r‖ ≤ ‖y r‖ + ‖ys r‖ := norm_sub_le _ _
        _ ≤ K * exp (ν * r) + G * exp (ν * r) := add_le_add (hyK r hr) (norm_yStar_le h bu bn n₀ r)
        _ = δ₀ * exp (ν * r) := by ring
    | succ k ih =>
      intro r hr
      rw [hfix r hr, hys r hr]
      have hs := lpMap_sub_le (K := max K G) (δ := h.q ^ k * δ₀) h.Pu_cont h.Pn_cont h.ν_pos
        h.α_lt h.lt_β h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound bu bn Nu Nv h.Nu_lip
        h.Nv_lip n₀ hy (yStar_continuous h bu bn n₀)
        (fun r hr => (hyK r hr).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le))
        (fun r _ => (norm_yStar_le h bu bn n₀ r).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le))
        ih hr
      calc _ ≤ M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) * (h.q ^ k * δ₀) * exp (ν * r) := hs
        _ = h.q ^ (k + 1) * δ₀ * exp (ν * r) := by unfold GraphHyp.q; ring
  have hlim : Tendsto (fun k : ℕ => h.q ^ k * δ₀ * exp (ν * t)) atTop (𝓝 (0 * δ₀ * exp (ν * t))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 h.contr).mul_const _).mul_const _
  rw [zero_mul, zero_mul] at hlim
  have hle : ‖y t - ys t‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun k => hiter k t ht)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- The graph `h(n₀) = u(0)` of the forward weighted trajectories. -/
noncomputable def graphMap (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) : U :=
  (yStar h bu bn n₀ 0).1

theorem yStar_zero_snd (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    (yStar h bu bn n₀ 0).2 = n₀ := by
  rw [yStar_eq_lpMap h bu bn n₀ le_rfl]
  simp [lpMap, h.Pn_zero]

/-- **The graph is Lipschitz**: `‖h(n₀) - h(n₀')‖ ≤ M/(1-q) ‖n₀ - n₀'‖`. -/
theorem graphMap_lipschitz (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ n₀' : Nn) :
    ‖graphMap h bu bn n₀ - graphMap h bu bn n₀'‖ ≤ M / (1 - h.q) * ‖n₀ - n₀'‖ := by
  have hc := lpOp_contracting h bu bn n₀
  have hd := hc.dist_fixedPoint_fixedPoint_of_dist_le' (lpOp h bu bn n₀')
    hc.fixedPoint_isFixedPt (lpOp_contracting h bu bn n₀').fixedPoint_isFixedPt
    (C := M * ‖n₀ - n₀'‖) (fun g => by
      refine (BoundedContinuousFunction.dist_le (by have := h.M_nonneg; positivity)).2
        fun t => ?_
      have ht : 0 ≤ max t 0 := le_max_right t 0
      rw [lpOp_apply, lpOp_apply, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (exp_pos _).le]
      have hdiff : lpMap Pu Pn bu bn Nu Nv n₀ (wt ν g) (max t 0) -
          lpMap Pu Pn bu bn Nu Nv n₀' (wt ν g) (max t 0) = (0, Pn (max t 0) (n₀ - n₀')) := by
        simp [lpMap, map_sub]
      rw [hdiff]
      have hP : ‖Pn (max t 0) (n₀ - n₀')‖ ≤ M * exp (α * max t 0) * ‖n₀ - n₀'‖ :=
        ((Pn _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h.Pn_bound _ ht) (norm_nonneg _))
      have hnorm : ‖((0 : U), Pn (max t 0) (n₀ - n₀'))‖ = ‖Pn (max t 0) (n₀ - n₀')‖ := by
        rw [Prod.norm_def]; simp
      rw [hnorm]
      calc exp (-ν * max t 0) * ‖Pn (max t 0) (n₀ - n₀')‖
          ≤ exp (-ν * max t 0) * (M * exp (α * max t 0) * ‖n₀ - n₀'‖) :=
            mul_le_mul_of_nonneg_left hP (exp_pos _).le
        _ = M * exp ((α - ν) * max t 0) * ‖n₀ - n₀'‖ := by
            rw [show (α - ν) * max t 0 = -ν * max t 0 + α * max t 0 by ring, exp_add]; ring
        _ ≤ M * 1 * ‖n₀ - n₀'‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ h.M_nonneg)
              (norm_nonneg _)
            rw [exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg (by linarith [h.α_lt]) ht
        _ = M * ‖n₀ - n₀'‖ := by ring)
  have hq1 : (0 : ℝ) < 1 - h.q := sub_pos.2 h.contr
  have h0 : ‖graphMap h bu bn n₀ - graphMap h bu bn n₀'‖ ≤
      dist (gStar h bu bn n₀) (gStar h bu bn n₀') := by
    unfold graphMap yStar wt
    simp only [mul_zero, exp_zero, one_smul]
    rw [← Prod.fst_sub]
    refine (norm_fst_le _).trans ?_
    rw [← dist_eq_norm]
    exact BoundedContinuousFunction.dist_coe_le_dist 0
  refine h0.trans ?_
  unfold gStar
  calc _ ≤ M * ‖n₀ - n₀'‖ / (1 - h.q) := hd
    _ = M / (1 - h.q) * ‖n₀ - n₀'‖ := by ring

end FixedPoint

/-! ### Time-translation invariance of the graph -/

section Invariance

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

theorem integral_Ioi_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a τ : ℝ) :
    ∫ r in Ioi a, F (r + τ) = ∫ r in Ioi (a + τ), F r := by
  have h := (measurePreserving_add_right volume τ).setIntegral_preimage_emb
    (measurableEmbedding_addRight τ) F (Ioi (a + τ))
  have hpre : (fun x => x + τ) ⁻¹' Ioi (a + τ) = Ioi a := by
    ext x; simp
  rw [hpre] at h
  exact h

/-- **Time translation**: the shifted forward weighted trajectory `s ↦ y_*(s + τ)` solves the
integral equations with initial value `n(τ)`. -/
theorem yStar_shift_fixed (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {τ : ℝ} (hτ : 0 ≤ τ) {s : ℝ} (hs : 0 ≤ s) :
    yStar h bu bn n₀ (s + τ) =
      lpMap Pu Pn bu bn Nu Nv (yStar h bu bn n₀ τ).2 (fun r => yStar h bu bn n₀ (r + τ)) s := by
  set ys := yStar h bu bn n₀ with hys
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nv_lip x x'
  have hGc : Continuous fun r => bn + Nv (ys r) :=
    (GraphHyp.lip_continuous hgv).comp (yStar_continuous h bu bn n₀)
  have hint : ∀ c : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun r => Pn (c - r) (bn + Nv (ys r)))
      volume a b := fun c a b =>
    ((h.Pn_cont.comp (continuous_const.sub continuous_id)).clm_apply hGc).intervalIntegrable a b
  have hτfix : ys τ = lpMap Pu Pn bu bn Nu Nv n₀ ys τ := yStar_eq_lpMap h bu bn n₀ hτ
  have hsfix : ys (s + τ) = lpMap Pu Pn bu bn Nu Nv n₀ ys (s + τ) :=
    yStar_eq_lpMap h bu bn n₀ (add_nonneg hs hτ)
  rw [hsfix]
  refine Prod.ext ?_ ?_
  · -- backward component: translation of the improper integral
    simp only [lpMap]
    congr 1
    rw [← integral_Ioi_comp_add (fun r => Pu (s + τ - r) (bu + Nu (ys r))) s τ]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [show s + τ - (r + τ) = s - r by ring]
  · -- forward component: split at `τ` and translate
    have hn : (ys τ).2 = Pn τ n₀ + ∫ r in (0 : ℝ)..τ, Pn (τ - r) (bn + Nv (ys r)) := by
      rw [hτfix]; rfl
    simp only [lpMap]
    rw [hn, ← intervalIntegral.integral_add_adjacent_intervals (hint (s + τ) 0 τ)
      (hint (s + τ) τ (s + τ))]
    have e1 : Pn (s + τ) n₀ = Pn s (Pn τ n₀) := by rw [h.Pn_add]; rfl
    have e2 : (∫ r in (0 : ℝ)..τ, Pn (s + τ - r) (bn + Nv (ys r))) =
        Pn s (∫ r in (0 : ℝ)..τ, Pn (τ - r) (bn + Nv (ys r))) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint τ 0 τ)]
      refine intervalIntegral.integral_congr fun r _ => ?_
      show Pn (s + τ - r) (bn + Nv (ys r)) = Pn s (Pn (τ - r) (bn + Nv (ys r)))
      rw [show s + τ - r = s + (τ - r) by ring, h.Pn_add]; rfl
    have e3 : (∫ r in τ..(s + τ), Pn (s + τ - r) (bn + Nv (ys r))) =
        ∫ r in (0 : ℝ)..s, Pn (s - r) (bn + Nv (ys (r + τ))) := by
      have := intervalIntegral.integral_comp_add_right
        (fun r => Pn (s + τ - r) (bn + Nv (ys r))) (a := 0) (b := s) τ
      rw [zero_add] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun r _ => ?_
      show Pn (s + τ - (r + τ)) (bn + Nv (ys (r + τ))) = Pn (s - r) (bn + Nv (ys (r + τ)))
      rw [show s + τ - (r + τ) = s - r by ring]
    rw [e1, e2, e3, map_add]
    abel

theorem norm_yStar_shift_le (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (τ r : ℝ) :
    ‖yStar h bu bn n₀ (r + τ)‖ ≤ (‖gStar h bu bn n₀‖ * exp (ν * τ)) * exp (ν * r) := by
  refine (norm_yStar_le h bu bn n₀ (r + τ)).trans (le_of_eq ?_)
  rw [mul_assoc, ← exp_add]; ring_nf

/-- **Forward invariance of the graph**: along the forward weighted trajectory through
`(h(n₀), n₀)`, every later state lies on the graph, `u(τ) = h(n(τ))` for `τ ≥ 0`; indeed the
whole shifted trajectory is the forward weighted trajectory of `n(τ)`. -/
theorem yStar_shift_eq (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {τ : ℝ} (hτ : 0 ≤ τ) {s : ℝ} (hs : 0 ≤ s) :
    yStar h bu bn n₀ (s + τ) = yStar h bu bn (yStar h bu bn n₀ τ).2 s :=
  eq_yStar_of_fixed h bu bn _
    ((yStar_continuous h bu bn n₀).comp (continuous_id.add continuous_const))
    (fun r _ => norm_yStar_shift_le h bu bn n₀ τ r)
    (fun _ ht => yStar_shift_fixed h bu bn n₀ hτ ht) hs

/-- **Graph invariance** `u(τ) = h(n(τ))`. -/
theorem yStar_mem_graph (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (yStar h bu bn n₀ τ).1 = graphMap h bu bn (yStar h bu bn n₀ τ).2 := by
  have := yStar_shift_eq h bu bn n₀ hτ le_rfl
  rw [zero_add] at this
  unfold graphMap
  rw [← this]

end Invariance

/-! ### The forward weighted trajectories solve the differential equation -/

section ODE

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- The split form of `𝒯 y` used for continuity and differentiation:
`(𝒯y)(t) = (-P_u(t)(∫_{(0,∞)} F - ∫_0^t F), P_n(t) n₀ + P_n(t) ∫_0^t G)` with
`F(r) = P_u(-r)(b_u + N_u(y r))`, `G(r) = P_n(-r)(b_n + N_n(y r))`. -/
theorem lpMap_eq_split (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    {y : ℝ → U × Nn} (hy : Continuous y) {K : ℝ} (hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ K * exp (ν * r))
    {t : ℝ} (ht : 0 ≤ t) :
    lpMap Pu Pn bu bn Nu Nv n₀ y t =
      (-(Pu t) ((∫ r in Ioi 0, Pu (-r) (bu + Nu (y r))) -
          ∫ r in (0 : ℝ)..t, Pu (-r) (bu + Nu (y r))),
        Pn t n₀ + Pn t (∫ r in (0 : ℝ)..t, Pn (-r) (bn + Nv (y r)))) := by
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nu_lip x x'
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nv_lip x x'
  have hGc : Continuous fun r => Pn (-r) (bn + Nv (y r)) :=
    (h.Pn_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgv).comp hy)
  have hFint : IntegrableOn (fun r => Pu (-r) (bu + Nu (y r))) (Ioi 0) := by
    have := backward_integrable (t := 0) h.Pu_cont h.ν_pos h.lt_β h.M_nonneg h.L_nonneg le_rfl
      h.Pu_bound (fun x => bu + Nu x) hgu hy hyK
    simpa using this
  have hFt : IntegrableOn (fun r => Pu (-r) (bu + Nu (y r))) (Ioi t) :=
    hFint.mono_set (Ioi_subset_Ioi ht)
  have e1 : (∫ r in Ioi t, Pu (t - r) (bu + Nu (y r))) =
      Pu t (∫ r in Ioi t, Pu (-r) (bu + Nu (y r))) := by
    rw [← ContinuousLinearMap.integral_comp_comm _ hFt]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    show Pu (t - r) (bu + Nu (y r)) = Pu t (Pu (-r) (bu + Nu (y r)))
    rw [sub_eq_add_neg, h.Pu_add]; rfl
  have e2 : (∫ r in Ioi t, Pu (-r) (bu + Nu (y r))) =
      (∫ r in Ioi 0, Pu (-r) (bu + Nu (y r))) - ∫ r in (0 : ℝ)..t, Pu (-r) (bu + Nu (y r)) := by
    rw [← intervalIntegral.integral_interval_add_Ioi hFint hFt]; abel
  have e3 : (∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y r))) =
      Pn t (∫ r in (0 : ℝ)..t, Pn (-r) (bn + Nv (y r))) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hGc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    show Pn (t - r) (bn + Nv (y r)) = Pn t (Pn (-r) (bn + Nv (y r)))
    rw [sub_eq_add_neg, h.Pn_add]; rfl
  simp only [lpMap, e1, e2, e3]

/-- **The forward weighted trajectory solves `eq:supp-exact-graph-field`.** If the propagators
have generators, `P_u'(t) = A_u P_u(t)`, `P_n'(t) = A_n P_n(t)` (as for `P = e^{tA}`), then for
`t > 0`: `u' = A_u u + b_u + N_u(u, n)`, `n' = A_n n + b_n + N_n(u, n)` along `y_*`. -/
theorem yStar_hasDerivAt (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) (hdu : ∀ t, HasDerivAt Pu (Au * Pu t) t)
    (hdn : ∀ t, HasDerivAt Pn (An * Pn t) t) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (yStar h bu bn n₀)
      (Au (yStar h bu bn n₀ t).1 + (bu + Nu (yStar h bu bn n₀ t)),
        An (yStar h bu bn n₀ t).2 + (bn + Nv (yStar h bu bn n₀ t))) t := by
  set y := yStar h bu bn n₀ with hydef
  have hy : Continuous y := yStar_continuous h bu bn n₀
  have hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ ‖gStar h bu bn n₀‖ * exp (ν * r) :=
    fun r _ => norm_yStar_le h bu bn n₀ r
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nu_lip x x'
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nv_lip x x'
  set F : ℝ → U := fun r => Pu (-r) (bu + Nu (y r)) with hF
  set G : ℝ → Nn := fun r => Pn (-r) (bn + Nv (y r)) with hG
  have hFc : Continuous F :=
    (h.Pu_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgu).comp hy)
  have hGc : Continuous G :=
    (h.Pn_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgv).comp hy)
  set c := ∫ r in Ioi 0, F r
  set Φ : ℝ → U × Nn := fun s => (-(Pu s) (c - ∫ r in (0 : ℝ)..s, F r),
      Pn s n₀ + Pn s (∫ r in (0 : ℝ)..s, G r)) with hΦ
  have hyΦ : y =ᶠ[𝓝 t] Φ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have h1 : y s = lpMap Pu Pn bu bn Nu Nv n₀ y s := yStar_eq_lpMap h bu bn n₀ hs0
    rw [h1, lpMap_eq_split h bu bn n₀ hy hyK hs0]
  have hPF : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, F r) (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable _ _)
      (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
  have hPG : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, G r) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
  have hdΦ1 := ((hdu t).clm_apply ((hasDerivAt_const t c).sub hPF)).neg
  have hdΦ2 := ((hdn t).clm_apply (hasDerivAt_const t n₀)).add ((hdn t).clm_apply hPG)
  have hdΦ := hdΦ1.prodMk hdΦ2
  have hΦt : y t = Φ t := hyΦ.eq_of_nhds
  have hid_u : Pu t (F t) = bu + Nu (y t) := by
    show Pu t (Pu (-t) (bu + Nu (y t))) = bu + Nu (y t)
    rw [← ContinuousLinearMap.comp_apply, ← h.Pu_add, add_neg_cancel, h.Pu_zero]; rfl
  have hid_n : Pn t (G t) = bn + Nv (y t) := by
    show Pn t (Pn (-t) (bn + Nv (y t))) = bn + Nv (y t)
    rw [← ContinuousLinearMap.comp_apply, ← h.Pn_add, add_neg_cancel, h.Pn_zero]; rfl
  have h1 : (y t).1 = -(Pu t) (c - ∫ r in (0 : ℝ)..t, F r) := by rw [hΦt]
  have h2 : (y t).2 = Pn t n₀ + Pn t (∫ r in (0 : ℝ)..t, G r) := by rw [hΦt]
  refine (hdΦ.congr_of_eventuallyEq hyΦ).congr_deriv ?_
  rw [h1, h2]
  refine Prod.ext ?_ ?_
  · simp only [ContinuousLinearMap.mul_apply, Pi.sub_apply, map_neg, map_sub, zero_sub, hid_u]
    abel
  · simp only [ContinuousLinearMap.mul_apply, map_zero, add_zero, map_add, hid_n]
    abel

end ODE

/-! ### Invariance of the graph under the flow, and localization -/

section Flow

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- The vector field of `eq:supp-exact-graph-field`. -/
def graphField (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) (bu : U) (bn : Nn) (Nu : U × Nn → U)
    (Nv : U × Nn → Nn) (x : U × Nn) : U × Nn :=
  (Au x.1 + (bu + Nu x), An x.2 + (bn + Nv x))

/-- One-sided derivative of the forward weighted trajectory at every `t ≥ 0`. -/
theorem yStar_hasDerivWithinAt (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn)
    (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) (hdu : ∀ t, HasDerivAt Pu (Au * Pu t) t)
    (hdn : ∀ t, HasDerivAt Pn (An * Pn t) t) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (yStar h bu bn n₀)
      (graphField Au An bu bn Nu Nv (yStar h bu bn n₀ t)) (Ici t) t := by
  set y := yStar h bu bn n₀ with hydef
  have hy : Continuous y := yStar_continuous h bu bn n₀
  have hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ ‖gStar h bu bn n₀‖ * exp (ν * r) :=
    fun r _ => norm_yStar_le h bu bn n₀ r
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nu_lip x x'
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nv_lip x x'
  set F : ℝ → U := fun r => Pu (-r) (bu + Nu (y r)) with hF
  set G : ℝ → Nn := fun r => Pn (-r) (bn + Nv (y r)) with hG
  have hFc : Continuous F :=
    (h.Pu_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgu).comp hy)
  have hGc : Continuous G :=
    (h.Pn_cont.comp continuous_neg).clm_apply ((GraphHyp.lip_continuous hgv).comp hy)
  set c := ∫ r in Ioi 0, F r
  set Φ : ℝ → U × Nn := fun s => (-(Pu s) (c - ∫ r in (0 : ℝ)..s, F r),
      Pn s n₀ + Pn s (∫ r in (0 : ℝ)..s, G r)) with hΦ
  have hyΦ : EqOn y Φ (Ici t) := by
    intro s hs
    have hs0 : 0 ≤ s := ht.trans hs
    have h1 : y s = lpMap Pu Pn bu bn Nu Nv n₀ y s := yStar_eq_lpMap h bu bn n₀ hs0
    rw [h1, lpMap_eq_split h bu bn n₀ hy hyK hs0]
  have hPF : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, F r) (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable _ _)
      (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
  have hPG : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, G r) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
  have hdΦ1 := ((hdu t).clm_apply ((hasDerivAt_const t c).sub hPF)).neg
  have hdΦ2 := ((hdn t).clm_apply (hasDerivAt_const t n₀)).add ((hdn t).clm_apply hPG)
  have hdΦ := hdΦ1.prodMk hdΦ2
  have hΦt : y t = Φ t := hyΦ (Set.mem_Ici.2 le_rfl)
  have hid_u : Pu t (F t) = bu + Nu (y t) := by
    show Pu t (Pu (-t) (bu + Nu (y t))) = bu + Nu (y t)
    rw [← ContinuousLinearMap.comp_apply, ← h.Pu_add, add_neg_cancel, h.Pu_zero]; rfl
  have hid_n : Pn t (G t) = bn + Nv (y t) := by
    show Pn t (Pn (-t) (bn + Nv (y t))) = bn + Nv (y t)
    rw [← ContinuousLinearMap.comp_apply, ← h.Pn_add, add_neg_cancel, h.Pn_zero]; rfl
  have h1 : (y t).1 = -(Pu t) (c - ∫ r in (0 : ℝ)..t, F r) := by rw [hΦt]
  have h2 : (y t).2 = Pn t n₀ + Pn t (∫ r in (0 : ℝ)..t, G r) := by rw [hΦt]
  refine (hdΦ.hasDerivWithinAt.congr hyΦ hΦt).congr_deriv ?_
  unfold graphField
  rw [h1, h2]
  refine Prod.ext ?_ ?_
  · simp only [ContinuousLinearMap.mul_apply, Pi.sub_apply, map_neg, map_sub, zero_sub, hid_u]
    abel
  · simp only [ContinuousLinearMap.mul_apply, map_zero, add_zero, map_add, hid_n]
    abel

theorem graphField_lipschitz (h : GraphHyp Pu Pn M α β ν L Nu Nv) (Au : U →L[ℝ] U)
    (An : Nn →L[ℝ] Nn) (bu : U) (bn : Nn) :
    LipschitzWith ⟨max ‖Au‖ ‖An‖ + L, by have := h.L_nonneg; positivity⟩
      (graphField Au An bu bn Nu Nv) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  simp only [NNReal.coe_mk, dist_eq_norm, graphField]
  have hx1 : ‖x.1 - x'.1‖ ≤ ‖x - x'‖ := by rw [← Prod.fst_sub]; exact norm_fst_le _
  have hx2 : ‖x.2 - x'.2‖ ≤ ‖x - x'‖ := by rw [← Prod.snd_sub]; exact norm_snd_le _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖(Au x.1 + (bu + Nu x)) - (Au x'.1 + (bu + Nu x'))‖
        = ‖Au (x.1 - x'.1) + (Nu x - Nu x')‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖Au‖ * ‖x.1 - x'.1‖ + L * ‖x - x'‖ :=
          (norm_add_le _ _).trans (add_le_add (Au.le_opNorm _) (h.Nu_lip x x'))
      _ ≤ (max ‖Au‖ ‖An‖ + L) * ‖x - x'‖ := by
          have := mul_le_mul (le_max_left ‖Au‖ ‖An‖) hx1 (norm_nonneg _)
            ((norm_nonneg _).trans (le_max_left _ _))
          nlinarith
  · calc ‖(An x.2 + (bn + Nv x)) - (An x'.2 + (bn + Nv x'))‖
        = ‖An (x.2 - x'.2) + (Nv x - Nv x')‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖An‖ * ‖x.2 - x'.2‖ + L * ‖x - x'‖ :=
          (norm_add_le _ _).trans (add_le_add (An.le_opNorm _) (h.Nv_lip x x'))
      _ ≤ (max ‖Au‖ ‖An‖ + L) * ‖x - x'‖ := by
          have := mul_le_mul (le_max_right ‖Au‖ ‖An‖) hx2 (norm_nonneg _)
            ((norm_nonneg _).trans (le_max_left _ _))
          nlinarith

theorem yStar_zero (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ : Nn) :
    yStar h bu bn n₀ 0 = (graphMap h bu bn n₀, n₀) :=
  Prod.ext rfl (yStar_zero_snd h bu bn n₀)

/-- **Invariance of the graph under the flow.** Every solution `z` of
`eq:supp-exact-graph-field` on `[0, T]` that starts on the graph, `z(0) = (h(n₀), n₀)`, is the
forward weighted trajectory and stays on the graph: `u(t) = h(n(t))` for `t ∈ [0, T]`. -/
theorem flow_mem_graph (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn)
    (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) (hdu : ∀ t, HasDerivAt Pu (Au * Pu t) t)
    (hdn : ∀ t, HasDerivAt Pn (An * Pn t) t) {T : ℝ} {z : ℝ → U × Nn}
    (hz : ContinuousOn z (Icc 0 T))
    (hz' : ∀ t ∈ Ico 0 T, HasDerivWithinAt z (graphField Au An bu bn Nu Nv (z t)) (Ici t) t)
    {n₀ : Nn} (hz0 : z 0 = (graphMap h bu bn n₀, n₀)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    z t = yStar h bu bn n₀ t ∧ (z t).1 = graphMap h bu bn (z t).2 := by
  have heq : EqOn z (yStar h bu bn n₀) (Icc 0 T) :=
    ODE_solution_unique (v := fun _ => graphField Au An bu bn Nu Nv)
      (fun _ => graphField_lipschitz h Au An bu bn) hz hz'
      (yStar_continuous h bu bn n₀).continuousOn
      (fun s hs => yStar_hasDerivWithinAt h bu bn n₀ Au An hdu hdn hs.1)
      (by rw [hz0, yStar_zero])
  refine ⟨heq ht, ?_⟩
  rw [heq ht]
  exact yStar_mem_graph h bu bn n₀ ht.1

/-- **Localization.** If a field `V` agrees with the localized field on a set `O`, then every
solution of `V` on `[0, T]` that stays in `O` and starts on the graph stays on the graph. -/
theorem flow_mem_graph_of_local (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn)
    (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) (hdu : ∀ t, HasDerivAt Pu (Au * Pu t) t)
    (hdn : ∀ t, HasDerivAt Pn (An * Pn t) t) {V : U × Nn → U × Nn} {O : Set (U × Nn)}
    (hVO : ∀ x ∈ O, V x = graphField Au An bu bn Nu Nv x) {T : ℝ} {z : ℝ → U × Nn}
    (hz : ContinuousOn z (Icc 0 T)) (hzO : ∀ t ∈ Ico 0 T, z t ∈ O)
    (hz' : ∀ t ∈ Ico 0 T, HasDerivWithinAt z (V (z t)) (Ici t) t)
    {n₀ : Nn} (hz0 : z 0 = (graphMap h bu bn n₀, n₀)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (z t).1 = graphMap h bu bn (z t).2 :=
  (flow_mem_graph h bu bn Au An hdu hdn hz
    (fun s hs => by rw [← hVO _ (hzO s hs)]; exact hz' s hs) hz0 ht).2

end Flow

/-! ### Non-vacuity -/

/-- The hypotheses `GraphHyp` are satisfiable: `P_u(t) = e^{3t}`, `P_n(t) = 1`, `M = 1`,
`α = 0`, `ν = 1`, `β = 3`, `L = 0`. -/
theorem graphHyp_nonvacuous :
    GraphHyp (U := ℝ) (Nn := ℝ) (fun t => exp (3 * t) • ContinuousLinearMap.id ℝ ℝ)
      (fun _ => ContinuousLinearMap.id ℝ ℝ) 1 0 3 1 0 (fun _ => 0) (fun _ => 0) where
  Pu_cont := ((continuous_const.mul continuous_id).rexp).smul continuous_const
  Pn_cont := continuous_const
  Pu_add s t := by
    ext
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, mul_one]
    rw [mul_add, exp_add]
  Pn_add _ _ := by ext; simp
  Pu_zero := by ext; simp
  Pn_zero := rfl
  ν_pos := one_pos
  α_lt := zero_lt_one
  lt_β := by norm_num
  M_nonneg := zero_le_one
  L_nonneg := le_rfl
  Pu_bound s _ := by
    rw [norm_smul, Real.norm_of_nonneg (exp_pos _).le]
    calc exp (3 * -s) * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ exp (3 * -s) * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (exp_pos _).le
      _ = 1 * exp (-3 * s) := by ring_nf
  Pn_bound s _ := by simp [ContinuousLinearMap.norm_id_le]
  Nu_lip _ _ := by simp
  Nv_lip _ _ := by simp
  contr := by norm_num

end LyapunovPerron
end RenewalGeometry
