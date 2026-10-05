/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ForwardBackwardIdempotentDichotomy
import RenewalGeometry.Gravity.ExactBoundaryBalancedField

/-!
# The amplitude-scaled boundary contraction on a graded chart

Emergent-spacetime manuscript, `thm:supp-exact-boundary`, `prop:supp-exact-sweep-accuracy`,
`prop:supp-exact-boundary-residual`, generic in the data of item (C3) of
`ass:supp-graded-exact-chart`.

Input: an unbalanced field with the graded bounds of (C3) (`ExactBoundaryChart.Graded`) and an
exponential dichotomy of `D = diag(0, B)` (the last sentence of (C3); `FBSweep.Dichotomy`).
With `C_M = ‖C_red‖ + C(1 + M₀)`, `C_f = C(1 + cβ + c²β²)` and `K = 2 M c C_f`, the smallness
conditions `ExactBoundaryHistory.Small` (`M c C_M ≤ 1/4`, `cβ ≤ M₀/2`, `K a ≤ M₀/2`,
`0 < a ≤ 1`, `M₀ a ≤ ρ₀`, `S a ≤ c`) are those of the manuscript's proof ("choose `c` and then
`a₀`").  Then:

* `ExactBoundaryHistory.fieldData`: the balanced field satisfies the hypotheses of the field sweep
  with `ε = C_M a`, `R = K a²`, `sup‖f_a‖ ≤ C_f a³` (from `lem:supp-exact-balanced-field`'s proved
  clauses);
* `ExactBoundaryHistory.boundary_history`: there is a unique balanced history `w_*` with
  `w_*' = 𝓗_a(w_*)`, `Π₋(w_*(0) - w_ref(0)) = 0`, `Π₊(w_*(S) - w_ref(S)) = 0`,
  `‖w_* - w_ref‖ ≤ K a²` (`eq:supp-exact-boundary-estimate`, lines 1–2 and the first bound);
  `ExactBoundaryHistory.exists_small` / `ExactBoundaryHistory.boundary_history_exists`: the
  constants `c, a₁ > 0` exist for every graded chart, giving the statement for all `0 < a < a₁`,
  `0 ≤ S ≤ c/a`;
* `ExactBoundaryHistory.velocity_error_le`: under the second-order graded bounds
  (`ExactBoundaryHistory.GradedSecond`: `‖D²R_s‖ ≤ C₂ a`, `‖D²R_f‖ ≤ C₂`, in Lipschitz form — the
  `j = 2` content of "analyticity and the factor `a` in the slow remainder"),
  `‖(w_* - w_ref)'‖ ≤ C_vel a³`;
* `ExactBoundaryHistory.sweep_accuracy`: the sweep iterates satisfy `‖δ_m‖ ≤ 4^{-m} K a²` and
  `‖δ_{m+1}'‖ ≤ (‖D‖ K/4 + C_M K a) 4^{-m} a²` (`eq:supp-exact-sweep-jets`, `j = 0, 1`);
* `ExactBoundaryHistory.residual_bound_scaled`: `eq:supp-exact-residual-bound` with `q ≤ 1/4`;
* `ExactBoundaryHistory.example_small`: the hypotheses are jointly satisfiable (explicit chart on
  `ℝ × ℝ` with `R_f(a, v) = a v_f`, `B = 1`, `D = diag(0,1)`, `a = 1/48`, `S = 1`).
-/

open Set Metric

namespace RenewalGeometry
namespace ExactBoundaryHistory

open ExactBoundaryChart ExactBoundaryChart.UnbalancedField FBField FBSweep FBVariation

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

variable {Es Ef : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es] [CompleteSpace Es]
  [NormedAddCommGroup Ef] [NormedSpace ℝ Ef] [CompleteSpace Ef]

/-- `C_M = ‖C_red‖ + C(1 + M₀)`, the constant of `‖D𝓗_a - D‖ ≤ C_M a`. -/
def Cm (V : UnbalancedField Es Ef) (C M₀ : ℝ) : ℝ := ‖V.Cred‖ + C * (1 + M₀)

/-- `C_f = C(1 + cβ + c²β²)`, the constant of `‖f_a‖ ≤ C_f a³`. -/
def Cf (V : UnbalancedField Es Ef) (C c : ℝ) : ℝ := C * (1 + c * V.beta + (c * V.beta) ^ 2)

/-- `C_d = C(1 + cβ)β`, the constant of `‖f_a'‖ ≤ C_d a⁴`. -/
def Cd (V : UnbalancedField Es Ef) (C c : ℝ) : ℝ := C * (1 + c * V.beta) * V.beta

/-- The radius constant `K = 2 M c C_f` (the paper's `K = 2C₀`). -/
def Kc (V : UnbalancedField Es Ef) (C M c : ℝ) : ℝ := 2 * M * c * Cf V C c

/-- The smallness conditions of the proof of `thm:supp-exact-boundary`. -/
structure Small (V : UnbalancedField Es Ef) (C ρ₀ a₀ M M₀ c a S : ℝ) : Prop where
  a_mem : a ∈ Ioo 0 a₀
  a_le_one : a ≤ 1
  tube_le : M₀ * a ≤ ρ₀
  S_nonneg : 0 ≤ S
  S_le : S * a ≤ c
  q_small : M * c * Cm V C M₀ ≤ 1 / 4
  ref_small : c * V.beta ≤ M₀ / 2
  ball_small : Kc V C M c * a ≤ M₀ / 2

variable {V : UnbalancedField Es Ef} {C ρ₀ a₀ M κ M₀ c a S : ℝ}
  {Pp Pm : Es × Ef →L[ℝ] Es × Ef}

theorem Small.c_nonneg (hs : Small V C ρ₀ a₀ M M₀ c a S) : 0 ≤ c :=
  (mul_nonneg hs.S_nonneg hs.a_mem.1.le).trans hs.S_le

theorem Small.M₀_nonneg (hs : Small V C ρ₀ a₀ M M₀ c a S) : 0 ≤ M₀ := by
  have := mul_nonneg hs.c_nonneg (norm_nonneg ((V.bs, V.bw) : Es × Ef))
  have h := hs.ref_small
  simp only [beta] at h
  linarith

theorem Small.s_mul_le (hs : Small V C ρ₀ a₀ M M₀ c a S) {s : ℝ} (h : s ∈ Icc 0 S) :
    s * a ≤ c :=
  (mul_le_mul_of_nonneg_right h.2 hs.a_mem.1.le).trans hs.S_le

theorem Small.ref_rho (hs : Small V C ρ₀ a₀ M M₀ c a S) : c * V.beta * a ^ 2 ≤ ρ₀ := by
  have ha := hs.a_mem.1
  have h1 : c * V.beta * a ^ 2 ≤ M₀ / 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_right hs.ref_small (by positivity)
  have h2 : a ^ 2 ≤ a := by nlinarith [hs.a_le_one]
  have h3 : M₀ / 2 * a ^ 2 ≤ M₀ * a := by nlinarith [hs.M₀_nonneg]
  linarith [hs.tube_le]

/-- **The balanced field satisfies the sweep hypotheses** with `ε = C_M a`, `R = K a²`,
`K_f = C_f a³` on the tube `‖w‖ ≤ M₀ a`. -/
theorem fieldData (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ)
    (hs : Small V C ρ₀ a₀ M M₀ c a S) :
    FieldData V.Dlin Pp Pm M κ (V.Hbal a) (V.DHbal a) (V.omega a) (M₀ * a) (Cm V C M₀ * a) S
      (Kc V C M c * a ^ 2) (Cf V C c * a ^ 3) := by
  have ha := hs.a_mem.1
  have hM := hD.M_nonneg
  have hC := hG.C_nonneg
  have hc := hs.c_nonneg
  have hb : 0 ≤ V.beta := norm_nonneg _
  have hCm : 0 ≤ Cm V C M₀ := by
    have := hs.M₀_nonneg; unfold Cm; positivity
  have hCf : 0 ≤ Cf V C c := by unfold Cf; positivity
  refine ⟨hD, hs.S_nonneg, fun w hw => ?_, fun w hw => ?_, fun s hsI => ?_, fun s hsI => ?_, ?_, ?_⟩
  · refine hasFDerivAt_Hbal hG hs.a_mem ?_
    exact (norm_balL_le ha.le hs.a_le_one w).trans
      ((mem_closedBall_zero_iff.1 hw).trans hs.tube_le)
  · exact norm_DHbal_sub_le hG hs.a_mem hs.a_le_one (mem_closedBall_zero_iff.1 hw) hs.tube_le
  · have h1 := norm_wref_le (V := V) ha hs.a_le_one hsI.1 (hs.s_mul_le hsI)
    have h2 : c * V.beta * a ≤ M₀ / 2 * a := mul_le_mul_of_nonneg_right hs.ref_small ha.le
    have h3 : Kc V C M c * a ^ 2 ≤ M₀ / 2 * a := by
      have := mul_le_mul_of_nonneg_right hs.ball_small ha.le
      nlinarith
    linarith
  · exact norm_src_le hG hs.a_mem hs.a_le_one hsI.1 (hs.s_mul_le hsI) hs.ref_rho
  · have : M * S * (Cm V C M₀ * a) = M * (S * a) * Cm V C M₀ := by ring
    rw [this]
    refine le_trans ?_ hs.q_small
    have := mul_le_mul_of_nonneg_left hs.S_le hM
    nlinarith
  · have e1 : M * S * (Cf V C c * a ^ 3) = M * (S * a) * Cf V C c * a ^ 2 := by ring
    have e2 : Kc V C M c * a ^ 2 / 2 = M * c * Cf V C c * a ^ 2 := by unfold Kc; ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hs.S_le hM
    have h4 : M * (S * a) * Cf V C c ≤ M * c * Cf V C c := mul_le_mul_of_nonneg_right this hCf
    nlinarith [sq_nonneg a]

/-- **`thm:supp-exact-boundary`, generic in the (C3) data**: for `0 < a ≤ 1` and `0 ≤ S ≤ c/a`
under the smallness conditions, there is a unique balanced history with
`w_*' = 𝓗_a(w_*)`, `Π₋(w_*(0) - w_ref(0)) = 0`, `Π₊(w_*(S) - w_ref(S)) = 0` and
`‖w_* - w_ref‖ ≤ K a²`. -/
theorem boundary_history (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ)
    (hs : Small V C ρ₀ a₀ M M₀ c a S) :
    ∃ w : ℝ → Es × Ef,
      IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w ∧
      ∀ w' : ℝ → Es × Ef,
        IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w' →
          ∀ s ∈ Icc 0 S, w' s = w s :=
  exists_unique_boundary_history (fieldData hG hD hs)

/-- Second-order graded bounds (the `j = 2` instance of the analytic divisibility of (C3):
`‖D²R_s‖ ≤ C₂ a`, `‖D²R_f‖ ≤ C₂` on the neighbourhood, in Lipschitz form). -/
structure GradedSecond (V : UnbalancedField Es Ef) (C₂ ρ₀ a₀ : ℝ) : Prop where
  C₂_nonneg : 0 ≤ C₂
  DRs_lip : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → ∀ v' : Es × Ef, ‖v'‖ ≤ ρ₀ →
    ‖V.DRs a v - V.DRs a v'‖ ≤ C₂ * a * ‖v - v'‖
  DRf_lip : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → ∀ v' : Es × Ef, ‖v'‖ ≤ ρ₀ →
    ‖V.DRf a v - V.DRf a v'‖ ≤ C₂ * ‖v - v'‖

/-- **Second balanced derivative** (`lem:supp-exact-balanced-field`, `j = 2`, Lipschitz form):
`‖D𝓗_a(w) - D𝓗_a(w')‖ ≤ C₂ ‖w - w'‖` on the tube. -/
theorem DHbal_lip (hG2 : GradedSecond V C₂ ρ₀ a₀) (ha : a ∈ Ioo 0 a₀) (ha1 : a ≤ 1)
    {w w' : Es × Ef} (hw : ‖w‖ ≤ ρ₀) (hw' : ‖w'‖ ≤ ρ₀) :
    ‖V.DHbal a w - V.DHbal a w'‖ ≤ C₂ * ‖w - w'‖ := by
  have ha0 := ha.1
  have hC₂ := hG2.C₂_nonneg
  have hv : ‖balL a w‖ ≤ ρ₀ := (norm_balL_le ha0.le ha1 w).trans hw
  have hv' : ‖balL a w'‖ ≤ ρ₀ := (norm_balL_le ha0.le ha1 w').trans hw'
  have hd : ‖balL a w - balL a w'‖ ≤ ‖w - w'‖ := by
    rw [← map_sub]; exact norm_balL_le ha0.le ha1 _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hbh := norm_balL_le (Es := Es) (Ef := Ef) ha0.le ha1 h
  have happ : (V.DHbal a w - V.DHbal a w') h
      = (a⁻¹ • (V.DRs a (balL a w) - V.DRs a (balL a w')) (balL a h),
          (V.DRf a (balL a w) - V.DRf a (balL a w')) (balL a h)) := by
    simp only [DHbal, ContinuousLinearMap.sub_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, Prod.mk_sub_mk, smul_sub]
    congr 1
    abel
  rw [happ, Prod.norm_mk]
  refine max_le ?_ ?_
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha0.le)]
    calc a⁻¹ * ‖(V.DRs a (balL a w) - V.DRs a (balL a w')) (balL a h)‖
        ≤ a⁻¹ * (C₂ * a * ‖w - w'‖ * ‖h‖) := by
          refine mul_le_mul_of_nonneg_left (((V.DRs a _ - V.DRs a _).le_opNorm _).trans ?_)
            (inv_nonneg.2 ha0.le)
          refine mul_le_mul ((hG2.DRs_lip a ha _ hv _ hv').trans ?_) hbh (norm_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_left hd (by positivity)
      _ = C₂ * ‖w - w'‖ * ‖h‖ := by field_simp
  · refine ((V.DRf a _ - V.DRf a _).le_opNorm _).trans ?_
    refine mul_le_mul ((hG2.DRf_lip a ha _ hv _ hv').trans ?_) hbh (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hd hC₂

/-- The velocity constant `C_vel = (4/3)(2M(C_f + C_M K) + M c (C_d + C₂ K β))`. -/
def Cvel (V : UnbalancedField Es Ef) (C C₂ M M₀ c : ℝ) : ℝ :=
  4 / 3 * (2 * M * (Cf V C c + Cm V C M₀ * Kc V C M c)
    + M * c * (Cd V C c + C₂ * Kc V C M c * V.beta))

/-- **Derivative estimate of `thm:supp-exact-boundary`**: `‖(w_* - w_ref)'‖ ≤ C_vel a³` (the
velocity error is `𝓗_a(w_*) - ω_a` on the whole interval). -/
theorem velocity_error_le (hG : Graded V C ρ₀ a₀) (hG2 : GradedSecond V C₂ ρ₀ a₀)
    (hD : Dichotomy V.Dlin Pp Pm M κ) (hs : Small V C ρ₀ a₀ M M₀ c a S) {w : ℝ → Es × Ef}
    (hw : IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w) :
    ∀ s ∈ Icc 0 S, ‖V.Hbal a (w s) - V.omega a‖ ≤ Cvel V C C₂ M M₀ c * a ^ 3 := by
  have hF := fieldData hG hD hs
  have ha := hs.a_mem.1
  have ha1 := hs.a_le_one
  have hM := hD.M_nonneg
  have hC := hG.C_nonneg
  have hc := hs.c_nonneg
  have hb : 0 ≤ V.beta := norm_nonneg _
  have hC₂ := hG2.C₂_nonneg
  have hM₀ := hs.M₀_nonneg
  have hCm : 0 ≤ Cm V C M₀ := by unfold Cm; positivity
  have hCf : 0 ≤ Cf V C c := by unfold Cf; positivity
  have hCd : 0 ≤ Cd V C c := by unfold Cd; positivity
  have hK : 0 ≤ Kc V C M c := by unfold Kc; positivity
  have hball : ∀ x ∈ closedBall (0 : Es × Ef) (M₀ * a), ‖x‖ ≤ ρ₀ := fun x hx =>
    (mem_closedBall_zero_iff.1 hx).trans hs.tube_le
  have hcont : ContinuousOn (V.DHbal a) (closedBall (0 : Es × Ef) (M₀ * a)) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := C₂.toNNReal) fun x hx y hy => ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hC₂]
    exact DHbal_lip hG2 hs.a_mem ha1 (hball x hx) (hball y hy)
  have hlip : ∀ x ∈ closedBall (0 : Es × Ef) (M₀ * a), ∀ y ∈ closedBall (0 : Es × Ef) (M₀ * a),
      ‖V.DHbal a x - V.DHbal a y‖ ≤ C₂ * ‖x - y‖ := fun x hx y hy =>
    DHbal_lip hG2 hs.a_mem ha1 (hball x hx) (hball y hy)
  have hfd : ∀ s ∈ Icc 0 S, ‖V.DHbal a (s • V.omega a) (V.omega a)‖ ≤ Cd V C c * a ^ 4 :=
    fun s hsI => norm_src_deriv_le hG hs.a_mem ha1 hsI.1 (hs.s_mul_le hsI) hs.ref_rho
  have key := norm_velocity_error_le hF hC₂ hcont hlip hfd hw
  intro s hsI
  refine (key s hsI).trans ?_
  have hω := norm_omega_le (V := V) ha.le ha1
  have hq : M * S * (Cm V C M₀ * a) ≤ 1 / 4 := hF.q_le
  have hq0 : 0 ≤ M * S * (Cm V C M₀ * a) := by have := hs.S_nonneg; positivity
  have hSa : M * S * a ≤ M * c := by
    have := mul_le_mul_of_nonneg_left hs.S_le hM; nlinarith
  -- numerator bound
  have hnum : M * (2 * (Cf V C c * a ^ 3 + Cm V C M₀ * a * (Kc V C M c * a ^ 2)))
      + M * S * (Cd V C c * a ^ 4 + C₂ * (Kc V C M c * a ^ 2) * ‖V.omega a‖)
      ≤ 3 / 4 * (Cvel V C C₂ M M₀ c * a ^ 3) := by
    have h1 : M * S * (Cd V C c * a ^ 4 + C₂ * (Kc V C M c * a ^ 2) * ‖V.omega a‖)
        ≤ M * S * a * ((Cd V C c + C₂ * Kc V C M c * V.beta) * a ^ 3) := by
      have : C₂ * (Kc V C M c * a ^ 2) * ‖V.omega a‖ ≤ C₂ * (Kc V C M c * a ^ 2) * (V.beta * a ^ 2)
        := mul_le_mul_of_nonneg_left hω (by positivity)
      have hMS : 0 ≤ M * S := mul_nonneg hM hs.S_nonneg
      calc _ ≤ M * S * (Cd V C c * a ^ 4 + C₂ * (Kc V C M c * a ^ 2) * (V.beta * a ^ 2)) := by
            gcongr
        _ = _ := by ring
    have h2 : M * S * a * ((Cd V C c + C₂ * Kc V C M c * V.beta) * a ^ 3)
        ≤ M * c * ((Cd V C c + C₂ * Kc V C M c * V.beta) * a ^ 3) :=
      mul_le_mul_of_nonneg_right hSa (by positivity)
    unfold Cvel
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  have hpos : 0 ≤ Cvel V C C₂ M M₀ c * a ^ 3 := by unfold Cvel; positivity
  nlinarith

/-- **Accuracy of the sweep iterates** (`prop:supp-exact-sweep-accuracy`, `j = 0, 1`): with
`hd = (fieldData …).toSweepData`, `δ_m = e^{[m]} - e_*` satisfies `‖δ_m‖ ≤ 4^{-m} K a²` on
`[0, S]` and `‖δ_{m+1}'‖ ≤ ‖D‖ 4^{-(m+1)} K a² + C_M a 4^{-m} K a²` inside. -/
theorem sweep_accuracy (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ)
    (hs : Small V C ρ₀ a₀ M M₀ c a S) {u : Ball S (Kc V C M c * a ^ 2) (Es × Ef)}
    (hu : sweepMap (fieldData hG hD hs).toSweepData u = u) (m : ℕ) :
    (∀ s : Icc (0 : ℝ) S,
      ‖((sweepMap (fieldData hG hD hs).toSweepData)^[m]
        (zeroBall (fieldData hG hD hs).toSweepData)).1 s - u.1 s‖
        ≤ (1 / 4) ^ m * (Kc V C M c * a ^ 2)) ∧
    ∀ s ∈ Ioo 0 S, ∃ δ' : Es × Ef,
      HasDerivAt (fun r => ext (fieldData hG hD hs).toSweepData
          ((sweepMap (fieldData hG hD hs).toSweepData)^[m + 1]
            (zeroBall (fieldData hG hD hs).toSweepData)) r
          - ext (fieldData hG hD hs).toSweepData u r) δ' s ∧
        ‖δ'‖ ≤ ‖V.Dlin‖ * ((1 / 4) ^ (m + 1) * (Kc V C M c * a ^ 2))
          + Cm V C M₀ * a * ((1 / 4) ^ m * (Kc V C M c * a ^ 2)) :=
  ⟨fun s => norm_iterate_sub_le _ hu m s, fun _ hsI => deriv_iterate_sub_le _ hu m hsI⟩

/-- **`eq:supp-exact-residual-bound`** on the graded chart: an approximate history in the
contraction tube with residual `r = w̃' - 𝓗_a(w̃)` satisfies
`‖w̃ - w_*‖ ≤ (M(|d₋| + |d₊|) + M S ‖r‖)/(1 - q)` with `q = M S C_M a ≤ 1/4`. -/
theorem residual_bound_scaled (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ)
    (hs : Small V C ρ₀ a₀ M M₀ c a S) {w : ℝ → Es × Ef}
    (hw : IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w)
    {wt res : ℝ → Es × Ef} {Kr : ℝ} (hwt : ContinuousOn wt (Icc 0 S))
    (htube : ∀ s ∈ Icc 0 S, ‖wt s - s • V.omega a‖ ≤ Kc V C M c * a ^ 2)
    (hres : ContinuousOn res (Icc 0 S))
    (hde : ∀ s ∈ Ioo 0 S, HasDerivAt wt (V.Hbal a (wt s) + res s) s)
    (hr : ∀ s ∈ Icc 0 S, ‖res s‖ ≤ Kr) :
    M * S * (Cm V C M₀ * a) ≤ 1 / 4 ∧ ∀ s ∈ Icc 0 S, ‖wt s - w s‖
      ≤ (M * (‖Pm (wt 0 - (0 : ℝ) • V.omega a)‖ + ‖Pp (wt S - S • V.omega a)‖) + M * S * Kr)
          / (1 - M * S * (Cm V C M₀ * a)) :=
  ⟨(fieldData hG hD hs).q_le, residual_bound (fieldData hG hD hs) hw hwt htube hres hde hr⟩

/-- **Choice of the constants** ("choose `c` and then `a₀`"): for every graded chart with a
dichotomy there are `c, a₁ > 0` such that the smallness conditions hold (with `M₀ = 1`) for all
`0 < a < a₁` and `0 ≤ S ≤ c/a`. -/
theorem exists_small (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀) :
    ∃ c > (0 : ℝ), ∃ a₁ > (0 : ℝ), ∀ a ∈ Ioo 0 a₁, ∀ S : ℝ, 0 ≤ S → S * a ≤ c →
      Small V C ρ₀ a₀ M 1 c a S := by
  have hM := hD.M_nonneg
  have hC := hG.C_nonneg
  have hb : 0 ≤ V.beta := norm_nonneg _
  have hCm : 0 ≤ Cm V C 1 := by unfold Cm; positivity
  set c := 1 / (4 * (M * Cm V C 1 + V.beta + 1)) with hc
  have hden : 0 < 4 * (M * Cm V C 1 + V.beta + 1) := by positivity
  have hc0 : 0 < c := by positivity
  have hK : 0 ≤ Kc V C M c := by unfold Kc Cf; positivity
  set a₁ := min (min a₀ 1) (min ρ₀ (1 / (2 * (Kc V C M c + 1)))) with ha₁
  have ha₁0 : 0 < a₁ := lt_min (lt_min ha₀ one_pos) (lt_min hρ₀ (by positivity))
  refine ⟨c, hc0, a₁, ha₁0, fun a ha S hS hSa => ?_⟩
  have ha1 : a < a₀ := lt_of_lt_of_le ha.2 ((min_le_left _ _).trans (min_le_left _ _))
  have ha2 : a < 1 := lt_of_lt_of_le ha.2 ((min_le_left _ _).trans (min_le_right _ _))
  have ha3 : a < ρ₀ := lt_of_lt_of_le ha.2 ((min_le_right _ _).trans (min_le_left _ _))
  have ha4 : a < 1 / (2 * (Kc V C M c + 1)) :=
    lt_of_lt_of_le ha.2 ((min_le_right _ _).trans (min_le_right _ _))
  have hcm : c * (4 * (M * Cm V C 1 + V.beta + 1)) = 1 := by rw [hc]; field_simp
  refine ⟨⟨ha.1, ha1⟩, ha2.le, by linarith, hS, hSa, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hc0.le hb]
  · nlinarith [mul_nonneg hc0.le (mul_nonneg hM hCm)]
  · have h1 : Kc V C M c * a ≤ Kc V C M c * (1 / (2 * (Kc V C M c + 1))) :=
      mul_le_mul_of_nonneg_left ha4.le hK
    have h2 : Kc V C M c * (1 / (2 * (Kc V C M c + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    linarith

/-- **`thm:supp-exact-boundary`, quantifier form**: there are `c, a₁ > 0` such that for every
`0 < a < a₁` and `0 ≤ S ≤ c/a` the balanced boundary history exists, is unique in the tube
`‖w - w_ref‖ ≤ K a²`, and satisfies the projected boundary conditions. -/
theorem boundary_history_exists (hG : Graded V C ρ₀ a₀) (hD : Dichotomy V.Dlin Pp Pm M κ)
    (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀) :
    ∃ c > (0 : ℝ), ∃ a₁ > (0 : ℝ), ∀ a ∈ Ioo 0 a₁, ∀ S : ℝ, 0 ≤ S → S * a ≤ c →
      ∃ w : ℝ → Es × Ef,
        IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w ∧
        ∀ w' : ℝ → Es × Ef,
          IsBoundaryHistory V.Dlin Pp Pm (V.Hbal a) (V.omega a) S (Kc V C M c * a ^ 2) w' →
            ∀ s ∈ Icc 0 S, w' s = w s := by
  obtain ⟨c, hc, a₁, ha₁, h⟩ := exists_small hG hD hρ₀ ha₀
  exact ⟨c, hc, a₁, ha₁, fun a ha S hS hSa => boundary_history hG hD (h a ha S hS hSa)⟩

/-! ### Non-vacuity -/

/-- An explicit unbalanced chart on `ℝ × ℝ`: `b_s = 1`, `b_w = 0`, `C_red = 0`, `B = 1`,
`R_s = 0`, `R_f(a, v) = a v_f`. -/
def exampleField : UnbalancedField ℝ ℝ where
  bs := 1
  bw := 0
  Cred := 0
  B := ContinuousLinearMap.id ℝ ℝ
  Rs := fun _ _ => 0
  Rf := fun a v => a • v.2
  DRs := fun _ _ => 0
  DRf := fun a _ => a • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem exampleField_graded : Graded exampleField 1 1 1 where
  C_nonneg := zero_le_one
  transport := by simp [exampleField]
  hasDeriv_s := fun a _ v _ => hasFDerivAt_const _ _
  hasDeriv_f := fun a _ v _ => (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.const_smul a
  Rs_le := fun a ha v _ => by simp only [exampleField, norm_zero]; have := ha.1; positivity
  DRs_le := fun a ha v _ => by simp only [exampleField, norm_zero]; have := ha.1; positivity
  Rf_le := fun a ha v _ => by
    simp only [exampleField, norm_smul, Real.norm_of_nonneg ha.1.le, one_mul]
    have h1 := norm_snd_le v
    have := ha.1
    nlinarith [norm_nonneg v, sq_nonneg ‖v‖, pow_pos ha.1 4, mul_le_mul_of_nonneg_left h1 ha.1.le]
  DRf_le := fun a ha v _ => by
    simp only [exampleField, norm_smul, Real.norm_of_nonneg ha.1.le, one_mul]
    have h := ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_left h ha.1.le]

theorem exampleField_Dlin : exampleField.Dlin = FBIdem.diagP := by
  ext <;> simp [UnbalancedField.Dlin, exampleField, FBIdem.diagP_apply]

theorem exampleField_beta : exampleField.beta = 1 := by
  simp [UnbalancedField.beta, exampleField]

/-- **The hypotheses of the scaled boundary theorem are jointly satisfiable**: the explicit
chart, the diagonal dichotomy `diag(0,1)` (`M = κ = 1`), `M₀ = 2`, `c = 1/12`, `a = 1/48`,
`S = 1`. -/
theorem example_small :
    Graded exampleField 1 1 1 ∧ Dichotomy exampleField.Dlin FBIdem.diagP (1 - FBIdem.diagP) 1 1 ∧
      Small exampleField 1 1 1 1 2 (1 / 12) (1 / 48) 1 := by
  refine ⟨exampleField_graded, exampleField_Dlin ▸ FBIdem.diag_dichotomy, ?_⟩
  have hCred : ‖exampleField.Cred‖ = 0 := by simp [exampleField]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simp only [Cm, hCred]; norm_num
  · rw [exampleField_beta]; norm_num
  · simp only [Kc, Cf, exampleField_beta]; norm_num

end

end ExactBoundaryHistory
end RenewalGeometry
