/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovPerronWeightedFixedPoint

/-!
# `C¹` regularity of the Lyapunov–Perron invariant graph

Third layer of the forward invariant-graph construction (`lem:supp-exact-graph-criterion`,
emergent-spacetime manuscript), on top of `Analysis/LyapunovPerronWeightedFixedPoint.lean`.

The graph `h(n₀) = u(0)` of the forward weighted trajectories (`graphMap`) is shown to be
**continuously differentiable, with a Lipschitz derivative**, when the nonlinearities have a
Lipschitz derivative (bounded second derivatives) and the `j = 2` inequality of
`eq:supp-exact-graph-contraction`, `M L ((2ν - α)⁻¹ + (β - 2ν)⁻¹) < 1` with `2ν < β`, holds.

The proof follows the manuscript ("differentiating in `n₀` gives a linear integral equation with
the same contractive principal term ... these belong to the weights `2ν`"), but avoids solving
the linearised equation in a function space: only **a priori bounds** in the weight `2ν` are used.

* `srcOp`, `srcOp_norm_le`: the Lyapunov–Perron integral operator applied to a source of growth
  `e^{κr}` has growth `M ((κ-α)⁻¹ + (β-κ)⁻¹) e^{κt}` (any `α < κ < β`);
* `apriori_le`: if `z = ℒ z + E` on `[0, ∞)` with `ℒ` the linearised operator along a trajectory
  (coefficients of norm `≤ L`) and `‖E(t)‖ ≤ σ e^{κt}`, and `z` has some `e^{κt}` growth, then
  `‖z(t)‖ ≤ σ/(1 - q_κ) e^{κt}` (`q_κ = M L((κ-α)⁻¹ + (β-κ)⁻¹) < 1`);
* `norm_comb_le`: for differences `w_v = y_*(n₀ + v) - y_*(n₀)` and scalars with
  `Σ aᵢ vᵢ = 0`, `‖Σ aᵢ w_{vᵢ}(0)‖ ≤ K Σ |aᵢ| ‖vᵢ‖²` (second-order Taylor remainders of the
  nonlinearity are sources in the weight `2ν`);
* `graphDeriv`, `graphMap_taylor`: the derivative `Λ(n₀)` (limit of difference quotients, linear
  and bounded) with the uniform second-order bound `‖h(n₀+v) - h(n₀) - Λ(n₀)v‖ ≤ K‖v‖²`;
* `graphMap_hasFDerivAt`, `graphDeriv_lipschitz`, `graphMap_contDiff_one` (**the graph is
  `C¹`, with `‖Dh(n) - Dh(n')‖ ≤ 6K‖n - n'‖`**);
* general analysis behind it (`QuadDefect`, `contDiff_one_of_quadDefect`): a map
  `H : E → F` (`F` complete) that is Lipschitz and has uniform quadratic three-point defects
  `‖Σ aᵢ(H(n+vᵢ) - H(n))‖ ≤ K Σ|aᵢ|‖vᵢ‖²` whenever `Σ aᵢvᵢ = 0` is `C^{1,1}`;
* `graphHyp_of_exp`, `hasDerivAt_exp_propagator`: the manuscript's propagators `e^{tA_u}`,
  `e^{tA_n}` (bounded generators) satisfy the group/continuity fields of `GraphHyp` and the
  generator relations `P' = A P`, so the abstract packet is exactly the manuscript's setting.

Not covered: the `C²` and `C³` layers (weights `3ν`, `j = 3`).
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

/-! ### The integral operator on sources of exponential growth -/

/-- The Lyapunov–Perron integral operator applied to a source `S`:
`(-∫_{(t,∞)} P_u(t-r) S_u(r) dr, ∫_0^t P_n(t-r) S_n(r) dr)`. -/
def srcOp (Pu : ℝ → U →L[ℝ] U) (Pn : ℝ → Nn →L[ℝ] Nn) (S : ℝ → U × Nn) (t : ℝ) : U × Nn :=
  (-∫ r in Ioi t, Pu (t - r) (S r).1, ∫ r in (0 : ℝ)..t, Pn (t - r) (S r).2)

section Src

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β κ σ : ℝ}

theorem backward_src_integrable (hPuc : Continuous Pu) (hκβ : κ < β) (hM : 0 ≤ M)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)) {S : ℝ → U × Nn} (hS : Continuous S)
    (hSb : ∀ r, 0 ≤ r → ‖S r‖ ≤ σ * exp (κ * r)) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun r => Pu (t - r) (S r).1) (Ioi t) := by
  have hmeas : AEStronglyMeasurable (fun r => Pu (t - r) (S r).1) (volume.restrict (Ioi t)) :=
    ((hPuc.comp (continuous_const.sub continuous_id)).clm_apply
      (continuous_fst.comp hS)).aestronglyMeasurable
  refine Integrable.mono' (backward_kernel_integrable (M := M) (K := σ) (t := t) hκβ) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  have hr0 : 0 ≤ r := ht.trans hr.out.le
  have hP : ‖Pu (t - r)‖ ≤ M * exp (-β * (r - t)) := by
    have := hPu (r - t) (by linarith [hr.out])
    rwa [show -(r - t) = t - r by ring] at this
  calc ‖Pu (t - r) (S r).1‖ ≤ ‖Pu (t - r)‖ * ‖(S r).1‖ := (Pu (t - r)).le_opNorm _
    _ ≤ M * exp (-β * (r - t)) * (σ * exp (κ * r)) :=
        mul_le_mul hP ((norm_fst_le _).trans (hSb r hr0)) (norm_nonneg _) (by positivity)

theorem forward_src_intervalIntegrable (hPnc : Continuous Pn) {S : ℝ → U × Nn}
    (hS : Continuous S) (t : ℝ) :
    IntervalIntegrable (fun r => Pn (t - r) (S r).2) volume 0 t :=
  ((hPnc.comp (continuous_const.sub continuous_id)).clm_apply
    (continuous_snd.comp hS)).intervalIntegrable _ _

/-- **Kernel bound for sources**: a continuous source with `‖S(r)‖ ≤ σ e^{κr}` (`r ≥ 0`) gives
`‖srcOp S t‖ ≤ M σ ((κ - α)⁻¹ + (β - κ)⁻¹) e^{κt}` for `t ≥ 0`. -/
theorem srcOp_norm_le (hPuc : Continuous Pu) (hPnc : Continuous Pn) (hακ : α < κ) (hκβ : κ < β)
    (hM : 0 ≤ M) (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s))
    (hPn : ∀ s, 0 ≤ s → ‖Pn s‖ ≤ M * exp (α * s)) {S : ℝ → U × Nn} (hS : Continuous S)
    (hSb : ∀ r, 0 ≤ r → ‖S r‖ ≤ σ * exp (κ * r)) {t : ℝ} (ht : 0 ≤ t) :
    ‖srcOp Pu Pn S t‖ ≤ M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹) * exp (κ * t) := by
  have hσ : 0 ≤ σ := by
    have := (norm_nonneg _).trans (hSb 0 le_rfl); simpa using this
  have hB : ‖∫ r in Ioi t, Pu (t - r) (S r).1‖ ≤ M * σ * exp (κ * t) / (β - κ) := by
    rw [← backward_kernel_eq (M := M) (K := σ) hκβ]
    refine norm_integral_le_of_norm_le (backward_kernel_integrable hκβ) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 ≤ r := ht.trans hr.out.le
    have hP : ‖Pu (t - r)‖ ≤ M * exp (-β * (r - t)) := by
      have := hPu (r - t) (by linarith [hr.out])
      rwa [show -(r - t) = t - r by ring] at this
    calc ‖Pu (t - r) (S r).1‖ ≤ ‖Pu (t - r)‖ * ‖(S r).1‖ := (Pu (t - r)).le_opNorm _
      _ ≤ M * exp (-β * (r - t)) * (σ * exp (κ * r)) :=
          mul_le_mul hP ((norm_fst_le _).trans (hSb r hr0)) (norm_nonneg _) (by positivity)
  have hF : ‖∫ r in (0 : ℝ)..t, Pn (t - r) (S r).2‖ ≤ M * σ * exp (κ * t) / (κ - α) := by
    refine (norm_integral_le_of_norm_le ht ?_ ?_).trans (forward_kernel_le hM hσ hακ ht)
    · refine Eventually.of_forall fun r hr => ?_
      have hr0 : 0 ≤ r := hr.1.le
      have hP : ‖Pn (t - r)‖ ≤ M * exp (α * (t - r)) := hPn (t - r) (by linarith [hr.2])
      calc ‖Pn (t - r) (S r).2‖ ≤ ‖Pn (t - r)‖ * ‖(S r).2‖ := (Pn (t - r)).le_opNorm _
        _ ≤ M * exp (α * (t - r)) * (σ * exp (κ * r)) :=
            mul_le_mul hP ((norm_snd_le _).trans (hSb r hr0)) (norm_nonneg _) (by positivity)
    · have : Continuous fun r : ℝ => M * exp (α * (t - r)) * (σ * exp (κ * r)) := by fun_prop
      exact this.intervalIntegrable _ _
  have hc1 : 0 < κ - α := sub_pos.mpr hακ
  have hc2 : 0 < β - κ := sub_pos.mpr hκβ
  rw [srcOp, Prod.norm_def, norm_neg]
  calc max ‖∫ r in Ioi t, Pu (t - r) (S r).1‖ ‖∫ r in (0 : ℝ)..t, Pn (t - r) (S r).2‖
      ≤ M * σ * exp (κ * t) / (β - κ) + M * σ * exp (κ * t) / (κ - α) := by
        refine max_le ?_ ?_
        · exact hB.trans (le_add_of_nonneg_right (by positivity))
        · exact hF.trans (le_add_of_nonneg_left (by positivity))
    _ = M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹) * exp (κ * t) := by field_simp; ring

/-- `srcOp` is additive on continuous sources of exponential growth. -/
theorem srcOp_add (hPuc : Continuous Pu) (hPnc : Continuous Pn) (hκβ : κ < β) (hM : 0 ≤ M)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)) {S T : ℝ → U × Nn} (hS : Continuous S)
    (hT : Continuous T) {σ τ : ℝ} (hSb : ∀ r, 0 ≤ r → ‖S r‖ ≤ σ * exp (κ * r))
    (hTb : ∀ r, 0 ≤ r → ‖T r‖ ≤ τ * exp (κ * r)) {t : ℝ} (ht : 0 ≤ t) :
    srcOp Pu Pn (S + T) t = srcOp Pu Pn S t + srcOp Pu Pn T t := by
  have h1 := backward_src_integrable hPuc hκβ hM hPu hS hSb ht
  have h2 := backward_src_integrable hPuc hκβ hM hPu hT hTb ht
  have h3 := forward_src_intervalIntegrable (U := U) hPnc hS t
  have h4 := forward_src_intervalIntegrable (U := U) hPnc hT t
  simp only [srcOp, Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
  rw [integral_add h1 h2, intervalIntegral.integral_add h3 h4, neg_add]

/-- `srcOp` is homogeneous. -/
theorem srcOp_smul (c : ℝ) (S : ℝ → U × Nn) (t : ℝ) :
    srcOp Pu Pn (c • S) t = c • srcOp Pu Pn S t := by
  simp only [srcOp, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk]
  rw [MeasureTheory.integral_smul, intervalIntegral.integral_smul, smul_neg]

end Src

/-! ### Functions with uniform quadratic three-point defects are `C^{1,1}` -/

section QuadraticDefect

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- The three-point defect condition: for every base point `n` and every combination
`a₁v₁ + a₂v₂ + a₃v₃ = 0`, `‖Σ aᵢ (H(n + vᵢ) - H(n))‖ ≤ K Σ |aᵢ| ‖vᵢ‖²`. -/
def QuadDefect (H : E → F) (K : ℝ) : Prop :=
  ∀ (n v₁ v₂ v₃ : E) (a₁ a₂ a₃ : ℝ), a₁ • v₁ + a₂ • v₂ + a₃ • v₃ = 0 →
    ‖a₁ • (H (n + v₁) - H n) + a₂ • (H (n + v₂) - H n) + a₃ • (H (n + v₃) - H n)‖ ≤
      K * (|a₁| * ‖v₁‖ ^ 2 + |a₂| * ‖v₂‖ ^ 2 + |a₃| * ‖v₃‖ ^ 2)

variable {H : E → F} {K : ℝ}

/-- The difference quotient `ℓ⁻¹ (H(n + ℓd) - H(n))`. -/
def diffQuot (H : E → F) (n d : E) (ℓ : ℝ) : F := ℓ⁻¹ • (H (n + ℓ • d) - H n)

theorem le_of_forall_pos_le_add_mul {x c C : ℝ} (h : ∀ ℓ : ℝ, 0 < ℓ → x ≤ c + C * ℓ) : x ≤ c := by
  by_contra hlt
  push Not at hlt
  rcases le_or_gt C 0 with hC | hC
  · have := h 1 one_pos; nlinarith
  · have h2 := h ((x - c) / (2 * C)) (div_pos (by linarith) (by positivity))
    have : C * ((x - c) / (2 * C)) = (x - c) / 2 := by field_simp
    linarith

theorem diffQuot_sub_le (hH : QuadDefect H K) (n d : E) {ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') :
    ‖diffQuot H n d ℓ - diffQuot H n d ℓ'‖ ≤ K * ‖d‖ ^ 2 * (ℓ + ℓ') := by
  have h := hH n (ℓ • d) (ℓ' • d) 0 ℓ⁻¹ (-ℓ'⁻¹) 0 (by
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hℓ.ne', neg_mul, inv_mul_cancel₀ hℓ'.ne']
    simp)
  simp only [zero_smul, add_zero, abs_zero, zero_mul, abs_neg, abs_inv, abs_of_pos hℓ,
    abs_of_pos hℓ', norm_smul, Real.norm_eq_abs] at h
  unfold diffQuot
  rw [sub_eq_add_neg, ← neg_smul]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- The (Gâteaux) derivative `Λ(n) d = lim_{ℓ → 0⁺} ℓ⁻¹ (H(n + ℓd) - H(n))`. -/
def quadDeriv (H : E → F) (n d : E) : F :=
  limUnder atTop fun k : ℕ => diffQuot H n d (1 / ((k : ℝ) + 1))

theorem tendsto_quadDeriv (hH : QuadDefect H K) (hK : 0 ≤ K) (n d : E) :
    Tendsto (fun k : ℕ => diffQuot H n d (1 / ((k : ℝ) + 1))) atTop (𝓝 (quadDeriv H n d)) := by
  refine CauchySeq.tendsto_limUnder ?_
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => K * ‖d‖ ^ 2 * (2 * (1 / ((N : ℝ) + 1))))
    (fun k m N hk hm => ?_) ?_
  · rw [dist_eq_norm]
    refine (diffQuot_sub_le hH n d (by positivity) (by positivity)).trans ?_
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    have : 0 ≤ K * ‖d‖ ^ 2 := by positivity
    nlinarith
  · have : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (this.const_mul 2).const_mul (K * ‖d‖ ^ 2)

theorem diffQuot_sub_quadDeriv_le (hH : QuadDefect H K) (hK : 0 ≤ K) (n d : E) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    ‖diffQuot H n d ℓ - quadDeriv H n d‖ ≤ K * ‖d‖ ^ 2 * ℓ := by
  have ht := tendsto_quadDeriv hH hK n d
  have hlim : Tendsto (fun k : ℕ => ‖diffQuot H n d ℓ - diffQuot H n d (1 / ((k : ℝ) + 1))‖)
      atTop (𝓝 ‖diffQuot H n d ℓ - quadDeriv H n d‖) :=
    (tendsto_const_nhds.sub ht).norm
  have hb : Tendsto (fun k : ℕ => K * ‖d‖ ^ 2 * (ℓ + 1 / ((k : ℝ) + 1))) atTop
      (𝓝 (K * ‖d‖ ^ 2 * (ℓ + 0))) :=
    (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).const_mul _
  rw [add_zero] at hb
  exact le_of_tendsto_of_tendsto hlim hb (Eventually.of_forall fun k =>
    diffQuot_sub_le hH n d hℓ (by positivity))

/-- **Second-order Taylor bound**: `‖H(n + d) - H(n) - Λ(n) d‖ ≤ K ‖d‖²`. -/
theorem quadDeriv_taylor (hH : QuadDefect H K) (hK : 0 ≤ K) (n d : E) :
    ‖H (n + d) - H n - quadDeriv H n d‖ ≤ K * ‖d‖ ^ 2 := by
  have := diffQuot_sub_quadDeriv_le hH hK n d one_pos
  simpa [diffQuot] using this

/-- `Λ(n)` is linear: `Λ(n)(a d + b e) = a Λ(n) d + b Λ(n) e`. -/
theorem quadDeriv_comb (hH : QuadDefect H K) (hK : 0 ≤ K) (n d e : E) (a b : ℝ) :
    quadDeriv H n (a • d + b • e) = a • quadDeriv H n d + b • quadDeriv H n e := by
  set X := quadDeriv H n (a • d + b • e) - (a • quadDeriv H n d + b • quadDeriv H n e)
  have hX : ‖X‖ ≤ 0 := by
    refine le_of_forall_pos_le_add_mul (C := 2 * K * (‖a • d + b • e‖ ^ 2 + |a| * ‖d‖ ^ 2 +
      |b| * ‖e‖ ^ 2)) fun ℓ hℓ => ?_
    have h3 := hH n (ℓ • (a • d + b • e)) (ℓ • d) (ℓ • e) ℓ⁻¹ (-(a * ℓ⁻¹)) (-(b * ℓ⁻¹)) (by
      simp only [smul_smul, smul_add]
      rw [show ℓ⁻¹ * (ℓ * a) = a by field_simp, show ℓ⁻¹ * (ℓ * b) = b by field_simp,
        show -(a * ℓ⁻¹) * ℓ = -a by field_simp, show -(b * ℓ⁻¹) * ℓ = -b by field_simp]
      simp only [neg_smul]; abel)
    have e3 : ℓ⁻¹ • (H (n + ℓ • (a • d + b • e)) - H n) + -(a * ℓ⁻¹) • (H (n + ℓ • d) - H n) +
        -(b * ℓ⁻¹) • (H (n + ℓ • e) - H n) =
        diffQuot H n (a • d + b • e) ℓ - (a • diffQuot H n d ℓ + b • diffQuot H n e ℓ) := by
      simp only [diffQuot, neg_smul, smul_smul, mul_comm a, mul_comm b]
      abel
    rw [e3] at h3
    have hd1 := diffQuot_sub_quadDeriv_le hH hK n (a • d + b • e) hℓ
    have hd2 := diffQuot_sub_quadDeriv_le hH hK n d hℓ
    have hd3 := diffQuot_sub_quadDeriv_le hH hK n e hℓ
    have eX : X = (diffQuot H n (a • d + b • e) ℓ - (a • diffQuot H n d ℓ + b • diffQuot H n e ℓ))
        - (diffQuot H n (a • d + b • e) ℓ - quadDeriv H n (a • d + b • e))
        + a • (diffQuot H n d ℓ - quadDeriv H n d) + b • (diffQuot H n e ℓ - quadDeriv H n e) := by
      simp only [X, smul_sub]; abel
    have hnorm : ‖X‖ ≤ ‖diffQuot H n (a • d + b • e) ℓ - (a • diffQuot H n d ℓ +
        b • diffQuot H n e ℓ)‖ + ‖diffQuot H n (a • d + b • e) ℓ - quadDeriv H n (a • d + b • e)‖
        + |a| * ‖diffQuot H n d ℓ - quadDeriv H n d‖ + |b| * ‖diffQuot H n e ℓ - quadDeriv H n e‖ := by
      rw [eX]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (norm_sub_le _ _) (by rw [norm_smul, Real.norm_eq_abs]))) (by rw [norm_smul, Real.norm_eq_abs]))
    have hR : K * (|ℓ⁻¹| * ‖ℓ • (a • d + b • e)‖ ^ 2 + |-(a * ℓ⁻¹)| * ‖ℓ • d‖ ^ 2 +
        |-(b * ℓ⁻¹)| * ‖ℓ • e‖ ^ 2) =
        K * ℓ * (‖a • d + b • e‖ ^ 2 + |a| * ‖d‖ ^ 2 + |b| * ‖e‖ ^ 2) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_inv, abs_of_pos hℓ]
      field_simp
    rw [hR] at h3
    have h3' := h3
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    calc ‖X‖ ≤ _ := hnorm
      _ ≤ K * ℓ * (‖a • d + b • e‖ ^ 2 + |a| * ‖d‖ ^ 2 + |b| * ‖e‖ ^ 2) +
            K * ‖a • d + b • e‖ ^ 2 * ℓ + |a| * (K * ‖d‖ ^ 2 * ℓ) + |b| * (K * ‖e‖ ^ 2 * ℓ) := by
          gcongr
      _ = 0 + 2 * K * (‖a • d + b • e‖ ^ 2 + |a| * ‖d‖ ^ 2 + |b| * ‖e‖ ^ 2) * ℓ := by ring
  have : X = 0 := norm_le_zero_iff.mp hX
  exact sub_eq_zero.mp this

theorem quadDeriv_norm_le (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n d : E) :
    ‖quadDeriv H n d‖ ≤ C₀ * ‖d‖ := by
  refine le_of_forall_pos_le_add_mul (C := K * ‖d‖ ^ 2) fun ℓ hℓ => ?_
  have h1 := diffQuot_sub_quadDeriv_le hH hK n d hℓ
  have h2 : ‖diffQuot H n d ℓ‖ ≤ C₀ * ‖d‖ := by
    unfold diffQuot
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
    have := hlip (n + ℓ • d) n
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at this
    rw [inv_mul_le_iff₀ hℓ]
    linarith
  calc ‖quadDeriv H n d‖ ≤ ‖diffQuot H n d ℓ‖ + ‖diffQuot H n d ℓ - quadDeriv H n d‖ := by
        have := norm_sub_le (diffQuot H n d ℓ) (diffQuot H n d ℓ - quadDeriv H n d)
        simpa using this
    _ ≤ C₀ * ‖d‖ + K * ‖d‖ ^ 2 * ℓ := add_le_add h2 h1

/-- `Λ(n)` as a continuous linear map. -/
def quadDerivCLM (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n : E) : E →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := quadDeriv H n
      map_add' := fun d e => by simpa using quadDeriv_comb hH hK n d e 1 1
      map_smul' := fun c d => by simpa using quadDeriv_comb hH hK n d 0 c 0 }
    C₀ (fun d => quadDeriv_norm_le hH hK hlip n d)

theorem quadDerivCLM_apply (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n d : E) :
    quadDerivCLM hH hK hlip n d = quadDeriv H n d := rfl

/-- **Differentiability**: `H` has Fréchet derivative `Λ(n)` at every `n`. -/
theorem quadDeriv_hasFDerivAt (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n : E) :
    HasFDerivAt H (quadDerivCLM hH hK hlip n) n := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun d => H (n + d) - H n - quadDerivCLM hH hK hlip n d) =O[𝓝 0]
      fun d : E => ‖d‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K (Eventually.of_forall fun d => ?_)
    rw [quadDerivCLM_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact quadDeriv_taylor hH hK n d
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

theorem quadDeriv_sub_apply_le (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n v e : E) :
    ‖quadDerivCLM hH hK hlip (n + v) e - quadDerivCLM hH hK hlip n e‖ ≤
      K * (‖e‖ ^ 2 + ‖v + e‖ ^ 2 + ‖v‖ ^ 2) := by
  simp only [quadDerivCLM_apply]
  have hA := quadDeriv_taylor hH hK (n + v) e
  have hB := quadDeriv_taylor hH hK n (v + e)
  have hC := quadDeriv_taylor hH hK n v
  have hlin : quadDeriv H n (v + e) = quadDeriv H n v + quadDeriv H n e := by
    simpa using quadDeriv_comb hH hK n v e 1 1
  have e1 : quadDeriv H (n + v) e - quadDeriv H n e =
      -(H (n + v + e) - H (n + v) - quadDeriv H (n + v) e) +
        (H (n + (v + e)) - H n - quadDeriv H n (v + e)) -
        (H (n + v) - H n - quadDeriv H n v) := by
    rw [hlin, ← add_assoc]; abel
  rw [e1]
  calc ‖-(H (n + v + e) - H (n + v) - quadDeriv H (n + v) e) +
        (H (n + (v + e)) - H n - quadDeriv H n (v + e)) - (H (n + v) - H n - quadDeriv H n v)‖
      ≤ ‖H (n + v + e) - H (n + v) - quadDeriv H (n + v) e‖ +
        ‖H (n + (v + e)) - H n - quadDeriv H n (v + e)‖ +
        ‖H (n + v) - H n - quadDeriv H n v‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (by rw [norm_neg]) le_rfl)) le_rfl)
    _ ≤ K * ‖e‖ ^ 2 + K * ‖v + e‖ ^ 2 + K * ‖v‖ ^ 2 := add_le_add (add_le_add hA hB) hC
    _ = K * (‖e‖ ^ 2 + ‖v + e‖ ^ 2 + ‖v‖ ^ 2) := by ring

/-- **The derivative is Lipschitz**: `‖Λ(n') - Λ(n)‖ ≤ 6K ‖n' - n‖`. -/
theorem quadDeriv_lipschitz (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) (n n' : E) :
    ‖quadDerivCLM hH hK hlip n' - quadDerivCLM hH hK hlip n‖ ≤ 6 * K * ‖n' - n‖ := by
  set v := n' - n
  have hn' : n' = n + v := by simp [v]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  rw [sub_apply, hn']
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  rcases eq_or_ne e 0 with he | he
  · simp [he]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
  set c : ℝ := ‖v‖ / ‖e‖
  have hc : 0 < c := div_pos hvn hen
  have hce : ‖c • e‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]; simp only [c]; field_simp
  have h := quadDeriv_sub_apply_le hH hK hlip n v (c • e)
  have hve : ‖v + c • e‖ ≤ 2 * ‖v‖ := (norm_add_le _ _).trans (by rw [hce]; linarith)
  have hve2 : ‖v + c • e‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by nlinarith [norm_nonneg (v + c • e)]
  rw [map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc, hce] at h
  have h2 : c * ‖quadDerivCLM hH hK hlip (n + v) e - quadDerivCLM hH hK hlip n e‖ ≤
      6 * K * ‖v‖ ^ 2 := by nlinarith
  have h3 : ‖quadDerivCLM hH hK hlip (n + v) e - quadDerivCLM hH hK hlip n e‖ ≤
      6 * K * ‖v‖ ^ 2 / c := by rw [le_div_iff₀ hc, mul_comm]; exact h2
  refine h3.trans (le_of_eq ?_)
  simp only [c]; field_simp

/-- **A function with uniform quadratic three-point defects is `C¹`** (indeed `C^{1,1}`). -/
theorem contDiff_one_of_quadDefect (hH : QuadDefect H K) (hK : 0 ≤ K) {C₀ : ℝ}
    (hlip : ∀ n n', ‖H n - H n'‖ ≤ C₀ * ‖n - n'‖) : ContDiff ℝ 1 H := by
  have hD : ∀ n, HasFDerivAt H (quadDerivCLM hH hK hlip n) n := quadDeriv_hasFDerivAt hH hK hlip
  have hfd : fderiv ℝ H = quadDerivCLM hH hK hlip := funext fun n => (hD n).fderiv
  refine contDiff_one_iff_fderiv.mpr ⟨fun n => (hD n).differentiableAt, ?_⟩
  rw [hfd]
  have hL : LipschitzWith ⟨6 * K, by positivity⟩ (quadDerivCLM hH hK hlip) :=
    LipschitzWith.of_dist_le_mul fun n n' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact quadDeriv_lipschitz hH hK hlip n' n
  exact hL.continuous

end QuadraticDefect

/-! ### A priori bound for the linearised Lyapunov–Perron equation -/

section Apriori

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β κ L : ℝ}

/-- **A priori bound in the weight `κ`.**  Let `B_u, B_n` be continuous coefficient families of
norm `≤ L` and `q_κ = M L ((κ-α)⁻¹ + (β-κ)⁻¹) < 1`.  If a continuous `z` of some growth
`‖z(r)‖ ≤ Z e^{κr}` satisfies `‖z(t) - ℒz(t)‖ ≤ σ e^{κt}` on `[0, ∞)`, where
`ℒz = srcOp (B z)` is the linearised Lyapunov–Perron operator, then
`‖z(t)‖ ≤ σ/(1 - q_κ) e^{κt}`. -/
theorem apriori_le (hPuc : Continuous Pu) (hPnc : Continuous Pn) (hακ : α < κ) (hκβ : κ < β)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s))
    (hPn : ∀ s, 0 ≤ s → ‖Pn s‖ ≤ M * exp (α * s))
    (hq : M * L * ((κ - α)⁻¹ + (β - κ)⁻¹) < 1)
    {Bu : ℝ → (U × Nn) →L[ℝ] U} {Bn : ℝ → (U × Nn) →L[ℝ] Nn} (hBu : Continuous Bu)
    (hBn : Continuous Bn) (hBub : ∀ r, ‖Bu r‖ ≤ L) (hBnb : ∀ r, ‖Bn r‖ ≤ L)
    {z : ℝ → U × Nn} (hz : Continuous z) {Z σ : ℝ} (hZ : ∀ r, 0 ≤ r → ‖z r‖ ≤ Z * exp (κ * r))
    (hσ : 0 ≤ σ)
    (hE : ∀ t, 0 ≤ t → ‖z t - srcOp Pu Pn (fun r => (Bu r (z r), Bn r (z r))) t‖ ≤
      σ * exp (κ * t)) {t : ℝ} (ht : 0 ≤ t) :
    ‖z t‖ ≤ σ / (1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) * exp (κ * t) := by
  set c := (κ - α)⁻¹ + (β - κ)⁻¹ with hc
  have hc0 : 0 ≤ c := by
    have h1 : 0 < κ - α := sub_pos.mpr hακ
    have h2 : 0 < β - κ := sub_pos.mpr hκβ
    positivity
  set q := M * L * c
  have hq0 : 0 ≤ q := by positivity
  have h1q : 0 < 1 - q := by linarith
  set Z' := max Z 0
  have hcont : Continuous fun r => (Bu r (z r), Bn r (z r)) :=
    (hBu.clm_apply hz).prodMk (hBn.clm_apply hz)
  have hsrc : ∀ r, ‖(Bu r (z r), Bn r (z r))‖ ≤ L * ‖z r‖ := fun r => by
    rw [Prod.norm_def]
    exact max_le (((Bu r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBub r) (norm_nonneg _)))
      (((Bn r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBnb r) (norm_nonneg _)))
  have hiter : ∀ k : ℕ, ∀ t, 0 ≤ t → ‖z t‖ ≤ (q ^ k * Z' + σ / (1 - q)) * exp (κ * t) := by
    intro k
    induction k with
    | zero =>
      intro t ht
      refine (hZ t ht).trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
      have : 0 ≤ σ / (1 - q) := div_nonneg hσ h1q.le
      simp only [pow_zero, one_mul]
      linarith [le_max_left Z 0]
    | succ k ih =>
      intro t ht
      set m := q ^ k * Z' + σ / (1 - q)
      have hm : 0 ≤ m := by
        have : 0 ≤ Z' := le_max_right _ _
        have : 0 ≤ σ / (1 - q) := div_nonneg hσ h1q.le
        positivity
      have hS : ∀ r, 0 ≤ r → ‖(Bu r (z r), Bn r (z r))‖ ≤ (L * m) * exp (κ * r) := fun r hr =>
        (hsrc r).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (ih r hr) hL)
      have hlin := srcOp_norm_le hPuc hPnc hακ hκβ hM hPu hPn hcont hS ht
      calc ‖z t‖ ≤ ‖z t - srcOp Pu Pn (fun r => (Bu r (z r), Bn r (z r))) t‖ +
            ‖srcOp Pu Pn (fun r => (Bu r (z r), Bn r (z r))) t‖ :=
            (norm_le_insert' _ _).trans (le_of_eq (add_comm _ _))
        _ ≤ σ * exp (κ * t) + M * (L * m) * c * exp (κ * t) := add_le_add (hE t ht) hlin
        _ = (σ + q * m) * exp (κ * t) := by simp only [q, c]; ring
        _ = (q ^ (k + 1) * Z' + σ / (1 - q)) * exp (κ * t) := by
            congr 1
            simp only [m]
            field_simp
            ring
  have hlim : Tendsto (fun k : ℕ => (q ^ k * Z' + σ / (1 - q)) * exp (κ * t)) atTop
      (𝓝 ((0 * Z' + σ / (1 - q)) * exp (κ * t))) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const _).add_const _).mul_const _
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun k => hiter k t ht)

end Apriori

/-! ### The `C¹` layer of the invariant graph -/

section Diff

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- Hypotheses of the `C¹` layer of `lem:supp-exact-graph-criterion`: the nonlinearities are
differentiable with `L₂`-Lipschitz derivatives (bounded second derivatives), and the `j = 2`
inequality of `eq:supp-exact-graph-contraction` holds, with `2ν < β`. -/
structure GraphC1Hyp (h : GraphHyp Pu Pn M α β ν L Nu Nv)
    (DNu : U × Nn → (U × Nn) →L[ℝ] U) (DNv : U × Nn → (U × Nn) →L[ℝ] Nn) (L₂ : ℝ) : Prop where
  hasDeriv_u : ∀ x, HasFDerivAt Nu (DNu x) x
  hasDeriv_v : ∀ x, HasFDerivAt Nv (DNv x) x
  L₂_nonneg : 0 ≤ L₂
  Du_lip : ∀ x x', ‖DNu x - DNu x'‖ ≤ L₂ * ‖x - x'‖
  Dv_lip : ∀ x x', ‖DNv x - DNv x'‖ ≤ L₂ * ‖x - x'‖
  two_lt : 2 * ν < β
  contr2 : M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) < 1

namespace GraphC1Hyp

variable {h : GraphHyp Pu Pn M α β ν L Nu Nv} {DNu : U × Nn → (U × Nn) →L[ℝ] U}
  {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}

theorem norm_DNu_le (hd : GraphC1Hyp h DNu DNv L₂) (x : U × Nn) : ‖DNu x‖ ≤ L := by
  have := (hd.hasDeriv_u x).le_of_lipschitz (C := ⟨L, h.L_nonneg⟩)
    (LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; exact h.Nu_lip a b)
  exact this

theorem norm_DNv_le (hd : GraphC1Hyp h DNu DNv L₂) (x : U × Nn) : ‖DNv x‖ ≤ L := by
  have := (hd.hasDeriv_v x).le_of_lipschitz (C := ⟨L, h.L_nonneg⟩)
    (LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; exact h.Nv_lip a b)
  exact this

theorem continuous_DNu (hd : GraphC1Hyp h DNu DNv L₂) : Continuous DNu :=
  GraphHyp.lip_continuous hd.Du_lip

theorem continuous_DNv (hd : GraphC1Hyp h DNu DNv L₂) : Continuous DNv :=
  GraphHyp.lip_continuous hd.Dv_lip

/-- Second-order Taylor remainder of a map with `L₂`-Lipschitz derivative. -/
theorem taylor_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} {Df : E → E →L[ℝ] G} {L₂ : ℝ} (hL₂ : 0 ≤ L₂)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (x w : E) : ‖f (x + w) - f x - Df x w‖ ≤ L₂ * ‖w‖ ^ 2 := by
  have hconv : Convex ℝ (Metric.closedBall x ‖w‖) := convex_closedBall _ _
  have hder : ∀ z ∈ Metric.closedBall x ‖w‖, HasFDerivWithinAt (fun z => f z - Df x z)
      (Df z - Df x) (Metric.closedBall x ‖w‖) z :=
    fun z _ => ((hf z).sub (Df x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall x ‖w‖, ‖Df z - Df x‖ ≤ L₂ * ‖w‖ := fun z hz =>
    (hDf z x).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hz) hL₂)
  have hxw : x + w ∈ Metric.closedBall x ‖w‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb
    (Metric.mem_closedBall_self (norm_nonneg w)) hxw
  rw [add_sub_cancel_left, map_add] at this
  calc ‖f (x + w) - f x - Df x w‖ = ‖f (x + w) - (Df x x + Df x w) - (f x - Df x x)‖ := by
        congr 1; abel
    _ ≤ L₂ * ‖w‖ * ‖w‖ := this
    _ = L₂ * ‖w‖ ^ 2 := by ring

end GraphC1Hyp

/-- Weighted distance of the fixed points: `dist(g_*(n₀), g_*(n₀')) ≤ M/(1-q) ‖n₀ - n₀'‖`. -/
theorem dist_gStar_le (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ n₀' : Nn) :
    dist (gStar h bu bn n₀) (gStar h bu bn n₀') ≤ M / (1 - h.q) * ‖n₀ - n₀'‖ := by
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
  calc _ ≤ M * ‖n₀ - n₀'‖ / (1 - h.q) := hd
    _ = M / (1 - h.q) * ‖n₀ - n₀'‖ := by ring

theorem norm_yStar_sub_le (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ n₀' : Nn)
    (r : ℝ) : ‖yStar h bu bn n₀ r - yStar h bu bn n₀' r‖ ≤
      M / (1 - h.q) * ‖n₀ - n₀'‖ * exp (ν * r) :=
  (norm_wt_sub_le ν _ _ r).trans
    (mul_le_mul_of_nonneg_right (dist_gStar_le h bu bn n₀ n₀') (exp_pos _).le)

/-- The difference of two forward weighted trajectories solves
`w(t) = (0, P_n(t) v) + srcOp (N(y₁) - N(y₀))(t)` on `[0, ∞)`. -/
theorem yStar_sub_eq (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ v : Nn)
    {t : ℝ} (ht : 0 ≤ t) :
    yStar h bu bn (n₀ + v) t - yStar h bu bn n₀ t = ((0 : U), Pn t v) +
      srcOp Pu Pn (fun r => (Nu (yStar h bu bn (n₀ + v) r) - Nu (yStar h bu bn n₀ r),
        Nv (yStar h bu bn (n₀ + v) r) - Nv (yStar h bu bn n₀ r))) t := by
  set y₁ := yStar h bu bn (n₀ + v)
  set y₀ := yStar h bu bn n₀
  have e1 : y₁ t = lpMap Pu Pn bu bn Nu Nv (n₀ + v) y₁ t := yStar_eq_lpMap h bu bn (n₀ + v) ht
  have e0 : y₀ t = lpMap Pu Pn bu bn Nu Nv n₀ y₀ t := yStar_eq_lpMap h bu bn n₀ ht
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact h.Nu_lip x x'
  have hgv : Continuous fun x : U × Nn => bn + Nv x :=
    continuous_const.add (GraphHyp.lip_continuous h.Nv_lip)
  have hI₁ := backward_integrable (t := t) h.Pu_cont h.ν_pos h.lt_β h.M_nonneg h.L_nonneg ht
    h.Pu_bound (fun x => bu + Nu x) hgu (yStar_continuous h bu bn (n₀ + v))
    (fun r _ => norm_yStar_le h bu bn (n₀ + v) r)
  have hI₀ := backward_integrable (t := t) h.Pu_cont h.ν_pos h.lt_β h.M_nonneg h.L_nonneg ht
    h.Pu_bound (fun x => bu + Nu x) hgu (yStar_continuous h bu bn n₀)
    (fun r _ => norm_yStar_le h bu bn n₀ r)
  have hF : ∀ y : ℝ → U × Nn, Continuous y →
      IntervalIntegrable (fun r => Pn (t - r) (bn + Nv (y r))) volume 0 t := fun y hy =>
    ((h.Pn_cont.comp (continuous_const.sub continuous_id)).clm_apply
      (hgv.comp hy)).intervalIntegrable _ _
  rw [e1, e0]
  simp only [lpMap, srcOp]
  ext
  · simp only [Prod.fst_sub, Prod.fst_add, zero_add]
    rw [neg_sub_neg, ← integral_sub hI₀ hI₁, ← MeasureTheory.integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [map_sub, map_add]
    abel
  · simp only [Prod.snd_sub, Prod.snd_add]
    rw [add_sub_add_comm, ← intervalIntegral.integral_sub
      (hF y₁ (yStar_continuous h bu bn (n₀ + v))) (hF y₀ (yStar_continuous h bu bn n₀)),
      (Pn t).map_add n₀ v, add_sub_cancel_left]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [map_sub, map_add]
    abel

end Diff

/-! ### The graph has uniform quadratic three-point defects, hence is `C¹` -/

section Main

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}

namespace GraphC1Hyp

/-- The uniform constant `K = M L₂ (M/(1-q))² c₂ / (1 - q₂)`, `c₂ = (2ν-α)⁻¹ + (β-2ν)⁻¹`,
`q₂ = M L c₂`. -/
def K (_ : GraphC1Hyp h DNu DNv L₂) : ℝ :=
  M * L₂ * (M / (1 - h.q)) ^ 2 * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) /
    (1 - M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹))

theorem K_nonneg (hd : GraphC1Hyp h DNu DNv L₂) : 0 ≤ hd.K := by
  have h1 : 0 < 2 * ν - α := by linarith [h.α_lt, h.ν_pos]
  have h2 : 0 < β - 2 * ν := by linarith [hd.two_lt]
  have h3 : 0 < 1 - M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) := by linarith [hd.contr2]
  have := h.M_nonneg
  have := hd.L₂_nonneg
  unfold K
  positivity

end GraphC1Hyp

/-- **The graph has uniform quadratic three-point defects**: for every base point `n₀` and every
combination `a₁v₁ + a₂v₂ + a₃v₃ = 0`,
`‖Σ aᵢ (h(n₀ + vᵢ) - h(n₀))‖ ≤ K Σ |aᵢ| ‖vᵢ‖²`.  Proof: `z = Σ aᵢ (y_*(n₀+vᵢ) - y_*(n₀))`
solves the linearised Lyapunov–Perron equation up to second-order Taylor remainders, which are
sources of growth `e^{2νt}`; the a priori bound in the weight `2ν` (`j = 2` inequality) at
`t = 0` gives the claim. -/
theorem graphMap_quadDefect (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) :
    QuadDefect (graphMap h bu bn) hd.K := by
  intro n₀ v₁ v₂ v₃ a₁ a₂ a₃ hsum
  set y₀ := yStar h bu bn n₀ with hy₀
  set C1 := M / (1 - h.q) with hC1def
  set c2 := (2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹ with hc2def
  have hν := h.ν_pos
  have h2α : α < 2 * ν := by linarith [h.α_lt]
  have h2β := hd.two_lt
  have hC1 : 0 ≤ C1 := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hexp : ∀ r : ℝ, 0 ≤ r → exp (ν * r) ≤ exp (2 * ν * r) := fun r hr =>
    exp_le_exp.2 (by nlinarith)
  have hexp2 : ∀ r : ℝ, exp (ν * r) ^ 2 = exp (2 * ν * r) := fun r => by
    rw [← exp_nat_mul]; ring_nf
  set w : Nn → ℝ → U × Nn := fun v r => yStar h bu bn (n₀ + v) r - y₀ r with hwdef
  set lin : (ℝ → U × Nn) → ℝ → U × Nn := fun z r => (DNu (y₀ r) (z r), DNv (y₀ r) (z r))
    with hlindef
  have hy0c : Continuous y₀ := yStar_continuous h bu bn n₀
  have hw_cont : ∀ v, Continuous (w v) := fun v =>
    (yStar_continuous h bu bn (n₀ + v)).sub hy0c
  have hw_bd1 : ∀ v r, ‖w v r‖ ≤ C1 * ‖v‖ * exp (ν * r) := by
    intro v r
    have := norm_yStar_sub_le h bu bn (n₀ + v) n₀ r
    rwa [add_sub_cancel_left] at this
  have hw_bd : ∀ v r, 0 ≤ r → ‖w v r‖ ≤ (C1 * ‖v‖) * exp (2 * ν * r) := fun v r hr =>
    (hw_bd1 v r).trans (mul_le_mul_of_nonneg_left (hexp r hr) (by positivity))
  have hBu : Continuous fun r => DNu (y₀ r) := hd.continuous_DNu.comp hy0c
  have hBn : Continuous fun r => DNv (y₀ r) := hd.continuous_DNv.comp hy0c
  have hlin_cont : ∀ z : ℝ → U × Nn, Continuous z → Continuous (lin z) := fun z hz =>
    (hBu.clm_apply hz).prodMk (hBn.clm_apply hz)
  have hlin_pt : ∀ z r, ‖lin z r‖ ≤ L * ‖z r‖ := fun z r => by
    simp only [hlindef]
    rw [Prod.norm_def]
    exact max_le (((DNu (y₀ r)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hd.norm_DNu_le _) (norm_nonneg _)))
      (((DNv (y₀ r)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hd.norm_DNv_le _) (norm_nonneg _)))
  have hlin_bd : ∀ (z : ℝ → U × Nn) (Z : ℝ), (∀ r, 0 ≤ r → ‖z r‖ ≤ Z * exp (2 * ν * r)) →
      ∀ r, 0 ≤ r → ‖lin z r‖ ≤ (L * Z) * exp (2 * ν * r) := fun z Z hz r hr =>
    (hlin_pt z r).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hz r hr) h.L_nonneg)
  -- the residual of each direction
  have hres : ∀ v t, 0 ≤ t → ‖w v t - ((0 : U), Pn t v) - srcOp Pu Pn (lin (w v)) t‖ ≤
      M * (L₂ * (C1 * ‖v‖) ^ 2) * c2 * exp (2 * ν * t) := by
    intro v t ht
    set yv := yStar h bu bn (n₀ + v)
    set R : ℝ → U × Nn := fun r => (Nu (yv r) - Nu (y₀ r) - DNu (y₀ r) (w v r),
      Nv (yv r) - Nv (y₀ r) - DNv (y₀ r) (w v r)) with hRdef
    have hNu_c : Continuous Nu := GraphHyp.lip_continuous h.Nu_lip
    have hNv_c : Continuous Nv := GraphHyp.lip_continuous h.Nv_lip
    have hyvc : Continuous yv := yStar_continuous h bu bn (n₀ + v)
    have hRc : Continuous R :=
      (((hNu_c.comp hyvc).sub (hNu_c.comp hy0c)).sub (hBu.clm_apply (hw_cont v))).prodMk
        (((hNv_c.comp hyvc).sub (hNv_c.comp hy0c)).sub (hBn.clm_apply (hw_cont v)))
    have hRb : ∀ r, 0 ≤ r → ‖R r‖ ≤ (L₂ * (C1 * ‖v‖) ^ 2) * exp (2 * ν * r) := by
      intro r hr
      have hyv : yv r = y₀ r + w v r := by simp [hwdef, yv]
      have hsq : L₂ * ‖w v r‖ ^ 2 ≤ L₂ * (C1 * ‖v‖) ^ 2 * exp (2 * ν * r) := by
        rw [mul_assoc, ← hexp2, ← mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hw_bd1 v r) 2)
          hd.L₂_nonneg
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · simp only [hRdef]
        rw [hyv]
        exact (GraphC1Hyp.taylor_le hd.L₂_nonneg hd.hasDeriv_u hd.Du_lip _ _).trans hsq
      · simp only [hRdef]
        rw [hyv]
        exact (GraphC1Hyp.taylor_le hd.L₂_nonneg hd.hasDeriv_v hd.Dv_lip _ _).trans hsq
    have hsplit : (fun r => (Nu (yv r) - Nu (y₀ r), Nv (yv r) - Nv (y₀ r))) = lin (w v) + R := by
      funext r
      simp only [hlindef, hRdef, Pi.add_apply, Prod.mk_add_mk]
      ext <;> simp
    have heq : w v t = ((0 : U), Pn t v) +
        srcOp Pu Pn (fun r => (Nu (yv r) - Nu (y₀ r), Nv (yv r) - Nv (y₀ r))) t :=
      yStar_sub_eq h bu bn n₀ v ht
    rw [hsplit, srcOp_add h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound
      (hlin_cont _ (hw_cont v)) hRc (hlin_bd _ _ (hw_bd v)) hRb ht] at heq
    have e : w v t - ((0 : U), Pn t v) - srcOp Pu Pn (lin (w v)) t = srcOp Pu Pn R t := by
      rw [heq]; abel
    rw [e]
    exact srcOp_norm_le h.Pu_cont h.Pn_cont h2α h2β h.M_nonneg h.Pu_bound h.Pn_bound hRc hRb ht
  -- the combination
  set z : ℝ → U × Nn := fun r => a₁ • w v₁ r + a₂ • w v₂ r + a₃ • w v₃ r with hzdef
  have hzc : Continuous z :=
    (((hw_cont v₁).const_smul a₁).add ((hw_cont v₂).const_smul a₂)).add
      ((hw_cont v₃).const_smul a₃)
  set Z := |a₁| * (C1 * ‖v₁‖) + |a₂| * (C1 * ‖v₂‖) + |a₃| * (C1 * ‖v₃‖)
  have hsm : ∀ (a : ℝ) (v : Nn) r, 0 ≤ r → ‖a • w v r‖ ≤ (|a| * (C1 * ‖v‖)) * exp (2 * ν * r) :=
    fun a v r hr => by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hw_bd v r hr) (abs_nonneg a)
  have hzb : ∀ r, 0 ≤ r → ‖z r‖ ≤ Z * exp (2 * ν * r) := fun r hr => by
    calc ‖z r‖ ≤ ‖a₁ • w v₁ r‖ + ‖a₂ • w v₂ r‖ + ‖a₃ • w v₃ r‖ := norm_add₃_le
      _ ≤ _ := add_le_add (add_le_add (hsm a₁ v₁ r hr) (hsm a₂ v₂ r hr)) (hsm a₃ v₃ r hr)
      _ = Z * exp (2 * ν * r) := by ring
  have hlin_z : lin z = a₁ • lin (w v₁) + a₂ • lin (w v₂) + a₃ • lin (w v₃) := by
    funext r
    simp only [hlindef, hzdef, Pi.add_apply, Pi.smul_apply, map_add, map_smul, Prod.smul_mk,
      Prod.mk_add_mk]
  have hsmc : ∀ (a : ℝ) (v : Nn), Continuous (a • lin (w v)) := fun a v =>
    (hlin_cont _ (hw_cont v)).const_smul a
  have hsmb : ∀ (a : ℝ) (v : Nn) r, 0 ≤ r →
      ‖(a • lin (w v)) r‖ ≤ (|a| * (L * (C1 * ‖v‖))) * exp (2 * ν * r) := fun a v r hr => by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlin_bd _ _ (hw_bd v) r hr) (abs_nonneg a)
  have hsrc_z : ∀ t, 0 ≤ t → srcOp Pu Pn (lin z) t = a₁ • srcOp Pu Pn (lin (w v₁)) t +
      a₂ • srcOp Pu Pn (lin (w v₂)) t + a₃ • srcOp Pu Pn (lin (w v₃)) t := by
    intro t ht
    have hb12 : ∀ r, 0 ≤ r → ‖(a₁ • lin (w v₁) + a₂ • lin (w v₂)) r‖ ≤
        (|a₁| * (L * (C1 * ‖v₁‖)) + |a₂| * (L * (C1 * ‖v₂‖))) * exp (2 * ν * r) :=
      fun r hr => (norm_add_le _ _).trans (by
        rw [add_mul]; exact add_le_add (hsmb a₁ v₁ r hr) (hsmb a₂ v₂ r hr))
    rw [hlin_z, srcOp_add h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound
      ((hsmc a₁ v₁).add (hsmc a₂ v₂)) (hsmc a₃ v₃) hb12 (hsmb a₃ v₃) ht,
      srcOp_add h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound (hsmc a₁ v₁) (hsmc a₂ v₂)
        (hsmb a₁ v₁) (hsmb a₂ v₂) ht, srcOp_smul, srcOp_smul, srcOp_smul]
  set σ := |a₁| * (M * (L₂ * (C1 * ‖v₁‖) ^ 2) * c2) + |a₂| * (M * (L₂ * (C1 * ‖v₂‖) ^ 2) * c2) +
    |a₃| * (M * (L₂ * (C1 * ‖v₃‖) ^ 2) * c2) with hσdef
  have hc2 : 0 ≤ c2 := by
    have h1 : 0 < 2 * ν - α := by linarith
    have h2 : 0 < β - 2 * ν := by linarith
    positivity
  have hσ : 0 ≤ σ := by
    have := h.M_nonneg; have := hd.L₂_nonneg
    positivity
  have hE : ∀ t, 0 ≤ t → ‖z t - srcOp Pu Pn (lin z) t‖ ≤ σ * exp (2 * ν * t) := by
    intro t ht
    have hPsum : a₁ • ((0 : U), Pn t v₁) + a₂ • ((0 : U), Pn t v₂) + a₃ • ((0 : U), Pn t v₃) = 0 := by
      have : Pn t (a₁ • v₁ + a₂ • v₂ + a₃ • v₃) = 0 := by rw [hsum, map_zero]
      simp only [map_add, map_smul] at this
      ext
      · simp
      · simpa using this
    have hid : z t - srcOp Pu Pn (lin z) t =
        a₁ • (w v₁ t - ((0 : U), Pn t v₁) - srcOp Pu Pn (lin (w v₁)) t) +
        a₂ • (w v₂ t - ((0 : U), Pn t v₂) - srcOp Pu Pn (lin (w v₂)) t) +
        a₃ • (w v₃ t - ((0 : U), Pn t v₃) - srcOp Pu Pn (lin (w v₃)) t) := by
      rw [hsrc_z t ht]
      simp only [hzdef]
      linear_combination (norm := module) hPsum
    rw [hid]
    have hr : ∀ (a : ℝ) (v : Nn), ‖a • (w v t - ((0 : U), Pn t v) - srcOp Pu Pn (lin (w v)) t)‖ ≤
        |a| * (M * (L₂ * (C1 * ‖v‖) ^ 2) * c2) * exp (2 * ν * t) := fun a v => by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hres v t ht) (abs_nonneg a)
    calc _ ≤ _ := norm_add₃_le
      _ ≤ _ := add_le_add (add_le_add (hr a₁ v₁) (hr a₂ v₂)) (hr a₃ v₃)
      _ = σ * exp (2 * ν * t) := by ring
  have hap := apriori_le h.Pu_cont h.Pn_cont h2α h2β h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound
    hd.contr2 hBu hBn (fun r => hd.norm_DNu_le _) (fun r => hd.norm_DNv_le _) hzc hzb hσ hE le_rfl
  have hz0 : (z 0).1 = a₁ • (graphMap h bu bn (n₀ + v₁) - graphMap h bu bn n₀) +
      a₂ • (graphMap h bu bn (n₀ + v₂) - graphMap h bu bn n₀) +
      a₃ • (graphMap h bu bn (n₀ + v₃) - graphMap h bu bn n₀) := by
    simp [hzdef, hwdef, graphMap, hy₀]
  rw [← hz0]
  refine (norm_fst_le _).trans (hap.trans (le_of_eq ?_))
  have h3 : 0 < 1 - M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) := by linarith [hd.contr2]
  simp only [mul_zero, exp_zero, mul_one, hσdef, GraphC1Hyp.K, hC1def, hc2def]
  field_simp

/-- **The invariant graph is `C¹`** (`lem:supp-exact-graph-criterion`, first-order regularity):
under `GraphHyp` (`j = 1`) and `GraphC1Hyp` (Lipschitz derivatives of the nonlinearities, `j = 2`
inequality, `2ν < β`), the graph `h = graphMap` of the forward weighted trajectories is
continuously differentiable. -/
theorem graphMap_contDiff_one (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) :
    ContDiff ℝ 1 (graphMap h bu bn) :=
  contDiff_one_of_quadDefect (graphMap_quadDefect hd bu bn) hd.K_nonneg
    (graphMap_lipschitz h bu bn)

/-- The derivative of the graph: `Dh(n₀) = lim_{ℓ→0⁺} ℓ⁻¹ (h(n₀ + ℓ ·) - h(n₀))`. -/
def graphDeriv (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn) : Nn →L[ℝ] U :=
  quadDerivCLM (graphMap_quadDefect hd bu bn) hd.K_nonneg (graphMap_lipschitz h bu bn) n₀

theorem graphMap_hasFDerivAt (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn) :
    HasFDerivAt (graphMap h bu bn) (graphDeriv hd bu bn n₀) n₀ :=
  quadDeriv_hasFDerivAt _ _ _ n₀

/-- **Uniform second-order Taylor bound**: `‖h(n₀ + v) - h(n₀) - Dh(n₀) v‖ ≤ K ‖v‖²`. -/
theorem graphMap_taylor (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v : Nn) :
    ‖graphMap h bu bn (n₀ + v) - graphMap h bu bn n₀ - graphDeriv hd bu bn n₀ v‖ ≤
      hd.K * ‖v‖ ^ 2 :=
  quadDeriv_taylor (graphMap_quadDefect hd bu bn) hd.K_nonneg n₀ v

/-- **The derivative of the graph is Lipschitz**: `‖Dh(n) - Dh(n')‖ ≤ 6K ‖n - n'‖`. -/
theorem graphDeriv_lipschitz (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n n' : Nn) :
    ‖graphDeriv hd bu bn n' - graphDeriv hd bu bn n‖ ≤ 6 * hd.K * ‖n' - n‖ :=
  quadDeriv_lipschitz _ _ _ n n'

end Main

/-- Non-vacuity of the `C¹` layer: the example of `graphHyp_nonvacuous` (`ν = 1`, `β = 3`,
`L = 0`) with zero nonlinearities satisfies `GraphC1Hyp` (`2ν = 2 < 3`). -/
theorem graphC1Hyp_nonvacuous :
    GraphC1Hyp graphHyp_nonvacuous (fun _ => 0) (fun _ => 0) 0 where
  hasDeriv_u _ := hasFDerivAt_const _ _
  hasDeriv_v _ := hasFDerivAt_const _ _
  L₂_nonneg := le_rfl
  Du_lip _ _ := by simp
  Dv_lip _ _ := by simp
  two_lt := by norm_num
  contr2 := by norm_num

/-! ### The manuscript's propagators `e^{tA}` -/

/-- **The manuscript's setting is an instance of `GraphHyp`**: for bounded generators `A_u, A_n`,
the propagators `P_u(t) = e^{tA_u}`, `P_n(t) = e^{tA_n}` are continuous groups with `P(0) = 1`, so
the hypotheses of `lem:supp-exact-graph-criterion` (`‖e^{-tA_u}‖ ≤ M e^{-βt}`,
`‖e^{tA_n}‖ ≤ M e^{αt}`, Lipschitz nonlinearities, `j = 1` inequality) give `GraphHyp`. -/
theorem graphHyp_of_exp (Au : U →L[ℝ] U) (An : Nn →L[ℝ] Nn) {M α β ν L : ℝ}
    {Nu : U × Nn → U} {Nv : U × Nn → Nn} (hν : 0 < ν) (hαν : α < ν) (hνβ : ν < β) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hPu : ∀ s, 0 ≤ s → ‖NormedSpace.exp ((-s) • Au)‖ ≤ M * exp (-β * s))
    (hPn : ∀ s, 0 ≤ s → ‖NormedSpace.exp (s • An)‖ ≤ M * exp (α * s))
    (hNu : ∀ x x', ‖Nu x - Nu x'‖ ≤ L * ‖x - x'‖) (hNv : ∀ x x', ‖Nv x - Nv x'‖ ≤ L * ‖x - x'‖)
    (hcontr : M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) < 1) :
    GraphHyp (fun t => NormedSpace.exp (t • Au)) (fun t => NormedSpace.exp (t • An))
      M α β ν L Nu Nv where
  Pu_cont := (differentiable_exp_smul_const ℝ Au).continuous
  Pn_cont := (differentiable_exp_smul_const ℝ An).continuous
  Pu_add s t := by
    let _ : NormedAlgebra ℚ (U →L[ℝ] U) := NormedAlgebra.restrictScalars ℚ ℝ (U →L[ℝ] U)
    rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Au).smul_left s).smul_right t),
      ContinuousLinearMap.mul_def]
  Pn_add s t := by
    let _ : NormedAlgebra ℚ (Nn →L[ℝ] Nn) := NormedAlgebra.restrictScalars ℚ ℝ (Nn →L[ℝ] Nn)
    rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl An).smul_left s).smul_right t),
      ContinuousLinearMap.mul_def]
  Pu_zero := by rw [zero_smul, NormedSpace.exp_zero]; rfl
  Pn_zero := by rw [zero_smul, NormedSpace.exp_zero]; rfl
  ν_pos := hν
  α_lt := hαν
  lt_β := hνβ
  M_nonneg := hM
  L_nonneg := hL
  Pu_bound := hPu
  Pn_bound := hPn
  Nu_lip := hNu
  Nv_lip := hNv
  contr := hcontr

/-- The generator relations `P' = A P` used by `yStar_hasDerivAt` / `flow_mem_graph` hold for
`P(t) = e^{tA}`. -/
theorem hasDerivAt_exp_propagator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) (A * NormedSpace.exp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t

end

end LyapunovPerron
end RenewalGeometry
