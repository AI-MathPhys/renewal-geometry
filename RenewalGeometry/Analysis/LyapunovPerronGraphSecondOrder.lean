/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovPerronGraphDifferentiable

/-!
# `C²` regularity of the Lyapunov–Perron invariant graph

Fourth layer of the forward invariant-graph construction (`lem:supp-exact-graph-criterion`,
emergent-spacetime manuscript), on top of `Analysis/LyapunovPerronGraphDifferentiable.lean`
(`C¹` layer: `graphMap_contDiff_one`, `graphDeriv`, the quadratic-defect criterion
`contDiff_one_of_quadDefect`).

Under the `j = 3` inequality of `eq:supp-exact-graph-contraction`,
`M L ((3ν - α)⁻¹ + (β - 3ν)⁻¹) < 1` with `3ν < β`, and bounded third derivatives of the
nonlinearities (`D²N` Lipschitz, `GraphC2Hyp`), the derivative `Dh = graphDeriv` of the graph has
uniform quadratic three-point defects in operator norm, so `Dh` is `C¹` and **the graph is `C²`**
(`graphMap_contDiff_two`).  As in the manuscript, the sources of the second-order equation are
products of lower-order objects and live in the weight `3ν`:

* `srcOp_sum`, `trajDiff`, `linSrc`, `remSrc`, `trajDiff_eq`, `comb_eq`, `comb_le`: for
  `Σ cᵢ vᵢ = 0`, the combination `z = Σ cᵢ (y_*(n₀+vᵢ) - y_*(n₀))` solves the linearised
  Lyapunov–Perron equation with source `Σ cᵢ R_{vᵢ}` (second-order Taylor remainders), and the a
  priori bound in any admissible weight `κ ≥ ν` controls `z`;
* `traj_first` (first-level defect at every time, weight `2ν`), `traj_mixed` (mixed second
  differences `‖w_{v+e} - w_v - w_e‖ ≤ K₂(‖v‖‖e‖ + ‖e‖²) e^{2νt}`);
* `taylor_mixed_le`, `taylor_second_le`, `second_src_le`, `second_level_src_le`: the
  second-level source `Σ (aᵢ/ℓ)(R_{vᵢ+ℓd} - R_{vᵢ} - R_{ℓd})` is
  `O((‖d‖ Σ|aᵢ|‖vᵢ‖² + ℓ (…)) e^{3νt})`;
* `second_level_le`, `graphDeriv_quadDefect`, `graphMap_contDiff_two`;
* `graphC2Hyp_nonvacuous`.

Not covered: the `C³` layer (the third derivative's equation has sources involving `D³N`, which is
only assumed bounded, so the quadratic-defect route would need a fourth weight; the manuscript's
`C³` claim needs an `o(‖v‖)` argument with the strict spectral margins).
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

section Src

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M β κ : ℝ}

/-- `srcOp` commutes with finite linear combinations of continuous sources of growth `e^{κr}`. -/
theorem srcOp_sum (hPuc : Continuous Pu) (hPnc : Continuous Pn) (hκβ : κ < β) (hM : 0 ≤ M)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (S : ι → ℝ → U × Nn) (hS : ∀ i, Continuous (S i)) (σ : ι → ℝ)
    (hSb : ∀ i r, 0 ≤ r → ‖S i r‖ ≤ σ i * exp (κ * r)) {t : ℝ} (ht : 0 ≤ t) :
    srcOp Pu Pn (∑ i ∈ s, c i • S i) t = ∑ i ∈ s, c i • srcOp Pu Pn (S i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [srcOp]
  | insert a s ha ih =>
    have hc : Continuous (∑ i ∈ s, c i • S i) := by
      have : (∑ i ∈ s, c i • S i) = fun r => ∑ i ∈ s, c i • S i r := by
        funext r; simp [Finset.sum_apply]
      rw [this]
      exact continuous_finsetSum _ fun i _ => (hS i).const_smul (c i)
    have hb : ∀ r, 0 ≤ r → ‖(∑ i ∈ s, c i • S i) r‖ ≤
        (∑ i ∈ s, |c i| * σ i) * exp (κ * r) := by
      intro r hr
      rw [Finset.sum_apply, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hSb i r hr) (abs_nonneg _)
    have ha' : ∀ r, 0 ≤ r → ‖(c a • S a) r‖ ≤ (|c a| * σ a) * exp (κ * r) := by
      intro r hr
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hSb a r hr) (abs_nonneg _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, srcOp_add hPuc hPnc hκβ hM hPu
      ((hS a).const_smul (c a)) hc ha' hb ht, srcOp_smul, ih]

end Src

/-! ### Trajectory differences and their linearised equation -/

section Traj

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn}

/-- `w_v = y_*(n₀ + v) - y_*(n₀)`. -/
def trajDiff (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn) (n₀ v : Nn) :
    ℝ → U × Nn := fun r => yStar h bu bn (n₀ + v) r - yStar h bu bn n₀ r

/-- The linearised source `(DN_u(y₀) z, DN_n(y₀) z)`. -/
def linSrc (DNu : U × Nn → (U × Nn) →L[ℝ] U) (DNv : U × Nn → (U × Nn) →L[ℝ] Nn)
    (y₀ : ℝ → U × Nn) (z : ℝ → U × Nn) : ℝ → U × Nn :=
  fun r => (DNu (y₀ r) (z r), DNv (y₀ r) (z r))

/-- The second-order remainder source `N(y₀ + w_v) - N(y₀) - DN(y₀) w_v`. -/
def remSrc (h : GraphHyp Pu Pn M α β ν L Nu Nv) (bu : U) (bn : Nn)
    (DNu : U × Nn → (U × Nn) →L[ℝ] U) (DNv : U × Nn → (U × Nn) →L[ℝ] Nn) (n₀ v : Nn) :
    ℝ → U × Nn := fun r =>
  (Nu (yStar h bu bn (n₀ + v) r) - Nu (yStar h bu bn n₀ r) -
      DNu (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ v r),
    Nv (yStar h bu bn (n₀ + v) r) - Nv (yStar h bu bn n₀ r) -
      DNv (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ v r))

variable {h : GraphHyp Pu Pn M α β ν L Nu Nv} {DNu : U × Nn → (U × Nn) →L[ℝ] U}
  {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}

theorem trajDiff_continuous (bu : U) (bn : Nn) (n₀ v : Nn) : Continuous (trajDiff h bu bn n₀ v) :=
  (yStar_continuous h bu bn (n₀ + v)).sub (yStar_continuous h bu bn n₀)

theorem norm_trajDiff_le (bu : U) (bn : Nn) (n₀ v : Nn) (r : ℝ) :
    ‖trajDiff h bu bn n₀ v r‖ ≤ M / (1 - h.q) * ‖v‖ * exp (ν * r) := by
  have := norm_yStar_sub_le h bu bn (n₀ + v) n₀ r
  rwa [add_sub_cancel_left] at this

theorem trajDiff_sub (bu : U) (bn : Nn) (n₀ v v' : Nn) (r : ℝ) :
    trajDiff h bu bn n₀ v' r - trajDiff h bu bn n₀ v r =
      yStar h bu bn (n₀ + v') r - yStar h bu bn (n₀ + v) r := by
  simp only [trajDiff]; abel

theorem norm_trajDiff_sub_le (bu : U) (bn : Nn) (n₀ v v' : Nn) (r : ℝ) :
    ‖trajDiff h bu bn n₀ v' r - trajDiff h bu bn n₀ v r‖ ≤
      M / (1 - h.q) * ‖v' - v‖ * exp (ν * r) := by
  rw [trajDiff_sub]
  have := norm_yStar_sub_le h bu bn (n₀ + v') (n₀ + v) r
  rwa [add_sub_add_left_eq_sub] at this

theorem linSrc_continuous (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn)
    {z : ℝ → U × Nn} (hz : Continuous z) :
    Continuous (linSrc DNu DNv (yStar h bu bn n₀) z) :=
  ((hd.continuous_DNu.comp (yStar_continuous h bu bn n₀)).clm_apply hz).prodMk
    ((hd.continuous_DNv.comp (yStar_continuous h bu bn n₀)).clm_apply hz)

theorem norm_linSrc_le (hd : GraphC1Hyp h DNu DNv L₂) (y₀ z : ℝ → U × Nn) (r : ℝ) :
    ‖linSrc DNu DNv y₀ z r‖ ≤ L * ‖z r‖ := by
  rw [linSrc, Prod.norm_def]
  exact max_le (((DNu (y₀ r)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hd.norm_DNu_le _) (norm_nonneg _)))
    (((DNv (y₀ r)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hd.norm_DNv_le _) (norm_nonneg _)))

theorem linSrc_sum (y₀ : ℝ → U × Nn) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (z : ι → ℝ → U × Nn) :
    linSrc DNu DNv y₀ (∑ i ∈ s, c i • z i) = ∑ i ∈ s, c i • linSrc DNu DNv y₀ (z i) := by
  funext r
  simp only [linSrc, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem remSrc_continuous (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v : Nn) :
    Continuous (remSrc h bu bn DNu DNv n₀ v) := by
  have hNu_c : Continuous Nu := GraphHyp.lip_continuous h.Nu_lip
  have hNv_c : Continuous Nv := GraphHyp.lip_continuous h.Nv_lip
  have hyv := yStar_continuous h bu bn (n₀ + v)
  have hy0 := yStar_continuous h bu bn n₀
  exact (((hNu_c.comp hyv).sub (hNu_c.comp hy0)).sub
      ((hd.continuous_DNu.comp hy0).clm_apply (trajDiff_continuous bu bn n₀ v))).prodMk
    (((hNv_c.comp hyv).sub (hNv_c.comp hy0)).sub
      ((hd.continuous_DNv.comp hy0).clm_apply (trajDiff_continuous bu bn n₀ v)))

theorem yStar_add_eq (bu : U) (bn : Nn) (n₀ v : Nn) (r : ℝ) :
    yStar h bu bn (n₀ + v) r = yStar h bu bn n₀ r + trajDiff h bu bn n₀ v r := by
  simp [trajDiff]

theorem norm_remSrc_le (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v : Nn) (r : ℝ) :
    ‖remSrc h bu bn DNu DNv n₀ v r‖ ≤ L₂ * ‖trajDiff h bu bn n₀ v r‖ ^ 2 := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · simp only [remSrc]
    rw [yStar_add_eq]
    exact GraphC1Hyp.taylor_le hd.L₂_nonneg hd.hasDeriv_u hd.Du_lip _ _
  · simp only [remSrc]
    rw [yStar_add_eq]
    exact GraphC1Hyp.taylor_le hd.L₂_nonneg hd.hasDeriv_v hd.Dv_lip _ _

/-- Growth of the remainder source: `‖R_v(r)‖ ≤ L₂ (M/(1-q))² ‖v‖² e^{2νr}`. -/
theorem norm_remSrc_le' (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v : Nn) (r : ℝ) :
    ‖remSrc h bu bn DNu DNv n₀ v r‖ ≤ (L₂ * (M / (1 - h.q) * ‖v‖) ^ 2) * exp (2 * ν * r) := by
  refine (norm_remSrc_le hd bu bn n₀ v r).trans ?_
  have h1 := norm_trajDiff_le (h := h) bu bn n₀ v r
  have hexp2 : exp (ν * r) ^ 2 = exp (2 * ν * r) := by rw [← exp_nat_mul]; ring_nf
  rw [mul_assoc, ← hexp2, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) hd.L₂_nonneg

/-- **The per-direction identity** `w_v = (0, P_n v) + srcOp(DN(y₀) w_v) + srcOp(R_v)`. -/
theorem trajDiff_eq (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v : Nn) {t : ℝ}
    (ht : 0 ≤ t) :
    trajDiff h bu bn n₀ v t = ((0 : U), Pn t v) +
      (srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n₀) (trajDiff h bu bn n₀ v)) t +
        srcOp Pu Pn (remSrc h bu bn DNu DNv n₀ v) t) := by
  have hν := h.ν_pos
  have h2β := hd.two_lt
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hexp : ∀ r : ℝ, 0 ≤ r → exp (ν * r) ≤ exp (2 * ν * r) := fun r hr =>
    exp_le_exp.2 (by nlinarith)
  have hsplit : (fun r => (Nu (yStar h bu bn (n₀ + v) r) - Nu (yStar h bu bn n₀ r),
      Nv (yStar h bu bn (n₀ + v) r) - Nv (yStar h bu bn n₀ r))) =
      linSrc DNu DNv (yStar h bu bn n₀) (trajDiff h bu bn n₀ v) +
        remSrc h bu bn DNu DNv n₀ v := by
    funext r
    simp only [linSrc, remSrc, Pi.add_apply, Prod.mk_add_mk]
    ext <;> simp
  have hlb : ∀ r, 0 ≤ r → ‖linSrc DNu DNv (yStar h bu bn n₀) (trajDiff h bu bn n₀ v) r‖ ≤
      (L * (M / (1 - h.q) * ‖v‖)) * exp (2 * ν * r) := fun r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((norm_trajDiff_le bu bn n₀ v r).trans
        (mul_le_mul_of_nonneg_left (hexp r hr) (by positivity))) h.L_nonneg)
  have heq : trajDiff h bu bn n₀ v t = ((0 : U), Pn t v) +
      srcOp Pu Pn (fun r => (Nu (yStar h bu bn (n₀ + v) r) - Nu (yStar h bu bn n₀ r),
        Nv (yStar h bu bn (n₀ + v) r) - Nv (yStar h bu bn n₀ r))) t :=
    yStar_sub_eq h bu bn n₀ v ht
  rw [heq, hsplit, srcOp_add h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound
    (linSrc_continuous hd bu bn n₀ (trajDiff_continuous bu bn n₀ v))
    (remSrc_continuous hd bu bn n₀ v) hlb (fun r _ => norm_remSrc_le' hd bu bn n₀ v r) ht]

/-- **Combination identity**: if `Σ cᵢ vᵢ = 0`, then `z = Σ cᵢ w_{vᵢ}` satisfies
`z - srcOp(DN(y₀) z) = srcOp(Σ cᵢ R_{vᵢ})` on `[0, ∞)`. -/
theorem comb_eq (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn) {ι : Type*}
    [Fintype ι] (c : ι → ℝ) (v : ι → Nn) (hsum : ∑ i, c i • v i = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, c i • trajDiff h bu bn n₀ (v i)) t -
        srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n₀)
          (∑ i, c i • trajDiff h bu bn n₀ (v i))) t =
      srcOp Pu Pn (∑ i, c i • remSrc h bu bn DNu DNv n₀ (v i)) t := by
  have hν := h.ν_pos
  have h2β := hd.two_lt
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hexp : ∀ r : ℝ, 0 ≤ r → exp (ν * r) ≤ exp (2 * ν * r) := fun r hr =>
    exp_le_exp.2 (by nlinarith)
  have hlb : ∀ i r, 0 ≤ r →
      ‖linSrc DNu DNv (yStar h bu bn n₀) (trajDiff h bu bn n₀ (v i)) r‖ ≤
        (L * (M / (1 - h.q) * ‖v i‖)) * exp (2 * ν * r) := fun i r hr =>
    (norm_linSrc_le hd _ _ r).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((norm_trajDiff_le bu bn n₀ (v i) r).trans
        (mul_le_mul_of_nonneg_left (hexp r hr) (by positivity))) h.L_nonneg)
  rw [linSrc_sum, srcOp_sum h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound _ _ _
      (fun i => linSrc_continuous hd bu bn n₀ (trajDiff_continuous bu bn n₀ (v i))) _ hlb ht,
    srcOp_sum h.Pu_cont h.Pn_cont h2β h.M_nonneg h.Pu_bound _ _ _
      (fun i => remSrc_continuous hd bu bn n₀ (v i)) _
      (fun i r _ => norm_remSrc_le' hd bu bn n₀ (v i) r) ht]
  have hP : ∑ i, c i • ((0 : U), Pn t (v i)) = 0 := by
    have : Pn t (∑ i, c i • v i) = 0 := by rw [hsum, map_zero]
    rw [map_sum] at this
    ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum] using this
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  have hterm : ∀ i, c i • trajDiff h bu bn n₀ (v i) t = c i • ((0 : U), Pn t (v i)) +
      (c i • srcOp Pu Pn (linSrc DNu DNv (yStar h bu bn n₀) (trajDiff h bu bn n₀ (v i))) t +
        c i • srcOp Pu Pn (remSrc h bu bn DNu DNv n₀ (v i)) t) := fun i => by
    rw [trajDiff_eq hd bu bn n₀ (v i) ht, smul_add, smul_add]
  simp only [hterm, Finset.sum_add_distrib, hP, zero_add]
  abel

/-- **A priori bound for combinations**: if `Σ cᵢ vᵢ = 0` and the combined remainder source has
growth `σ e^{κr}` with `ν ≤ κ`, `α < κ < β`, `q_κ < 1`, then
`‖Σ cᵢ w_{vᵢ}(t)‖ ≤ M σ c_κ/(1 - q_κ) e^{κt}`. -/
theorem comb_le (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn) {ι : Type*}
    [Fintype ι] (c : ι → ℝ) (v : ι → Nn) (hsum : ∑ i, c i • v i = 0) {κ σ : ℝ} (hνκ : ν ≤ κ)
    (hακ : α < κ) (hκβ : κ < β) (hq : M * L * ((κ - α)⁻¹ + (β - κ)⁻¹) < 1) (hσ : 0 ≤ σ)
    (hS : ∀ r, 0 ≤ r → ‖(∑ i, c i • remSrc h bu bn DNu DNv n₀ (v i)) r‖ ≤ σ * exp (κ * r))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(∑ i, c i • trajDiff h bu bn n₀ (v i)) t‖ ≤
      M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹) / (1 - M * L * ((κ - α)⁻¹ + (β - κ)⁻¹)) *
        exp (κ * t) := by
  have hν := h.ν_pos
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hc : 0 ≤ (κ - α)⁻¹ + (β - κ)⁻¹ := by
    have h1 : 0 < κ - α := sub_pos.mpr hακ
    have h2 : 0 < β - κ := sub_pos.mpr hκβ
    positivity
  set z := ∑ i, c i • trajDiff h bu bn n₀ (v i) with hzdef
  have hzc : Continuous z := by
    have : z = fun r => ∑ i, c i • trajDiff h bu bn n₀ (v i) r := by
      funext r; simp [hzdef, Finset.sum_apply]
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      (trajDiff_continuous bu bn n₀ (v i)).const_smul (c i)
  have hzb : ∀ r, 0 ≤ r → ‖z r‖ ≤ (∑ i, |c i| * (M / (1 - h.q) * ‖v i‖)) * exp (κ * r) := by
    intro r hr
    rw [hzdef, Finset.sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((norm_trajDiff_le bu bn n₀ (v i) r).trans ?_)
      (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (by positivity)
  have hSc : Continuous (∑ i, c i • remSrc h bu bn DNu DNv n₀ (v i)) := by
    have : (∑ i, c i • remSrc h bu bn DNu DNv n₀ (v i)) =
        fun r => ∑ i, c i • remSrc h bu bn DNu DNv n₀ (v i) r := by
      funext r; simp [Finset.sum_apply]
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      (remSrc_continuous hd bu bn n₀ (v i)).const_smul (c i)
  have hE : ∀ s, 0 ≤ s → ‖z s - srcOp Pu Pn (fun r => (DNu (yStar h bu bn n₀ r) (z r),
      DNv (yStar h bu bn n₀ r) (z r))) s‖ ≤
        (M * σ * ((κ - α)⁻¹ + (β - κ)⁻¹)) * exp (κ * s) := by
    intro s hs
    have e := comb_eq hd bu bn n₀ c v hsum hs
    rw [← hzdef] at e
    have e' : (fun r => (DNu (yStar h bu bn n₀ r) (z r), DNv (yStar h bu bn n₀ r) (z r))) =
        linSrc DNu DNv (yStar h bu bn n₀) z := rfl
    rw [e', e]
    exact srcOp_norm_le h.Pu_cont h.Pn_cont hακ hκβ h.M_nonneg h.Pu_bound h.Pn_bound hSc hS hs
  have := apriori_le h.Pu_cont h.Pn_cont hακ hκβ h.M_nonneg h.L_nonneg h.Pu_bound h.Pn_bound hq
    ((hd.continuous_DNu.comp (yStar_continuous h bu bn n₀)))
    ((hd.continuous_DNv.comp (yStar_continuous h bu bn n₀)))
    (fun r => hd.norm_DNu_le _) (fun r => hd.norm_DNv_le _) hzc hzb
    (by have := h.M_nonneg; positivity) hE ht
  refine this.trans (le_of_eq ?_)
  ring

end Traj

/-! ### Pointwise Taylor estimates with Lipschitz second derivative -/

section Pointwise

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Mixed first-order remainder: `‖f(x+a) - f(x+b) - Df(x)(a-b)‖ ≤ L₂ (‖a‖+‖b‖) ‖a-b‖`. -/
theorem taylor_mixed_le {f : E → G} {Df : E → E →L[ℝ] G} {L₂ : ℝ} (hL₂ : 0 ≤ L₂)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (x a b : E) : ‖f (x + a) - f (x + b) - Df x (a - b)‖ ≤ L₂ * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  set ρ := ‖a‖ + ‖b‖
  have hconv : Convex ℝ (Metric.closedBall x ρ) := convex_closedBall _ _
  have hder : ∀ z ∈ Metric.closedBall x ρ, HasFDerivWithinAt (fun z => f z - Df x z)
      (Df z - Df x) (Metric.closedBall x ρ) z :=
    fun z _ => ((hf z).sub (Df x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall x ρ, ‖Df z - Df x‖ ≤ L₂ * ρ := fun z hz =>
    (hDf z x).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hz) hL₂)
  have hxa : x + a ∈ Metric.closedBall x ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    simp only [ρ]; linarith [norm_nonneg b]
  have hxb : x + b ∈ Metric.closedBall x ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    simp only [ρ]; linarith [norm_nonneg a]
  have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb hxb hxa
  rw [add_sub_add_left_eq_sub] at this
  calc ‖f (x + a) - f (x + b) - Df x (a - b)‖ =
        ‖f (x + a) - Df x (x + a) - (f (x + b) - Df x (x + b))‖ := by
        congr 1; rw [map_sub, map_add, map_add]; abel
    _ ≤ L₂ * ρ * ‖a - b‖ := this

/-- Second-order mixed remainder with `L₃`-Lipschitz second derivative:
`‖f(x+a) - f(x+b) - Df(x)(a-b) - D²f(x)(b)(a-b)‖ ≤ L₂ ‖a-b‖² + L₃ ‖b‖² ‖a-b‖`. -/
theorem taylor_second_le {f : E → G} {Df : E → E →L[ℝ] G} {D2f : E → E →L[ℝ] (E →L[ℝ] G)}
    {L₂ L₃ : ℝ} (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (hDf' : ∀ x, HasFDerivAt Df (D2f x) x) (hD2f : ∀ x x', ‖D2f x - D2f x'‖ ≤ L₃ * ‖x - x'‖)
    (x a b : E) :
    ‖f (x + a) - f (x + b) - Df x (a - b) - D2f x b (a - b)‖ ≤
      L₂ * ‖a - b‖ ^ 2 + L₃ * ‖b‖ ^ 2 * ‖a - b‖ := by
  have h1 := GraphC1Hyp.taylor_le hL₂ hf hDf (x + b) (a - b)
  rw [show x + b + (a - b) = x + a by abel] at h1
  have h2 := GraphC1Hyp.taylor_le hL₃ hDf' hD2f x b
  have h3 : ‖(Df (x + b) - Df x - D2f x b) (a - b)‖ ≤ L₃ * ‖b‖ ^ 2 * ‖a - b‖ :=
    ((Df (x + b) - Df x - D2f x b).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have e : f (x + a) - f (x + b) - Df x (a - b) - D2f x b (a - b) =
      (f (x + a) - f (x + b) - Df (x + b) (a - b)) + (Df (x + b) - Df x - D2f x b) (a - b) := by
    simp only [sub_apply]; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h1 h3)

/-- The second derivative is bounded by the Lipschitz constant of the first. -/
theorem norm_D2_le {Df : E → E →L[ℝ] G} {D2f : E → E →L[ℝ] (E →L[ℝ] G)} {L₂ : ℝ}
    (hL₂ : 0 ≤ L₂) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (hDf' : ∀ x, HasFDerivAt Df (D2f x) x) (x : E) : ‖D2f x‖ ≤ L₂ :=
  (hDf' x).le_of_lipschitz (C := ⟨L₂, hL₂⟩)
    (LipschitzWith.of_dist_le_mul fun a b => by rw [dist_eq_norm, dist_eq_norm]; exact hDf a b)

/-- **The second-level source bound** (one component). -/
theorem second_src_le {f : E → G} {Df : E → E →L[ℝ] G} {D2f : E → E →L[ℝ] (E →L[ℝ] G)}
    {L₂ L₃ : ℝ} (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (hDf' : ∀ x, HasFDerivAt Df (D2f x) x) (hD2f : ∀ x x', ‖D2f x - D2f x'‖ ≤ L₃ * ‖x - x'‖)
    (y : E) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3 → ℝ) (W W' : Fin 3 → E) (Wl : E) {A B : ℝ}
    (ω Z : Fin 3 → ℝ) (hA : ‖∑ i, a i • W i‖ ≤ A) (hB0 : 0 ≤ B) (hB : ‖Wl‖ ≤ B * ℓ)
    (hBi : ∀ i, ‖W' i - W i‖ ≤ B * ℓ) (hω : ∀ i, ‖W i‖ ≤ ω i) (hZ : ∀ i, ‖W' i - W i - Wl‖ ≤ Z i) :
    ‖∑ i, (a i / ℓ) • ((f (y + W' i) - f (y + W i) - Df y (W' i - W i)) -
        (f (y + Wl) - f y - Df y Wl))‖ ≤
      L₂ * A * B + ∑ i, |a i| * (L₂ * ω i * (Z i / ℓ) + 2 * L₂ * B ^ 2 * ℓ + L₃ * ω i ^ 2 * B) := by
  have hD2 : ‖D2f y‖ ≤ L₂ := norm_D2_le hL₂ hDf hDf' y
  set Rl := f (y + Wl) - f y - Df y Wl
  have hRl : ‖Rl‖ ≤ L₂ * (B * ℓ) ^ 2 :=
    (GraphC1Hyp.taylor_le hL₂ hf hDf y Wl).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB 2) hL₂)
  set E1 : Fin 3 → G := fun i =>
    f (y + W' i) - f (y + W i) - Df y (W' i - W i) - D2f y (W i) (W' i - W i)
  have hE1 : ∀ i, ‖E1 i‖ ≤ L₂ * (B * ℓ) ^ 2 + L₃ * ω i ^ 2 * (B * ℓ) := fun i => by
    have := taylor_second_le (x := y) (a := W' i) (b := W i) hL₂ hL₃ hf hDf hDf' hD2f
    refine this.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hBi i) 2) hL₂
    · refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hω i) 2) hL₃)
        (hBi i) (norm_nonneg _) (by positivity)
  have hdecomp : ∀ i, (f (y + W' i) - f (y + W i) - Df y (W' i - W i)) - Rl =
      D2f y (W i) Wl + (D2f y (W i) (W' i - W i - Wl) + E1 i - Rl) := fun i => by
    simp only [E1, map_sub]; abel
  have hsum : ∑ i, (a i / ℓ) • ((f (y + W' i) - f (y + W i) - Df y (W' i - W i)) - Rl) =
      ℓ⁻¹ • D2f y (∑ i, a i • W i) Wl +
        ∑ i, (a i / ℓ) • (D2f y (W i) (W' i - W i - Wl) + E1 i - Rl) := by
    simp only [hdecomp, smul_add, Finset.sum_add_distrib, map_sum, map_smul,
      FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, Finset.smul_sum, smul_smul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv, mul_comm]
  rw [hsum]
  have hfirst : ‖ℓ⁻¹ • D2f y (∑ i, a i • W i) Wl‖ ≤ L₂ * A * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
    have h1 : ‖D2f y (∑ i, a i • W i) Wl‖ ≤ L₂ * A * (B * ℓ) := by
      calc ‖D2f y (∑ i, a i • W i) Wl‖ ≤ ‖D2f y (∑ i, a i • W i)‖ * ‖Wl‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖D2f y‖ * ‖∑ i, a i • W i‖) * ‖Wl‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (L₂ * A) * (B * ℓ) := by
            refine mul_le_mul (mul_le_mul hD2 hA (norm_nonneg _) hL₂) hB (norm_nonneg _)
              (mul_nonneg hL₂ ((norm_nonneg _).trans hA))
    rw [inv_mul_le_iff₀ hℓ]
    calc ‖D2f y (∑ i, a i • W i) Wl‖ ≤ L₂ * A * (B * ℓ) := h1
      _ = ℓ * (L₂ * A * B) := by ring
  have hrest : ∀ i, ‖(a i / ℓ) • (D2f y (W i) (W' i - W i - Wl) + E1 i - Rl)‖ ≤
      |a i| * (L₂ * ω i * (Z i / ℓ) + 2 * L₂ * B ^ 2 * ℓ + L₃ * ω i ^ 2 * B) := fun i => by
    have hω0 : 0 ≤ ω i := (norm_nonneg _).trans (hω i)
    have hZ0 : 0 ≤ Z i := (norm_nonneg _).trans (hZ i)
    have hD : ‖D2f y (W i) (W' i - W i - Wl)‖ ≤ L₂ * ω i * Z i :=
      calc ‖D2f y (W i) (W' i - W i - Wl)‖ ≤ ‖D2f y (W i)‖ * ‖W' i - W i - Wl‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖D2f y‖ * ‖W i‖) * ‖W' i - W i - Wl‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (L₂ * ω i) * Z i :=
            mul_le_mul (mul_le_mul hD2 (hω i) (norm_nonneg _) hL₂) (hZ i) (norm_nonneg _)
              (mul_nonneg hL₂ hω0)
    have hin : ‖D2f y (W i) (W' i - W i - Wl) + E1 i - Rl‖ ≤
        L₂ * ω i * Z i + (L₂ * (B * ℓ) ^ 2 + L₃ * ω i ^ 2 * (B * ℓ)) + L₂ * (B * ℓ) ^ 2 :=
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hD (hE1 i))) hRl)
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hℓ]
    calc |a i| / ℓ * ‖D2f y (W i) (W' i - W i - Wl) + E1 i - Rl‖
        ≤ |a i| / ℓ * (L₂ * ω i * Z i + (L₂ * (B * ℓ) ^ 2 + L₃ * ω i ^ 2 * (B * ℓ)) +
            L₂ * (B * ℓ) ^ 2) := mul_le_mul_of_nonneg_left hin (by positivity)
      _ = |a i| * (L₂ * ω i * (Z i / ℓ) + 2 * L₂ * B ^ 2 * ℓ + L₃ * ω i ^ 2 * B) := by
          field_simp; ring
  calc _ ≤ ‖ℓ⁻¹ • D2f y (∑ i, a i • W i) Wl‖ +
        ‖∑ i, (a i / ℓ) • (D2f y (W i) (W' i - W i - Wl) + E1 i - Rl)‖ := norm_add_le _ _
    _ ≤ L₂ * A * B + ∑ i, |a i| * (L₂ * ω i * (Z i / ℓ) + 2 * L₂ * B ^ 2 * ℓ +
        L₃ * ω i ^ 2 * B) :=
        add_le_add hfirst ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hrest i))

end Pointwise

/-! ### The `C²` layer -/

section Second

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}

/-- Hypotheses of the `C²` layer of `lem:supp-exact-graph-criterion`: the derivatives `DN` are
differentiable with `L₃`-Lipschitz derivatives `D²N` (bounded third derivatives), and the `j = 3`
inequality of `eq:supp-exact-graph-contraction` holds, with `3ν < β`. -/
structure GraphC2Hyp (hd : GraphC1Hyp h DNu DNv L₂)
    (D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U))
    (D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)) (L₃ : ℝ) : Prop where
  hasDeriv2_u : ∀ x, HasFDerivAt DNu (D2Nu x) x
  hasDeriv2_v : ∀ x, HasFDerivAt DNv (D2Nv x) x
  L₃_nonneg : 0 ≤ L₃
  D2u_lip : ∀ x x', ‖D2Nu x - D2Nu x'‖ ≤ L₃ * ‖x - x'‖
  D2v_lip : ∀ x x', ‖D2Nv x - D2Nv x'‖ ≤ L₃ * ‖x - x'‖
  three_lt : 3 * ν < β
  contr3 : M * L * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) < 1

theorem remSrc_eq (bu : U) (bn : Nn) (n₀ v : Nn) (r : ℝ) :
    remSrc h bu bn DNu DNv n₀ v r =
      (Nu (yStar h bu bn n₀ r + trajDiff h bu bn n₀ v r) - Nu (yStar h bu bn n₀ r) -
          DNu (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ v r),
        Nv (yStar h bu bn n₀ r + trajDiff h bu bn n₀ v r) - Nv (yStar h bu bn n₀ r) -
          DNv (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ v r)) := by
  simp only [remSrc, ← yStar_add_eq]

/-- The constants: `C₁ = M/(1-q)`, `c₂`, `q₂`, `c₃`, `q₃`. -/
def GraphC1Hyp.K1 (hd : GraphC1Hyp h DNu DNv L₂) : ℝ :=
  M * L₂ * (M / (1 - h.q)) ^ 2 * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) /
    (1 - M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹))

theorem GraphC1Hyp.K1_nonneg (hd : GraphC1Hyp h DNu DNv L₂) : 0 ≤ hd.K1 := by
  have h1 : 0 < 2 * ν - α := by linarith [h.α_lt, h.ν_pos]
  have h2 : 0 < β - 2 * ν := by linarith [hd.two_lt]
  have h3 : 0 < 1 - M * L * ((2 * ν - α)⁻¹ + (β - 2 * ν)⁻¹) := by linarith [hd.contr2]
  have := h.M_nonneg
  have := hd.L₂_nonneg
  unfold GraphC1Hyp.K1
  positivity

/-- **First-level defect at every time**: if `Σ aᵢ vᵢ = 0` then
`‖Σ aᵢ w_{vᵢ}(t)‖ ≤ K₁ Σ |aᵢ| ‖vᵢ‖² e^{2νt}`. -/
theorem traj_first (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ : Nn) (a : Fin 3 → ℝ)
    (v : Fin 3 → Nn) (hsum : ∑ i, a i • v i = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑ i, a i • trajDiff h bu bn n₀ (v i) t‖ ≤
      hd.K1 * (∑ i, |a i| * ‖v i‖ ^ 2) * exp (2 * ν * t) := by
  have hν := h.ν_pos
  have hS : ∀ r, 0 ≤ r → ‖(∑ i, a i • remSrc h bu bn DNu DNv n₀ (v i)) r‖ ≤
      (∑ i, |a i| * (L₂ * (M / (1 - h.q) * ‖v i‖) ^ 2)) * exp (2 * ν * r) := by
    intro r hr
    rw [Finset.sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_remSrc_le' hd bu bn n₀ (v i) r) (abs_nonneg _)
  have hσ : 0 ≤ ∑ i, |a i| * (L₂ * (M / (1 - h.q) * ‖v i‖) ^ 2) := by
    have := hd.L₂_nonneg
    exact Finset.sum_nonneg fun i _ => by positivity
  have := comb_le hd bu bn n₀ a v hsum (by linarith) (by linarith [h.α_lt]) hd.two_lt hd.contr2
    hσ hS ht
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply] at this
  have hσeq : (∑ i, |a i| * (L₂ * (M / (1 - h.q) * ‖v i‖) ^ 2)) =
      L₂ * (M / (1 - h.q)) ^ 2 * ∑ i, |a i| * ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hσeq] at this
  refine this.trans (le_of_eq ?_)
  simp only [GraphC1Hyp.K1]
  ring

/-- The constant of the mixed second difference. -/
def GraphC1Hyp.K2 (hd : GraphC1Hyp h DNu DNv L₂) : ℝ := 2 * hd.K1

/-- Generic component bound for the mixed second difference. -/
theorem mixed_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} {Df : E → E →L[ℝ] G} {L₂ : ℝ} (hL₂ : 0 ≤ L₂)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (y W' W We : E) {P Q R : ℝ} (hP : ‖W'‖ + ‖W‖ ≤ P) (hQ : ‖W' - W‖ ≤ Q) (hR : ‖We‖ ≤ R) :
    ‖(f (y + W') - f y - Df y W') - (f (y + W) - f y - Df y W) - (f (y + We) - f y - Df y We)‖
      ≤ L₂ * P * Q + L₂ * R ^ 2 := by
  have e1 : (f (y + W') - f y - Df y W') - (f (y + W) - f y - Df y W) -
      (f (y + We) - f y - Df y We) =
      (f (y + W') - f (y + W) - Df y (W' - W)) - (f (y + We) - f y - Df y We) := by
    rw [map_sub]; abel
  rw [e1]
  have h1 := taylor_mixed_le hL₂ hf hDf y W' W
  have h2 := GraphC1Hyp.taylor_le hL₂ hf hDf y We
  calc _ ≤ ‖f (y + W') - f (y + W) - Df y (W' - W)‖ + ‖f (y + We) - f y - Df y We‖ :=
        norm_sub_le _ _
    _ ≤ L₂ * (‖W'‖ + ‖W‖) * ‖W' - W‖ + L₂ * ‖We‖ ^ 2 := add_le_add h1 h2
    _ ≤ L₂ * P * Q + L₂ * R ^ 2 := by
        have h0 : 0 ≤ ‖W'‖ + ‖W‖ := by positivity
        have hP0 : 0 ≤ P := h0.trans hP
        have h3 := mul_le_mul (mul_le_mul_of_nonneg_left hP hL₂) hQ (norm_nonneg _)
          (mul_nonneg hL₂ hP0)
        have h4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hR 2) hL₂
        linarith

/-- Source bound for the mixed second difference. -/
theorem mixed_src_le (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v e : Nn) (r : ℝ) :
    ‖remSrc h bu bn DNu DNv n₀ (v + e) r - remSrc h bu bn DNu DNv n₀ v r -
        remSrc h bu bn DNu DNv n₀ e r‖ ≤
      (L₂ * (M / (1 - h.q)) ^ 2 * (2 * (‖v‖ * ‖e‖ + ‖e‖ ^ 2))) * exp (2 * ν * r) := by
  set C1 := M / (1 - h.q) with hC1def
  have hC1 : 0 ≤ C1 := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  set E1 := exp (ν * r) with hE1def
  have hE : 0 < E1 := exp_pos _
  have hexp2 : E1 * E1 = exp (2 * ν * r) := by rw [hE1def, ← exp_add]; ring_nf
  have hW' := norm_trajDiff_le (h := h) bu bn n₀ (v + e) r
  have hW := norm_trajDiff_le (h := h) bu bn n₀ v r
  have hWe := norm_trajDiff_le (h := h) bu bn n₀ e r
  have hd' : ‖trajDiff h bu bn n₀ (v + e) r - trajDiff h bu bn n₀ v r‖ ≤ C1 * ‖e‖ * E1 := by
    have := norm_trajDiff_sub_le (h := h) bu bn n₀ v (v + e) r
    rwa [add_sub_cancel_left] at this
  have hve : ‖v + e‖ ≤ ‖v‖ + ‖e‖ := norm_add_le _ _
  have hsum1 : ‖trajDiff h bu bn n₀ (v + e) r‖ + ‖trajDiff h bu bn n₀ v r‖ ≤
      C1 * (2 * ‖v‖ + ‖e‖) * E1 := by
    have h1 : C1 * ‖v + e‖ * E1 ≤ C1 * (‖v‖ + ‖e‖) * E1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hve hC1) hE.le
    calc _ ≤ C1 * ‖v + e‖ * E1 + C1 * ‖v‖ * E1 := add_le_add hW' hW
      _ ≤ C1 * (‖v‖ + ‖e‖) * E1 + C1 * ‖v‖ * E1 := add_le_add h1 le_rfl
      _ = C1 * (2 * ‖v‖ + ‖e‖) * E1 := by ring
  have hfin : L₂ * (C1 * (2 * ‖v‖ + ‖e‖) * E1) * (C1 * ‖e‖ * E1) + L₂ * (C1 * ‖e‖ * E1) ^ 2 =
      (L₂ * C1 ^ 2 * (2 * (‖v‖ * ‖e‖ + ‖e‖ ^ 2))) * exp (2 * ν * r) := by
    rw [← hexp2]; ring
  rw [remSrc_eq, remSrc_eq, remSrc_eq, Prod.norm_def]
  simp only [Prod.fst_sub, Prod.snd_sub]
  refine max_le ?_ ?_
  · exact (mixed_comp_le hd.L₂_nonneg hd.hasDeriv_u hd.Du_lip _ _ _ _ hsum1 hd' hWe).trans
      (le_of_eq hfin)
  · exact (mixed_comp_le hd.L₂_nonneg hd.hasDeriv_v hd.Dv_lip _ _ _ _ hsum1 hd' hWe).trans
      (le_of_eq hfin)

/-- **Mixed second difference**: `‖w_{v+e}(t) - w_v(t) - w_e(t)‖ ≤ K₂ (‖v‖‖e‖ + ‖e‖²) e^{2νt}`. -/
theorem traj_mixed (hd : GraphC1Hyp h DNu DNv L₂) (bu : U) (bn : Nn) (n₀ v e : Nn) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖trajDiff h bu bn n₀ (v + e) t - trajDiff h bu bn n₀ v t - trajDiff h bu bn n₀ e t‖ ≤
      hd.K2 * (‖v‖ * ‖e‖ + ‖e‖ ^ 2) * exp (2 * ν * t) := by
  have hν := h.ν_pos
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hsum : ∑ i, (![1, -1, -1] : Fin 3 → ℝ) i • (![v + e, v, e] : Fin 3 → Nn) i = 0 := by
    simp [Fin.sum_univ_three]
  have hval : ∀ r, (∑ i, (![1, -1, -1] : Fin 3 → ℝ) i •
      remSrc h bu bn DNu DNv n₀ ((![v + e, v, e] : Fin 3 → Nn) i)) r =
      remSrc h bu bn DNu DNv n₀ (v + e) r - remSrc h bu bn DNu DNv n₀ v r -
        remSrc h bu bn DNu DNv n₀ e r := fun r => by
    simp [Fin.sum_univ_three, Finset.sum_apply]; abel
  have hσ : 0 ≤ L₂ * (M / (1 - h.q)) ^ 2 * (2 * (‖v‖ * ‖e‖ + ‖e‖ ^ 2)) := by
    have := hd.L₂_nonneg; positivity
  have hνκ : ν ≤ 2 * ν := by linarith
  have hακ : α < 2 * ν := by linarith [h.α_lt]
  have := comb_le hd bu bn n₀ _ _ hsum hνκ hακ hd.two_lt hd.contr2 hσ
    (fun r _ => by rw [hval]; exact mixed_src_le hd bu bn n₀ v e r) ht
  have hz : (∑ i, (![1, -1, -1] : Fin 3 → ℝ) i •
      trajDiff h bu bn n₀ ((![v + e, v, e] : Fin 3 → Nn) i)) t =
      trajDiff h bu bn n₀ (v + e) t - trajDiff h bu bn n₀ v t - trajDiff h bu bn n₀ e t := by
    simp [Fin.sum_univ_three, Finset.sum_apply]; abel
  rw [hz] at this
  refine this.trans (le_of_eq ?_)
  simp only [GraphC1Hyp.K2, GraphC1Hyp.K1]
  ring

end Second

section SecondLevel

theorem remSrc_comp_identity {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (Df : E →L[ℝ] G) (y W' W Wl : E) :
    (f (y + W') - f y - Df W') - (f (y + W) - f y - Df W) - (f (y + Wl) - f y - Df Wl) =
      (f (y + W') - f (y + W) - Df (W' - W)) - (f (y + Wl) - f y - Df Wl) := by
  rw [map_sub]; abel

/-- The second-level component bound in remainder form. -/
theorem second_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {Df : E → E →L[ℝ] G}
    {D2f : E → E →L[ℝ] (E →L[ℝ] G)} {L₂ L₃ : ℝ} (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hDf : ∀ x x', ‖Df x - Df x'‖ ≤ L₂ * ‖x - x'‖)
    (hDf' : ∀ x, HasFDerivAt Df (D2f x) x) (hD2f : ∀ x x', ‖D2f x - D2f x'‖ ≤ L₃ * ‖x - x'‖)
    (y : E) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3 → ℝ) (W W' : Fin 3 → E) (Wl : E) {A B : ℝ}
    (ω Z : Fin 3 → ℝ) (hA : ‖∑ i, a i • W i‖ ≤ A) (hB0 : 0 ≤ B) (hB : ‖Wl‖ ≤ B * ℓ)
    (hBi : ∀ i, ‖W' i - W i‖ ≤ B * ℓ) (hω : ∀ i, ‖W i‖ ≤ ω i) (hZ : ∀ i, ‖W' i - W i - Wl‖ ≤ Z i) :
    ‖∑ i, (a i / ℓ) • ((f (y + W' i) - f y - Df y (W' i)) - (f (y + W i) - f y - Df y (W i)) -
        (f (y + Wl) - f y - Df y Wl))‖ ≤
      L₂ * A * B + ∑ i, |a i| * (L₂ * ω i * (Z i / ℓ) + 2 * L₂ * B ^ 2 * ℓ + L₃ * ω i ^ 2 * B) := by
  simp only [remSrc_comp_identity f (Df y)]
  exact second_src_le hL₂ hL₃ hf hDf hDf' hD2f y hℓ a W W' Wl ω Z hA hB0 hB hBi hω hZ

/-- Real bookkeeping for the second-level bound. -/
theorem second_scalar_le {L₂ L₃ K1 K2 C1 E ℓ nd : ℝ} (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (hC1 : 0 ≤ C1) (hE1 : 1 ≤ E) (hℓ : 0 < ℓ) (hnd : 0 ≤ nd) (a : Fin 3 → ℝ) (nv : Fin 3 → ℝ) :
    L₂ * (K1 * (∑ i, |a i| * nv i ^ 2) * E ^ 2) * (C1 * nd * E) +
        ∑ i, |a i| * (L₂ * (C1 * nv i * E) * (K2 * (nv i * (ℓ * nd) + (ℓ * nd) ^ 2) * E ^ 2 / ℓ) +
          2 * L₂ * (C1 * nd * E) ^ 2 * ℓ + L₃ * (C1 * nv i * E) ^ 2 * (C1 * nd * E)) ≤
      (L₂ * K1 * C1 * nd * (∑ i, |a i| * nv i ^ 2) +
        ∑ i, |a i| * (L₂ * C1 * K2 * nv i * (nv i * nd + ℓ * nd ^ 2) +
          2 * L₂ * C1 ^ 2 * nd ^ 2 * ℓ + L₃ * C1 ^ 3 * nv i ^ 2 * nd)) * E ^ 3 := by
  have hE23 : E ^ 2 ≤ E ^ 3 := pow_le_pow_right₀ hE1 (by norm_num)
  rw [add_mul, Finset.sum_mul]
  refine add_le_add (le_of_eq (by ring)) (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_assoc (|a i|)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have e1 : L₂ * (C1 * nv i * E) * (K2 * (nv i * (ℓ * nd) + (ℓ * nd) ^ 2) * E ^ 2 / ℓ) =
      L₂ * C1 * K2 * nv i * (nv i * nd + ℓ * nd ^ 2) * E ^ 3 := by
    field_simp
  have e3 : 2 * L₂ * (C1 * nd * E) ^ 2 * ℓ ≤ 2 * L₂ * C1 ^ 2 * nd ^ 2 * ℓ * E ^ 3 := by
    have : 2 * L₂ * (C1 * nd * E) ^ 2 * ℓ = 2 * L₂ * C1 ^ 2 * nd ^ 2 * ℓ * E ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hE23 (by positivity)
  have e2 : L₃ * (C1 * nv i * E) ^ 2 * (C1 * nd * E) = L₃ * C1 ^ 3 * nv i ^ 2 * nd * E ^ 3 := by
    ring
  rw [e1, e2]
  linarith [e3]

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}
  {D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)}
  {D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)} {L₃ : ℝ}

/-- The second-level source bound, assembled for both components. -/
theorem second_level_src_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n₀ d : Nn) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3 → ℝ) (v : Fin 3 → Nn)
    (hsum : ∑ i, a i • v i = 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖∑ i, (a i / ℓ) • (remSrc h bu bn DNu DNv n₀ (v i + ℓ • d) r -
        remSrc h bu bn DNu DNv n₀ (v i) r - remSrc h bu bn DNu DNv n₀ (ℓ • d) r)‖ ≤
      (L₂ * hd.K1 * (M / (1 - h.q)) * ‖d‖ * (∑ i, |a i| * ‖v i‖ ^ 2) +
        ∑ i, |a i| * (L₂ * (M / (1 - h.q)) * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
          2 * L₂ * (M / (1 - h.q)) ^ 2 * ‖d‖ ^ 2 * ℓ +
          L₃ * (M / (1 - h.q)) ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) * exp (3 * ν * r) := by
  have hν := h.ν_pos
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have hE1 : 1 ≤ exp (ν * r) := one_le_exp (by positivity)
  have hE2 : exp (2 * ν * r) = exp (ν * r) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hE3 : exp (3 * ν * r) = exp (ν * r) ^ 3 := by rw [← exp_nat_mul]; ring_nf
  have hA : ‖∑ i, a i • trajDiff h bu bn n₀ (v i) r‖ ≤
      hd.K1 * (∑ i, |a i| * ‖v i‖ ^ 2) * exp (ν * r) ^ 2 := by
    have := traj_first hd bu bn n₀ a v hsum hr
    rwa [hE2] at this
  have hB0 : 0 ≤ M / (1 - h.q) * ‖d‖ * exp (ν * r) := by positivity
  have hnl : ‖ℓ • d‖ = ℓ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have hB : ‖trajDiff h bu bn n₀ (ℓ • d) r‖ ≤ M / (1 - h.q) * ‖d‖ * exp (ν * r) * ℓ := by
    have := norm_trajDiff_le (h := h) bu bn n₀ (ℓ • d) r
    rw [hnl] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hBi : ∀ i, ‖trajDiff h bu bn n₀ (v i + ℓ • d) r - trajDiff h bu bn n₀ (v i) r‖ ≤
      M / (1 - h.q) * ‖d‖ * exp (ν * r) * ℓ := fun i => by
    have := norm_trajDiff_sub_le (h := h) bu bn n₀ (v i) (v i + ℓ • d) r
    rw [add_sub_cancel_left, hnl] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hω : ∀ i, ‖trajDiff h bu bn n₀ (v i) r‖ ≤ M / (1 - h.q) * ‖v i‖ * exp (ν * r) :=
    fun i => norm_trajDiff_le bu bn n₀ (v i) r
  have hZ : ∀ i, ‖trajDiff h bu bn n₀ (v i + ℓ • d) r - trajDiff h bu bn n₀ (v i) r -
      trajDiff h bu bn n₀ (ℓ • d) r‖ ≤
      hd.K2 * (‖v i‖ * (ℓ * ‖d‖) + (ℓ * ‖d‖) ^ 2) * exp (ν * r) ^ 2 := fun i => by
    have := traj_mixed hd bu bn n₀ (v i) (ℓ • d) hr
    rwa [hnl, hE2] at this
  have hval : ∑ i, (a i / ℓ) • (remSrc h bu bn DNu DNv n₀ (v i + ℓ • d) r -
        remSrc h bu bn DNu DNv n₀ (v i) r - remSrc h bu bn DNu DNv n₀ (ℓ • d) r) =
      (∑ i, (a i / ℓ) •
          ((Nu (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (v i + ℓ • d) r) -
              Nu (yStar h bu bn n₀ r) -
              DNu (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (v i + ℓ • d) r)) -
            (Nu (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (v i) r) - Nu (yStar h bu bn n₀ r) -
              DNu (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (v i) r)) -
            (Nu (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (ℓ • d) r) - Nu (yStar h bu bn n₀ r) -
              DNu (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (ℓ • d) r))),
        ∑ i, (a i / ℓ) •
          ((Nv (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (v i + ℓ • d) r) -
              Nv (yStar h bu bn n₀ r) -
              DNv (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (v i + ℓ • d) r)) -
            (Nv (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (v i) r) - Nv (yStar h bu bn n₀ r) -
              DNv (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (v i) r)) -
            (Nv (yStar h bu bn n₀ r + trajDiff h bu bn n₀ (ℓ • d) r) - Nv (yStar h bu bn n₀ r) -
              DNv (yStar h bu bn n₀ r) (trajDiff h bu bn n₀ (ℓ • d) r)))) := by
    simp only [remSrc_eq]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  have hfinal := second_scalar_le (K1 := hd.K1) (K2 := hd.K2) hd.L₂_nonneg hd2.L₃_nonneg hC1 hE1
    hℓ (norm_nonneg d) a (fun i => ‖v i‖)
  rw [hval, Prod.norm_def, hE3]
  refine max_le ?_ ?_
  · refine le_trans ?_ hfinal
    exact second_comp_le hd.L₂_nonneg hd2.L₃_nonneg hd.hasDeriv_u hd.Du_lip hd2.hasDeriv2_u
      hd2.D2u_lip (yStar h bu bn n₀ r) hℓ a (fun i => trajDiff h bu bn n₀ (v i) r)
      (fun i => trajDiff h bu bn n₀ (v i + ℓ • d) r) (trajDiff h bu bn n₀ (ℓ • d) r)
      (fun i => M / (1 - h.q) * ‖v i‖ * exp (ν * r))
      (fun i => hd.K2 * (‖v i‖ * (ℓ * ‖d‖) + (ℓ * ‖d‖) ^ 2) * exp (ν * r) ^ 2) hA hB0 hB hBi hω hZ
  · refine le_trans ?_ hfinal
    exact second_comp_le hd.L₂_nonneg hd2.L₃_nonneg hd.hasDeriv_v hd.Dv_lip hd2.hasDeriv2_v
      hd2.D2v_lip (yStar h bu bn n₀ r) hℓ a (fun i => trajDiff h bu bn n₀ (v i) r)
      (fun i => trajDiff h bu bn n₀ (v i + ℓ • d) r) (trajDiff h bu bn n₀ (ℓ • d) r)
      (fun i => M / (1 - h.q) * ‖v i‖ * exp (ν * r))
      (fun i => hd.K2 * (‖v i‖ * (ℓ * ‖d‖) + (ℓ * ‖d‖) ^ 2) * exp (ν * r) ^ 2) hA hB0 hB hBi hω hZ

end SecondLevel

section C2

variable {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} {M α β ν L : ℝ}
  {Nu : U × Nn → U} {Nv : U × Nn → Nn} {h : GraphHyp Pu Pn M α β ν L Nu Nv}
  {DNu : U × Nn → (U × Nn) →L[ℝ] U} {DNv : U × Nn → (U × Nn) →L[ℝ] Nn} {L₂ : ℝ}
  {D2Nu : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] U)}
  {D2Nv : U × Nn → (U × Nn) →L[ℝ] ((U × Nn) →L[ℝ] Nn)} {L₃ : ℝ}

/-- `M c₃ / (1 - q₃)`. -/
def GraphC2Hyp.Kc {hd : GraphC1Hyp h DNu DNv L₂} (_ : GraphC2Hyp hd D2Nu D2Nv L₃) : ℝ :=
  M * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) / (1 - M * L * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹))

theorem GraphC2Hyp.Kc_nonneg {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) :
    0 ≤ hd2.Kc := by
  have h1 : 0 < 3 * ν - α := by linarith [h.α_lt, h.ν_pos]
  have h2 : 0 < β - 3 * ν := by linarith [hd2.three_lt]
  have h3 : 0 < 1 - M * L * ((3 * ν - α)⁻¹ + (β - 3 * ν)⁻¹) := by linarith [hd2.contr3]
  have := h.M_nonneg
  unfold GraphC2Hyp.Kc
  positivity

/-- **Second-level defect of the difference quotients**: if `Σ aᵢ vᵢ = 0` then for `ℓ > 0`
`‖Σ aᵢ (ℓ⁻¹(h(n₀+vᵢ+ℓd) - h(n₀+vᵢ)) - ℓ⁻¹(h(n₀+ℓd) - h(n₀)))‖ ≤ K_c σ₃(ℓ)`, the source of the
second-level combination being bounded in the weight `3ν` (`j = 3` inequality). -/
theorem second_level_le (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) (n₀ d : Nn) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3 → ℝ) (v : Fin 3 → Nn)
    (hsum : ∑ i, a i • v i = 0) :
    ‖∑ i, a i • (diffQuot (graphMap h bu bn) (n₀ + v i) d ℓ -
        diffQuot (graphMap h bu bn) n₀ d ℓ)‖ ≤
      hd2.Kc * (L₂ * hd.K1 * (M / (1 - h.q)) * ‖d‖ * (∑ i, |a i| * ‖v i‖ ^ 2) +
        ∑ i, |a i| * (L₂ * (M / (1 - h.q)) * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
          2 * L₂ * (M / (1 - h.q)) ^ 2 * ‖d‖ ^ 2 * ℓ +
          L₃ * (M / (1 - h.q)) ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) := by
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
  have hvalS : ∀ r, (∑ p, c p • remSrc h bu bn DNu DNv n₀ (w p)) r =
      ∑ i, (a i / ℓ) • (remSrc h bu bn DNu DNv n₀ (v i + ℓ • d) r -
        remSrc h bu bn DNu DNv n₀ (v i) r - remSrc h bu bn DNu DNv n₀ (ℓ • d) r) := by
    intro r
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcdef, hwdef, Fin.sum_univ_three, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [mul_one, mul_neg, neg_smul, smul_sub]; abel
  have hσ : 0 ≤ L₂ * hd.K1 * (M / (1 - h.q)) * ‖d‖ * (∑ i, |a i| * ‖v i‖ ^ 2) +
      ∑ i, |a i| * (L₂ * (M / (1 - h.q)) * hd.K2 * ‖v i‖ * (‖v i‖ * ‖d‖ + ℓ * ‖d‖ ^ 2) +
        2 * L₂ * (M / (1 - h.q)) ^ 2 * ‖d‖ ^ 2 * ℓ + L₃ * (M / (1 - h.q)) ^ 3 * ‖v i‖ ^ 2 * ‖d‖) := by
    have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
    have := hd.L₂_nonneg; have := hd2.L₃_nonneg; have := hd.K1_nonneg
    have hK2 : 0 ≤ hd.K2 := by unfold GraphC1Hyp.K2; linarith [hd.K1_nonneg]
    positivity
  have hcomb := comb_le hd bu bn n₀ c w hsumF (by linarith) (by linarith [h.α_lt])
    hd2.three_lt hd2.contr3 hσ
    (fun r hr => by rw [hvalS]; exact second_level_src_le hd hd2 bu bn n₀ d hℓ a v hsum hr)
    (le_refl (0 : ℝ))
  have hz0 : ((∑ p, c p • trajDiff h bu bn n₀ (w p)) 0).1 =
      ∑ i, a i • (diffQuot (graphMap h bu bn) (n₀ + v i) d ℓ -
        diffQuot (graphMap h bu bn) n₀ d ℓ) := by
    rw [Finset.sum_apply, Prod.fst_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcdef, hwdef, Fin.sum_univ_three, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Prod.smul_fst, trajDiff, Prod.fst_sub, diffQuot]
    have e1 : (yStar h bu bn (n₀ + (v i + ℓ • d)) 0).1 = graphMap h bu bn (n₀ + v i + ℓ • d) := by
      rw [← add_assoc]; rfl
    have e2 : (yStar h bu bn (n₀ + v i) 0).1 = graphMap h bu bn (n₀ + v i) := rfl
    have e3 : (yStar h bu bn (n₀ + ℓ • d) 0).1 = graphMap h bu bn (n₀ + ℓ • d) := rfl
    have e4 : (yStar h bu bn n₀ 0).1 = graphMap h bu bn n₀ := rfl
    rw [e1, e2, e3, e4]
    module
  rw [← hz0]
  refine (norm_fst_le _).trans (hcomb.trans (le_of_eq ?_))
  simp only [mul_zero, exp_zero, mul_one, GraphC2Hyp.Kc]
  ring

/-- The uniform constant of the second-level defect. -/
def GraphC2Hyp.Kd {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) : ℝ :=
  hd2.Kc * (L₂ * hd.K1 * (M / (1 - h.q)) + L₂ * (M / (1 - h.q)) * hd.K2 +
    L₃ * (M / (1 - h.q)) ^ 3)

theorem GraphC2Hyp.Kd_nonneg {hd : GraphC1Hyp h DNu DNv L₂} (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃) :
    0 ≤ hd2.Kd := by
  have hC1 : 0 ≤ M / (1 - h.q) := div_nonneg h.M_nonneg (sub_pos.2 h.contr).le
  have := hd.L₂_nonneg; have := hd2.L₃_nonneg; have := hd.K1_nonneg; have := hd2.Kc_nonneg
  have hK2 : 0 ≤ hd.K2 := by unfold GraphC1Hyp.K2; linarith [hd.K1_nonneg]
  unfold GraphC2Hyp.Kd
  positivity

/-- **The derivative of the graph has uniform quadratic three-point defects** (in operator norm). -/
theorem graphDeriv_quadDefect (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) : QuadDefect (graphDeriv hd bu bn) hd2.Kd := by
  intro n₀ v₁ v₂ v₃ a₁ a₂ a₃ hsum
  have hS0 : 0 ≤ |a₁| * ‖v₁‖ ^ 2 + |a₂| * ‖v₂‖ ^ 2 + |a₃| * ‖v₃‖ ^ 2 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hd2.Kd_nonneg hS0) fun d => ?_
  set a : Fin 3 → ℝ := ![a₁, a₂, a₃]
  set v : Fin 3 → Nn := ![v₁, v₂, v₃]
  have hsum' : ∑ i, a i • v i = 0 := by simpa [a, v, Fin.sum_univ_three] using hsum
  have hH := graphMap_quadDefect hd bu bn
  have hK := hd.K_nonneg
  have happ : (a₁ • (graphDeriv hd bu bn (n₀ + v₁) - graphDeriv hd bu bn n₀) +
      a₂ • (graphDeriv hd bu bn (n₀ + v₂) - graphDeriv hd bu bn n₀) +
      a₃ • (graphDeriv hd bu bn (n₀ + v₃) - graphDeriv hd bu bn n₀)) d =
      ∑ i, a i • (quadDeriv (graphMap h bu bn) (n₀ + v i) d -
        quadDeriv (graphMap h bu bn) n₀ d) := by
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
    ‖d‖ ^ 2 + 2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) + ∑ i, |a i| * (2 * hd.K * ‖d‖ ^ 2)) fun ℓ hℓ => ?_
  have h2 := second_level_le hd hd2 bu bn n₀ d hℓ a v hsum'
  have hq1 : ∀ n, ‖diffQuot (graphMap h bu bn) n d ℓ - quadDeriv (graphMap h bu bn) n d‖ ≤
      hd.K * ‖d‖ ^ 2 * ℓ := fun n => diffQuot_sub_quadDeriv_le hH hK n d hℓ
  have hdecomp : ∑ i, a i • (quadDeriv (graphMap h bu bn) (n₀ + v i) d -
        quadDeriv (graphMap h bu bn) n₀ d) =
      ∑ i, a i • (diffQuot (graphMap h bu bn) (n₀ + v i) d ℓ -
        diffQuot (graphMap h bu bn) n₀ d ℓ) -
      ∑ i, a i • ((diffQuot (graphMap h bu bn) (n₀ + v i) d ℓ -
          quadDeriv (graphMap h bu bn) (n₀ + v i) d) -
        (diffQuot (graphMap h bu bn) n₀ d ℓ - quadDeriv (graphMap h bu bn) n₀ d)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_sub]; congr 1; abel
  have herr : ‖∑ i, a i • ((diffQuot (graphMap h bu bn) (n₀ + v i) d ℓ -
          quadDeriv (graphMap h bu bn) (n₀ + v i) d) -
        (diffQuot (graphMap h bu bn) n₀ d ℓ - quadDeriv (graphMap h bu bn) n₀ d))‖ ≤
      (∑ i, |a i| * (2 * hd.K * ‖d‖ ^ 2)) * ℓ := by
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
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2 * ℓ + L₃ * C1 ^ 3 * ‖v i‖ ^ 2 * ‖d‖)) =
      hd2.Kd * S * ‖d‖ + hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * ‖d‖ ^ 2 +
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * ℓ := by
    simp only [GraphC2Hyp.Kd, S, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have := h2.trans (le_of_eq hsplit)
  calc _ ≤ hd2.Kd * S * ‖d‖ + hd2.Kc * (∑ i, |a i| * (L₂ * C1 * hd.K2 * ‖v i‖ * ‖d‖ ^ 2 +
        2 * L₂ * C1 ^ 2 * ‖d‖ ^ 2)) * ℓ + (∑ i, |a i| * (2 * hd.K * ‖d‖ ^ 2)) * ℓ :=
        add_le_add this herr
    _ = _ := by ring

/-- **The invariant graph is `C²`** (`lem:supp-exact-graph-criterion`, second-order regularity):
under `GraphHyp` (`j = 1`), `GraphC1Hyp` (`j = 2`, Lipschitz `DN`) and `GraphC2Hyp` (`j = 3`,
`3ν < β`, Lipschitz `D²N`, i.e. bounded third derivatives), the graph `h = graphMap` is `C²`; its
derivative `Dh = graphDeriv` is itself `C¹` with Lipschitz derivative. -/
theorem graphMap_contDiff_two (hd : GraphC1Hyp h DNu DNv L₂) (hd2 : GraphC2Hyp hd D2Nu D2Nv L₃)
    (bu : U) (bn : Nn) : ContDiff ℝ 2 (graphMap h bu bn) := by
  have hΛ : ContDiff ℝ 1 (graphDeriv hd bu bn) :=
    contDiff_one_of_quadDefect (graphDeriv_quadDefect hd hd2 bu bn) hd2.Kd_nonneg
      (fun n n' => graphDeriv_lipschitz hd bu bn n' n)
  have hfd : fderiv ℝ (graphMap h bu bn) = graphDeriv hd bu bn :=
    funext fun n => (graphMap_hasFDerivAt hd bu bn n).fderiv
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_fderiv]
  refine ⟨fun n => (graphMap_hasFDerivAt hd bu bn n).differentiableAt, fun h1 => ?_, ?_⟩
  · exact absurd h1 (by decide)
  · rw [hfd]; exact hΛ

end C2

/-- Non-vacuity of the `C²` layer: `P_u(t) = e^{4t}`, `P_n(t) = 1`, `M = 1`, `α = 0`, `ν = 1`,
`β = 4` (so `3ν < β`), `L = 0`, zero nonlinearities. -/
theorem graphC2Hyp_nonvacuous :
    ∃ (h : GraphHyp (U := ℝ) (Nn := ℝ) (fun t => exp (4 * t) • ContinuousLinearMap.id ℝ ℝ)
        (fun _ => ContinuousLinearMap.id ℝ ℝ) 1 0 4 1 0 (fun _ => 0) (fun _ => 0))
      (hd : GraphC1Hyp h (fun _ => 0) (fun _ => 0) 0), GraphC2Hyp hd (fun _ => 0) (fun _ => 0) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact
    { Pu_cont := ((continuous_const.mul continuous_id).rexp).smul continuous_const
      Pn_cont := continuous_const
      Pu_add := fun s t => by
        ext
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, smul_eq_mul, mul_one]
        rw [mul_add, exp_add]
      Pn_add := fun _ _ => by ext; simp
      Pu_zero := by ext; simp
      Pn_zero := rfl
      ν_pos := one_pos
      α_lt := zero_lt_one
      lt_β := by norm_num
      M_nonneg := zero_le_one
      L_nonneg := le_rfl
      Pu_bound := fun s _ => by
        rw [norm_smul, Real.norm_of_nonneg (exp_pos _).le]
        calc exp (4 * -s) * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ exp (4 * -s) * 1 :=
              mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (exp_pos _).le
          _ = 1 * exp (-4 * s) := by ring_nf
      Pn_bound := fun s _ => by simp
      Nu_lip := fun _ _ => by simp
      Nv_lip := fun _ _ => by simp
      contr := by norm_num }
  · exact
    { hasDeriv_u := fun _ => hasFDerivAt_const _ _
      hasDeriv_v := fun _ => hasFDerivAt_const _ _
      L₂_nonneg := le_rfl
      Du_lip := fun _ _ => by rw [zero_mul]; exact norm_le_zero_iff.mpr (sub_self _)
      Dv_lip := fun _ _ => by rw [zero_mul]; exact norm_le_zero_iff.mpr (sub_self _)
      two_lt := by norm_num
      contr2 := by norm_num }
  · exact
    { hasDeriv2_u := fun _ => hasFDerivAt_const _ _
      hasDeriv2_v := fun _ => hasFDerivAt_const _ _
      L₃_nonneg := le_rfl
      D2u_lip := fun _ _ => by
        rw [zero_mul]
        refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun p => ?_
        simp
      D2v_lip := fun _ _ => by
        rw [zero_mul]
        refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun p => ?_
        simp
      three_lt := by norm_num
      contr3 := by norm_num }

end

end LyapunovPerron
end RenewalGeometry
