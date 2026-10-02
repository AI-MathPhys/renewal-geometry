/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdySplitCharacteristicStability
import RenewalGeometry.Analysis.TensorHermiteReadout
import RenewalGeometry.Analysis.SecondOrderChainRuleLipschitz
import RenewalGeometry.Analysis.VectorLineTaylorRemainderBound
import RenewalGeometry.Gravity.CoordinateCurvatureJetLipschitz

/-!
# Pathwise full-curvature control of the Gowdy Hermite readout
  (`thm:supp-gowdy-full-curvature`; emergent-spacetime supplement)

This file assembles, for the concrete Gowdy scheme, the shared tensor-product cubic Hermite
readout of `f = (P, Q, λ)` from the derivative records `eq:supp-gowdy-hermite-jets` and proves the
pathwise estimates `eq:supp-gowdy-second-jet`, `eq:supp-gowdy-full-curvature` and the curvature
certificate `eq:supp-gowdy-curvature-certificate`.

* `GowdySmoothReference`: a smooth (`C^∞`) solution of the frame system
  `eq:supp-gowdy-frame-system` together with the coordinate constraints
  `eq:supp-gowdy-coordinate-constraints` (the manuscript's smooth reference `X_*`).
* `timeRec`, `spaceRec`: the time and space records `u, v` of `eq:supp-gowdy-hermite-jets` as
  smooth functions of the local state; `GowdySmoothReference.dT_fld`, `dΘ_fld`: on the slab they
  are the exact `t`- and `θ`-derivatives of the reference fields.
* `cellReadout X τ₀ ℓ n j k`: the readout of `f_k` on the space-time cell `(n, j)` from the nodal
  records of the numerical history `X` (values, `u`, `v`, `w = D₀u`).
* `GowdySmoothReference.readout_second_jet` (**`eq:supp-gowdy-second-jet`**): under the offset cap
  `eq:supp-gowdy-offset-cap` (residuals `≤ c₀ h⁴`) and the pathwise `C¹_h` bound
  `eq:supp-gowdy-pathwise-c1` (`≤ C₁ h²`), on every cell the readout and its first derivatives
  differ from the reference by `O(h²)`, its second derivatives by `O(h)`.
* `cellReadout_glue_t`, `cellReadout_glue_θ`: neighbouring cells share their nodal jets, so the
  readout is `C¹` across interfaces (`TensorHermiteReadout.readout_glue_x/y`).
* `gowdyMetric`, `gowdyInvMetric`: the metric `eq:supp-gowdy-metric` and its inverse as smooth
  maps of `(t, P, Q, λ)` on `t > 0` (`gowdyInvMetric_eq_inv`: it is the matrix inverse).
* `GowdySmoothReference.readout_full_curvature` (**`eq:supp-gowdy-full-curvature` and
  `eq:supp-gowdy-curvature-certificate`**): the metric reconstructed from the readout satisfies,
  on every cell, `‖g_h - g_*‖ + ‖Dg_h - Dg_*‖ ≤ C h²`, `‖D²g_h - D²g_*‖ ≤ C h`,
  `‖Riem(g_h) - Riem(g_*)‖ ≤ C h`, `‖Riem(g_h)‖ ≤ C`, and `‖Ric(g_h)‖ ≤ C h` wherever the
  reference is Ricci flat.  (That the reference metric is Ricci flat, i.e. that the frame system
  with constraints is the vacuum system for `eq:supp-gowdy-metric`, is not formalised here.)
* `zeroReference`, `zeroReference_pathwiseHistory`: non-vacuity of the reference structure and of
  the pathwise hypothesis packet.
-/

open Set Finset
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered

namespace HermiteReadout

open CubicHermite CubicHermiteRemainder TensorHermiteReadout CharStability

noncomputable section

/-! ### Periodicity and slab bounds of partial derivatives -/

theorem periodic_dP {F : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (p : ℝ × ℝ) : dP F (p.1, p.2 + 2 * Real.pi) = dP F p := by
  have hfun : (fun x : ℝ × ℝ => F (x + ((0 : ℝ), 2 * Real.pi))) = F := by
    funext x; rw [← hper x]; congr 1; ext <;> simp
  have e : ((p.1, p.2 + 2 * Real.pi) : ℝ × ℝ) = p + ((0 : ℝ), 2 * Real.pi) := by ext <;> simp
  unfold dP
  rw [e, ← fderiv_comp_add_right, hfun]

theorem periodic_dQ {F : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (p : ℝ × ℝ) : dQ F (p.1, p.2 + 2 * Real.pi) = dQ F p := by
  have hfun : (fun x : ℝ × ℝ => F (x + ((0 : ℝ), 2 * Real.pi))) = F := by
    funext x; rw [← hper x]; congr 1; ext <;> simp
  have e : ((p.1, p.2 + 2 * Real.pi) : ℝ × ℝ) = p + ((0 : ℝ), 2 * Real.pi) := by ext <;> simp
  unfold dQ
  rw [e, ← fderiv_comp_add_right, hfun]

theorem periodic_iterate_dP_dQ {F : ℝ × ℝ → ℝ}
    (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p) (a b : ℕ) (p : ℝ × ℝ) :
    (dP^[a] (dQ^[b] F)) (p.1, p.2 + 2 * Real.pi) = (dP^[a] (dQ^[b] F)) p := by
  have hb : ∀ b : ℕ, ∀ p : ℝ × ℝ, (dQ^[b] F) (p.1, p.2 + 2 * Real.pi) = (dQ^[b] F) p := by
    intro b
    induction b with
    | zero => exact hper
    | succ b ih => intro p; rw [Function.iterate_succ_apply']; exact periodic_dQ ih p
  induction a generalizing p with
  | zero => exact hb b p
  | succ a ih => rw [Function.iterate_succ_apply']; exact periodic_dP ih p

/-- A smooth function, `2π`-periodic in `θ`, has all partial derivatives of order `≤ 6` in each
variable uniformly bounded on the slab. -/
theorem exists_partials_bound {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p) (t₀ t₁ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ∀ a b : ℕ, a ≤ 6 → b ≤ 6 →
      |(dP^[a] (dQ^[b] F)) p| ≤ M := by
  have h := fun a b : ℕ => exists_bound_of_periodic (dP^[a] (dQ^[b] F))
    (contDiff_iterate_dP (contDiff_iterate_dQ hF b) a).continuous
    (periodic_iterate_dP_dQ hper a b) t₀ t₁
  choose C hC0 hC using h
  refine ⟨∑ a ∈ range 7, ∑ b ∈ range 7, C a b,
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hC0 a b, fun p hp a b ha hb => ?_⟩
  have h1 := hC a b p hp
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hb' : C a b ≤ ∑ b ∈ range 7, C a b :=
    Finset.single_le_sum (f := fun b => C a b) (fun b _ => hC0 a b) (mem_range.2 (by omega))
  have ha' : ∑ b ∈ range 7, C a b ≤ ∑ a ∈ range 7, ∑ b ∈ range 7, C a b :=
    Finset.single_le_sum (f := fun a => ∑ b ∈ range 7, C a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hC0 a b) (mem_range.2 (by omega))
  linarith

/-! ### The smooth reference -/

/-- **The smooth reference `X_*`**: a `C^∞` solution of the Gowdy frame system
`eq:supp-gowdy-frame-system` on `[t₀, t₁] × 𝕋¹` which also satisfies the coordinate constraints
`eq:supp-gowdy-coordinate-constraints` `P_θ = b`, `e^P Q_θ = d`, `λ_θ = 2 t f` with
`f = ab + cd`. -/
structure GowdySmoothReference (t₀ t₁ : ℝ) extends GowdyFrameSolution t₀ t₁ where
  smoothInf_a : ContDiff ℝ ∞ a
  smoothInf_b : ContDiff ℝ ∞ b
  smoothInf_c : ContDiff ℝ ∞ c
  smoothInf_d : ContDiff ℝ ∞ d
  smoothInf_P : ContDiff ℝ ∞ P
  smoothInf_Q : ContDiff ℝ ∞ Q
  smoothInf_lam : ContDiff ℝ ∞ lam
  constraint_P : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dΘ P p = b p
  constraint_Q : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → Real.exp (P p) * dΘ Q p = d p
  constraint_lam : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dΘ lam p = 2 * p.1 * (a p * b p + c p * d p)

/-! ### Records of the local state -/

/-- The time records `u = (u₁/√t, e^{-P} u₃/√t, |U|²)` of `eq:supp-gowdy-hermite-jets`. -/
def timeRec (k : Fin 3) (v : StateVec) : ℝ :=
  ![v.1 0 / Real.sqrt v.2.2.2, Real.exp (-v.2.1) * v.1 2 / Real.sqrt v.2.2.2,
    v.1 0 ^ 2 + v.1 1 ^ 2 + v.1 2 ^ 2 + v.1 3 ^ 2] k

/-- The space records `v = (u₂/√t, e^{-P} u₄/√t, 2 𝒥(U))` of `eq:supp-gowdy-hermite-jets`. -/
def spaceRec (k : Fin 3) (v : StateVec) : ℝ :=
  ![v.1 1 / Real.sqrt v.2.2.2, Real.exp (-v.2.1) * v.1 3 / Real.sqrt v.2.2.2,
    2 * (v.1 0 * v.1 1 + v.1 2 * v.1 3)] k

/-- The open region `t > 0` of the local state space. -/
def posClock : Set StateVec := {v | 0 < v.2.2.2}

theorem isOpen_posClock : IsOpen posClock :=
  isOpen_lt continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd))

theorem contDiffOn_timeRec (k : Fin 3) : ContDiffOn ℝ ∞ (timeRec k) posClock := by
  have hs : ContDiffOn ℝ ∞ (fun v : StateVec => Real.sqrt v.2.2.2) posClock :=
    ContDiffOn.sqrt (by fun_prop) fun v hv => (ne_of_gt hv)
  have hne : ∀ v ∈ posClock, Real.sqrt v.2.2.2 ≠ 0 := fun v hv =>
    (Real.sqrt_pos.2 hv).ne'
  fin_cases k
  · show ContDiffOn ℝ ∞ (fun v => timeRec _ v) posClock
    simp only [timeRec]
    exact ContDiffOn.div (by fun_prop) hs hne
  · show ContDiffOn ℝ ∞ (fun v => timeRec _ v) posClock
    simp only [timeRec]
    exact ContDiffOn.div (by fun_prop) hs hne
  · show ContDiffOn ℝ ∞ (fun v => timeRec _ v) posClock
    simp only [timeRec]
    exact (by fun_prop : ContDiff ℝ ∞ fun v : StateVec =>
      v.1 0 ^ 2 + v.1 1 ^ 2 + v.1 2 ^ 2 + v.1 3 ^ 2).contDiffOn

theorem contDiffOn_spaceRec (k : Fin 3) : ContDiffOn ℝ ∞ (spaceRec k) posClock := by
  have hs : ContDiffOn ℝ ∞ (fun v : StateVec => Real.sqrt v.2.2.2) posClock :=
    ContDiffOn.sqrt (by fun_prop) fun v hv => (ne_of_gt hv)
  have hne : ∀ v ∈ posClock, Real.sqrt v.2.2.2 ≠ 0 := fun v hv =>
    (Real.sqrt_pos.2 hv).ne'
  fin_cases k
  · show ContDiffOn ℝ ∞ (fun v => spaceRec _ v) posClock
    simp only [spaceRec]
    exact ContDiffOn.div (by fun_prop) hs hne
  · show ContDiffOn ℝ ∞ (fun v => spaceRec _ v) posClock
    simp only [spaceRec]
    exact ContDiffOn.div (by fun_prop) hs hne
  · show ContDiffOn ℝ ∞ (fun v => spaceRec _ v) posClock
    simp only [spaceRec]
    exact (by fun_prop : ContDiff ℝ ∞ fun v : StateVec =>
      2 * (v.1 0 * v.1 1 + v.1 2 * v.1 3)).contDiffOn

theorem chartK_subset_posClock {t₀ R : ℝ} (h0 : 0 < t₀) : chartK t₀ R ⊆ posClock :=
  fun v hv => lt_of_lt_of_le (by linarith : (0 : ℝ) < t₀ / 2) hv.2

/-- **Discrete chain rule**: for `G` differentiable on a convex set `K` with `‖DG‖ ≤ M₁` and
`DG` `L₁`-Lipschitz on `K`, and `x, x', y, y' ∈ K`,
`‖G x' - G y' - (G x - G y)‖ ≤ M₁ ‖(x' - y') - (x - y)‖ + L₁ max(‖x - y‖, ‖x' - y'‖) ‖y' - y‖`. -/
theorem norm_sub_sub_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {K : Set E} (hK : Convex ℝ K)
    (hG : ∀ x ∈ K, DifferentiableAt ℝ G x) {M₁ L₁ : ℝ}
    (hM : ∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ M₁)
    (hL : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ L₁ * ‖x - y‖) (hL0 : 0 ≤ L₁)
    {x x' y y' : E} (hx : x ∈ K) (hx' : x' ∈ K) (hy : y ∈ K) (hy' : y' ∈ K) :
    ‖G x' - G y' - (G x - G y)‖ ≤
      M₁ * ‖(x' - y') - (x - y)‖ + L₁ * max ‖x - y‖ ‖x' - y'‖ * ‖y' - y‖ := by
  set a := x' - x
  set b := y' - y
  have hpx : ∀ s ∈ Icc (0 : ℝ) 1, x + s • a ∈ K := by
    intro s hs
    have := hK.add_smul_sub_mem hx hx' hs
    simpa [a] using this
  have hpy : ∀ s ∈ Icc (0 : ℝ) 1, y + s • b ∈ K := by
    intro s hs
    have := hK.add_smul_sub_mem hy hy' hs
    simpa [b] using this
  set φ : ℝ → F := fun s => G (x + s • a) - G (y + s • b)
  set φ' : ℝ → F := fun s => fderiv ℝ G (x + s • a) a - fderiv ℝ G (y + s • b) b
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Icc 0 1) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    have h2 : HasDerivAt (fun s : ℝ => y + s • b) b s := by
      simpa using ((hasDerivAt_id s).smul_const b).const_add y
    have g1 := (hG _ (hpx s hs)).hasFDerivAt.comp_hasDerivAt s h1
    have g2 := (hG _ (hpy s hs)).hasFDerivAt.comp_hasDerivAt s h2
    exact (g1.sub g2).hasDerivWithinAt
  set D := max ‖x - y‖ ‖x' - y'‖
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖φ' s‖ ≤ M₁ * ‖a - b‖ + L₁ * D * ‖b‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    have e : φ' s = fderiv ℝ G (x + s • a) (a - b) +
        (fderiv ℝ G (x + s • a) - fderiv ℝ G (y + s • b)) b := by
      simp only [φ', map_sub, ContinuousLinearMap.sub_apply]; abel
    rw [e]
    have t1 : ‖fderiv ℝ G (x + s • a) (a - b)‖ ≤ M₁ * ‖a - b‖ :=
      ((fderiv ℝ G (x + s • a)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hM _ (hpx s hs')) (norm_nonneg _))
    have hdist : ‖(x + s • a) - (y + s • b)‖ ≤ D := by
      have e2 : (x + s • a) - (y + s • b) = (1 - s) • (x - y) + s • (x' - y') := by
        simp only [a, b, smul_sub]; module
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs.1,
        abs_of_nonneg (by linarith [hs.2])]
      have := le_max_left ‖x - y‖ ‖x' - y'‖
      have := le_max_right ‖x - y‖ ‖x' - y'‖
      nlinarith [hs.1, hs.2, norm_nonneg (x - y), norm_nonneg (x' - y')]
    have t2 : ‖(fderiv ℝ G (x + s • a) - fderiv ℝ G (y + s • b)) b‖ ≤ L₁ * D * ‖b‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_
        (norm_nonneg _))
      exact (hL _ (hpx s hs') _ (hpy s hs')).trans (mul_le_mul_of_nonneg_left hdist hL0)
    exact (norm_add_le _ _).trans (add_le_add t1 t2)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_refl _⟩
  have e0 : φ 0 = G x - G y := by simp [φ]
  have e1 : φ 1 = G x' - G y' := by simp [φ, a, b]
  rw [e0, e1, sub_zero, mul_one] at this
  have hab : a - b = (x' - y') - (x - y) := by simp only [a, b]; abel
  rw [hab] at this
  exact this


/-- Constants of a `C²` map on a compact convex subset of an open set: a Lipschitz constant, a
bound of the derivative and a Lipschitz constant of the derivative. -/
theorem exists_map_consts {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {V K : Set E} (hV : IsOpen V)
    (hG : ContDiffOn ℝ 2 G V) (hKV : K ⊆ V) (hKc : IsCompact K) (hKx : Convex ℝ K) :
    ∃ L₀ M₁ L₁ : ℝ, 0 ≤ L₀ ∧ 0 ≤ M₁ ∧ 0 ≤ L₁ ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖G x - G y‖ ≤ L₀ * ‖x - y‖) ∧
      (∀ x ∈ K, DifferentiableAt ℝ G x) ∧ (∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ M₁) ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ L₁ * ‖x - y‖) := by
  have hd1 : ContDiffOn ℝ 1 (fderiv ℝ G) V := hG.fderiv_of_isOpen hV (by norm_num)
  obtain ⟨L₀, hL₀⟩ := (hG.mono hKV).exists_lipschitzOnWith (by norm_num) hKx hKc
  obtain ⟨L₁, hL₁⟩ := (hd1.mono hKV).exists_lipschitzOnWith (by norm_num) hKx hKc
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ G)
    (hd1.continuousOn.mono hKV)
  refine ⟨L₀, |M₁|, L₁, L₀.2, abs_nonneg _, L₁.2, fun x hx y hy => ?_, fun x hx => ?_,
    fun x hx => (hM₁ x hx).trans (le_abs_self _), fun x hx y hy => ?_⟩
  · have := hL₀.dist_le_mul x hx y hy; rwa [dist_eq_norm, dist_eq_norm] at this
  · exact (hG.contDiffAt (hV.mem_nhds (hKV hx))).differentiableAt (by norm_num)
  · have := hL₁.dist_le_mul x hx y hy; rwa [dist_eq_norm, dist_eq_norm] at this

/-! ### The reference fields and their records -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

/-- The reference fields `f = (P, Q, λ)`. -/
def fld : Fin 3 → ℝ × ℝ → ℝ := ![sol.P, sol.Q, sol.lam]

theorem smooth_fld (k : Fin 3) : ContDiff ℝ ∞ (sol.fld k) := by
  fin_cases k
  · exact sol.smoothInf_P
  · exact sol.smoothInf_Q
  · exact sol.smoothInf_lam

theorem periodic_fld (k : Fin 3) (p : ℝ × ℝ) :
    sol.fld k (p.1, p.2 + 2 * Real.pi) = sol.fld k p := by
  fin_cases k
  · exact sol.periodic_P p
  · exact sol.periodic_Q p
  · exact sol.periodic_lam p

/-- **The time records are the exact `t`-derivatives on the slab**: `∂_t f_k = u_k(X_*)`. -/
theorem dT_fld (h0 : 0 < t₀) (k : Fin 3) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    dP (sol.fld k) p = timeRec k (sol.Z p) := by
  have hp2 : t₀ / 2 ≤ p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hpos.le
  rw [sol.Z_eq h0 hp2]
  fin_cases k
  · show dT sol.P p = _
    rw [sol.eq_P p hp]
    simp only [timeRec, GowdyFrameSolution.fr]
    simp
    field_simp
  · show dT sol.Q p = _
    rw [sol.eq_Q p hp]
    simp only [timeRec, GowdyFrameSolution.fr]
    simp
    field_simp
  · show dT sol.lam p = _
    rw [sol.eq_lam p hp]
    simp only [timeRec, GowdyFrameSolution.fr]
    simp
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hss]
    ring

/-- **The space records are the exact `θ`-derivatives on the slab** (by the coordinate
constraints): `∂_θ f_k = v_k(X_*)`. -/
theorem dΘ_fld (h0 : 0 < t₀) (k : Fin 3) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    dQ (sol.fld k) p = spaceRec k (sol.Z p) := by
  have hp2 : t₀ / 2 ≤ p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hpos.le
  rw [sol.Z_eq h0 hp2]
  fin_cases k
  · show dΘ sol.P p = _
    rw [sol.constraint_P p hp]
    simp only [spaceRec, GowdyFrameSolution.fr]
    simp
    field_simp
  · show dΘ sol.Q p = _
    have hc := sol.constraint_Q p hp
    have hQ : dΘ sol.Q p = Real.exp (-sol.P p) * sol.d p := by
      rw [← hc, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hQ]
    simp only [spaceRec, GowdyFrameSolution.fr]
    simp
    field_simp
  · show dΘ sol.lam p = _
    rw [sol.constraint_lam p hp]
    simp only [spaceRec, GowdyFrameSolution.fr]
    simp
    have : Real.sqrt p.1 * sol.a p * (Real.sqrt p.1 * sol.b p) +
        Real.sqrt p.1 * sol.c p * (Real.sqrt p.1 * sol.d p) =
        Real.sqrt p.1 ^ 2 * (sol.a p * sol.b p + sol.c p * sol.d p) := by ring
    rw [this, hss]
    ring

/-- The reference state is Lipschitz in `θ` on the slab, with constant `derivBound`. -/
theorem norm_Z_sub_le (h0 : 0 < t₀) {τ θ θ' : ℝ} (hτ : τ ∈ Icc t₀ t₁) :
    ‖sol.Z (τ, θ') - sol.Z (τ, θ)‖ ≤ sol.derivBound h0 * |θ' - θ| := by
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc t₀ t₁}
  have hS : Convex ℝ S := (convex_Icc t₀ t₁).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have hd : ∀ x ∈ S, DifferentiableAt ℝ sol.Z x := fun x _ =>
    (sol.contDiff_Z h0).differentiable (by norm_num) x
  have hb : ∀ x ∈ S, ‖fderiv ℝ sol.Z x‖ ≤ sol.derivBound h0 := by
    intro x hx
    rw [← norm_iteratedFDeriv_one]
    exact ((sol.derivBound_spec h0).2 x hx).1
  have := hS.norm_image_sub_le_of_norm_fderiv_le hd hb (show (τ, θ) ∈ S from hτ)
    (show (τ, θ') ∈ S from hτ)
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [Prod.norm_def]
  simp

end GowdySmoothReference

/-! ### Nodal values of grid states -/

variable {N : ℕ} [NeZero N]

/-- The nodal value of the field `f_k` (`P`, `Q` or `λ`) of a grid state. -/
def gval (k : Fin 3) (S : GridState N) (j : ZMod N) : ℝ :=
  ![(S.site j).P, (S.site j).Q, S.lam j] k

theorem abs_gval_sub_le (k : Fin 3) (X Y : GridState N) (j : ZMod N) :
    |gval k X j - gval k Y j| ≤ ‖errArr X Y j‖ := by
  have h1 : ‖(X.site j).toVec - (Y.site j).toVec‖ ≤ ‖errArr X Y j‖ := norm_fst_le (errArr X Y j)
  have h2 : |X.lam j - Y.lam j| ≤ ‖errArr X Y j‖ := by
    have := norm_snd_le (errArr X Y j); rwa [Real.norm_eq_abs] at this
  fin_cases k
  · exact (abs_P_le _).trans h1
  · exact (abs_Q_le _).trans h1
  · exact h2

theorem norm_site_sub_le_errArr (X Y : GridState N) (j : ZMod N) :
    ‖(X.site j).toVec - (Y.site j).toVec‖ ≤ ‖errArr X Y j‖ := norm_fst_le (errArr X Y j)

theorem errArr_succ_sub (ℓ : ℝ) (hℓ : 0 < ℓ) (X Y : GridState N) (j : ZMod N) :
    ‖errArr X Y (j + 1) - errArr X Y j‖ ≤ ℓ * ‖PeriodicGridResidual.fwdDiff ℓ (errArr X Y)‖ := by
  have e : errArr X Y (j + 1) - errArr X Y j =
      ℓ • PeriodicGridResidual.fwdDiff ℓ (errArr X Y) j := by
    simp only [PeriodicGridResidual.fwdDiff, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) hℓ.le

theorem norm_le_crNorm_one (ℓ : ℝ) (v : ZMod N → StateVec × ℝ) :
    ‖v‖ ≤ PeriodicGridResidual.crNorm 1 ℓ v := by
  have h := Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖)
    (mem_range.2 (by norm_num : 0 < 1 + 1))
  exact h

theorem norm_fwdDiff_le_crNorm_one (ℓ : ℝ) (v : ZMod N → StateVec × ℝ) :
    ‖PeriodicGridResidual.fwdDiff ℓ v‖ ≤ PeriodicGridResidual.crNorm 1 ℓ v := by
  have h := Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖)
    (mem_range.2 (by norm_num : 1 < 1 + 1))
  exact h

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

theorem sample_toVec (τ : ℝ) (j : ZMod N) :
    ((sol.sample N τ).site j).toVec = sol.Z (τ, sampleAngle N j) := rfl

theorem gval_sample (k : Fin 3) (τ : ℝ) (j : ZMod N) :
    gval k (sol.sample N τ) j = sol.fld k (τ, sampleAngle N j) := by
  fin_cases k <;> rfl

/-- Corner evaluation: on the cell `(n, j)`, the corner `(a, b)` is the node
`(τ₀ + (n + a) ℓ, θ_{j+b})` up to a period in `θ`. -/
theorem corner_eval {F : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (τ₀ : ℝ) (n : ℕ) (j : ZMod N) (a b : Fin 2) :
    F (cellMap (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j) (2 * Real.pi / N)
        (((a : ℕ) : ℝ), ((b : ℕ) : ℝ))) =
      F (τ₀ + ((n + a : ℕ) : ℝ) * (2 * Real.pi / N), sampleAngle N (j + ((b : ℕ) : ZMod N))) := by
  simp only [cellMap]
  have et : τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N * ((a : ℕ) : ℝ) =
      τ₀ + ((n + a : ℕ) : ℝ) * (2 * Real.pi / N) := by push_cast; ring
  rw [et]
  fin_cases b
  · simp
  · simp only [Nat.cast_one]
    rw [sample_succ F hper N]
    congr 2
    ring

end GowdySmoothReference


/-! ### The nodal records and the cellwise readout -/

/-- Value records `f` of the field `f_k` on the cell `(n, j)`: nodal values at the corners
`(n + a, j + b)`. -/
def numF (X : ℕ → GridState N) (n : ℕ) (j : ZMod N) (k : Fin 3) : Fin 2 → Fin 2 → ℝ :=
  fun a b => gval k (X (n + a)) (j + ((b : ℕ) : ZMod N))

/-- Time records `u` (`eq:supp-gowdy-hermite-jets`) on the cell `(n, j)`. -/
def numU (X : ℕ → GridState N) (n : ℕ) (j : ZMod N) (k : Fin 3) : Fin 2 → Fin 2 → ℝ :=
  fun a b => timeRec k ((X (n + a)).site (j + ((b : ℕ) : ZMod N))).toVec

/-- Space records `v` (`eq:supp-gowdy-hermite-jets`) on the cell `(n, j)`. -/
def numV (X : ℕ → GridState N) (n : ℕ) (j : ZMod N) (k : Fin 3) : Fin 2 → Fin 2 → ℝ :=
  fun a b => spaceRec k ((X (n + a)).site (j + ((b : ℕ) : ZMod N))).toVec

/-- Mixed records `w = D₀ u`, `D₀ = (S₊ - S₋)/(2h)` (`eq:supp-gowdy-hermite-jets`). -/
def numW (X : ℕ → GridState N) (n : ℕ) (j : ZMod N) (k : Fin 3) : Fin 2 → Fin 2 → ℝ :=
  fun a b => (timeRec k ((X (n + a)).site (j + ((b : ℕ) : ZMod N) + 1)).toVec -
    timeRec k ((X (n + a)).site (j + ((b : ℕ) : ZMod N) - 1)).toVec) / (2 * (2 * Real.pi / N))

/-- **The shared tensor-product cubic Hermite readout** of `f_k` on the space-time cell
`[τ₀ + nℓ, τ₀ + (n+1)ℓ] × [θ_j, θ_j + ℓ]`, `ℓ = h = 2π/N`, built from the nodal records of the
numerical history `X`. -/
def cellReadout (X : ℕ → GridState N) (τ₀ : ℝ) (n : ℕ) (j : ZMod N) (k : Fin 3) :
    ℝ × ℝ → ℝ :=
  readout (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j) (2 * Real.pi / N) (numF X n j k)
    (numU X n j k) (numV X n j k) (numW X n j k)

/-! ### Elementary estimates for the corner records -/

theorem abs_gval_diff_le (k : Fin 3) (X Y : GridState N) (j j' : ZMod N) :
    |gval k X j' - gval k Y j' - (gval k X j - gval k Y j)| ≤
      ‖errArr X Y j' - errArr X Y j‖ := by
  have e1 : errArr X Y j' - errArr X Y j =
      (((X.site j').toVec - (Y.site j').toVec) - ((X.site j).toVec - (Y.site j).toVec),
        (X.lam j' - Y.lam j') - (X.lam j - Y.lam j)) := rfl
  have h1 := norm_fst_le (errArr X Y j' - errArr X Y j)
  have h2 := norm_snd_le (errArr X Y j' - errArr X Y j)
  rw [e1] at h1 h2
  simp only at h1 h2
  rw [Real.norm_eq_abs] at h2
  fin_cases k
  · refine le_trans (le_of_eq ?_) ((abs_P_le _).trans h1)
    simp [gval, LocalState.toVec]
  · refine le_trans (le_of_eq ?_) ((abs_Q_le _).trans h1)
    simp [gval, LocalState.toVec]
  · show |X.lam j' - Y.lam j' - (X.lam j - Y.lam j)| ≤ _
    exact h2

/-- Mixed records: `D₀` of a smooth function of two nearby grid histories. -/
theorem abs_centered_sub_le {G : StateVec → ℝ} {K : Set StateVec} (hK : Convex ℝ K)
    (hG : ∀ x ∈ K, DifferentiableAt ℝ G x) {M₁ L₁ : ℝ}
    (hM : ∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ M₁)
    (hL : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ L₁ * ‖x - y‖) (hL0 : 0 ≤ L₁)
    {xm x0 xp ym y0 yp : StateVec} (hxm : xm ∈ K) (hx0 : x0 ∈ K) (hxp : xp ∈ K)
    (hym : ym ∈ K) (hy0 : y0 ∈ K) (hyp : yp ∈ K) {ℓ ε δ D : ℝ} (hℓ : 0 < ℓ)
    (hεm : ‖xm - ym‖ ≤ ε) (hε0 : ‖x0 - y0‖ ≤ ε) (hεp : ‖xp - yp‖ ≤ ε)
    (hδp : ‖(xp - yp) - (x0 - y0)‖ ≤ ℓ * δ) (hδm : ‖(x0 - y0) - (xm - ym)‖ ≤ ℓ * δ)
    (hDp : ‖yp - y0‖ ≤ D * ℓ) (hDm : ‖y0 - ym‖ ≤ D * ℓ) :
    |(G xp - G xm) / (2 * ℓ) - (G yp - G ym) / (2 * ℓ)| ≤ M₁ * δ + L₁ * ε * D := by
  have hM0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM _ hx0)
  have hε : 0 ≤ ε := (norm_nonneg _).trans hε0
  have t1 := norm_sub_sub_sub_le hK hG hM hL hL0 hx0 hxp hy0 hyp
  have t2 := norm_sub_sub_sub_le hK hG hM hL hL0 hxm hx0 hym hy0
  rw [Real.norm_eq_abs] at t1 t2
  have hmax1 : max ‖x0 - y0‖ ‖xp - yp‖ ≤ ε := max_le hε0 hεp
  have hmax2 : max ‖xm - ym‖ ‖x0 - y0‖ ≤ ε := max_le hεm hε0
  have b1 : M₁ * ‖(xp - yp) - (x0 - y0)‖ + L₁ * max ‖x0 - y0‖ ‖xp - yp‖ * ‖yp - y0‖ ≤
      M₁ * (ℓ * δ) + L₁ * ε * (D * ℓ) := by
    have := mul_le_mul_of_nonneg_left hδp hM0
    have := mul_le_mul (mul_le_mul_of_nonneg_left hmax1 hL0) hDp (norm_nonneg _)
      (mul_nonneg hL0 hε)
    linarith
  have b2 : M₁ * ‖(x0 - y0) - (xm - ym)‖ + L₁ * max ‖xm - ym‖ ‖x0 - y0‖ * ‖y0 - ym‖ ≤
      M₁ * (ℓ * δ) + L₁ * ε * (D * ℓ) := by
    have := mul_le_mul_of_nonneg_left hδm hM0
    have := mul_le_mul (mul_le_mul_of_nonneg_left hmax2 hL0) hDm (norm_nonneg _)
      (mul_nonneg hL0 hε)
    linarith
  have e : (G xp - G xm) / (2 * ℓ) - (G yp - G ym) / (2 * ℓ) =
      ((G xp - G yp - (G x0 - G y0)) + (G x0 - G y0 - (G xm - G ym))) / (2 * ℓ) := by ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ℓ), div_le_iff₀ (by positivity)]
  have := abs_add_le (G xp - G yp - (G x0 - G y0)) (G x0 - G y0 - (G xm - G ym))
  nlinarith

/-- **Centered-difference consistency of the mixed record**:
`|(∂_tφ(τ, ψ+ℓ) - ∂_tφ(τ, ψ-ℓ))/(2ℓ) - ∂_t∂_θφ(τ, ψ)| ≤ M ℓ²/2` when `|∂_θ³∂_tφ(τ, ·)| ≤ M`. -/
theorem abs_centered_partial_le {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ψ : ℝ) {M ℓ : ℝ}
    (hℓ : 0 < ℓ) (hM : ∀ s : ℝ, |(dP^[1] (dQ^[3] φ)) (τ, s)| ≤ M) :
    |(dP φ (τ, ψ + ℓ) - dP φ (τ, ψ - ℓ)) / (2 * ℓ) - dP (dQ φ) (τ, ψ)| ≤ M * ℓ ^ 2 / 2 := by
  have hdP : ContDiff ℝ ∞ (dP φ) := contDiff_dP hφ
  set f : ℝ → ℝ := fun q => dP φ (τ, q)
  set g : ℝ → ℝ := fun s => f (ψ + s)
  have hf : ContDiff ℝ ∞ f := contDiff_section_q hdP τ
  have hg : ContDiff ℝ 3 g := (hf.comp (contDiff_const.add contDiff_id)).of_le (by norm_cast)
  have hit : ∀ m : ℕ, iteratedDeriv m g = fun s => (dQ^[m] (dP φ)) (τ, ψ + s) := by
    intro m
    have h1 := iteratedDeriv_comp_const_add m f ψ
    rw [iteratedDeriv_section_q hdP m τ] at h1
    exact h1
  have hM' : ∀ s, ‖iteratedDeriv 3 g s‖ ≤ M := by
    intro s
    rw [hit 3, Real.norm_eq_abs]
    have e : dQ^[3] (dP φ) = dP^[1] (dQ^[3] φ) := iterate_dQ_iterate_dP hφ 1 3
    rw [e]
    exact hM _
  have h := VectorLineTaylor.norm_centered_difference_sub_deriv_le g M hg hM' hℓ
  rw [hit 1, Real.norm_eq_abs] at h
  simp only [Function.iterate_one, add_zero, smul_eq_mul] at h
  have e2 : dQ (dP φ) = dP (dQ φ) := dQ_dP hφ
  rw [e2] at h
  have e3 : (2 * ℓ)⁻¹ * (g ℓ - g (-ℓ)) = (dP φ (τ, ψ + ℓ) - dP φ (τ, ψ - ℓ)) / (2 * ℓ) := by
    simp only [g, f, ← sub_eq_add_neg]; ring
  rw [e3] at h
  exact h

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

/-- Nodes near the reference lie in the compact chart `chartK t₀ chartRadius`. -/
theorem node_mem (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) {x : StateVec} {ε : ℝ}
    (hx : ‖x - sol.Z p‖ ≤ ε) (hε1 : ε ≤ 1) (hεt : ε ≤ t₀ / 2) :
    x ∈ chartK t₀ (sol.chartRadius h0) ∧ sol.Z p ∈ chartK t₀ (sol.chartRadius h0) := by
  have hZ := (sol.chartRadius_spec h0).2 p hp
  have hZt : (sol.Z p).2.2.2 = p.1 := rfl
  refine ⟨⟨?_, ?_⟩, ⟨by linarith, by rw [hZt]; linarith [hp.1]⟩⟩
  · have := norm_sub_norm_le x (sol.Z p)
    linarith
  · have h1 := abs_t_le (x - sol.Z p)
    have h2 : (x - sol.Z p).2.2.2 = x.2.2.2 - p.1 := rfl
    rw [h2] at h1
    have := (abs_le.1 (h1.trans hx)).1
    linarith [hp.1]

end GowdySmoothReference


/-! ### The pathwise hypotheses and the nodal record errors -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

/-- **The pathwise hypotheses of `thm:supp-gowdy-full-curvature`** on a numerical history
`X_n` (`n ≤ n₀`, times `τ₀ + nℓ`, `ℓ = h = 2π/N`): every step `X_n → A_n → B_n` is a split step
of the scheme in the enforced envelope of radius `R`, the accepted offsets/solver errors obey the
cap `charDist(X_{n+1}, B_n) ≤ c₀ h⁴` (`eq:supp-gowdy-offset-cap`), and the pathwise `C¹_h` error is
`‖X_n - 𝖲_h X_*(t_n)‖_{1,∞,h} ≤ C₁ h²` (`eq:supp-gowdy-pathwise-c1`). -/
structure PathwiseHistory (h0 : 0 < t₀) (R c₀ C₁ : ℝ) (N : ℕ) [NeZero N] (τ₀ : ℝ) (n₀ : ℕ)
    (X A B : ℕ → GridState N) : Prop where
  start : t₀ ≤ τ₀
  stop : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁
  step : ∀ n < n₀, IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
    SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n)
  offset : ∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4
  c1 : ∀ n ≤ n₀, PeriodicGridResidual.crNorm 1 (2 * Real.pi / N)
    (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤ C₁ * (2 * Real.pi / N) ^ 2

variable {sol}

theorem PathwiseHistory.time_mem {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    {m : ℕ} (hm : m ≤ n₀) : τ₀ + m * (2 * Real.pi / N) ∈ Icc t₀ t₁ := by
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hm' : (m : ℝ) ≤ n₀ := by exact_mod_cast hm
  constructor
  · have : 0 ≤ (m : ℝ) * (2 * Real.pi / N) := by positivity
    linarith [H.start]
  · have := mul_le_mul_of_nonneg_right hm' hℓ.le
    linarith [H.stop]

/-- Nodal value error. -/
theorem PathwiseHistory.value_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    (k : Fin 3) {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    |gval k (X m) j - sol.fld k (τ₀ + m * (2 * Real.pi / N), sampleAngle N j)| ≤
      C₁ * (2 * Real.pi / N) ^ 2 := by
  rw [← gval_sample]
  exact (abs_gval_sub_le k _ _ j).trans ((norm_le_pi_norm _ j).trans
    ((norm_le_crNorm_one _ _).trans (H.c1 m hm)))

theorem PathwiseHistory.site_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    ‖((X m).site j).toVec - sol.Z (τ₀ + m * (2 * Real.pi / N), sampleAngle N j)‖ ≤
      C₁ * (2 * Real.pi / N) ^ 2 := by
  rw [← sample_toVec]
  exact (norm_site_sub_le_errArr _ _ j).trans ((norm_le_pi_norm _ j).trans
    ((norm_le_crNorm_one _ _).trans (H.c1 m hm)))

theorem PathwiseHistory.site_diff_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    ‖(((X m).site (j + 1)).toVec - sol.Z (τ₀ + m * (2 * Real.pi / N), sampleAngle N (j + 1))) -
        (((X m).site j).toVec - sol.Z (τ₀ + m * (2 * Real.pi / N), sampleAngle N j))‖ ≤
      (2 * Real.pi / N) * (C₁ * (2 * Real.pi / N) ^ 2) := by
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  rw [← sample_toVec, ← sample_toVec]
  set E := errArr (X m) (sol.sample N (τ₀ + m * (2 * Real.pi / N)))
  have h1 := norm_fst_le (E (j + 1) - E j)
  have h2 := errArr_succ_sub _ hℓ (X m) (sol.sample N (τ₀ + m * (2 * Real.pi / N))) j
  refine h1.trans (h2.trans (mul_le_mul_of_nonneg_left ((norm_fwdDiff_le_crNorm_one _ _).trans
    (H.c1 m hm)) hℓ.le))

/-- Nodal first differences in space of the value errors: `O(h³)`. -/
theorem PathwiseHistory.space_diff_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N]
    {τ₀ : ℝ} {n₀ : ℕ} {X A B : ℕ → GridState N}
    (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B) (k : Fin 3) {m : ℕ} (hm : m ≤ n₀)
    (j : ZMod N) :
    |gval k (X m) (j + 1) - sol.fld k (τ₀ + m * (2 * Real.pi / N), sampleAngle N (j + 1)) -
        (gval k (X m) j - sol.fld k (τ₀ + m * (2 * Real.pi / N), sampleAngle N j))| ≤
      (2 * Real.pi / N) * (C₁ * (2 * Real.pi / N) ^ 2) := by
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  rw [← gval_sample, ← gval_sample]
  refine (abs_gval_diff_le k _ _ j (j + 1)).trans ((errArr_succ_sub _ hℓ _ _ j).trans ?_)
  exact mul_le_mul_of_nonneg_left ((norm_fwdDiff_le_crNorm_one _ _).trans (H.c1 m hm)) hℓ.le

/-- Nodal first differences in time of the value errors: `O(h³)`, from the scheme
(`GowdyFrameSolution.nodal_time_difference`), the offset cap and the pathwise bound. -/
theorem PathwiseHistory.time_diff_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N]
    {τ₀ : ℝ} {n₀ : ℕ} {X A B : ℕ → GridState N}
    (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B) (hR : sol.chartRadius h0 ≤ R)
    (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (hℓ1 : 2 * Real.pi / N ≤ 1) (hc₀ : 0 ≤ c₀)
    (k : Fin 3) {n : ℕ} (hn : n < n₀) (j : ZMod N) :
    |gval k (X (n + 1)) j -
        sol.fld k (τ₀ + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi / N), sampleAngle N j) -
        (gval k (X n) j - sol.fld k (τ₀ + n * (2 * Real.pi / N), sampleAngle N j))| ≤
      ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * C₁ + sol.charConsConst h0 + c₀) *
        (2 * Real.pi / N) ^ 3 := by
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hE : ∀ m ≤ n₀, charDist (X m) (sol.sample N (τ₀ + m * ℓ)) ≤ C₁ * ℓ ^ 2 := fun m hm =>
    (charDist_le_norm_errArr _ _).trans ((norm_le_crNorm_one _ _).trans (H.c1 m hm))
  have hT := sol.nodal_time_difference h0 hR N hN τ₀ n₀ H.start H.stop X A B H.step hE
    H.offset n hn j
  obtain ⟨hT1, hT2⟩ := hT
  rw [← hℓdef] at hT1 hT2
  push_cast at hT1 hT2
  rw [div_le_iff₀ hℓ] at hT1 hT2
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  have hL0 := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
  have hK : 0 ≤ 15 * gowdyLipschitz (t₀ / 2) R + 32 * R := by positivity
  have hCc := sol.charConsConst_nonneg h0
  have hbound : ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * (C₁ * ℓ ^ 2) + c₀ * ℓ ^ 4 / ℓ +
      sol.charConsConst h0 * ℓ ^ 2) * ℓ ≤
      ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * C₁ + sol.charConsConst h0 + c₀) * ℓ ^ 3 := by
    have e : c₀ * ℓ ^ 4 / ℓ = c₀ * ℓ ^ 3 := by field_simp
    rw [e]
    have : c₀ * ℓ ^ 3 * ℓ ≤ c₀ * ℓ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hℓ1 (by positivity : 0 ≤ c₀ * ℓ ^ 3)
      linarith
    nlinarith
  rw [← gval_sample, ← gval_sample]
  push_cast
  fin_cases k
  · refine le_trans (le_of_eq ?_) (((abs_P_le _).trans hT1).trans hbound)
    simp [gval, LocalState.toVec, projZero_apply]
  · refine le_trans (le_of_eq ?_) (((abs_Q_le _).trans hT1).trans hbound)
    simp [gval, LocalState.toVec, projZero_apply]
  · exact hT2.trans hbound

end GowdySmoothReference


/-! ### Constants of the record maps on the chart -/

/-- Uniform constants of the record maps `u_k, v_k` on the compact chart `chartK t₀ R`. -/
theorem exists_record_consts {t₀ : ℝ} (h0 : 0 < t₀) (R : ℝ) :
    ∃ L M₁ L₁ : ℝ, 0 ≤ L ∧ 0 ≤ M₁ ∧ 0 ≤ L₁ ∧ ∀ k : Fin 3,
      (∀ x ∈ chartK t₀ R, ∀ y ∈ chartK t₀ R, |timeRec k x - timeRec k y| ≤ L * ‖x - y‖) ∧
      (∀ x ∈ chartK t₀ R, ∀ y ∈ chartK t₀ R, |spaceRec k x - spaceRec k y| ≤ L * ‖x - y‖) ∧
      (∀ x ∈ chartK t₀ R, DifferentiableAt ℝ (timeRec k) x) ∧
      (∀ x ∈ chartK t₀ R, ‖fderiv ℝ (timeRec k) x‖ ≤ M₁) ∧
      (∀ x ∈ chartK t₀ R, ∀ y ∈ chartK t₀ R,
        ‖fderiv ℝ (timeRec k) x - fderiv ℝ (timeRec k) y‖ ≤ L₁ * ‖x - y‖) := by
  have hT := fun k : Fin 3 => exists_map_consts isOpen_posClock
    ((contDiffOn_timeRec k).of_le (by norm_cast)) (chartK_subset_posClock h0 (R := R))
    (isCompact_chartK t₀ R) (convex_chartK t₀ R)
  have hS := fun k : Fin 3 => exists_map_consts isOpen_posClock
    ((contDiffOn_spaceRec k).of_le (by norm_cast)) (chartK_subset_posClock h0 (R := R))
    (isCompact_chartK t₀ R) (convex_chartK t₀ R)
  choose a b c ha hb hc h1 h2 h3 h4 using hT
  choose a' b' c' ha' hb' hc' h1' h2' h3' h4' using hS
  set L := ∑ k, (a k + a' k)
  set M₁ := ∑ k, b k
  set L₁ := ∑ k, c k
  have hLk : ∀ k, a k ≤ L ∧ a' k ≤ L := fun k => by
    have := Finset.single_le_sum (f := fun k => a k + a' k)
      (fun k _ => add_nonneg (ha k) (ha' k)) (mem_univ k)
    exact ⟨by linarith [ha' k], by linarith [ha k]⟩
  have hMk : ∀ k, b k ≤ M₁ := fun k =>
    Finset.single_le_sum (f := b) (fun k _ => hb k) (mem_univ k)
  have hLk' : ∀ k, c k ≤ L₁ := fun k =>
    Finset.single_le_sum (f := c) (fun k _ => hc k) (mem_univ k)
  refine ⟨L, M₁, L₁, Finset.sum_nonneg fun k _ => add_nonneg (ha k) (ha' k),
    Finset.sum_nonneg fun k _ => hb k, Finset.sum_nonneg fun k _ => hc k, fun k => ⟨?_, ?_, h2 k,
    fun x hx => (h3 k x hx).trans (hMk k), ?_⟩⟩
  · intro x hx y hy
    have := h1 k x hx y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hLk k).1 (norm_nonneg _))
  · intro x hx y hy
    have := h1' k x hx y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hLk k).2 (norm_nonneg _))
  · intro x hx y hy
    exact (h4 k x hx y hy).trans (mul_le_mul_of_nonneg_right (hLk' k) (norm_nonneg _))

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} {sol : GowdySmoothReference t₀ t₁}

/-- Nodal time-record error `|u_k(X_n,j) - ∂_t f_k(t_n, θ_j)| = O(h²)`. -/
theorem PathwiseHistory.timeRec_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    (hs1 : C₁ * (2 * Real.pi / N) ^ 2 ≤ 1) (hs2 : C₁ * (2 * Real.pi / N) ^ 2 ≤ t₀ / 2)
    (k : Fin 3) {L : ℝ} (hL : ∀ x ∈ chartK t₀ (sol.chartRadius h0),
      ∀ y ∈ chartK t₀ (sol.chartRadius h0), |timeRec k x - timeRec k y| ≤ L * ‖x - y‖)
    (hL0 : 0 ≤ L) {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    |timeRec k ((X m).site j).toVec - dP (sol.fld k) (τ₀ + m * (2 * Real.pi / N), sampleAngle N j)|
      ≤ L * (C₁ * (2 * Real.pi / N) ^ 2) := by
  have hτ := H.time_mem hm
  have hx := H.site_err hm j
  obtain ⟨hxK, hyK⟩ := sol.node_mem h0 hτ hx hs1 hs2
  rw [sol.dT_fld h0 k hτ]
  exact (hL _ hxK _ hyK).trans (mul_le_mul_of_nonneg_left hx hL0)

/-- Nodal space-record error `|v_k(X_n,j) - ∂_θ f_k(t_n, θ_j)| = O(h²)`. -/
theorem PathwiseHistory.spaceRec_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    (hs1 : C₁ * (2 * Real.pi / N) ^ 2 ≤ 1) (hs2 : C₁ * (2 * Real.pi / N) ^ 2 ≤ t₀ / 2)
    (k : Fin 3) {L : ℝ} (hL : ∀ x ∈ chartK t₀ (sol.chartRadius h0),
      ∀ y ∈ chartK t₀ (sol.chartRadius h0), |spaceRec k x - spaceRec k y| ≤ L * ‖x - y‖)
    (hL0 : 0 ≤ L) {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    |spaceRec k ((X m).site j).toVec - dQ (sol.fld k) (τ₀ + m * (2 * Real.pi / N), sampleAngle N j)|
      ≤ L * (C₁ * (2 * Real.pi / N) ^ 2) := by
  have hτ := H.time_mem hm
  have hx := H.site_err hm j
  obtain ⟨hxK, hyK⟩ := sol.node_mem h0 hτ hx hs1 hs2
  rw [sol.dΘ_fld h0 k hτ]
  exact (hL _ hxK _ hyK).trans (mul_le_mul_of_nonneg_left hx hL0)

/-- Nodal mixed-record error `|D₀u_k(X_n)(j) - ∂_t∂_θ f_k(t_n, θ_j)| = O(h²)`: discrete chain
rule for `D₀` of the record map, plus centered-difference consistency. -/
theorem PathwiseHistory.mixedRec_err {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    (hs1 : C₁ * (2 * Real.pi / N) ^ 2 ≤ 1) (hs2 : C₁ * (2 * Real.pi / N) ^ 2 ≤ t₀ / 2)
    (k : Fin 3) {M₁ L₁ M₃ : ℝ}
    (hD : ∀ x ∈ chartK t₀ (sol.chartRadius h0), DifferentiableAt ℝ (timeRec k) x)
    (hM : ∀ x ∈ chartK t₀ (sol.chartRadius h0), ‖fderiv ℝ (timeRec k) x‖ ≤ M₁)
    (hL : ∀ x ∈ chartK t₀ (sol.chartRadius h0), ∀ y ∈ chartK t₀ (sol.chartRadius h0),
      ‖fderiv ℝ (timeRec k) x - fderiv ℝ (timeRec k) y‖ ≤ L₁ * ‖x - y‖) (hL0 : 0 ≤ L₁)
    (hM₃ : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → |(dP^[1] (dQ^[3] (sol.fld k))) p| ≤ M₃)
    {m : ℕ} (hm : m ≤ n₀) (j : ZMod N) :
    |(timeRec k ((X m).site (j + 1)).toVec - timeRec k ((X m).site (j - 1)).toVec) /
        (2 * (2 * Real.pi / N)) -
        dP (dQ (sol.fld k)) (τ₀ + m * (2 * Real.pi / N), sampleAngle N j)| ≤
      (M₁ * C₁ + L₁ * C₁ * sol.derivBound h0 + M₃) * (2 * Real.pi / N) ^ 2 := by
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  set τ := τ₀ + m * ℓ
  have hτ : τ ∈ Icc t₀ t₁ := H.time_mem hm
  set ψ := sampleAngle N j
  have hD0 := (sol.derivBound_spec h0).1
  -- the reference nodes
  have hyp : sol.Z (τ, sampleAngle N (j + 1)) = sol.Z (τ, ψ + ℓ) :=
    sample_succ sol.Z sol.periodic_Z N τ j
  have hym : sol.Z (τ, sampleAngle N (j - 1)) = sol.Z (τ, ψ - ℓ) :=
    sample_pred sol.Z sol.periodic_Z N τ j
  have exm := H.site_err hm (j - 1)
  have ex0 := H.site_err hm j
  have exp := H.site_err hm (j + 1)
  obtain ⟨hxmK, hymK⟩ := sol.node_mem h0 hτ exm hs1 hs2
  obtain ⟨hx0K, hy0K⟩ := sol.node_mem h0 hτ ex0 hs1 hs2
  obtain ⟨hxpK, hypK⟩ := sol.node_mem h0 hτ exp hs1 hs2
  have hdp := H.site_diff_err hm j
  have hdm := H.site_diff_err hm (j - 1)
  rw [sub_add_cancel] at hdm
  have hDp : ‖sol.Z (τ, sampleAngle N (j + 1)) - sol.Z (τ, ψ)‖ ≤ sol.derivBound h0 * ℓ := by
    rw [hyp]
    refine (sol.norm_Z_sub_le h0 hτ).trans (le_of_eq ?_)
    rw [add_sub_cancel_left, abs_of_pos hℓ]
  have hDm : ‖sol.Z (τ, ψ) - sol.Z (τ, sampleAngle N (j - 1))‖ ≤ sol.derivBound h0 * ℓ := by
    rw [hym]
    refine (sol.norm_Z_sub_le h0 hτ).trans (le_of_eq ?_)
    rw [sub_sub_cancel, abs_of_pos hℓ]
  have hC := abs_centered_sub_le (convex_chartK t₀ _) hD hM hL hL0 hxmK hx0K hxpK hymK hy0K hypK
    hℓ exm ex0 exp hdp hdm hDp hDm
  have hcent := abs_centered_partial_le (sol.smooth_fld k) τ ψ (M := M₃) hℓ
    (fun s => hM₃ (τ, s) hτ)
  rw [hyp, hym, ← sol.dT_fld h0 k (p := (τ, ψ + ℓ)) hτ,
    ← sol.dT_fld h0 k (p := (τ, ψ - ℓ)) hτ] at hC
  have tri := abs_sub_le ((timeRec k ((X m).site (j + 1)).toVec -
      timeRec k ((X m).site (j - 1)).toVec) / (2 * ℓ))
    ((dP (sol.fld k) (τ, ψ + ℓ) - dP (sol.fld k) (τ, ψ - ℓ)) / (2 * ℓ))
    (dP (dQ (sol.fld k)) (τ, ψ))
  have hM₃0 : 0 ≤ M₃ := (abs_nonneg _).trans (hM₃ (τ, ψ) hτ)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM _ hx0K)
  calc _ ≤ _ := tri
    _ ≤ (M₁ * (C₁ * ℓ ^ 2) + L₁ * (C₁ * ℓ ^ 2) * sol.derivBound h0) + M₃ * ℓ ^ 2 / 2 :=
        add_le_add hC hcent
    _ ≤ (M₁ * C₁ + L₁ * C₁ * sol.derivBound h0 + M₃) * ℓ ^ 2 := by
        have : M₃ * ℓ ^ 2 / 2 ≤ M₃ * ℓ ^ 2 := by
          have := mul_nonneg hM₃0 (sq_nonneg ℓ); linarith
        nlinarith

end GowdySmoothReference


/-! ### Corner jet errors and the second-jet estimate -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} {sol : GowdySmoothReference t₀ t₁}

/-- The coefficient `C_η` of the corner jet errors `η = C_η h²`. -/
def jetConst (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) (R c₀ C₁ L M₁ L₁ M₃ : ℝ) : ℝ :=
  C₁ + L * C₁ + (M₁ * C₁ + L₁ * C₁ * sol.derivBound h0 + M₃) +
    ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * C₁ + sol.charConsConst h0 + c₀)

/-- **Corner jet errors of the Gowdy readout** (`eq:supp-gowdy-hermite-jets` with
`eq:supp-gowdy-pathwise-c1`, the nodal time differences and centered-difference consistency):
on every cell the records of the numerical history differ from the exact records of the
reference within `CubicHermite.JetBound h (C_η h²)`. -/
theorem PathwiseHistory.cell_jetBound {h0 : 0 < t₀} {R c₀ C₁ : ℝ} {N : ℕ} [NeZero N] {τ₀ : ℝ}
    {n₀ : ℕ} {X A B : ℕ → GridState N} (H : sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B)
    (hR : sol.chartRadius h0 ≤ R) (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R)
    (hℓ1 : 2 * Real.pi / N ≤ 1) (hc₀ : 0 ≤ c₀) (hC₁ : 0 ≤ C₁)
    (hs1 : C₁ * (2 * Real.pi / N) ^ 2 ≤ 1) (hs2 : C₁ * (2 * Real.pi / N) ^ 2 ≤ t₀ / 2)
    {L M₁ L₁ M₃ : ℝ} (hL0 : 0 ≤ L) (hM₁0 : 0 ≤ M₁) (hL₁0 : 0 ≤ L₁) (hM₃0 : 0 ≤ M₃)
    (hrec : ∀ k : Fin 3,
      (∀ x ∈ chartK t₀ (sol.chartRadius h0), ∀ y ∈ chartK t₀ (sol.chartRadius h0),
        |timeRec k x - timeRec k y| ≤ L * ‖x - y‖) ∧
      (∀ x ∈ chartK t₀ (sol.chartRadius h0), ∀ y ∈ chartK t₀ (sol.chartRadius h0),
        |spaceRec k x - spaceRec k y| ≤ L * ‖x - y‖) ∧
      (∀ x ∈ chartK t₀ (sol.chartRadius h0), DifferentiableAt ℝ (timeRec k) x) ∧
      (∀ x ∈ chartK t₀ (sol.chartRadius h0), ‖fderiv ℝ (timeRec k) x‖ ≤ M₁) ∧
      (∀ x ∈ chartK t₀ (sol.chartRadius h0), ∀ y ∈ chartK t₀ (sol.chartRadius h0),
        ‖fderiv ℝ (timeRec k) x - fderiv ℝ (timeRec k) y‖ ≤ L₁ * ‖x - y‖))
    (hM₃ : ∀ k : Fin 3, ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ∀ a b : ℕ, a ≤ 6 → b ≤ 6 →
      |(dP^[a] (dQ^[b] (sol.fld k))) p| ≤ M₃)
    {n : ℕ} (hn : n < n₀) (j : ZMod N) (k : Fin 3) :
    JetBound (2 * Real.pi / N) (sol.jetConst h0 R c₀ C₁ L M₁ L₁ M₃ * (2 * Real.pi / N) ^ 2)
      (numF X n j k - cellF (sol.fld k) (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j)
        (2 * Real.pi / N))
      (numU X n j k - cellU (sol.fld k) (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j)
        (2 * Real.pi / N))
      (numV X n j k - cellV (sol.fld k) (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j)
        (2 * Real.pi / N))
      (numW X n j k - cellW (sol.fld k) (τ₀ + n * (2 * Real.pi / N)) (sampleAngle N j)
        (2 * Real.pi / N)) := by
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  have hLg := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
  have hCc := sol.charConsConst_nonneg h0
  have hDb := (sol.derivBound_spec h0).1
  set Cη := sol.jetConst h0 R c₀ C₁ L M₁ L₁ M₃ with hCη
  have p1 : 0 ≤ C₁ := hC₁
  have p2 : 0 ≤ L * C₁ := mul_nonneg hL0 hC₁
  have p3 : 0 ≤ M₁ * C₁ + L₁ * C₁ * sol.derivBound h0 + M₃ := by positivity
  have p4 : 0 ≤ (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * C₁ + sol.charConsConst h0 + c₀ := by
    positivity
  have c1 : C₁ ≤ Cη := by rw [hCη, jetConst]; linarith
  have c2 : L * C₁ ≤ Cη := by rw [hCη, jetConst]; linarith
  have c3 : M₁ * C₁ + L₁ * C₁ * sol.derivBound h0 + M₃ ≤ Cη := by rw [hCη, jetConst]; linarith
  have c4 : (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * C₁ + sol.charConsConst h0 + c₀ ≤ Cη := by
    rw [hCη, jetConst]; linarith
  have hsq : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hmem : ∀ a : Fin 2, n + (a : ℕ) ≤ n₀ := fun a => by have := a.isLt; omega
  have hper := sol.periodic_fld k
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a b => ?_, fun b => ?_, fun a => ?_⟩
  · simp only [Pi.sub_apply, numF, cellF]
    rw [corner_eval hper]
    exact (H.value_err k (hmem a) _).trans (mul_le_mul_of_nonneg_right c1 hsq)
  · simp only [Pi.sub_apply, numU, cellU]
    rw [corner_eval (periodic_dP hper)]
    refine (H.timeRec_err hs1 hs2 k (hrec k).1 hL0 (hmem a) _).trans ?_
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right c2 hsq
  · simp only [Pi.sub_apply, numV, cellV]
    rw [corner_eval (periodic_dQ hper)]
    refine (H.spaceRec_err hs1 hs2 k (hrec k).2.1 hL0 (hmem a) _).trans ?_
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right c2 hsq
  · simp only [Pi.sub_apply, numW, cellW]
    rw [corner_eval (periodic_dP (periodic_dQ hper))]
    refine (H.mixedRec_err hs1 hs2 k (hrec k).2.2.1 (hrec k).2.2.2.1 (hrec k).2.2.2.2 hL₁0
      (fun p hp => hM₃ k p hp 1 3 (by norm_num) (by norm_num)) (hmem a) _).trans ?_
    exact mul_le_mul_of_nonneg_right c3 hsq
  · simp only [Pi.sub_apply, numF, cellF]
    rw [corner_eval hper, corner_eval hper]
    have := H.time_diff_err hR hN hℓ1 hc₀ k hn (j + ((b : ℕ) : ZMod N))
    have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
    simp only [e1, e0, add_zero]
    refine this.trans ?_
    have : Cη * ℓ ^ 2 * ℓ = Cη * ℓ ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right c4 (by positivity)
  · simp only [Pi.sub_apply, numF, cellF]
    rw [corner_eval hper, corner_eval hper]
    have := H.space_diff_err k (hmem a) j
    have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
    simp only [e1, e0, Nat.cast_one, Nat.cast_zero, add_zero]
    refine this.trans ?_
    have : Cη * ℓ ^ 2 * ℓ = ℓ * (Cη * ℓ ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c1 hsq) hℓ.le

/-- **`eq:supp-gowdy-second-jet`, cellwise and pathwise.**  Let `X_*` be a smooth reference and
`R ≥ chartRadius`.  For every `c₀, C₁ ≥ 0` there are `C` and `h₀ > 0` such that for every
`h = ℓ = 2π/N ≤ h₀` and every numerical history satisfying the pathwise hypotheses
(`PathwiseHistory`: split steps in the envelope, offset cap `≤ c₀ h⁴`, pathwise `C¹_h` error
`≤ C₁ h²`), on every cell `[τ₀ + nh, τ₀ + (n+1)h] × [θ_j, θ_j + h]` and for `f = P, Q, λ`, the
shared Hermite readout `f_h` satisfies
`|∂_t^i∂_θ^{i'}(f_h - f_*)| ≤ C h²` for `i + i' ≤ 1` and `≤ C h` for `i + i' = 2`. -/
theorem readout_second_jet (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) {c₀ C₁ : ℝ} (hc₀ : 0 ≤ c₀) (hC₁ : 0 ≤ C₁) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ) (X A B : ℕ → GridState N),
        sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B →
        ∀ n < n₀, ∀ (j : ZMod N) (k : Fin 3),
        ∀ x ∈ Icc (τ₀ + n * (2 * Real.pi / N)) (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N),
        ∀ y ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N), ∀ i i' : ℕ,
          (i + i' ≤ 1 → |(dP^[i] (dQ^[i'] (cellReadout X τ₀ n j k))) (x, y) -
            (dP^[i] (dQ^[i'] (sol.fld k))) (x, y)| ≤ C * (2 * Real.pi / N) ^ 2) ∧
          (i + i' = 2 → |(dP^[i] (dQ^[i'] (cellReadout X τ₀ n j k))) (x, y) -
            (dP^[i] (dQ^[i'] (sol.fld k))) (x, y)| ≤ C * (2 * Real.pi / N)) := by
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  obtain ⟨L, M₁, L₁, hL0, hM₁0, hL₁0, hrec⟩ := exists_record_consts h0 (sol.chartRadius h0)
  have hb := fun k : Fin 3 => exists_partials_bound (sol.smooth_fld k) (sol.periodic_fld k) t₀ t₁
  choose Mk hMk0 hMk using hb
  set M₃ := ∑ k, Mk k
  have hM₃0 : 0 ≤ M₃ := Finset.sum_nonneg fun k _ => hMk0 k
  have hM₃ : ∀ k : Fin 3, ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ∀ a b : ℕ, a ≤ 6 → b ≤ 6 →
      |(dP^[a] (dQ^[b] (sol.fld k))) p| ≤ M₃ := fun k p hp a b ha hb =>
    (hMk k p hp a b ha hb).trans (Finset.single_le_sum (f := Mk) (fun k _ => hMk0 k) (mem_univ k))
  set Cη := sol.jetConst h0 R c₀ C₁ L M₁ L₁ M₃
  have hstep := sol.charStabStep_pos h0 hR0
  set ℓ₀ := min (min 1 (sol.charStabStep h0 R)) (min 1 (t₀ / 2) / (C₁ + 1))
  have hℓ₀ : 0 < ℓ₀ := lt_min (lt_min one_pos hstep) (div_pos (lt_min one_pos (by linarith))
    (by linarith))
  refine ⟨72 * Cη + hermRemConst * M₃, ℓ₀, ?_, hℓ₀, ?_⟩
  · have hLg := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
    have hCc := sol.charConsConst_nonneg h0
    have hDb := (sol.derivBound_spec h0).1
    have : 0 ≤ Cη := by
      simp only [Cη, jetConst]; positivity
    have := hermRemConst_nonneg
    positivity
  intro N _ hN τ₀ n₀ X A B H n hn j k x hx y hy i i'
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hℓ1 : ℓ ≤ 1 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hNs : ℓ ≤ sol.charStabStep h0 R := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNc : ℓ ≤ min 1 (t₀ / 2) / (C₁ + 1) := hN.trans (min_le_right _ _)
  have hsm : C₁ * ℓ ^ 2 ≤ min 1 (t₀ / 2) := by
    rw [le_div_iff₀ (by linarith)] at hNc
    have h1 : C₁ * ℓ ^ 2 ≤ C₁ * ℓ := by
      have : ℓ ^ 2 ≤ ℓ := by nlinarith
      exact mul_le_mul_of_nonneg_left this hC₁
    nlinarith
  have hs1 : C₁ * ℓ ^ 2 ≤ 1 := hsm.trans (min_le_left _ _)
  have hs2 : C₁ * ℓ ^ 2 ≤ t₀ / 2 := hsm.trans (min_le_right _ _)
  have hJ := H.cell_jetBound hR hNs hℓ1 hc₀ hC₁ hs1 hs2 hL0 hM₁0 hL₁0 hM₃0 hrec hM₃ hn j k
  have hcell : ∀ x' ∈ Icc (τ₀ + n * ℓ) (τ₀ + n * ℓ + ℓ), x' ∈ Icc t₀ t₁ := by
    intro x' hx'
    have h1 := H.time_mem (m := n) hn.le
    have h2 := H.time_mem (m := n + 1) hn
    push_cast at h2
    exact ⟨h1.1.trans hx'.1, hx'.2.trans (by linarith [h2.2])⟩
  have hMcell : ∀ x' ∈ Icc (τ₀ + n * ℓ) (τ₀ + n * ℓ + ℓ),
      ∀ y' ∈ Icc (sampleAngle N j) (sampleAngle N j + ℓ), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
        |(dP^[a] (dQ^[b] (sol.fld k))) (x', y')| ≤ M₃ :=
    fun x' hx' y' _ a b _ h6 => hM₃ k (x', y') (hcell x' hx') a b (by omega) (by omega)
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · exact readout_jet_error_le_one (sol.smooth_fld k) hℓ hℓ1 hMcell hJ (le_refl _) hij hx hy
  · exact readout_jet_error_two (sol.smooth_fld k) hℓ hℓ1 hMcell hJ (le_refl _) hij hx hy

end GowdySmoothReference


/-! ### The Gowdy metric map and its inverse -/

/-- The Gowdy metric `eq:supp-gowdy-metric` in the coordinates `(t, θ, x, y)` as a function of
`y = (t, P, Q, λ)`:
`g = t^{-1/2} e^{λ/2}(-dt² + dθ²) + t [e^P (dx + Q dy)² + e^{-P} dy²]`. -/
def gowdyMetric (y : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-(Real.exp (y 3 / 2) / Real.sqrt (y 0)), 0, 0, 0],
    ![0, Real.exp (y 3 / 2) / Real.sqrt (y 0), 0, 0],
    ![0, 0, y 0 * Real.exp (y 1), y 0 * Real.exp (y 1) * y 2],
    ![0, 0, y 0 * Real.exp (y 1) * y 2, y 0 * (Real.exp (y 1) * y 2 ^ 2 + Real.exp (-y 1))]]

/-- The inverse Gowdy metric (`gowdyInvMetric_eq_inv`). -/
def gowdyInvMetric (y : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-(Real.sqrt (y 0) / Real.exp (y 3 / 2)), 0, 0, 0],
    ![0, Real.sqrt (y 0) / Real.exp (y 3 / 2), 0, 0],
    ![0, 0, (Real.exp (y 1) * y 2 ^ 2 + Real.exp (-y 1)) / y 0, -(Real.exp (y 1) * y 2) / y 0],
    ![0, 0, -(Real.exp (y 1) * y 2) / y 0, Real.exp (y 1) / y 0]]

/-- `gowdyInvMetric` is the matrix inverse of the Gowdy metric for `t > 0` (inverted at type
`Matrix`). -/
theorem gowdyInvMetric_eq_inv {y : Fin 4 → ℝ} (hy : 0 < y 0) :
    (Matrix.of (gowdyMetric y))⁻¹ = Matrix.of (gowdyInvMetric y) := by
  have hs : Real.sqrt (y 0) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have he : Real.exp (y 3 / 2) ≠ 0 := Real.exp_ne_zero _
  have he1 : Real.exp (y 1) ≠ 0 := Real.exp_ne_zero _
  have ht : y 0 ≠ 0 := hy.ne'
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, gowdyMetric, gowdyInvMetric, Real.exp_neg] <;>
    field_simp <;> ring

/-- The open chart `t > 0` of `(t, P, Q, λ)`. -/
def posTime : Set (Fin 4 → ℝ) := {y | 0 < y 0}

theorem isOpen_posTime : IsOpen posTime := isOpen_lt continuous_const (continuous_apply 0)

theorem contDiffOn_sqrt_posTime :
    ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => Real.sqrt (y 0)) posTime :=
  ContDiffOn.sqrt (by fun_prop) fun y hy => (ne_of_gt hy)

theorem contDiffOn_gowdyMetric : ContDiffOn ℝ ∞ gowdyMetric posTime := by
  have hs := contDiffOn_sqrt_posTime
  have hne : ∀ y ∈ posTime, Real.sqrt (y 0) ≠ 0 := fun y hy => (Real.sqrt_pos.2 hy).ne'
  have h1 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => Real.exp (y 3 / 2) / Real.sqrt (y 0)) posTime :=
    ContDiffOn.div (by fun_prop) hs hne
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [gowdyMetric]
  all_goals first
    | exact contDiffOn_const
    | exact h1
    | exact h1.neg
    | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0 * Real.exp (y 1)).contDiffOn
    | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ =>
        y 0 * Real.exp (y 1) * y 2).contDiffOn
    | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ =>
        y 0 * (Real.exp (y 1) * y 2 ^ 2 + Real.exp (-y 1))).contDiffOn

theorem contDiffOn_gowdyInvMetric : ContDiffOn ℝ ∞ gowdyInvMetric posTime := by
  have hs := contDiffOn_sqrt_posTime
  have hne : ∀ y ∈ posTime, y 0 ≠ 0 := fun y hy => (ne_of_gt hy)
  have h1 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => Real.sqrt (y 0) / Real.exp (y 3 / 2)) posTime :=
    ContDiffOn.div hs (by fun_prop) fun y _ => Real.exp_ne_zero _
  have hd : ∀ f : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ f →
      ContDiffOn ℝ ∞ (fun y => f y / y 0) posTime := fun f hf =>
    ContDiffOn.div hf.contDiffOn (by fun_prop) hne
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [gowdyInvMetric]
  all_goals first
    | exact contDiffOn_const
    | exact h1
    | exact h1.neg
    | exact hd _ (by fun_prop)

/-- The compact convex chart `{t ≥ t₀} ∩ closedBall 0 ρ` of `(t, P, Q, λ)`. -/
def metricChart (t₀ ρ : ℝ) : Set (Fin 4 → ℝ) := {y | t₀ ≤ y 0} ∩ Metric.closedBall 0 ρ

theorem metricChart_subset {t₀ ρ : ℝ} (h0 : 0 < t₀) : metricChart t₀ ρ ⊆ posTime :=
  fun _ hy => lt_of_lt_of_le h0 hy.1

theorem isCompact_metricChart (t₀ ρ : ℝ) : IsCompact (metricChart t₀ ρ) :=
  (isCompact_closedBall 0 ρ).inter_left (isClosed_le continuous_const (continuous_apply 0))

theorem convex_metricChart (t₀ ρ : ℝ) : Convex ℝ (metricChart t₀ ρ) := by
  refine Convex.inter ?_ (convex_closedBall 0 ρ)
  exact (convex_Ici t₀).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)

/-! ### Metric jets in the coordinates `(t, θ, x, y)` -/

/-- Coordinate directions `∂_t, ∂_θ` in `ℝ²`; the fields do not depend on `x, y`. -/
def coordDir : Fin 4 → ℝ × ℝ := ![(1, 0), (0, 1), 0, 0]

theorem norm_coordDir_le (i : Fin 4) : ‖coordDir i‖ ≤ 1 := by
  fin_cases i <;> simp [coordDir]

/-- First metric jet `∂_i g_{ej}` of `g : ℝ² → Sym`, in the index convention of
`CoordinateCurvatureJet` (`dg i e j = ∂_i g_{ej}`). -/
def metricD1 (g : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun i e j => fderiv ℝ g z (coordDir i) e j

/-- Second metric jet `∂_d ∂_i g_{ej}`. -/
def metricD2 (g : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun d i e j => fderiv ℝ (fderiv ℝ g) z (coordDir d) (coordDir i) e j

theorem norm_metricD1_sub_le (g g' : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) :
    ‖metricD1 g z - metricD1 g' z‖ ≤ ‖fderiv ℝ g z - fderiv ℝ g' z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 : ‖(fderiv ℝ g z - fderiv ℝ g' z) (coordDir i)‖ ≤ ‖fderiv ℝ g z - fderiv ℝ g' z‖ :=
    ((fderiv ℝ g z - fderiv ℝ g' z).le_opNorm _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le i))
  refine le_trans (le_of_eq ?_) h1
  rfl

theorem norm_metricD1_le (g : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) :
    ‖metricD1 g z‖ ≤ ‖fderiv ℝ g z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 : ‖(fderiv ℝ g z) (coordDir i)‖ ≤ ‖fderiv ℝ g z‖ :=
    ((fderiv ℝ g z).le_opNorm _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le i))
  exact h1

theorem norm_metricD2_sub_le (g g' : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) :
    ‖metricD2 g z - metricD2 g' z‖ ≤ ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g') z‖ := by
  have h0 := norm_nonneg (fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g') z)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun d => ?_
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  set T := fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g') z
  have h1 : ‖T (coordDir d) (coordDir i)‖ ≤ ‖T‖ := by
    refine ((T (coordDir d)).le_opNorm _).trans ?_
    refine (mul_le_mul (T.le_opNorm _) (norm_coordDir_le i) (norm_nonneg _)
      (by positivity)).trans ?_
    rw [mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le d)
  exact h1

theorem norm_metricD2_le (g : ℝ × ℝ → Fin 4 → Fin 4 → ℝ) (z : ℝ × ℝ) :
    ‖metricD2 g z‖ ≤ ‖fderiv ℝ (fderiv ℝ g) z‖ := by
  have h0 := norm_nonneg (fderiv ℝ (fderiv ℝ g) z)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun d => ?_
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  set T := fderiv ℝ (fderiv ℝ g) z
  have h1 : ‖T (coordDir d) (coordDir i)‖ ≤ ‖T‖ := by
    refine ((T (coordDir d)).le_opNorm _).trans ?_
    refine (mul_le_mul (T.le_opNorm _) (norm_coordDir_le i) (norm_nonneg _)
      (by positivity)).trans ?_
    rw [mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le d)
  exact h1

/-- The metric 2-jet `(g⁻¹, ∂g, ∂²g)` of the Gowdy metric along `A : ℝ² → (t, P, Q, λ)`. -/
def gowdyJet (A : ℝ × ℝ → Fin 4 → ℝ) (z : ℝ × ℝ) : CoordinateCurvatureJet.Jet :=
  (gowdyInvMetric (A z), metricD1 (fun y => gowdyMetric (A y)) z,
    metricD2 (fun y => gowdyMetric (A y)) z)


open CoordinateCurvatureJet SecondOrderChainRule in
set_option maxHeartbeats 1000000 in
/-- **Jet transfer through the Gowdy metric** (`eq:supp-gowdy-full-curvature`, pointwise): on the
chart `metricChart t₀ ρ` and for reference jets bounded by `M`, there is `C` such that jet errors
`ε₁` (values and first derivatives of `(t, P, Q, λ)`) and `ε₂` (second derivatives) give metric
errors `C ε₁` in `(g, ∂g)`, `C (ε₁ + ε₂)` in `∂²g` and in the Riemann tensor of the 2-jet
`(g⁻¹, ∂g, ∂²g)`, a uniform bound `C` for the Riemann tensor, and Ricci `≤ C (ε₁ + ε₂)` where
the reference is Ricci flat. -/
theorem gowdy_jet_transfer {t₀ : ℝ} (h0 : 0 < t₀) (ρ M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B : ℝ × ℝ → Fin 4 → ℝ, ContDiff ℝ 2 A → ContDiff ℝ 2 B → ∀ z,
      A z ∈ metricChart t₀ ρ → B z ∈ metricChart t₀ ρ →
      ‖fderiv ℝ B z‖ ≤ M → ‖fderiv ℝ (fderiv ℝ B) z‖ ≤ M →
      ∀ ε₁ ε₂ : ℝ, ε₁ ≤ 1 → ε₂ ≤ 1 → ‖A z - B z‖ ≤ ε₁ →
        ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ ε₁ →
        ‖fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z‖ ≤ ε₂ →
        ‖gowdyMetric (A z) - gowdyMetric (B z)‖ ≤ C * ε₁ ∧
        ‖fderiv ℝ (fun y => gowdyMetric (A y)) z - fderiv ℝ (fun y => gowdyMetric (B y)) z‖ ≤
          C * ε₁ ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (A y))) z -
          fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (B y))) z‖ ≤ C * (ε₁ + ε₂) ∧
        ‖riemJet (gowdyJet A z) - riemJet (gowdyJet B z)‖ ≤ C * (ε₁ + ε₂) ∧
        ‖riemJet (gowdyJet A z)‖ ≤ C ∧
        (ricciJet (gowdyJet B z) = 0 → ‖ricciJet (gowdyJet A z)‖ ≤ C * (ε₁ + ε₂)) := by
  have hKV := metricChart_subset (ρ := ρ) h0
  have hKc := isCompact_metricChart t₀ ρ
  have hKx := convex_metricChart t₀ ρ
  obtain ⟨Cg, hCg0, hg⟩ := comp_jet_sub_le (E := ℝ × ℝ) isOpen_posTime
    (contDiffOn_gowdyMetric.of_le (by norm_cast)) hKV hKc hKx
  obtain ⟨Ci, hCi0, hi⟩ := comp_jet_sub_le (E := ℝ × ℝ) isOpen_posTime
    (contDiffOn_gowdyInvMetric.of_le (by norm_cast)) hKV hKc hKx
  obtain ⟨Cn, hCn0, hn⟩ := comp_jet_norm_le (E := ℝ × ℝ) isOpen_posTime
    (contDiffOn_gowdyMetric.of_le (by norm_cast)) hKV hKc
  obtain ⟨Cin, hCin⟩ := hKc.exists_bound_of_continuousOn
    (contDiffOn_gowdyInvMetric.continuousOn.mono hKV)
  set M' := M + 1
  have hM' : 0 ≤ M' := by positivity
  have hP1 : 0 ≤ 1 + M' := by positivity
  have q1 : 0 ≤ Cn * (1 + M') ^ 2 := by positivity
  have q2 : 0 ≤ Cg * (1 + M') := by positivity
  have q3 : 0 ≤ Cg * (1 + M') ^ 2 := by positivity
  have q4 : 0 ≤ |Cin| := abs_nonneg _
  set Brad := |Cin| + Ci + Cn * (1 + M') ^ 2 + Cn * (1 + M') ^ 2 + 2 * Cg * (1 + M') +
    3 * Cg * (1 + M') ^ 2 with hBrad
  obtain ⟨Lr, hLr0, hLr⟩ := riemJet_sub_le Brad
  obtain ⟨Lc, hLc0, hLc⟩ := ricciJet_lipschitz Brad
  obtain ⟨Rb, hRb⟩ := (isCompact_closedBall (0 : Jet) Brad).exists_bound_of_continuousOn
    contDiff_riemJet.continuous.continuousOn
  set K1 := Ci + 2 * Cg * (1 + M') + 2 * Cg * (1 + M') ^ 2
  have hK1 : 0 ≤ K1 := by positivity
  have q5 : 0 ≤ Lr * K1 := mul_nonneg hLr0 hK1
  have q6 : 0 ≤ Lc * K1 := mul_nonneg hLc0 hK1
  have q7 : 0 ≤ |Rb| := abs_nonneg _
  set C := Cg + 2 * Cg * (1 + M') + 3 * Cg * (1 + M') ^ 2 + (Lr + Lc) * K1 + |Rb| +
    2 * Lr * K1 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have cA : Cg ≤ C := by rw [hCdef]; nlinarith
  have cB : 2 * Cg * (1 + M') ≤ C := by rw [hCdef]; nlinarith
  have cC : 3 * Cg * (1 + M') ^ 2 ≤ C := by rw [hCdef]; nlinarith
  have cD : Lr * K1 ≤ C := by rw [hCdef]; nlinarith
  have cE : Lc * K1 ≤ C := by rw [hCdef]; nlinarith
  have cF : |Rb| + 2 * Lr * K1 ≤ C := by rw [hCdef]; nlinarith
  refine ⟨C, hC0, fun A B hA hB z hAz hBz hB1 hB2 ε₁ ε₂ hε₁ hε₂ h0' h1' h2' => ?_⟩
  have hε₁0 : 0 ≤ ε₁ := (norm_nonneg _).trans h0'
  have hε₂0 : 0 ≤ ε₂ :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ A) z - fderiv ℝ (fderiv ℝ B) z)).trans h2'
  have hA1 : ‖fderiv ℝ A z‖ ≤ M' := by
    have := norm_sub_norm_le (fderiv ℝ A z) (fderiv ℝ B z)
    simp only [M']; linarith
  obtain ⟨g0, g1, g2⟩ := hg A B hA hB z hAz hBz M' hM' hA1 (hB1.trans (by simp [M']))
    (hB2.trans (by simp [M']))
  obtain ⟨i0, -, -⟩ := hi A B hA hB z hAz hBz M' hM' hA1 (hB1.trans (by simp [M']))
    (hB2.trans (by simp [M']))
  obtain ⟨n0, n1, n2⟩ := hn B hB z hBz M' hM' (hB1.trans (by simp [M']))
    (hB2.trans (by simp [M']))
  -- metric errors
  have e0 : ‖gowdyMetric (A z) - gowdyMetric (B z)‖ ≤ Cg * ε₁ :=
    g0.trans (mul_le_mul_of_nonneg_left h0' hCg0)
  have e1 : ‖fderiv ℝ (fun y => gowdyMetric (A y)) z - fderiv ℝ (fun y => gowdyMetric (B y)) z‖
      ≤ 2 * Cg * (1 + M') * ε₁ := by
    refine g1.trans ?_
    have : ‖A z - B z‖ + ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ 2 * ε₁ := by linarith
    calc Cg * (1 + M') * (‖A z - B z‖ + ‖fderiv ℝ A z - fderiv ℝ B z‖)
        ≤ Cg * (1 + M') * (2 * ε₁) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Cg * (1 + M') * ε₁ := by ring
  have e2 : ‖fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (A y))) z -
      fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (B y))) z‖ ≤
      Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) := by
    refine g2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have ei : ‖gowdyInvMetric (A z) - gowdyInvMetric (B z)‖ ≤ Ci * ε₁ :=
    i0.trans (mul_le_mul_of_nonneg_left h0' hCi0)
  -- the jets lie in the ball of radius `Brad`
  have hJB : gowdyJet B z ∈ Metric.closedBall (0 : Jet) Brad := by
    rw [mem_closedBall_zero_iff]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · show ‖gowdyInvMetric (B z)‖ ≤ Brad
      have := (hCin _ hBz).trans (le_abs_self Cin)
      rw [hBrad]; linarith
    · show ‖metricD1 (fun y => gowdyMetric (B y)) z‖ ≤ Brad
      have := (norm_metricD1_le (fun y => gowdyMetric (B y)) z).trans n1
      rw [hBrad]; linarith
    · show ‖metricD2 (fun y => gowdyMetric (B y)) z‖ ≤ Brad
      have := (norm_metricD2_le (fun y => gowdyMetric (B y)) z).trans n2
      rw [hBrad]; linarith
  have hJA : gowdyJet A z ∈ Metric.closedBall (0 : Jet) Brad := by
    rw [mem_closedBall_zero_iff]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · show ‖gowdyInvMetric (A z)‖ ≤ Brad
      have h1 := (hCin _ hBz).trans (le_abs_self Cin)
      have h2 := norm_le_insert' (gowdyInvMetric (A z)) (gowdyInvMetric (B z))
      have h3 : Ci * ε₁ ≤ Ci := mul_le_of_le_one_right hCi0 hε₁
      rw [hBrad]; linarith
    · show ‖metricD1 (fun y => gowdyMetric (A y)) z‖ ≤ Brad
      have h1 := (norm_metricD1_le (fun y => gowdyMetric (B y)) z).trans n1
      have h2 := norm_metricD1_sub_le (fun y => gowdyMetric (A y)) (fun y => gowdyMetric (B y)) z
      have h3 := norm_le_insert' (metricD1 (fun y => gowdyMetric (A y)) z)
        (metricD1 (fun y => gowdyMetric (B y)) z)
      have h4 : 2 * Cg * (1 + M') * ε₁ ≤ 2 * Cg * (1 + M') :=
        mul_le_of_le_one_right (by positivity) hε₁
      rw [hBrad]; linarith
    · show ‖metricD2 (fun y => gowdyMetric (A y)) z‖ ≤ Brad
      have h1 := (norm_metricD2_le (fun y => gowdyMetric (B y)) z).trans n2
      have h2 := norm_metricD2_sub_le (fun y => gowdyMetric (A y)) (fun y => gowdyMetric (B y)) z
      have h3 := norm_le_insert' (metricD2 (fun y => gowdyMetric (A y)) z)
        (metricD2 (fun y => gowdyMetric (B y)) z)
      have h4 : Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) ≤ 3 * Cg * (1 + M') ^ 2 := by
        have : 2 * ε₁ + ε₂ ≤ 3 := by linarith
        calc Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) ≤ Cg * (1 + M') ^ 2 * 3 :=
              mul_le_mul_of_nonneg_left this q3
          _ = 3 * Cg * (1 + M') ^ 2 := by ring
      rw [hBrad]; linarith
  -- jet errors
  have hd0 : ‖(gowdyJet A z).1 - (gowdyJet B z).1‖ ≤ Ci * ε₁ := ei
  have hd1 : ‖(gowdyJet A z).2.1 - (gowdyJet B z).2.1‖ ≤ 2 * Cg * (1 + M') * ε₁ :=
    (norm_metricD1_sub_le (fun y => gowdyMetric (A y)) (fun y => gowdyMetric (B y)) z).trans e1
  have hd2 : ‖(gowdyJet A z).2.2 - (gowdyJet B z).2.2‖ ≤ Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) :=
    (norm_metricD2_sub_le (fun y => gowdyMetric (A y)) (fun y => gowdyMetric (B y)) z).trans e2
  have hsum : Ci * ε₁ + 2 * Cg * (1 + M') * ε₁ + Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) ≤
      K1 * (ε₁ + ε₂) := by
    have r1 := mul_nonneg hCi0 hε₂0
    have r2 := mul_nonneg q2 hε₂0
    have r3 := mul_nonneg q3 hε₂0
    have r4 := mul_nonneg q3 hε₁0
    have e : K1 * (ε₁ + ε₂) = Ci * ε₁ + Ci * ε₂ + 2 * (Cg * (1 + M')) * ε₁ +
        2 * (Cg * (1 + M')) * ε₂ + 2 * (Cg * (1 + M') ^ 2) * ε₁ + 2 * (Cg * (1 + M') ^ 2) * ε₂ := by
      simp only [K1]; ring
    have e2 : Ci * ε₁ + 2 * Cg * (1 + M') * ε₁ + Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) =
        Ci * ε₁ + 2 * (Cg * (1 + M')) * ε₁ + 2 * (Cg * (1 + M') ^ 2) * ε₁ +
          (Cg * (1 + M') ^ 2) * ε₂ := by ring
    rw [e, e2]
    linarith
  have hR := hLr _ hJA _ hJB _ _ _ hd0 hd1 hd2
  have hRiem : ‖riemJet (gowdyJet A z) - riemJet (gowdyJet B z)‖ ≤ Lr * K1 * (ε₁ + ε₂) := by
    refine hR.trans ?_
    have := mul_le_mul_of_nonneg_left hsum hLr0
    calc _ ≤ Lr * (K1 * (ε₁ + ε₂)) := this
      _ = Lr * K1 * (ε₁ + ε₂) := by ring
  have hJdist : ‖gowdyJet A z - gowdyJet B z‖ ≤ K1 * (ε₁ + ε₂) :=
    (norm_jet_sub_le _ _).trans (by linarith)
  have hεs : 0 ≤ ε₁ + ε₂ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e0.trans (mul_le_mul_of_nonneg_right cA hε₁0)
  · exact e1.trans (mul_le_mul_of_nonneg_right cB hε₁0)
  · refine e2.trans ?_
    have : Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) ≤ 3 * Cg * (1 + M') ^ 2 * (ε₁ + ε₂) := by
      have r3 := mul_nonneg q3 hε₂0
      have r4 := mul_nonneg q3 hε₁0
      have e : 3 * Cg * (1 + M') ^ 2 * (ε₁ + ε₂) =
          3 * (Cg * (1 + M') ^ 2) * ε₁ + 3 * (Cg * (1 + M') ^ 2) * ε₂ := by ring
      have e2 : Cg * (1 + M') ^ 2 * (2 * ε₁ + ε₂) =
          2 * (Cg * (1 + M') ^ 2) * ε₁ + (Cg * (1 + M') ^ 2) * ε₂ := by ring
      rw [e, e2]; linarith
    exact this.trans (mul_le_mul_of_nonneg_right cC hεs)
  · exact hRiem.trans (mul_le_mul_of_nonneg_right cD hεs)
  · have hb := (hRb _ hJB).trans (le_abs_self Rb)
    have h2 := norm_le_insert' (riemJet (gowdyJet A z)) (riemJet (gowdyJet B z))
    have h3 : Lr * K1 * (ε₁ + ε₂) ≤ 2 * Lr * K1 := by
      have : ε₁ + ε₂ ≤ 2 := by linarith
      calc Lr * K1 * (ε₁ + ε₂) ≤ Lr * K1 * 2 := mul_le_mul_of_nonneg_left this q5
        _ = 2 * Lr * K1 := by ring
    linarith
  · intro hvac
    have h1 := hLc _ hJA _ hJB
    rw [hvac, sub_zero] at h1
    refine h1.trans ((mul_le_mul_of_nonneg_left hJdist hLc0).trans ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right cE hεs


/-! ### The state map `(t, P, Q, λ)` of three fields and its jets -/

/-- The map `z ↦ (t, f₀(z), f₁(z), f₂(z))` feeding the metric. -/
def stateMap (φ : Fin 3 → ℝ × ℝ → ℝ) (z : ℝ × ℝ) : Fin 4 → ℝ := ![z.1, φ 0 z, φ 1 z, φ 2 z]

theorem contDiff_stateMap {φ : Fin 3 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ ∞ (φ k)) :
    ContDiff ℝ ∞ (stateMap φ) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_fst
  · exact hφ 0
  · exact hφ 1
  · exact hφ 2

theorem fderiv_apply_component {F : ℝ × ℝ → Fin 4 → ℝ} {z : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F z) (v : ℝ × ℝ) (i : Fin 4) :
    fderiv ℝ F z v i = fderiv ℝ (fun y => F y i) z v :=
  (SecondOrderChainRule.fderiv_clm_comp' (ContinuousLinearMap.proj i) hF v).symm

theorem fderiv_fderiv_apply_component {F : ℝ × ℝ → Fin 4 → ℝ} (hF : ContDiff ℝ 2 F)
    (z v w : ℝ × ℝ) (i : Fin 4) :
    fderiv ℝ (fderiv ℝ F) z v w i = fderiv ℝ (fderiv ℝ (fun y => F y i)) z v w :=
  (SecondOrderChainRule.fderiv_fderiv_clm_comp (ContinuousLinearMap.proj i) hF z v w).symm

theorem fderiv_fderiv_apply {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (z v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ φ) z v w = fderiv ℝ (fun y => fderiv ℝ φ y w) z v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

theorem stateMap_component_zero (φ : Fin 3 → ℝ × ℝ → ℝ) :
    (fun y => stateMap φ y 0) = Prod.fst := rfl

theorem fderiv_fst_apply (z v : ℝ × ℝ) : fderiv ℝ (fun y : ℝ × ℝ => y.1) z v = v.1 := by
  rw [show (fun y : ℝ × ℝ => y.1) = Prod.fst from rfl, fderiv_fst]; rfl

theorem fderiv_fderiv_fst (z : ℝ × ℝ) : fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ => y.1)) z = 0 := by
  have : fderiv ℝ (fun y : ℝ × ℝ => y.1) = fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ := by
    funext y; rw [show (fun y : ℝ × ℝ => y.1) = Prod.fst from rfl, fderiv_fst]
  rw [this]; exact fderiv_const_apply _

/-- First-derivative errors of state maps from the partial derivatives of the fields. -/
theorem norm_fderiv_stateMap_sub_le {φ ψ : Fin 3 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ ∞ (φ k))
    (hψ : ∀ k, ContDiff ℝ ∞ (ψ k)) (z : ℝ × ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h1 : ∀ k, |dP (φ k) z - dP (ψ k) z| ≤ ε) (h2 : ∀ k, |dQ (φ k) z - dQ (ψ k) z| ≤ ε) :
    ‖fderiv ℝ (stateMap φ) z - fderiv ℝ (stateMap ψ) z‖ ≤ 2 * ε := by
  have hdA := ((contDiff_stateMap hφ).differentiable (by norm_num)) z
  have hdB := ((contDiff_stateMap hψ).differentiable (by norm_num)) z
  have hcomp : ∀ v : ℝ × ℝ, (∀ k, |fderiv ℝ (φ k) z v - fderiv ℝ (ψ k) z v| ≤ ε) →
      ‖(fderiv ℝ (stateMap φ) z - fderiv ℝ (stateMap ψ) z) v‖ ≤ ε := by
    intro v hv
    refine (pi_norm_le_iff_of_nonneg hε).2 fun i => ?_
    rw [ContinuousLinearMap.sub_apply, Pi.sub_apply, fderiv_apply_component hdA,
      fderiv_apply_component hdB, Real.norm_eq_abs]
    fin_cases i
    · simp [stateMap_component_zero, hε]
    · exact hv 0
    · exact hv 1
    · exact hv 2
  refine (SecondOrderChainRule.norm_clm_prod_le _).trans ?_
  have := hcomp (1, 0) h1
  have := hcomp (0, 1) h2
  linarith

/-- Second-derivative errors of state maps from the second partial derivatives of the fields. -/
theorem norm_fderiv_fderiv_stateMap_sub_le {φ ψ : Fin 3 → ℝ × ℝ → ℝ}
    (hφ : ∀ k, ContDiff ℝ ∞ (φ k)) (hψ : ∀ k, ContDiff ℝ ∞ (ψ k)) (z : ℝ × ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (h11 : ∀ k, |dP (dP (φ k)) z - dP (dP (ψ k)) z| ≤ ε)
    (h12 : ∀ k, |dP (dQ (φ k)) z - dP (dQ (ψ k)) z| ≤ ε)
    (h22 : ∀ k, |dQ (dQ (φ k)) z - dQ (dQ (ψ k)) z| ≤ ε) :
    ‖fderiv ℝ (fderiv ℝ (stateMap φ)) z - fderiv ℝ (fderiv ℝ (stateMap ψ)) z‖ ≤ 4 * ε := by
  have hA : ContDiff ℝ 2 (stateMap φ) := (contDiff_stateMap hφ).of_le (by norm_cast)
  have hB : ContDiff ℝ 2 (stateMap ψ) := (contDiff_stateMap hψ).of_le (by norm_cast)
  have hcomp : ∀ v w : ℝ × ℝ, (∀ k, |fderiv ℝ (fderiv ℝ (φ k)) z v w -
      fderiv ℝ (fderiv ℝ (ψ k)) z v w| ≤ ε) →
      ‖(fderiv ℝ (fderiv ℝ (stateMap φ)) z - fderiv ℝ (fderiv ℝ (stateMap ψ)) z) v w‖ ≤ ε := by
    intro v w hv
    refine (pi_norm_le_iff_of_nonneg hε).2 fun i => ?_
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, Pi.sub_apply,
      fderiv_fderiv_apply_component hA, fderiv_fderiv_apply_component hB, Real.norm_eq_abs]
    fin_cases i
    · simp [stateMap_component_zero, hε]
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have conv : ∀ (χ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ χ →
      fderiv ℝ (fderiv ℝ χ) z (1, 0) (1, 0) = dP (dP χ) z ∧
      fderiv ℝ (fderiv ℝ χ) z (1, 0) (0, 1) = dP (dQ χ) z ∧
      fderiv ℝ (fderiv ℝ χ) z (0, 1) (1, 0) = dP (dQ χ) z ∧
      fderiv ℝ (fderiv ℝ χ) z (0, 1) (0, 1) = dQ (dQ χ) z := by
    intro χ hχ
    have h2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    refine ⟨fderiv_fderiv_apply h2 z _ _, fderiv_fderiv_apply h2 z _ _, ?_,
      fderiv_fderiv_apply h2 z _ _⟩
    rw [fderiv_fderiv_apply h2 z, ← dQ_dP hχ]
    rfl
  refine (SecondOrderChainRule.norm_bilin_prod_le _).trans ?_
  have a1 := hcomp (1, 0) (1, 0) fun k => by
    rw [(conv _ (hφ k)).1, (conv _ (hψ k)).1]; exact h11 k
  have a2 := hcomp (1, 0) (0, 1) fun k => by
    rw [(conv _ (hφ k)).2.1, (conv _ (hψ k)).2.1]; exact h12 k
  have a3 := hcomp (0, 1) (1, 0) fun k => by
    rw [(conv _ (hφ k)).2.2.1, (conv _ (hψ k)).2.2.1]; exact h12 k
  have a4 := hcomp (0, 1) (0, 1) fun k => by
    rw [(conv _ (hφ k)).2.2.2, (conv _ (hψ k)).2.2.2]; exact h22 k
  linarith

/-- Bounds on the jets of a state map from bounds on the partial derivatives of the fields. -/
theorem norm_fderiv_stateMap_le {ψ : Fin 3 → ℝ × ℝ → ℝ} (hψ : ∀ k, ContDiff ℝ ∞ (ψ k))
    (z : ℝ × ℝ) {M : ℝ} (hM : 0 ≤ M) (h1 : ∀ k, |dP (ψ k) z| ≤ M) (h2 : ∀ k, |dQ (ψ k) z| ≤ M)
    (h11 : ∀ k, |dP (dP (ψ k)) z| ≤ M) (h12 : ∀ k, |dP (dQ (ψ k)) z| ≤ M)
    (h22 : ∀ k, |dQ (dQ (ψ k)) z| ≤ M) :
    ‖fderiv ℝ (stateMap ψ) z‖ ≤ 2 * (1 + M) ∧
      ‖fderiv ℝ (fderiv ℝ (stateMap ψ)) z‖ ≤ 4 * M := by
  have hd := ((contDiff_stateMap hψ).differentiable (by norm_num)) z
  have hB : ContDiff ℝ 2 (stateMap ψ) := (contDiff_stateMap hψ).of_le (by norm_cast)
  constructor
  · refine (SecondOrderChainRule.norm_clm_prod_le _).trans ?_
    have hv : ∀ v : ℝ × ℝ, |v.1| ≤ 1 → (∀ k, |fderiv ℝ (ψ k) z v| ≤ M) →
        ‖fderiv ℝ (stateMap ψ) z v‖ ≤ 1 + M := by
      intro v hv1 hv
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [fderiv_apply_component hd, Real.norm_eq_abs]
      fin_cases i
      · show |fderiv ℝ (fun y : ℝ × ℝ => y.1) z v| ≤ 1 + M
        rw [fderiv_fst_apply]; linarith
      · exact (hv 0).trans (by linarith)
      · exact (hv 1).trans (by linarith)
      · exact (hv 2).trans (by linarith)
    have := hv (1, 0) (by norm_num) h1
    have := hv (0, 1) (by norm_num) h2
    linarith
  · have hcomp : ∀ v w : ℝ × ℝ, (∀ k, |fderiv ℝ (fderiv ℝ (ψ k)) z v w| ≤ M) →
        ‖fderiv ℝ (fderiv ℝ (stateMap ψ)) z v w‖ ≤ M := by
      intro v w hv
      refine (pi_norm_le_iff_of_nonneg hM).2 fun i => ?_
      rw [fderiv_fderiv_apply_component hB, Real.norm_eq_abs]
      fin_cases i
      · show |fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ => y.1)) z v w| ≤ M
        rw [fderiv_fderiv_fst]; simpa using hM
      · exact hv 0
      · exact hv 1
      · exact hv 2
    have conv : ∀ (χ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ χ →
        fderiv ℝ (fderiv ℝ χ) z (1, 0) (1, 0) = dP (dP χ) z ∧
        fderiv ℝ (fderiv ℝ χ) z (1, 0) (0, 1) = dP (dQ χ) z ∧
        fderiv ℝ (fderiv ℝ χ) z (0, 1) (1, 0) = dP (dQ χ) z ∧
        fderiv ℝ (fderiv ℝ χ) z (0, 1) (0, 1) = dQ (dQ χ) z := by
      intro χ hχ
      have h2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
      refine ⟨fderiv_fderiv_apply h2 z _ _, fderiv_fderiv_apply h2 z _ _, ?_,
        fderiv_fderiv_apply h2 z _ _⟩
      rw [fderiv_fderiv_apply h2 z, ← dQ_dP hχ]
      rfl
    refine (SecondOrderChainRule.norm_bilin_prod_le _).trans ?_
    have a1 := hcomp (1, 0) (1, 0) fun k => by rw [(conv _ (hψ k)).1]; exact h11 k
    have a2 := hcomp (1, 0) (0, 1) fun k => by rw [(conv _ (hψ k)).2.1]; exact h12 k
    have a3 := hcomp (0, 1) (1, 0) fun k => by rw [(conv _ (hψ k)).2.2.1]; exact h12 k
    have a4 := hcomp (0, 1) (0, 1) fun k => by rw [(conv _ (hψ k)).2.2.2]; exact h22 k
    linarith


/-! ### The full-curvature theorem -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ}

open CoordinateCurvatureJet in
set_option maxHeartbeats 1600000 in
/-- **Pathwise full-curvature control on the Gowdy alphabet** (`thm:supp-gowdy-full-curvature`,
`eq:supp-gowdy-full-curvature` and `eq:supp-gowdy-curvature-certificate`).  Let `X_*` be a smooth
reference (frame system and coordinate constraints on `[t₀, t₁] × 𝕋¹`, `t₀ > 0`) and
`R ≥ chartRadius`.  For every `c₀, C₁ ≥ 0` there are `C` and `h₀ > 0` such that for every mesh
`h = ℓ = 2π/N ≤ h₀` and every numerical history obeying the offset cap `≤ c₀ h⁴` and the
pathwise `C¹_h` bound `≤ C₁ h²` (`PathwiseHistory`), on every cell
`[τ₀ + nh, τ₀ + (n+1)h] × [θ_j, θ_j + h]`, with `g_h = g(t, P_h, Q_h, λ_h)` the metric
`eq:supp-gowdy-metric` of the shared Hermite readout and `g_* = g(t, P, Q, λ)`:
`‖g_h - g_*‖ ≤ C h²`, `‖Dg_h - Dg_*‖ ≤ C h²`, `‖D²g_h - D²g_*‖ ≤ C h`,
`‖Riem(g_h) - Riem(g_*)‖ ≤ C h`, `‖Riem(g_h)‖ ≤ C`, and `‖Ric(g_h)‖ ≤ C h` wherever `g_*` is
Ricci flat.  Here `Riem`, `Ric` are the coordinate curvature tensors of the 2-jet
`(g⁻¹, ∂g, ∂²g)` (`CoordinateCurvatureJet.riemJet`, `ricciJet`), `g⁻¹` the matrix inverse
(`gowdyInvMetric_eq_inv`). -/
theorem readout_full_curvature (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) {c₀ C₁ : ℝ} (hc₀ : 0 ≤ c₀) (hC₁ : 0 ≤ C₁) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ) (X A B : ℕ → GridState N),
        sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B →
        ∀ n < n₀, ∀ (j : ZMod N),
        ∀ x ∈ Icc (τ₀ + n * (2 * Real.pi / N)) (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N),
        ∀ y ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
          ‖gowdyMetric (stateMap (cellReadout X τ₀ n j) (x, y)) -
              gowdyMetric (stateMap sol.fld (x, y))‖ ≤ C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z)) (x, y) -
              fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z)) (x, y)‖ ≤
            C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z))) (x, y) -
              fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z))) (x, y)‖ ≤
            C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y)) -
              riemJet (gowdyJet (stateMap sol.fld) (x, y))‖ ≤ C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤ C ∧
          (ricciJet (gowdyJet (stateMap sol.fld) (x, y)) = 0 →
            ‖ricciJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤
              C * (2 * Real.pi / N)) := by
  obtain ⟨Csj, ℓ₁, hCsj, hℓ₁, hsj⟩ := sol.readout_second_jet h0 hR hc₀ hC₁
  have hb := fun k : Fin 3 => exists_partials_bound (sol.smooth_fld k) (sol.periodic_fld k) t₀ t₁
  choose Mk hMk0 hMk using hb
  set M₃ := ∑ k, Mk k
  have hM₃0 : 0 ≤ M₃ := Finset.sum_nonneg fun k _ => hMk0 k
  have hM₃ : ∀ k : Fin 3, ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ∀ a b : ℕ, a ≤ 6 → b ≤ 6 →
      |(dP^[a] (dQ^[b] (sol.fld k))) p| ≤ M₃ := fun k p hp a b ha hb =>
    (hMk k p hp a b ha hb).trans (Finset.single_le_sum (f := Mk) (fun k _ => hMk0 k) (mem_univ k))
  set ρ := t₁ + M₃ + 1
  set Mref := 2 * (1 + M₃) + 4 * M₃
  have hMref : 0 ≤ Mref := by positivity
  obtain ⟨Ct, hCt0, ht⟩ := gowdy_jet_transfer h0 ρ Mref hMref
  set ℓ₀ := min ℓ₁ (min 1 (1 / (4 * Csj + 1)))
  have hℓ₀ : 0 < ℓ₀ := lt_min hℓ₁ (lt_min one_pos (by positivity))
  refine ⟨Ct * (6 * Csj + 1), ℓ₀, by positivity, hℓ₀, ?_⟩
  intro N _ hN τ₀ n₀ X A B H n hn j x hx y hy
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hℓ1 : ℓ ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hℓc : ℓ ≤ 1 / (4 * Csj + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 4 * Csj * ℓ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hℓc
    nlinarith
  have hsj' := hsj N (hN.trans (min_le_left _ _)) τ₀ n₀ X A B H n hn j
  set z : ℝ × ℝ := (x, y)
  -- the cell lies in the slab
  have hzs : z.1 ∈ Icc t₀ t₁ := by
    have h1 := H.time_mem (m := n) hn.le
    have h2 := H.time_mem (m := n + 1) hn
    push_cast at h2
    exact ⟨h1.1.trans hx.1, hx.2.trans (by linarith [h2.2])⟩
  have hφ : ∀ k, ContDiff ℝ ∞ (cellReadout X τ₀ n j k) := fun k => contDiff_readout _ _ _ _ _ _ _
  have hψ := sol.smooth_fld
  -- field errors
  have E := fun k i i' => hsj' k x hx y hy i i'
  have e00 : ∀ k, |cellReadout X τ₀ n j k z - sol.fld k z| ≤ Csj * ℓ ^ 2 := fun k =>
    (E k 0 0).1 (by norm_num)
  have e10 : ∀ k, |dP (cellReadout X τ₀ n j k) z - dP (sol.fld k) z| ≤ Csj * ℓ ^ 2 := fun k =>
    (E k 1 0).1 (by norm_num)
  have e01 : ∀ k, |dQ (cellReadout X τ₀ n j k) z - dQ (sol.fld k) z| ≤ Csj * ℓ ^ 2 := fun k =>
    (E k 0 1).1 (by norm_num)
  have e20 : ∀ k, |dP (dP (cellReadout X τ₀ n j k)) z - dP (dP (sol.fld k)) z| ≤ Csj * ℓ :=
    fun k => (E k 2 0).2 (by norm_num)
  have e11 : ∀ k, |dP (dQ (cellReadout X τ₀ n j k)) z - dP (dQ (sol.fld k)) z| ≤ Csj * ℓ :=
    fun k => (E k 1 1).2 (by norm_num)
  have e02 : ∀ k, |dQ (dQ (cellReadout X τ₀ n j k)) z - dQ (dQ (sol.fld k)) z| ≤ Csj * ℓ :=
    fun k => (E k 0 2).2 (by norm_num)
  have hℓ2 : ℓ ^ 2 ≤ ℓ := by nlinarith
  have hCℓ2 : Csj * ℓ ^ 2 ≤ Csj * ℓ := mul_le_mul_of_nonneg_left hℓ2 hCsj
  have hCℓ : Csj * ℓ ≤ 1 := by nlinarith
  set ε₁ := 2 * Csj * ℓ ^ 2
  set ε₂ := 4 * Csj * ℓ
  have hε₁ : ε₁ ≤ 1 := by simp only [ε₁]; nlinarith
  have hε₂ : ε₂ ≤ 1 := hsmall
  have d0 : ‖stateMap (cellReadout X τ₀ n j) z - stateMap sol.fld z‖ ≤ ε₁ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    fin_cases i
    · simp [stateMap]; positivity
    · exact (e00 0).trans (by simp only [ε₁]; nlinarith [sq_nonneg ℓ])
    · exact (e00 1).trans (by simp only [ε₁]; nlinarith [sq_nonneg ℓ])
    · exact (e00 2).trans (by simp only [ε₁]; nlinarith [sq_nonneg ℓ])
  have d1 := norm_fderiv_stateMap_sub_le hφ hψ z (by positivity) e10 e01
  have d2 := norm_fderiv_fderiv_stateMap_sub_le hφ hψ z (by positivity) e20 e11 e02
  -- reference bounds
  have r1 : ∀ k, |dP (sol.fld k) z| ≤ M₃ := fun k => hM₃ k z hzs 1 0 (by norm_num) (by norm_num)
  have r2 : ∀ k, |dQ (sol.fld k) z| ≤ M₃ := fun k => hM₃ k z hzs 0 1 (by norm_num) (by norm_num)
  have r11 : ∀ k, |dP (dP (sol.fld k)) z| ≤ M₃ := fun k =>
    hM₃ k z hzs 2 0 (by norm_num) (by norm_num)
  have r12 : ∀ k, |dP (dQ (sol.fld k)) z| ≤ M₃ := fun k =>
    hM₃ k z hzs 1 1 (by norm_num) (by norm_num)
  have r22 : ∀ k, |dQ (dQ (sol.fld k)) z| ≤ M₃ := fun k =>
    hM₃ k z hzs 0 2 (by norm_num) (by norm_num)
  obtain ⟨b1, b2⟩ := norm_fderiv_stateMap_le hψ z hM₃0 r1 r2 r11 r12 r22
  -- chart membership
  have hx0 : 0 < x := lt_of_lt_of_le h0 hzs.1
  have hρ0 : 0 ≤ ρ := by simp only [ρ]; linarith [hzs.1, hzs.2]
  have hBz : stateMap sol.fld z ∈ metricChart t₀ ρ := by
    refine ⟨hzs.1, ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hρ0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · simp only [stateMap]; simp; rw [abs_of_pos hx0]; linarith [hzs.2]
    · exact (hM₃ 0 z hzs 0 0 (by norm_num) (by norm_num)).trans (by linarith [hzs.2])
    · exact (hM₃ 1 z hzs 0 0 (by norm_num) (by norm_num)).trans (by linarith [hzs.2])
    · exact (hM₃ 2 z hzs 0 0 (by norm_num) (by norm_num)).trans (by linarith [hzs.2])
  have hAz : stateMap (cellReadout X τ₀ n j) z ∈ metricChart t₀ ρ := by
    refine ⟨hzs.1, ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hρ0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hb : ∀ k, |cellReadout X τ₀ n j k z| ≤ M₃ + 1 := fun k => by
      have h1 := hM₃ k z hzs 0 0 (by norm_num) (by norm_num)
      have h2 := e00 k
      have h3 : |cellReadout X τ₀ n j k z| ≤ |sol.fld k z| +
          |cellReadout X τ₀ n j k z - sol.fld k z| := by
        have := abs_add_le (sol.fld k z) (cellReadout X τ₀ n j k z - sol.fld k z)
        simpa using this
      simp only [Function.iterate_zero, id] at h1
      linarith
    fin_cases i
    · simp only [stateMap]; simp; rw [abs_of_pos hx0]; linarith [hzs.2]
    · exact (hb 0).trans (by linarith [hzs.2])
    · exact (hb 1).trans (by linarith [hzs.2])
    · exact (hb 2).trans (by linarith [hzs.2])
  have hA2 : ContDiff ℝ 2 (stateMap (cellReadout X τ₀ n j)) :=
    (contDiff_stateMap hφ).of_le (by norm_cast)
  have hB2 : ContDiff ℝ 2 (stateMap sol.fld) := (contDiff_stateMap hψ).of_le (by norm_cast)
  have hd1' : ‖fderiv ℝ (stateMap (cellReadout X τ₀ n j)) z - fderiv ℝ (stateMap sol.fld) z‖ ≤
      ε₁ := d1.trans (by simp only [ε₁]; linarith)
  have hd2' : ‖fderiv ℝ (fderiv ℝ (stateMap (cellReadout X τ₀ n j))) z -
      fderiv ℝ (fderiv ℝ (stateMap sol.fld)) z‖ ≤ ε₂ := d2.trans (by simp only [ε₂]; linarith)
  have hb1' : ‖fderiv ℝ (stateMap sol.fld) z‖ ≤ Mref := b1.trans (by simp only [Mref]; linarith)
  have hb2' : ‖fderiv ℝ (fderiv ℝ (stateMap sol.fld)) z‖ ≤ Mref :=
    b2.trans (by simp only [Mref]; linarith)
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := ht _ _ hA2 hB2 z hAz hBz hb1' hb2' ε₁ ε₂ hε₁ hε₂ d0 hd1' hd2'
  have hCt' : 0 ≤ Ct * (6 * Csj + 1) := by positivity
  have k1 : Ct * ε₁ ≤ Ct * (6 * Csj + 1) * ℓ ^ 2 := by
    have : ε₁ ≤ (6 * Csj + 1) * ℓ ^ 2 := by
      simp only [ε₁]; nlinarith [sq_nonneg ℓ]
    calc Ct * ε₁ ≤ Ct * ((6 * Csj + 1) * ℓ ^ 2) := mul_le_mul_of_nonneg_left this hCt0
      _ = _ := by ring
  have k2 : Ct * (ε₁ + ε₂) ≤ Ct * (6 * Csj + 1) * ℓ := by
    have : ε₁ + ε₂ ≤ (6 * Csj + 1) * ℓ := by
      simp only [ε₁, ε₂]; nlinarith
    calc Ct * (ε₁ + ε₂) ≤ Ct * ((6 * Csj + 1) * ℓ) := mul_le_mul_of_nonneg_left this hCt0
      _ = _ := by ring
  refine ⟨m0.trans k1, m1.trans k1, m2.trans k2, m3.trans k2, m4.trans ?_,
    fun hv => (m5 hv).trans k2⟩
  nlinarith [mul_nonneg hCt0 hCsj]

end GowdySmoothReference

/-! ### `C¹` gluing of the cellwise readout -/

/-- **`C¹` gluing in time**: the readouts of the cells `(n, j)` and `(n+1, j)` share their nodal
jets at `t = τ₀ + (n+1)h`, so their values, first time derivatives and all space derivatives (up
to order 2) agree on the common edge. -/
theorem cellReadout_glue_t (X : ℕ → GridState N) (τ₀ : ℝ) (n : ℕ) (j : ZMod N) (k : Fin 3)
    {i i' : ℕ} (hi : i ≤ 1) (hi' : i' ≤ 2) (y : ℝ) :
    (dP^[i] (dQ^[i'] (cellReadout X τ₀ n j k))) (τ₀ + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi / N), y) =
      (dP^[i] (dQ^[i'] (cellReadout X τ₀ (n + 1) j k)))
        (τ₀ + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi / N), y) := by
  have hℓ : (2 * Real.pi / N) ≠ 0 := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have e : τ₀ + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi / N) =
      τ₀ + (n : ℝ) * (2 * Real.pi / N) + 2 * Real.pi / N := by push_cast; ring
  unfold cellReadout
  rw [e]
  have hg := readout_glue_x (x₀ := τ₀ + (n : ℝ) * (2 * Real.pi / N)) (y₀ := sampleAngle N j)
    hℓ (f := numF X n j k) (u := numU X n j k) (v := numV X n j k) (w := numW X n j k)
    (f' := numF X (n + 1) j k) (u' := numU X (n + 1) j k) (v' := numV X (n + 1) j k)
    (w' := numW X (n + 1) j k) (fun b => by simp [numF]) (fun b => by simp [numU])
    (fun b => by simp [numV]) (fun b => by simp [numW]) hi hi' y
  rw [hg]

/-- **`C¹` gluing in space**: the readouts of the cells `(n, j)` and `(n, j+1)` share their nodal
jets at the common edge `θ = θ_j + h` (which is `θ_{j+1}` modulo `2π`), so their values, first
space derivatives and all time derivatives (up to order 2) agree there. -/
theorem cellReadout_glue_θ (X : ℕ → GridState N) (τ₀ : ℝ) (n : ℕ) (j : ZMod N) (k : Fin 3)
    {i i' : ℕ} (hi : i ≤ 2) (hi' : i' ≤ 1) (x : ℝ) :
    (dP^[i] (dQ^[i'] (cellReadout X τ₀ n j k))) (x, sampleAngle N j + 2 * Real.pi / N) =
      (dP^[i] (dQ^[i'] (cellReadout X τ₀ n (j + 1) k))) (x, sampleAngle N (j + 1)) := by
  have hℓ : (2 * Real.pi / N) ≠ 0 := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  set ℓ := 2 * Real.pi / N
  set x₀ := τ₀ + (n : ℝ) * ℓ
  have ex : x = x₀ + ℓ * ((x - x₀) / ℓ) := by field_simp; ring
  unfold cellReadout
  have e1 := iterate_dP_dQ_readout (x₀ := x₀) (y₀ := sampleAngle N j) hℓ (numF X n j k)
    (numU X n j k) (numV X n j k) (numW X n j k) hi (by omega : i' ≤ 2) ((x - x₀) / ℓ) 1
  have e2 := iterate_dP_dQ_readout (x₀ := x₀) (y₀ := sampleAngle N (j + 1)) hℓ
    (numF X n (j + 1) k) (numU X n (j + 1) k) (numV X n (j + 1) k) (numW X n (j + 1) k) hi
    (by omega : i' ≤ 2) ((x - x₀) / ℓ) 0
  rw [mul_one, ← ex] at e1
  rw [mul_zero, add_zero, ← ex] at e2
  rw [e1, e2, cellDeriv_glue_q ℓ (f' := numF X n (j + 1) k) (u' := numU X n (j + 1) k)
    (v' := numV X n (j + 1) k) (w' := numW X n (j + 1) k) (fun a => by simp [numF])
    (fun a => by simp [numU]) (fun a => by simp [numV]) (fun a => by simp [numW]) i hi']

/-! ### Non-vacuity -/

/-- The constant solution `a = b = c = d = 0`, `P = Q = λ = 0` is a smooth reference: the
hypotheses of `GowdySmoothReference` are satisfiable. -/
def zeroReference (t₀ t₁ : ℝ) : GowdySmoothReference t₀ t₁ where
  a := fun _ => 0
  b := fun _ => 0
  c := fun _ => 0
  d := fun _ => 0
  P := fun _ => 0
  Q := fun _ => 0
  lam := fun _ => 0
  smooth_a := contDiff_const
  smooth_b := contDiff_const
  smooth_c := contDiff_const
  smooth_d := contDiff_const
  smooth_P := contDiff_const
  smooth_Q := contDiff_const
  smooth_lam := contDiff_const
  periodic_a _ := rfl
  periodic_b _ := rfl
  periodic_c _ := rfl
  periodic_d _ := rfl
  periodic_P _ := rfl
  periodic_Q _ := rfl
  periodic_lam _ := rfl
  eq_a _ _ := by simp [dT, dΘ]
  eq_b _ _ := by simp [dT, dΘ]
  eq_c _ _ := by simp [dT, dΘ]
  eq_d _ _ := by simp [dT, dΘ]
  eq_P _ _ := by simp [dT]
  eq_Q _ _ := by simp [dT]
  eq_lam _ _ := by simp [dT]
  smoothInf_a := contDiff_const
  smoothInf_b := contDiff_const
  smoothInf_c := contDiff_const
  smoothInf_d := contDiff_const
  smoothInf_P := contDiff_const
  smoothInf_Q := contDiff_const
  smoothInf_lam := contDiff_const
  constraint_P _ _ := by simp [dΘ]
  constraint_Q _ _ := by simp [dΘ]
  constraint_lam _ _ := by simp [dΘ]


/-- The grid state `U = 0, P = Q = λ = 0` at time `τ`. -/
def zeroState (N : ℕ) (τ : ℝ) : GridState N :=
  ⟨fun _ => ⟨0, 0, 0, τ⟩, fun _ => 0⟩

theorem zeroReference_sample (t₀ t₁ τ : ℝ) :
    (zeroReference t₀ t₁).sample N τ = zeroState N τ := by
  simp only [GowdyFrameSolution.sample, zeroState, GowdyFrameSolution.Z, LocalState.ofVec]
  congr
  funext j
  congr 1
  funext i
  simp [GowdyFrameSolution.fr, zeroReference]
  fin_cases i <;> simp

theorem isSourceStep_zeroState (σ τ : ℝ) :
    IsSourceStep σ (zeroState N τ) (zeroState N (τ + σ)) := by
  refine ⟨fun j => ⟨?_, ?_, ?_, ?_⟩, rfl⟩ <;>
    simp [zeroState, localField, midpoint, sourceField]
  funext i; fin_cases i <;> rfl

theorem transport_zeroState (ℓ τ : ℝ) : transport ℓ (zeroState N τ) = zeroState N τ := by
  simp only [transport, zeroState]
  congr
  · funext j
    congr 1
    funext i
    fin_cases i <;> simp [recombine, wPlus, wMinus]
  · funext j
    simp [gPlus, gMinus, wPlus, wMinus]

theorem charDist_self (X : GridState N) : charDist X X = 0 :=
  le_antisymm (charDist_le (fun j => by simp [charNorm]) (fun j => by simp))
    (charDist_nonneg X X)

theorem crNorm_errArr_self (ℓ : ℝ) (X : GridState N) :
    PeriodicGridResidual.crNorm 1 ℓ (errArr X X) = 0 := by
  have h0 : errArr X X = 0 := by funext j; simp [errArr]
  have hi : ∀ k, (PeriodicGridResidual.fwdDiff ℓ)^[k] (errArr X X) = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext j; simp [PeriodicGridResidual.fwdDiff]
  refine le_antisymm (Finset.sup'_le _ _ fun k _ => by rw [hi k]; simp)
    (PeriodicGridResidual.crNorm_nonneg _ _ _)

/-- **Non-vacuity of `PathwiseHistory`**: for the zero reference, the exact history
`X_n = zeroState (τ₀ + nh)` with the exact split stages satisfies all pathwise hypotheses (split
steps in the envelope of any radius `R ≥ t₁`, zero offsets, zero `C¹_h` error). -/
theorem zeroReference_pathwiseHistory {t₀ t₁ : ℝ} (h0 : 0 < t₀) (N : ℕ) [NeZero N] (τ₀ : ℝ)
    (n₀ : ℕ) (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) {R c₀ C₁ : ℝ}
    (hR : t₁ ≤ R) (hc₀ : 0 ≤ c₀) (hC₁ : 0 ≤ C₁) :
    ∃ X A B : ℕ → GridState N,
      (zeroReference t₀ t₁).PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B := by
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓ : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  refine ⟨fun n => zeroState N (τ₀ + n * ℓ), fun n => zeroState N (τ₀ + n * ℓ + ℓ / 2),
    fun n => zeroState N (τ₀ + n * ℓ + ℓ / 2 + ℓ / 2), ⟨hτ₀, hn₀, fun n hn => ?_, fun n _ => ?_,
    fun n _ => ?_⟩⟩
  · have hτn : τ₀ + n * ℓ + ℓ ≤ t₁ := by
      have hm' : ((n + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hn
      have := mul_le_mul_of_nonneg_right hm' hℓ.le
      push_cast at this
      linarith
    have hn0 : 0 ≤ (n : ℝ) * ℓ := by positivity
    refine ⟨⟨isSourceStep_zeroState _ _, ?_⟩, fun j => ⟨?_, ?_, ?_⟩⟩
    · rw [transport_zeroState]; exact isSourceStep_zeroState _ _
    · refine ⟨?_, fun i => ?_, ?_⟩ <;>
        simp [zeroState, LocalState.toVec] <;> linarith
    · have hR0 : 0 ≤ R := by linarith
      refine norm_stateVec_le hR0 (fun i => ?_) ?_ ?_ ?_
      · simp [zeroState, LocalState.toVec]; exact hR0
      · simp [zeroState, LocalState.toVec]; exact hR0
      · simp [zeroState, LocalState.toVec]; exact hR0
      · simp only [zeroState, LocalState.toVec]
        rw [abs_of_nonneg (by linarith)]
        linarith
    · rw [transport_zeroState]
      refine ⟨?_, fun i => ?_, ?_⟩ <;>
        simp [zeroState, LocalState.toVec] <;> linarith
  · have e : τ₀ + ((n + 1 : ℕ) : ℝ) * ℓ = τ₀ + n * ℓ + ℓ / 2 + ℓ / 2 := by push_cast; ring
    show charDist (zeroState N (τ₀ + ((n + 1 : ℕ) : ℝ) * ℓ))
      (zeroState N (τ₀ + n * ℓ + ℓ / 2 + ℓ / 2)) ≤ c₀ * ℓ ^ 4
    rw [e, charDist_self]
    positivity
  · show PeriodicGridResidual.crNorm 1 ℓ (errArr (zeroState N (τ₀ + n * ℓ))
      ((zeroReference t₀ t₁).sample N (τ₀ + n * ℓ))) ≤ C₁ * ℓ ^ 2
    rw [zeroReference_sample, crNorm_errArr_self]
    positivity


/-- Non-vacuity of the hypothesis packet of `GowdySmoothReference.readout_second_jet` and
`readout_full_curvature`: an envelope radius `R ≥ chartRadius` and a history satisfying
`PathwiseHistory` exist (zero reference, exact history). -/
example {t₀ t₁ : ℝ} (h0 : 0 < t₀) (N : ℕ) [NeZero N] (τ₀ : ℝ) (n₀ : ℕ) (hτ₀ : t₀ ≤ τ₀)
    (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) :
    ∃ R, (zeroReference t₀ t₁).chartRadius h0 ≤ R ∧ ∃ X A B : ℕ → GridState N,
      (zeroReference t₀ t₁).PathwiseHistory h0 R 0 0 N τ₀ n₀ X A B :=
  ⟨max t₁ ((zeroReference t₀ t₁).chartRadius h0), le_max_right _ _,
    zeroReference_pathwiseHistory h0 N τ₀ n₀ hτ₀ hn₀ (le_max_left _ _) le_rfl le_rfl⟩

end

end HermiteReadout

end RenewalGeometry.GowdyStaggered
