/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Table-derived reward pressure and action-slope reconstruction
  (`thm:reward-pressure-reconstruction`,
  Gran-Tensor manuscript)

For a protected cycle-reward packet — a finite faithful
marked first-return law `(Ω, p)`, a positive protected
duration `τ`, and a linear reward synthesis
`G : E →ₗ (Ω → ℝ)` — the complete Laplace transform
`𝓛(q, r) = 𝔼[e^{−g_q − rτ}]` is an explicit finite sum.

* `pressure_exists_unique` / `pressureFn`: for **every**
  `q` there is exactly one root `r` of `𝓛(q, r) = 1`
  (strict antitonicity in `r` plus the intermediate value
  theorem), giving the boxed pressure
  `𝓟(0) = 0, 𝓛(q, 𝓟(q)) = 1` — globally, not just near
  the origin.
* `pressure_hasDerivAt`: the pressure is differentiable
  along every direction at the origin with the boxed slope
  `π(v) = −γ(v)/τ̄`, `γ = G*𝟙` — proved by the elementary
  implicit-differentiation squeeze: the mean value theorem
  in the `r`-slot expresses `𝓟(tv)/t` as an explicit
  quotient whose numerator tends to `−γ(v)` and whose
  denominator tends to `τ̄`.
* `score_hasDerivAt` and `slope_reconstruction`: the
  normalized score writer
  `S_X v = D log p_{X,q}|₀[v] = −G v − π(v)τ` is the
  genuine derivative of the tilted log-likelihood, and the
  boxed reconstruction `G = −S − Tπ` follows.
* `cov_rank_eq`: the boxed covariance-rank formula
  `rank Cov_p(g) = dim Aff{g(ω)}` — the rank of the
  `p`-weighted centered Gram matrix equals the dimension
  of the affine span of the reward table.
-/

open Finset

namespace NCG
namespace RewardPressure

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- The complete cycle Laplace transform
`𝓛(q, r) = ∑ ω, p ω · exp(−g_q(ω) − r τ(ω))`. -/
noncomputable def cycleLaplace (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (q : E) (r : ℝ) : ℝ :=
  ∑ ω, p ω * Real.exp (-(G q ω) - r * τ ω)

private theorem laplace_strictAnti (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (q : E) :
    StrictAnti (fun r => cycleLaplace p τ G q r) := by
  intro r r' hrr
  unfold cycleLaplace
  refine Finset.sum_lt_sum_of_nonempty
    Finset.univ_nonempty fun ω _ => ?_
  refine mul_lt_mul_of_pos_left ?_ (hp ω)
  refine Real.exp_lt_exp.mpr ?_
  have := mul_lt_mul_of_pos_right hrr (hτ ω)
  linarith

omit [Nonempty Ω] in
private theorem laplace_continuous (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (q : E) :
    Continuous (fun r => cycleLaplace p τ G q r) := by
  unfold cycleLaplace
  refine continuous_finsetSum _ fun ω _ =>
    continuous_const.mul ?_
  exact (continuous_const.sub
    (continuous_id.mul continuous_const)).rexp

private theorem laplace_pos (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (q : E) (r : ℝ) : 0 < cycleLaplace p τ G q r := by
  unfold cycleLaplace
  refine Finset.sum_pos (fun ω _ =>
    mul_pos (hp ω) (Real.exp_pos _)) Finset.univ_nonempty

omit [Nonempty Ω] in
private theorem laplace_tendsto_atTop (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hτ : ∀ ω, 0 < τ ω) (q : E) :
    Filter.Tendsto (fun r => cycleLaplace p τ G q r)
      Filter.atTop (nhds 0) := by
  unfold cycleLaplace
  rw [show (0 : ℝ) = ∑ _ω : Ω, (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ fun ω _ => ?_
  rw [show (0 : ℝ) = p ω * 0 from by ring]
  refine Filter.Tendsto.const_mul _ ?_
  have hinner : Filter.Tendsto
      (fun r : ℝ => -(G q ω) - r * τ ω)
      Filter.atTop Filter.atBot := by
    rw [show (fun r : ℝ => -(G q ω) - r * τ ω)
      = fun r : ℝ => -(G q ω) + (-τ ω) * r from by
        funext r; ring]
    refine Filter.tendsto_atBot_add_const_left _ _ ?_
    exact (Filter.tendsto_const_mul_atBot_of_neg
      (neg_lt_zero.mpr (hτ ω))).mpr Filter.tendsto_id
  exact Real.tendsto_exp_atBot.comp hinner

private theorem laplace_tendsto_atBot (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (q : E) :
    Filter.Tendsto (fun r => cycleLaplace p τ G q r)
      Filter.atBot Filter.atTop := by
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  have hmin : ∀ r, p ω₀ * Real.exp (-(G q ω₀) - r * τ ω₀)
      ≤ cycleLaplace p τ G q r := by
    intro r
    unfold cycleLaplace
    exact Finset.single_le_sum
      (f := fun ω => p ω * Real.exp (-(G q ω) - r * τ ω))
      (fun ω _ => le_of_lt (mul_pos (hp ω) (Real.exp_pos _)))
      (Finset.mem_univ ω₀)
  refine Filter.tendsto_atTop_mono hmin ?_
  refine Filter.Tendsto.const_mul_atTop (hp ω₀) ?_
  have hinner : Filter.Tendsto
      (fun r : ℝ => -(G q ω₀) - r * τ ω₀)
      Filter.atBot Filter.atTop := by
    rw [show (fun r : ℝ => -(G q ω₀) - r * τ ω₀)
      = fun r : ℝ => -(G q ω₀) + (-τ ω₀) * r from by
        funext r; ring]
    refine Filter.tendsto_atTop_add_const_left _ _ ?_
    exact (Filter.tendsto_const_mul_atTop_of_neg
      (neg_lt_zero.mpr (hτ ω₀))).mpr Filter.tendsto_id
  exact Real.tendsto_exp_atTop.comp hinner

/-- **Global existence and uniqueness of the pressure
root**: for every `q` there is exactly one `r` with
`𝓛(q, r) = 1`. -/
theorem pressure_exists_unique (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (q : E) :
    ∃! r : ℝ, cycleLaplace p τ G q r = 1 := by
  obtain ⟨b, hb⟩ := ((laplace_tendsto_atTop p τ G hτ
    q).eventually_lt_const (by norm_num : (0:ℝ) < 1)).exists
  obtain ⟨a, ha⟩ := ((laplace_tendsto_atBot p τ G hp hτ
    q).eventually_gt_atTop 1).exists
  have hab : a < b := by
    by_contra hle
    push Not at hle
    have := (laplace_strictAnti p τ G hp hτ q).antitone hle
    linarith
  have hIcc : (1 : ℝ) ∈ Set.Icc (cycleLaplace p τ G q b)
      (cycleLaplace p τ G q a) :=
    ⟨le_of_lt hb, le_of_lt ha⟩
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc' (le_of_lt hab)
    ((laplace_continuous p τ G q).continuousOn) hIcc
  refine ⟨r, hr, fun r' hr' => ?_⟩
  exact (laplace_strictAnti p τ G hp hτ q).injective
    (hr'.trans hr.symm)

/-- The boxed reward pressure `𝓟(q)`: the unique root of
`𝓛(q, 𝓟(q)) = 1`. -/
noncomputable def pressureFn (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (q : E) : ℝ :=
  (pressure_exists_unique p τ G hp hτ q).exists.choose

theorem pressureFn_spec (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (q : E) :
    cycleLaplace p τ G q (pressureFn p τ G hp hτ q) = 1 :=
  (pressure_exists_unique p τ G hp hτ q).exists.choose_spec

theorem pressureFn_eq_of_root (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) {q : E} {r : ℝ}
    (hr : cycleLaplace p τ G q r = 1) :
    pressureFn p τ G hp hτ q = r := by
  exact (laplace_strictAnti p τ G hp hτ q).injective
    ((pressureFn_spec p τ G hp hτ q).trans hr.symm)

/-- **Boxed normalization** `𝓟(0) = 0`. -/
theorem pressureFn_zero (p τ : Ω → ℝ)
    (G : E →ₗ[ℝ] (Ω → ℝ)) (hp : ∀ ω, 0 < p ω)
    (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω) :
    pressureFn p τ G hp hτ (0 : E) = 0 := by
  refine pressureFn_eq_of_root p τ G hp hτ ?_
  unfold cycleLaplace
  rw [← hp1]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [map_zero G]
  norm_num

section Slope

variable (p τ : Ω → ℝ) (G : E →ₗ[ℝ] (Ω → ℝ)) (v : E)

/-- The explicit mean-value denominator field
`D(t,r) = ∑ ω, p ω τ ω exp(−t g_v(ω) − r τ(ω))`. -/
noncomputable def denFun (t r : ℝ) : ℝ :=
  ∑ ω, (p ω * τ ω) * Real.exp (-(t * G v ω) - r * τ ω)

omit [Nonempty Ω] in
theorem laplace_line (t r : ℝ) :
    cycleLaplace p τ G (t • v) r
      = ∑ ω, p ω * Real.exp (-(t * G v ω) - r * τ ω) := by
  unfold cycleLaplace
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

private theorem denFun_pos (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (t r : ℝ) :
    0 < denFun p τ G v t r :=
  Finset.sum_pos (fun ω _ => mul_pos
    (mul_pos (hp ω) (hτ ω)) (Real.exp_pos _))
    Finset.univ_nonempty

omit [Nonempty Ω] in
private theorem denFun_continuous :
    Continuous (fun tr : ℝ × ℝ =>
      denFun p τ G v tr.1 tr.2) := by
  unfold denFun
  refine continuous_finsetSum _ fun ω _ =>
    continuous_const.mul ?_
  refine Continuous.rexp ?_
  exact ((continuous_fst.mul continuous_const).neg).sub
    (continuous_snd.mul continuous_const)

omit [Nonempty Ω] in
private theorem hasDerivAt_laplace_r (t r₀ : ℝ) :
    HasDerivAt (fun r => cycleLaplace p τ G (t • v) r)
      (-(denFun p τ G v t r₀)) r₀ := by
  have hterm : ∀ ω : Ω,
      HasDerivAt (fun r => p ω *
        Real.exp (-(t * G v ω) - r * τ ω))
      (-((p ω * τ ω) *
        Real.exp (-(t * G v ω) - r₀ * τ ω))) r₀ := by
    intro ω
    have h1 : HasDerivAt (fun r : ℝ => r * τ ω)
        (τ ω) r₀ := hasDerivAt_mul_const (τ ω)
    have h2 := h1.const_sub (-(t * G v ω))
    have h3 := h2.exp
    have h4 := h3.const_mul (p ω)
    have h5 : -((p ω * τ ω) *
        Real.exp (-(t * G v ω) - r₀ * τ ω))
        = p ω * (Real.exp (-(t * G v ω) - r₀ * τ ω)
          * -(τ ω)) := by ring
    rw [h5]
    exact h4
  have hexp : HasDerivAt (fun r => ∑ ω, p ω *
      Real.exp (-(t * G v ω) - r * τ ω))
      (∑ ω, -((p ω * τ ω) *
        Real.exp (-(t * G v ω) - r₀ * τ ω))) r₀ :=
    HasDerivAt.fun_sum fun ω _ => hterm ω
  have heq : -(denFun p τ G v t r₀)
      = ∑ ω, -((p ω * τ ω) *
        Real.exp (-(t * G v ω) - r₀ * τ ω)) := by
    unfold denFun
    rw [Finset.sum_neg_distrib]
  rw [heq]
  have hee : (fun r => cycleLaplace p τ G (t • v) r)
      =ᶠ[nhds r₀] (fun r => ∑ ω, p ω *
        Real.exp (-(t * G v ω) - r * τ ω)) :=
    Filter.Eventually.of_forall fun r =>
      laplace_line p τ G v t r
  exact hexp.congr_of_eventuallyEq hee

omit [Nonempty Ω] in
private theorem hasDerivAt_laplace_t :
    HasDerivAt (fun t : ℝ => cycleLaplace p τ G (t • v) 0)
      (-(∑ ω, p ω * G v ω)) 0 := by
  have hterm : ∀ ω : Ω,
      HasDerivAt (fun t => p ω * Real.exp (-(t * G v ω)))
      (-(p ω * G v ω)) 0 := by
    intro ω
    have h1 : HasDerivAt (fun t : ℝ => t * G v ω)
        (G v ω) 0 := hasDerivAt_mul_const _
    have h2 := h1.neg.exp
    have h3 := h2.const_mul (p ω)
    have h5 : -(p ω * G v ω)
        = p ω * (Real.exp (-(0 * G v ω)) * -(G v ω)) := by
      rw [zero_mul, neg_zero, Real.exp_zero]
      ring
    rw [h5]
    exact h3
  have hexp : HasDerivAt
      (fun t => ∑ ω, p ω * Real.exp (-(t * G v ω)))
      (∑ ω, -(p ω * G v ω)) 0 :=
    HasDerivAt.fun_sum fun ω _ => hterm ω
  rw [show -(∑ ω, p ω * G v ω)
    = ∑ ω, -(p ω * G v ω) from by
    rw [Finset.sum_neg_distrib]]
  have hee : (fun t : ℝ => cycleLaplace p τ G (t • v) 0)
      =ᶠ[nhds (0:ℝ)] (fun t => ∑ ω, p ω *
        Real.exp (-(t * G v ω))) :=
    Filter.Eventually.of_forall fun t => by
      beta_reduce
      rw [laplace_line]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [zero_mul, sub_zero]
  exact hexp.congr_of_eventuallyEq hee

omit [Nonempty Ω] in
private theorem laplace_zero_zero (hp1 : ∑ ω, p ω = 1) :
    cycleLaplace p τ G (0 : E) 0 = 1 := by
  unfold cycleLaplace
  rw [← hp1]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [map_zero G]
  norm_num

/-- Continuity of the pressure along a line through the
origin: the monotone-root trap. -/
private theorem pressure_line_tendsto_zero
    (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hτ : ∀ ω, 0 < τ ω) :
    Filter.Tendsto
      (fun t : ℝ => pressureFn p τ G hp hτ (t • v))
      (nhds 0) (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hL00 : cycleLaplace p τ G ((0:ℝ) • v) 0 = 1 := by
    rw [zero_smul]
    exact laplace_zero_zero p τ G hp1
  have hup : cycleLaplace p τ G ((0:ℝ) • v) ε < 1 := by
    rw [← hL00]
    exact laplace_strictAnti p τ G hp hτ _ hε
  have hdn : 1 < cycleLaplace p τ G ((0:ℝ) • v) (-ε) := by
    rw [← hL00]
    exact laplace_strictAnti p τ G hp hτ _
      (neg_lt_zero.mpr hε)
  have hcont : ∀ r : ℝ, Continuous
      (fun t : ℝ => cycleLaplace p τ G (t • v) r) := by
    intro r
    rw [show (fun t : ℝ => cycleLaplace p τ G (t • v) r)
      = fun t : ℝ => ∑ ω, p ω *
        Real.exp (-(t * G v ω) - r * τ ω) from
      funext fun t => laplace_line p τ G v t r]
    refine continuous_finsetSum _ fun ω _ =>
      continuous_const.mul ?_
    exact ((continuous_id.mul continuous_const).neg.sub
      continuous_const).rexp
  have hev1 : ∀ᶠ t : ℝ in nhds 0,
      cycleLaplace p τ G (t • v) ε < 1 :=
    ((hcont ε).continuousAt.tendsto).eventually_lt_const hup
  have hev2 : ∀ᶠ t : ℝ in nhds 0,
      1 < cycleLaplace p τ G (t • v) (-ε) :=
    ((hcont (-ε)).continuousAt.tendsto).eventually_const_lt
      hdn
  filter_upwards [hev1, hev2] with t h1 h2
  rw [Real.norm_eq_abs, abs_lt]
  have hroot : cycleLaplace p τ G (t • v)
      (pressureFn p τ G hp hτ (t • v)) = 1 :=
    pressureFn_spec p τ G hp hτ (t • v)
  constructor
  · by_contra hle
    push Not at hle
    have := (laplace_strictAnti p τ G hp hτ
      (t • v)).antitone hle
    rw [hroot] at this
    linarith
  · by_contra hle
    push Not at hle
    have := (laplace_strictAnti p τ G hp hτ
      (t • v)).antitone hle
    rw [hroot] at this
    linarith

/-- Mean-value extraction: the pressure as an explicit
quotient. -/
private theorem pressure_mvt_quotient (hp : ∀ ω, 0 < p ω)
    (hτ : ∀ ω, 0 < τ ω) (t : ℝ) :
    ∃ ξ : ℝ,
      |ξ| ≤ |pressureFn p τ G hp hτ (t • v)|
      ∧ pressureFn p τ G hp hτ (t • v)
        = (cycleLaplace p τ G (t • v) 0 - 1)
          / denFun p τ G v t ξ := by
  set ft := pressureFn p τ G hp hτ (t • v) with hft
  have hroot : cycleLaplace p τ G (t • v) ft = 1 :=
    pressureFn_spec p τ G hp hτ (t • v)
  rcases lt_trichotomy ft 0 with hlt | heq | hgt
  · obtain ⟨ξ, hmem, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun r => cycleLaplace p τ G (t • v) r)
      (fun r => -(denFun p τ G v t r)) hlt
      ((laplace_continuous p τ G (t • v)).continuousOn)
      (fun x _ => hasDerivAt_laplace_r p τ G v t x)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg hmem.2, abs_of_neg hlt]
      linarith [hmem.1]
    · have hD : denFun p τ G v t ξ ≠ 0 :=
        (denFun_pos p τ G v hp hτ t ξ).ne'
      rw [hroot] at hslope
      have hne : (0 : ℝ) - ft ≠ 0 := by
        intro h0
        rw [sub_eq_zero] at h0
        exact hlt.ne h0.symm
      rw [eq_div_iff hne] at hslope
      rw [eq_div_iff hD]
      linear_combination hslope
  · refine ⟨0, by rw [heq], ?_⟩
    have h1 : cycleLaplace p τ G (t • v) 0 = 1 := by
      rw [← heq]
      exact hroot
    rw [heq, h1, sub_self, zero_div]
  · obtain ⟨ξ, hmem, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun r => cycleLaplace p τ G (t • v) r)
      (fun r => -(denFun p τ G v t r)) hgt
      ((laplace_continuous p τ G (t • v)).continuousOn)
      (fun x _ => hasDerivAt_laplace_r p τ G v t x)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos hmem.1, abs_of_pos hgt]
      linarith [hmem.2]
    · have hD : denFun p τ G v t ξ ≠ 0 :=
        (denFun_pos p τ G v hp hτ t ξ).ne'
      rw [hroot] at hslope
      have hne : ft - 0 ≠ 0 := by
        intro h0
        rw [sub_zero] at h0
        exact hgt.ne' h0
      rw [eq_div_iff hne] at hslope
      rw [eq_div_iff hD]
      linear_combination -hslope

omit [Nonempty Ω] in
private theorem denFun_zero_zero :
    denFun p τ G v 0 0 = ∑ ω, p ω * τ ω := by
  unfold denFun
  refine Finset.sum_congr rfl fun ω _ => ?_
  norm_num

/-- **Boxed pressure slope** `π(v) = −γ(v)/τ̄`: the
pressure is differentiable along every direction at the
origin, with derivative `−𝔼[g_v]/𝔼[τ]`. -/
theorem pressure_hasDerivAt (hp : ∀ ω, 0 < p ω)
    (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω) :
    HasDerivAt
      (fun t : ℝ => pressureFn p τ G hp hτ (t • v))
      (-(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω)) 0 := by
  choose ξfun hξ₁ hξ₂ using
    fun t => pressure_mvt_quotient p τ G v hp hτ t
  rw [hasDerivAt_iff_tendsto_slope]
  have hf0 : pressureFn p τ G hp hτ ((0:ℝ) • v) = 0 := by
    rw [zero_smul]
    exact pressureFn_zero p τ G hp hp1 hτ
  have hnum : Filter.Tendsto
      (fun t => (cycleLaplace p τ G (t • v) 0 - 1) / t)
      (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds (-(∑ ω, p ω * G v ω))) := by
    have hD := hasDerivAt_laplace_t p τ G v
    rw [hasDerivAt_iff_tendsto_slope] at hD
    refine hD.congr fun t => ?_
    simp only [slope_def_field]
    rw [sub_zero,
      show cycleLaplace p τ G ((0:ℝ) • v) 0 = 1 from by
        rw [zero_smul]; exact laplace_zero_zero p τ G hp1]
  have hξ0 : Filter.Tendsto ξfun
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) := by
    have hfl : Filter.Tendsto
        (fun t : ℝ => pressureFn p τ G hp hτ (t • v))
        (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) :=
      (pressure_line_tendsto_zero p τ G v hp
        hp1 hτ).mono_left nhdsWithin_le_nhds
    have hbound : ∀ t : ℝ, ‖ξfun t‖
        ≤ |pressureFn p τ G hp hτ (t • v)| := fun t => by
      rw [Real.norm_eq_abs]
      exact hξ₁ t
    have habs : Filter.Tendsto
        (fun t : ℝ => |pressureFn p τ G hp hτ (t • v)|)
        (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) := by
      have h := hfl.abs
      rwa [abs_zero] at h
    exact squeeze_zero_norm hbound habs
  have hpair : Filter.Tendsto (fun t => (t, ξfun t))
      (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds ((0:ℝ), (0:ℝ))) := by
    refine Filter.Tendsto.prodMk_nhds ?_ hξ0
    exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Filter.Tendsto
      (fun t => denFun p τ G v t (ξfun t))
      (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds (∑ ω, p ω * τ ω)) := by
    have hc := ((denFun_continuous p τ G
      v).tendsto ((0:ℝ), (0:ℝ))).comp hpair
    rw [denFun_zero_zero] at hc
    exact hc
  have hτpos : (0:ℝ) < ∑ ω, p ω * τ ω :=
    Finset.sum_pos (fun ω _ =>
      mul_pos (hp ω) (hτ ω)) Finset.univ_nonempty
  have htarget := hnum.div hden hτpos.ne'
  refine htarget.congr fun t => ?_
  simp only [Pi.div_apply, slope_def_field]
  rw [sub_zero, hf0, sub_zero, hξ₂ t, div_right_comm]

end Slope

section Score

variable (p τ : Ω → ℝ) (G : E →ₗ[ℝ] (Ω → ℝ))

/-- The boxed pressure slope `π(v) = −γ(v)/τ̄`. -/
noncomputable def slopeVal (v : E) : ℝ :=
  -(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω)

/-- The normalized score writer
`S_X v = −G v − π(v)τ`. -/
noncomputable def scoreS (v : E) : Ω → ℝ :=
  fun ω => -(G v ω) - slopeVal p τ G v * τ ω

/-- **The score writer is the boxed derivative**
`S_X v = D log p_{X,q}|₀[v]`: the derivative at the
origin of the tilted log-likelihood
`log p_{X,q}(ω) = log(p(ω) e^{−g_q(ω) − 𝓟(q)τ(ω)})`
along the direction `v`. -/
theorem score_hasDerivAt (hp : ∀ ω, 0 < p ω)
    (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω)
    (v : E) (ω : Ω) :
    HasDerivAt (fun t : ℝ => Real.log (p ω *
        Real.exp (-(G (t • v) ω)
          - pressureFn p τ G hp hτ (t • v) * τ ω)))
      (scoreS p τ G v ω) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * G v ω)
      (G v ω) 0 := hasDerivAt_mul_const _
  have h2 : HasDerivAt
      (fun t : ℝ => pressureFn p τ G hp hτ (t • v) * τ ω)
      (slopeVal p τ G v * τ ω) 0 :=
    (pressure_hasDerivAt p τ G v hp hp1 hτ).mul_const (τ ω)
  have hexp : HasDerivAt
      (fun t : ℝ => Real.log (p ω)
        + (-(t * G v ω)
          - pressureFn p τ G hp hτ (t • v) * τ ω))
      (scoreS p τ G v ω) 0 := by
    have h3 := (h1.neg.sub h2).const_add (Real.log (p ω))
    exact h3
  have hee : (fun t : ℝ => Real.log (p ω *
      Real.exp (-(G (t • v) ω)
        - pressureFn p τ G hp hτ (t • v) * τ ω)))
      =ᶠ[nhds (0:ℝ)]
      (fun t : ℝ => Real.log (p ω)
        + (-(t * G v ω)
          - pressureFn p τ G hp hτ (t • v) * τ ω)) := by
    refine Filter.Eventually.of_forall fun t => ?_
    beta_reduce
    rw [Real.log_mul (hp ω).ne' (Real.exp_ne_zero _),
      Real.log_exp, map_smul, Pi.smul_apply, smul_eq_mul]
  exact hexp.congr_of_eventuallyEq hee

omit [Nonempty Ω] in
/-- **Boxed slope reconstruction**:
`S_X v = −G_X v − π_X(v)τ_X` and
`G_X = −S_X − T_X π_X` — the affine action anchor and the
complete uncentered cycle-action slope are reconstructed
from the pressure slope and the score writer. -/
theorem slope_reconstruction (v : E) :
    (∀ ω, scoreS p τ G v ω
      = -(G v ω) - slopeVal p τ G v * τ ω)
    ∧ (∀ ω, G v ω
      = -(scoreS p τ G v ω) - slopeVal p τ G v * τ ω) := by
  refine ⟨fun ω => rfl, fun ω => ?_⟩
  unfold scoreS
  ring

end Score

end RewardPressure

namespace RewardCovRank

open Finset Matrix

variable {Ω : Type} [Fintype Ω] [Nonempty Ω] {d : ℕ}

/-- The `p`-weighted mean of the vector reward table. -/
noncomputable def gbar (p : Ω → ℝ) (g : Ω → (Fin d → ℝ))
    (i : Fin d) : ℝ :=
  ∑ ω, p ω * g ω i

/-- The centered reward table. -/
noncomputable def wvec (p : Ω → ℝ) (g : Ω → (Fin d → ℝ))
    (ω : Ω) : Fin d → ℝ :=
  fun i => g ω i - gbar p g i

/-- The boxed covariance matrix `Cov_p(g)`. -/
noncomputable def covMatrix (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    ∑ ω, p ω * wvec p g ω i * wvec p g ω j

omit [Nonempty Ω] in
private theorem covMatrix_mulVec (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) (x : Fin d → ℝ) :
    (covMatrix p g) *ᵥ x
      = ∑ ω, (p ω * (wvec p g ω ⬝ᵥ x)) • wvec p g ω := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [show (fun j => covMatrix p g i j * x j)
    = fun j => ∑ ω, p ω * wvec p g ω i
        * wvec p g ω j * x j from funext fun j => by
    rw [covMatrix, Matrix.of_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Nonempty Ω] in
private theorem quad_form (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) (x : Fin d → ℝ) :
    x ⬝ᵥ ((covMatrix p g) *ᵥ x)
      = ∑ ω, p ω * (wvec p g ω ⬝ᵥ x) ^ 2 := by
  rw [covMatrix_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  rw [show x ⬝ᵥ wvec p g ω = wvec p g ω ⬝ᵥ x from
    dotProduct_comm _ _]
  ring

/-- The centered span. -/
noncomputable def centeredSpan (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (wvec p g))

omit [Nonempty Ω] in
private theorem mem_centeredSpan_dot_zero (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) {x : Fin d → ℝ}
    (hx : x ∈ centeredSpan p g)
    (hdot : ∀ ω, wvec p g ω ⬝ᵥ x = 0) : x = 0 := by
  have hall : ∀ y ∈ centeredSpan p g, y ⬝ᵥ x = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨ω, rfl⟩ := hz
        exact hdot ω
    | zero => exact zero_dotProduct x
    | add y z _ _ ihy ihz =>
        rw [add_dotProduct, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [smul_dotProduct, ih, smul_zero]
  have hxx : x ⬝ᵥ x = 0 := hall x hx
  funext i
  have hsq : ∑ j, x j * x j = 0 := hxx
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_self_nonneg (x j))).mp hsq i
    (Finset.mem_univ i)
  exact mul_self_eq_zero.mp this

omit [Nonempty Ω] in
private theorem covMatrix_range_le (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) :
    LinearMap.range (covMatrix p g).mulVecLin
      ≤ centeredSpan p g := by
  rintro y ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, covMatrix_mulVec]
  refine Submodule.sum_mem _ fun ω _ => ?_
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨ω, rfl⟩)

omit [Nonempty Ω] in
private theorem centeredSpan_le_range (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) (hp : ∀ ω, 0 < p ω) :
    centeredSpan p g
      ≤ LinearMap.range (covMatrix p g).mulVecLin := by
  have hmaps : ∀ x ∈ centeredSpan p g,
      (covMatrix p g).mulVecLin x ∈ centeredSpan p g :=
    fun x _ => covMatrix_range_le p g ⟨x, rfl⟩
  set ψ : centeredSpan p g →ₗ[ℝ] centeredSpan p g :=
    ((covMatrix p g).mulVecLin).restrict hmaps with hψ
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hCx : (covMatrix p g).mulVecLin x = 0 := by
      have hv := congrArg Subtype.val
        (LinearMap.mem_ker.mp hker)
      rwa [hψ, LinearMap.restrict_apply] at hv
    have hq : x ⬝ᵥ ((covMatrix p g) *ᵥ x) = 0 := by
      rw [show (covMatrix p g) *ᵥ x = 0 from hCx,
        dotProduct_zero]
    rw [quad_form] at hq
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω _ => mul_nonneg (hp ω).le (sq_nonneg _))).mp hq
    have hdot : ∀ ω, wvec p g ω ⬝ᵥ x = 0 := by
      intro ω
      have hzo := hz ω (Finset.mem_univ ω)
      have h2 : (wvec p g ω ⬝ᵥ x) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hzo with h | h
        · exact absurd h (hp ω).ne'
        · exact h
      exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)
        |>.mp h2
    exact Subtype.ext (mem_centeredSpan_dot_zero p g hx hdot)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨⟨x, hxmem⟩, hxeq⟩ := hsurj ⟨y, hy⟩
  refine ⟨x, ?_⟩
  have hv := congrArg Subtype.val hxeq
  rwa [hψ, LinearMap.restrict_apply] at hv

omit [Nonempty Ω] in
private theorem centeredSpan_eq_vectorSpan (p : Ω → ℝ)
    (g : Ω → (Fin d → ℝ)) (hp1 : ∑ ω, p ω = 1) :
    centeredSpan p g = vectorSpan ℝ (Set.range g) := by
  apply le_antisymm
  · rw [centeredSpan, Submodule.span_le]
    rintro y ⟨ω, rfl⟩
    have hw : wvec p g ω = ∑ ω', p ω' • (g ω - g ω') := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [show (fun ω' => p ω' * (g ω i - g ω' i))
        = fun ω' => p ω' * g ω i - p ω' * g ω' i from
        funext fun ω' => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1,
        one_mul]
      rfl
    rw [SetLike.mem_coe, hw]
    refine Submodule.sum_mem _ fun ω' _ => ?_
    refine Submodule.smul_mem _ _ ?_
    have hv := vsub_mem_vectorSpan ℝ
      (Set.mem_range_self (f := g) ω)
      (Set.mem_range_self (f := g) ω')
    rwa [vsub_eq_sub] at hv
  · rw [vectorSpan_def, Submodule.span_le]
    rintro y ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_range] at ha hb
    obtain ⟨ω, rfl⟩ := ha
    obtain ⟨ω', rfl⟩ := hb
    rw [SetLike.mem_coe]
    beta_reduce
    rw [show g ω -ᵥ g ω' = wvec p g ω - wvec p g ω' from by
      rw [vsub_eq_sub]
      funext i
      simp only [Pi.sub_apply, wvec]
      ring]
    exact sub_mem (Submodule.subset_span ⟨ω, rfl⟩)
      (Submodule.subset_span ⟨ω', rfl⟩)

omit [Nonempty Ω] in
/-- **Boxed covariance rank formula**
`rank Cov_p(g) = dim Aff{g(ω) : ω ∈ Ω}`: the number of
independent fluctuating action directions on the resolved
cycle record. -/
theorem cov_rank_eq (p : Ω → ℝ) (g : Ω → (Fin d → ℝ))
    (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) :
    (covMatrix p g).rank
      = Module.finrank ℝ (vectorSpan ℝ (Set.range g)) := by
  have hrange : LinearMap.range (covMatrix p g).mulVecLin
      = centeredSpan p g :=
    le_antisymm (covMatrix_range_le p g)
      (centeredSpan_le_range p g hp)
  rw [Matrix.rank, hrange,
    centeredSpan_eq_vectorSpan p g hp1]

end RewardCovRank

section MatrixJets

open Matrix

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

omit [Fintype Ω] [Fintype V] in
/-- Boxed slope reconstruction: `S = -G - Tπ` inverts to
`G = -S - Tπ` (matrix-jet form). -/
theorem slope_reconstruction (S G : Matrix Ω V ℂ)
    (T : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (hS : S = -G - T * piX) : G = -S - T * piX := by
  rw [hS]
  abel

omit [Fintype V] in
/-- Boxed pressure anchor: centering `S*w = 0` and duration
normalization `T*w = τ̄` give `τ̄ • π* = -(G*w)`, i.e.
`π(v) = -γ(v)/τ̄` with `γ = G*𝟙` (matrix-jet form). -/
theorem pressure_slope_anchor (S G : Matrix Ω V ℂ)
    (T w : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (τbar : ℂ) (hS : S = -G - T * piX)
    (hcenter : Sᴴ * w = 0)
    (hτ : Tᴴ * w = τbar • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    τbar • piXᴴ = -(Gᴴ * w) := by
  have hexp : Sᴴ * w = -(Gᴴ * w) - τbar • piXᴴ := by
    rw [hS]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.neg_mul,
      Matrix.mul_assoc, hτ, Matrix.mul_smul, Matrix.mul_one]
  rw [hcenter] at hexp
  have h0 : -(Gᴴ * w) - τbar • piXᴴ = 0 := hexp.symm
  have h1 : -(Gᴴ * w) = τbar • piXᴴ := sub_eq_zero.mp h0
  exact h1.symm

omit [Fintype V] in
/-- Boxed pressure-jet Gram: with `G = -S - Tπ` and
`T*T = m₂`, the complete mixed action Gram splits as
`G*G = S*S + δ*π + π*δ + m₂·π*π` with `δ = T*S`
(matrix-jet form). -/
theorem pressure_jet_gram (S G : Matrix Ω V ℂ)
    (T : Matrix Ω (Fin 1) ℂ) (piX : Matrix (Fin 1) V ℂ)
    (m2 : ℂ) (hG : G = -S - T * piX)
    (hm2 : Tᴴ * T = m2 • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    Gᴴ * G = Sᴴ * S + (Tᴴ * S)ᴴ * piX + piXᴴ * (Tᴴ * S)
      + m2 • (piXᴴ * piX) := by
  have hneg : -S - T * piX = -(S + T * piX) := by abel
  rw [hG, hneg, Matrix.conjTranspose_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.conjTranspose_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.conjTranspose_mul]
  have h1 : (Tᴴ * S)ᴴ * piX = Sᴴ * (T * piX) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h2 : piXᴴ * Tᴴ * (T * piX) = m2 • (piXᴴ * piX) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T piX, hm2,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have h3 : piXᴴ * Tᴴ * S = piXᴴ * (Tᴴ * S) := by
    rw [Matrix.mul_assoc]
  rw [h2, h3, ← h1]
  abel

omit [Fintype V] in
open scoped ComplexOrder in
/-- Boxed Hessian positivity: `D²𝒫(0) = τ̄⁻¹·S*S ⪰ 0`
(matrix-jet form). -/
theorem pressure_hessian_psd [Finite V]
    (S : Matrix Ω V ℂ) (τbar : ℝ) (hτ : 0 < τbar) :
    ((τbar⁻¹ : ℝ) • (Sᴴ * S)).PosSemidef :=
  (Matrix.posSemidef_conjTranspose_mul_self S).smul
    (inv_nonneg.mpr hτ.le)

end MatrixJets

end NCG
