/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.RewardPressure

/-!
# Analyticity of the renewal pressure and the Fréchet slope reconstruction
  (`thm:main-action-reconstruction`, `eq:main-renewal-pressure`,
  `eq:main-action-slope-reconstruction`, emergent-spacetime manuscript)

Let `(Ω, p)` be a finite faithful marked first-return law (`p > 0`, `∑ p = 1`), `τ > 0` the
protected duration and `G : E →ₗ (Ω → ℝ)` a linear reward synthesis on a finite-dimensional
variation space `E`.  `RewardPressure.pressureFn` is the table-defined pressure: the unique
root of `𝓛(q, 𝓟(q)) = 1` (`RewardPressure.pressure_exists_unique`).

* `RewardPressureAnalytic.contDiff_laplace`: `(q, r) ↦ 𝓛(q, r)` is `C^ω` on `E × ℝ`.
* `RewardPressureAnalytic.contDiffAt_pressure`, `contDiff_pressure`, `analyticAt_pressure`:
  by the analytic implicit-function theorem (`ContDiffAt.implicitFunction`, with
  `∂_r 𝓛(q, 𝓟(q)) = -∑ p τ e^{…} < 0`), the pressure is `C^ω` — real analytic — on all of
  `E`; hence the marked table reconstructs `𝓟` together with **all** of its finite jets
  `iteratedFDeriv ℝ k 𝓟 0` (`pressure_jets_exist`).
* `RewardPressureAnalytic.pressure_unique_near`: any function solving `𝓛(q, P'(q)) = 1`
  near the origin coincides with `𝓟` there.
* `RewardPressureAnalytic.fderiv_pressure_zero`: `π_X = D𝓟(0)`, `π_X(v) = -𝔼 g_v / τ̄`.
* `RewardPressureAnalytic.hasFDerivAt_logTilt`: the score `S_X v = D log p_{X,q}|_{q=0}[v]`
  is the genuine Fréchet derivative of the tilted log-likelihood, equal to `-g_v - π_X(v) τ`.
* `RewardPressureAnalytic.action_slope_reconstruction` (`eq:main-action-slope-reconstruction`):
  `G_X v = -(D log p_{X,·}(ω)|₀ v) - (D𝓟(0) v) τ(ω)`, i.e. `𝒢_X = -S_X - T_X π_X` with `S_X`
  and `π_X` the actual derivatives — not a definitional unfolding.
-/

open Finset

namespace RenewalGeometry
namespace RewardPressureAnalytic

open RewardPressure

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (p τ : Ω → ℝ) (G : E →ₗ[ℝ] (Ω → ℝ))

/-- The coordinate reward `q ↦ g_q(ω)` as a continuous linear functional (finite-dimensional
`E`). -/
noncomputable def coordCLM (ω : Ω) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj ω).comp G)

omit [Nonempty Ω] [Fintype Ω] in
theorem coordCLM_apply (ω : Ω) (q : E) : coordCLM G ω q = G q ω := rfl

/-- The cycle Laplace transform on the product space `E × ℝ`. -/
noncomputable def laplaceProd (u : E × ℝ) : ℝ := cycleLaplace p τ G u.1 u.2

omit [Nonempty Ω] in
/-- `𝓛` is `C^ω` (a finite sum of exponentials of continuous affine maps). -/
theorem contDiff_laplace {n : WithTop ℕ∞} : ContDiff ℝ n (laplaceProd p τ G) := by
  unfold laplaceProd cycleLaplace
  refine ContDiff.sum fun ω _ => contDiff_const.mul ?_
  refine Real.contDiff_exp.comp ?_
  have h1 : ContDiff ℝ n (fun u : E × ℝ => G u.1 ω) :=
    (coordCLM G ω).contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ n (fun u : E × ℝ => u.2 * τ ω) := contDiff_snd.mul contDiff_const
  exact h1.neg.sub h2

omit [Nonempty Ω] in
private theorem hasDerivAt_expSum (g : Ω → ℝ) (r : ℝ) :
    HasDerivAt (fun s => ∑ ω, p ω * Real.exp (-(g ω) - s * τ ω))
      (-∑ ω, p ω * τ ω * Real.exp (-(g ω) - r * τ ω)) r := by
  rw [show (-∑ ω, p ω * τ ω * Real.exp (-(g ω) - r * τ ω))
      = ∑ ω, -(p ω * τ ω * Real.exp (-(g ω) - r * τ ω)) from by
        rw [Finset.sum_neg_distrib]]
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have h : HasDerivAt (fun s : ℝ => -(g ω) - s * τ ω) (-τ ω) r := by
    simpa using ((hasDerivAt_id r).mul_const (τ ω)).const_sub (-(g ω))
  have h2 := (h.exp).const_mul (p ω)
  refine h2.congr_deriv ?_
  change p ω * (Real.exp (-(g ω) - r * τ ω) * -τ ω) = _
  ring

omit [Nonempty Ω] [FiniteDimensional ℝ E] in
/-- `∂_r 𝓛(q, r) = -∑ p τ e^{-g_q - rτ}`. -/
theorem hasDerivAt_laplace_r (q : E) (r : ℝ) :
    HasDerivAt (fun s => cycleLaplace p τ G q s)
      (-∑ ω, p ω * τ ω * Real.exp (-(G q ω) - r * τ ω)) r :=
  hasDerivAt_expSum p τ (fun ω => G q ω) r

variable {p τ}

/-- **The pressure is `C^ω` at every point** (analytic implicit-function theorem). -/
theorem contDiffAt_pressure (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (q₀ : E) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (pressureFn p τ G hp hτ) q₀ := by
  set u : E × ℝ := (q₀, pressureFn p τ G hp hτ q₀) with hu
  have cdf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (laplaceProd p τ G) u := (contDiff_laplace p τ G).contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  -- the `r`-partial derivative
  set d : ℝ := -∑ ω, p ω * τ ω * Real.exp (-(G q₀ ω) - pressureFn p τ G hp hτ q₀ * τ ω)
    with hd
  have hdne : d ≠ 0 := by
    have : 0 < ∑ ω, p ω * τ ω * Real.exp (-(G q₀ ω) - pressureFn p τ G hp hτ q₀ * τ ω) :=
      Finset.sum_pos (fun ω _ => mul_pos (mul_pos (hp ω) (hτ ω)) (Real.exp_pos _))
        Finset.univ_nonempty
    rw [hd]; linarith
  have hF : HasFDerivAt (laplaceProd p τ G) (fderiv ℝ (laplaceProd p τ G) u) u :=
    (cdf.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => laplaceProd p τ G (q₀, s))
      (fderiv ℝ (laplaceProd p τ G) u ((ContinuousLinearMap.inr ℝ E ℝ) 1))
      (pressureFn p τ G hp hτ q₀) := by
    have hi : HasDerivAt (fun s : ℝ => ((q₀, s) : E × ℝ))
        ((ContinuousLinearMap.inr ℝ E ℝ) 1) (pressureFn p τ G hp hτ q₀) := by
      have := ((ContinuousLinearMap.inr ℝ E ℝ).hasFDerivAt (x := pressureFn p τ G hp hτ q₀))
      have h2 := this.hasDerivAt
      have h3 : HasDerivAt (fun s : ℝ => ((q₀, 0) : E × ℝ) + (ContinuousLinearMap.inr ℝ E ℝ) s)
          ((ContinuousLinearMap.inr ℝ E ℝ) 1) (pressureFn p τ G hp hτ q₀) :=
        h2.const_add _
      convert h3 using 1
      funext s
      simp
    exact hF.comp_hasDerivAt _ hi
  have hval : fderiv ℝ (laplaceProd p τ G) u ((ContinuousLinearMap.inr ℝ E ℝ) 1) = d :=
    hline.unique (hasDerivAt_laplace_r p τ G q₀ _)
  have if₂ : (fderiv ℝ (laplaceProd p τ G) u ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hdne), ?_⟩
    refine ContinuousLinearMap.ext_ring ?_
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply,
      Units.val_mk0, one_mul, ContinuousLinearMap.comp_apply]
    exact hval.symm
  have hψ := cdf.contDiffAt_implicitFunction pn if₂
  have hev := cdf.eventually_apply_implicitFunction pn if₂
  have hroot : laplaceProd p τ G u = 1 := pressureFn_spec p τ G hp hτ q₀
  refine hψ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with x hx
  rw [hroot] at hx
  exact pressureFn_eq_of_root p τ G hp hτ hx

/-- **The pressure is `C^ω` on all of `E`.** -/
theorem contDiff_pressure (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (pressureFn p τ G hp hτ) :=
  contDiff_iff_contDiffAt.2 fun q => contDiffAt_pressure G hp hτ q

/-- **The pressure is real analytic** at every point (`eq:main-renewal-pressure`). -/
theorem analyticAt_pressure (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (q : E) :
    AnalyticAt ℝ (pressureFn p τ G hp hτ) q :=
  (contDiffAt_pressure G hp hτ q).analyticAt

/-- **All finite jets.**  For every order `k` the pressure is `C^k` and its `k`-th Fréchet
jet at the origin exists; the jets are functions of the marked table `(p, τ, G)` only. -/
theorem pressure_jets_exist (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (k : ℕ) :
    ContDiff ℝ k (pressureFn p τ G hp hτ) ∧
    HasFTaylorSeriesUpTo k (pressureFn p τ G hp hτ)
      (ftaylorSeries ℝ (pressureFn p τ G hp hτ)) :=
  ⟨(contDiff_pressure G hp hτ).of_le (by exact_mod_cast le_top),
    ((contDiff_pressure G hp hτ).of_le
      (by exact_mod_cast le_top)).ftaylorSeries⟩

omit [FiniteDimensional ℝ E] in
/-- **Uniqueness of the pressure near the origin**: any `P'` solving `𝓛(q, P'(q)) = 1` on a
neighbourhood of `0` coincides with `𝓟` there. -/
theorem pressure_unique_near (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (P' : E → ℝ)
    (hP' : ∀ᶠ q in nhds (0 : E), cycleLaplace p τ G q (P' q) = 1) :
    P' =ᶠ[nhds (0 : E)] pressureFn p τ G hp hτ := by
  filter_upwards [hP'] with q hq
  exact (pressureFn_eq_of_root p τ G hp hτ hq).symm

/-- **Boxed slope** `π_X = D𝓟(0)`, `π_X(v) = -𝔼 g_v / τ̄`. -/
theorem fderiv_pressure_zero (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω)
    (v : E) :
    fderiv ℝ (pressureFn p τ G hp hτ) 0 v = slopeVal p τ G v := by
  have hD : DifferentiableAt ℝ (pressureFn p τ G hp hτ) 0 :=
    (contDiffAt_pressure G hp hτ 0).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 : HasDerivAt (fun t : ℝ => pressureFn p τ G hp hτ (t • v))
      (fderiv ℝ (pressureFn p τ G hp hτ) 0 v) 0 := by
    have hD' : HasFDerivAt (pressureFn p τ G hp hτ) (fderiv ℝ (pressureFn p τ G hp hτ) 0)
        ((0 : ℝ) • v) := by
      rw [zero_smul]; exact hD.hasFDerivAt
    exact hD'.comp_hasDerivAt (0 : ℝ) hl
  exact h1.unique (pressure_hasDerivAt p τ G v hp hp1 hτ)

/-- `π_X` as a continuous linear functional is `D𝓟(0)`. -/
theorem fderiv_pressure_zero_eq (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hτ : ∀ ω, 0 < τ ω) :
    fderiv ℝ (pressureFn p τ G hp hτ) 0
      = -(∑ ω, p ω * τ ω)⁻¹ • ∑ ω, p ω • coordCLM G ω := by
  ext v
  rw [fderiv_pressure_zero G hp hp1 hτ v]
  simp only [slopeVal, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, coordCLM_apply,
    smul_eq_mul]
  ring

/-- The tilted log-likelihood `q ↦ log p_{X,q}(ω) = log(p(ω) e^{-g_q(ω) - 𝓟(q) τ(ω)})`. -/
noncomputable def logTilt (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (ω : Ω) (q : E) : ℝ :=
  Real.log (p ω * Real.exp (-(G q ω) - pressureFn p τ G hp hτ q * τ ω))

/-- **The score is the Fréchet derivative of the tilted log-likelihood**:
`D log p_{X,q}(ω)|_{q=0} = -g_·(ω) - D𝓟(0)(·) τ(ω)`. -/
theorem hasFDerivAt_logTilt (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (ω : Ω) :
    HasFDerivAt (logTilt G hp hτ ω)
      (-(coordCLM G ω) - τ ω • fderiv ℝ (pressureFn p τ G hp hτ) 0) 0 := by
  have hD : HasFDerivAt (pressureFn p τ G hp hτ) (fderiv ℝ (pressureFn p τ G hp hτ) 0) 0 :=
    ((contDiffAt_pressure G hp hτ 0).differentiableAt (by simp)).hasFDerivAt
  have h1 := (coordCLM G ω).hasFDerivAt (x := (0 : E))
  have h2 := hD.mul_const (τ ω)
  have h3 := (h1.neg.sub h2).const_add (Real.log (p ω))
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply, coordCLM_apply]
  unfold logTilt
  rw [Real.log_mul (hp ω).ne' (Real.exp_ne_zero _), Real.log_exp]

/-- `S_X v (ω) = D log p_{X,q}(ω)|_{q=0}[v]` equals the score writer `-g_v - π(v) τ`. -/
theorem fderiv_logTilt (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω)
    (ω : Ω) (v : E) :
    fderiv ℝ (logTilt G hp hτ ω) 0 v = scoreS p τ G v ω := by
  rw [(hasFDerivAt_logTilt G hp hτ ω).fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, coordCLM_apply, smul_eq_mul,
    fderiv_pressure_zero G hp hp1 hτ v, scoreS]
  ring

/-- **`eq:main-action-slope-reconstruction`** (`thm:main-action-reconstruction`), with the
score and the pressure slope as the actual Fréchet derivatives of table-defined objects:
`π_X(v) = D𝓟(0)v = -𝔼 g_v / τ̄` and
`g_v(ω) = -(D log p_{X,·}(ω)|₀ v) - (D𝓟(0) v) τ(ω)`, i.e. `𝒢_X = -S_X - T_X π_X`; the
anchor is fixed by the centering `𝔼[S_X v] = 0`. -/
theorem action_slope_reconstruction (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hτ : ∀ ω, 0 < τ ω) :
    (∀ v : E, fderiv ℝ (pressureFn p τ G hp hτ) 0 v
        = -(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω)) ∧
    (∀ (v : E) (ω : Ω), G v ω = -(fderiv ℝ (logTilt G hp hτ ω) 0 v)
        - fderiv ℝ (pressureFn p τ G hp hτ) 0 v * τ ω) ∧
    (∀ v : E, ∑ ω, p ω * fderiv ℝ (logTilt G hp hτ ω) 0 v = 0) := by
  have hτb : (∑ ω, p ω * τ ω) ≠ 0 :=
    (Finset.sum_pos (fun ω _ => mul_pos (hp ω) (hτ ω)) Finset.univ_nonempty).ne'
  refine ⟨fun v => fderiv_pressure_zero G hp hp1 hτ v, fun v ω => ?_, fun v => ?_⟩
  · rw [fderiv_logTilt G hp hp1 hτ, fderiv_pressure_zero G hp hp1 hτ]
    unfold scoreS
    ring
  · simp_rw [fderiv_logTilt G hp hp1 hτ, scoreS, slopeVal]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
    have : ∑ ω, p ω * (-(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω) * τ ω)
        = -(∑ ω, p ω * G v ω) := by
      rw [show (fun ω => p ω * (-(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω) * τ ω))
          = fun ω => (-(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω)) * (p ω * τ ω) by
            funext ω; ring, ← Finset.mul_sum]
      field_simp
    rw [this]
    ring

/-- Non-vacuity: a two-point table `p = (1/2, 1/2)`, `τ = (1, 2)` with the reward synthesis
`G q = (q, -q)` on `E = ℝ` satisfies every hypothesis, and the reconstruction applies. -/
example : ∀ v : ℝ,
    fderiv ℝ (pressureFn (Ω := Fin 2) (fun _ => (1 / 2 : ℝ)) ![1, 2]
      ((LinearMap.pi fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i • LinearMap.id))
      (fun _ => by norm_num) (fun i => by fin_cases i <;> norm_num)) 0 v = 0 := by
  intro v
  rw [fderiv_pressure_zero _ _ (by simp)]
  simp [slopeVal, Fin.sum_univ_two]

end RewardPressureAnalytic
end RenewalGeometry
