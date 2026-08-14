/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RewardPressure

/-!
# Pressure-jet reconstruction of the mixed action Gram
  (`thm:reward-pressure-jet`, Gran-Tensor manuscript)

Second-order jet of the table-derived reward pressure.
The key mechanism making everything first-order: the
pressure along a line at a shifted base point `t₀` equals
the pressure of the **tilted packet**
`p_ω e^{−t₀ g_v(ω) − 𝓟(t₀v) τ(ω)}` — which is again a
normalized faithful packet because `𝓛(t₀v, 𝓟(t₀v)) = 1`.
So the slope theorem of `RewardPressure` applies at every
base point, the derivative field is the explicit quotient
`φ(t, 𝓟(tv)) = −N/D` of exponential sums, and the second
derivative at the origin is a chain-rule computation on
explicit functions.

* `pressure_hasDerivAt_at`: `𝓟` is differentiable along
  `v` at every `t₀`, with the tilted-mean slope.
* `pressure_hasDerivAt_deriv` (boxed):
  `D²𝓟(0)[v,v] = τ̄⁻¹ 𝔼[(S_X v)²]` — the derivative of
  the pressure-slope field at the origin is exactly
  `τ̄⁻¹ S*S` on the diagonal, and it is nonnegative.
* `duration_slope` (boxed): `δ_X = D τ̄_X(0) = T_X^* S_X`
  — the tilt-derivative of the mean duration is the
  duration/score pairing.
* Together with the retained matrix-jet identities
  (`pressure_jet_gram`, `pressure_hessian_psd` in
  `RewardPressure`), one pressure surface reconstructs
  the boxed complete mixed action Gram
  `G*G = τ̄ D²𝓟 + δ*π + π*δ + m₂ π*π`.
-/

open Finset

namespace NCG
namespace RewardPressureJet

open RewardPressure

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {E : Type} [AddCommGroup E] [Module ℝ E]
variable (p τ : Ω → ℝ) (G : E →ₗ[ℝ] (Ω → ℝ)) (v : E)

/-- The tilted packet at base `(t₀, r₀)`. -/
noncomputable def tiltP (t₀ r₀ : ℝ) : Ω → ℝ :=
  fun ω => p ω * Real.exp (-(t₀ * G v ω) - r₀ * τ ω)

variable (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
variable (hτ : ∀ ω, 0 < τ ω)

omit [Nonempty Ω] [Fintype Ω] in
include hp in
private theorem tiltP_pos (t₀ r₀ : ℝ) (ω : Ω) :
    0 < tiltP p τ G v t₀ r₀ ω :=
  mul_pos (hp ω) (Real.exp_pos _)

/-- Along the line, write `f t := 𝓟(t v)`. -/
noncomputable def fLine (t : ℝ) : ℝ :=
  pressureFn p τ G hp hτ (t • v)

private theorem tiltP_sum_one (t₀ : ℝ) :
    ∑ ω, tiltP p τ G v t₀ (fLine p τ G v hp hτ t₀) ω
      = 1 := by
  have hs := pressureFn_spec p τ G hp hτ (t₀ • v)
  rw [laplace_line] at hs
  exact hs

omit [Nonempty Ω] in
private theorem tilt_laplace (t₀ r₀ s r : ℝ) :
    cycleLaplace (tiltP p τ G v t₀ r₀) τ G (s • v) r
      = cycleLaplace p τ G ((t₀ + s) • v) (r₀ + r) := by
  rw [laplace_line, laplace_line]
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold tiltP
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The shifted pressure is the tilted-packet pressure. -/
private theorem tilt_pressure_shift (t₀ : ℝ)
    (hp'' : ∀ ω, 0 < tiltP p τ G v t₀
      (fLine p τ G v hp hτ t₀) ω) (s : ℝ) :
    pressureFn (tiltP p τ G v t₀
        (fLine p τ G v hp hτ t₀)) τ G hp'' hτ (s • v)
      = fLine p τ G v hp hτ (t₀ + s)
        - fLine p τ G v hp hτ t₀ := by
  refine pressureFn_eq_of_root _ τ G _ hτ ?_
  rw [tilt_laplace]
  rw [show fLine p τ G v hp hτ t₀
      + (fLine p τ G v hp hτ (t₀ + s)
        - fLine p τ G v hp hτ t₀)
    = fLine p τ G v hp hτ (t₀ + s) from by ring]
  exact pressureFn_spec p τ G hp hτ ((t₀ + s) • v)

/-- The explicit slope numerator field
`N(t,r) = ∑ ω, p ω g_v(ω) e^{−t g_v(ω) − r τ(ω)}`. -/
noncomputable def numFld (t r : ℝ) : ℝ :=
  ∑ ω, (p ω * G v ω) * Real.exp (-(t * G v ω) - r * τ ω)

/-- The explicit slope denominator field (the tilted mean
duration) `D(t,r) = ∑ ω, p ω τ(ω) e^{−t g_v(ω) − r τ(ω)}`. -/
noncomputable def denFld (t r : ℝ) : ℝ :=
  ∑ ω, (p ω * τ ω) * Real.exp (-(t * G v ω) - r * τ ω)

omit [Nonempty Ω] in
private theorem tilt_num (t₀ r₀ : ℝ) :
    ∑ ω, tiltP p τ G v t₀ r₀ ω * G v ω
      = numFld p τ G v t₀ r₀ := by
  unfold numFld
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold tiltP
  ring

omit [Nonempty Ω] in
private theorem tilt_den (t₀ r₀ : ℝ) :
    ∑ ω, tiltP p τ G v t₀ r₀ ω * τ ω
      = denFld p τ G v t₀ r₀ := by
  unfold denFld
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold tiltP
  ring

/-- **The pressure is differentiable along `v` at every
base point**, with the tilted-mean slope
`−N(t₀, 𝓟(t₀v))/D(t₀, 𝓟(t₀v))`. -/
theorem pressure_hasDerivAt_at (t₀ : ℝ) :
    HasDerivAt (fLine p τ G v hp hτ)
      (-(numFld p τ G v t₀ (fLine p τ G v hp hτ t₀))
        / denFld p τ G v t₀ (fLine p τ G v hp hτ t₀)) t₀ := by
  have hp' : ∀ ω, 0 < tiltP p τ G v t₀
      (fLine p τ G v hp hτ t₀) ω :=
    tiltP_pos p τ G v hp t₀ _
  have hp1' := tiltP_sum_one p τ G v hp hτ t₀
  have hbase := pressure_hasDerivAt
    (tiltP p τ G v t₀ (fLine p τ G v hp hτ t₀)) τ G v
    hp' hp1' hτ
  rw [tilt_num, tilt_den] at hbase
  have hinner : HasDerivAt (fun t : ℝ => t - t₀) 1 t₀ :=
    (hasDerivAt_id t₀).sub_const t₀
  have hzero : t₀ - t₀ = 0 := sub_self t₀
  have hcomp := HasDerivAt.comp (𝕜 := ℝ) t₀
    (by rw [hzero] at *; exact hbase) hinner
  rw [mul_one] at hcomp
  have hfinal := hcomp.add_const
    (fLine p τ G v hp hτ t₀)
  refine hfinal.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => ?_)
  have hshift := tilt_pressure_shift p τ G v hp hτ t₀
    hp' (t - t₀)
  rw [show t₀ + (t - t₀) = t from by ring] at hshift
  show fLine p τ G v hp hτ t = _
  beta_reduce
  rw [Function.comp_apply, hshift]
  ring

include hp1 in
private theorem fLine_zero :
    fLine p τ G v hp hτ 0 = 0 := by
  unfold fLine
  rw [zero_smul]
  exact pressureFn_zero p τ G hp hp1 hτ

include hp1 in
/-- Term-wise derivative of an exponential composite along
the pressure line. -/
private theorem hasDerivAt_expTerm (c a b : ℝ) :
    HasDerivAt (fun t : ℝ => c *
        Real.exp (-(t * a) - fLine p τ G v hp hτ t * b))
      (c * (-(a) - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * b)) 0 := by
  have hf := pressure_hasDerivAt p τ G v hp hp1 hτ
  have hf' : HasDerivAt (fLine p τ G v hp hτ)
      (-(∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω)) 0 := hf
  have h1 : HasDerivAt (fun t : ℝ => t * a) a 0 :=
    hasDerivAt_mul_const a
  have h2 := hf'.mul_const b
  have h3 := (h1.neg.sub h2).exp
  have h4 := h3.const_mul c
  have hval : c * (Real.exp (-(0 * a)
      - fLine p τ G v hp hτ 0 * b)
        * (-(a) - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * b))
      = c * (-(a) - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * b) := by
    rw [fLine_zero p τ G v hp hp1 hτ]
    norm_num
  rw [← hval]
  exact h4

include hp1 in
private theorem hasDerivAt_numComp :
    HasDerivAt (fun t : ℝ =>
        numFld p τ G v t (fLine p τ G v hp hτ t))
      (∑ ω, (p ω * G v ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)) 0 := by
  have hexp : HasDerivAt (fun t : ℝ => ∑ ω,
      (p ω * G v ω) * Real.exp (-(t * G v ω)
        - fLine p τ G v hp hτ t * τ ω))
      (∑ ω, (p ω * G v ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)) 0 :=
    HasDerivAt.fun_sum fun ω _ =>
      hasDerivAt_expTerm p τ G v hp hp1 hτ _ _ _
  exact hexp

include hp1 in
private theorem hasDerivAt_denComp :
    HasDerivAt (fun t : ℝ =>
        denFld p τ G v t (fLine p τ G v hp hτ t))
      (∑ ω, (p ω * τ ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)) 0 := by
  have hexp : HasDerivAt (fun t : ℝ => ∑ ω,
      (p ω * τ ω) * Real.exp (-(t * G v ω)
        - fLine p τ G v hp hτ t * τ ω))
      (∑ ω, (p ω * τ ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)) 0 :=
    HasDerivAt.fun_sum fun ω _ =>
      hasDerivAt_expTerm p τ G v hp hp1 hτ _ _ _
  exact hexp

include hp1 in
/-- **Boxed duration slope** `δ_X = D τ̄_X(0) = T_X^* S_X`:
the tilt-derivative of the mean duration is the
duration/score pairing. -/
theorem duration_slope :
    HasDerivAt (fun t : ℝ =>
        denFld p τ G v t (fLine p τ G v hp hτ t))
      (∑ ω, (p ω * τ ω) * scoreS p τ G v ω) 0 := by
  have h := hasDerivAt_denComp p τ G v hp hp1 hτ
  rw [show (∑ ω, (p ω * τ ω) * scoreS p τ G v ω)
    = ∑ ω, (p ω * τ ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω) from
    Finset.sum_congr rfl fun ω _ => rfl]
  exact h

include hp1 in
private theorem denComp_zero :
    denFld p τ G v 0 (fLine p τ G v hp hτ 0)
      = ∑ ω, p ω * τ ω := by
  rw [fLine_zero p τ G v hp hp1 hτ]
  unfold denFld
  refine Finset.sum_congr rfl fun ω _ => ?_
  norm_num

include hp1 in
private theorem numComp_zero :
    numFld p τ G v 0 (fLine p τ G v hp hτ 0)
      = ∑ ω, p ω * G v ω := by
  rw [fLine_zero p τ G v hp hp1 hτ]
  unfold numFld
  refine Finset.sum_congr rfl fun ω _ => ?_
  norm_num

include hp hτ in
private theorem taubar_pos : 0 < ∑ ω, p ω * τ ω :=
  Finset.sum_pos (fun ω _ => mul_pos (hp ω) (hτ ω))
    Finset.univ_nonempty

include hp1 in
/-- **Boxed pressure Hessian**
`D²𝓟(0)[v,v] = τ̄⁻¹ 𝔼[(S_X v)²] ≥ 0`: the derivative of
the pressure-slope field at the origin is the normalized
score Gram diagonal. -/
theorem pressure_second_deriv :
    HasDerivAt (deriv (fLine p τ G v hp hτ))
      ((∑ ω, p ω * τ ω)⁻¹
        * ∑ ω, p ω * scoreS p τ G v ω ^ 2) 0 := by
  have hτb := taubar_pos p τ hp hτ
  have hderiv_eq : deriv (fLine p τ G v hp hτ)
      = fun t => -(numFld p τ G v t
          (fLine p τ G v hp hτ t))
        / denFld p τ G v t (fLine p τ G v hp hτ t) :=
    funext fun t =>
      (pressure_hasDerivAt_at p τ G v hp hτ t).deriv
  rw [hderiv_eq]
  have hN := hasDerivAt_numComp p τ G v hp hp1 hτ
  have hD := hasDerivAt_denComp p τ G v hp hp1 hτ
  have hDne : denFld p τ G v 0 (fLine p τ G v hp hτ 0)
      ≠ 0 := by
    rw [denComp_zero p τ G v hp hp1 hτ]
    exact hτb.ne'
  have hquot := (hN.neg).div hD hDne
  have hval :
      (-(∑ ω, (p ω * G v ω) * (-(G v ω)
          - (-(∑ ω, p ω * G v ω)
            / (∑ ω, p ω * τ ω)) * τ ω))
        * denFld p τ G v 0 (fLine p τ G v hp hτ 0)
        - -(numFld p τ G v 0 (fLine p τ G v hp hτ 0))
          * (∑ ω, (p ω * τ ω) * (-(G v ω)
            - (-(∑ ω, p ω * G v ω)
              / (∑ ω, p ω * τ ω)) * τ ω)))
        / denFld p τ G v 0 (fLine p τ G v hp hτ 0) ^ 2
      = (∑ ω, p ω * τ ω)⁻¹
        * ∑ ω, p ω * scoreS p τ G v ω ^ 2 := by
    rw [denComp_zero p τ G v hp hp1 hτ,
      numComp_zero p τ G v hp hp1 hτ]
    have hE1 : ∑ ω, (p ω * G v ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)
        = -(∑ ω, p ω * G v ω * G v ω)
          + (∑ ω, p ω * G v ω)
            / (∑ ω, p ω * τ ω)
            * ∑ ω, p ω * G v ω * τ ω := by
      rw [show (fun ω => (p ω * G v ω) * (-(G v ω)
          - (-(∑ ω, p ω * G v ω)
            / (∑ ω, p ω * τ ω)) * τ ω))
        = fun ω => -(p ω * G v ω * G v ω)
          + ((∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω))
            * (p ω * G v ω * τ ω) from
        funext fun ω => by ring]
      rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
        ← Finset.mul_sum]
    have hE2 : ∑ ω, (p ω * τ ω) * (-(G v ω)
        - (-(∑ ω, p ω * G v ω)
          / (∑ ω, p ω * τ ω)) * τ ω)
        = -(∑ ω, p ω * τ ω * G v ω)
          + (∑ ω, p ω * G v ω)
            / (∑ ω, p ω * τ ω)
            * ∑ ω, p ω * τ ω * τ ω := by
      rw [show (fun ω => (p ω * τ ω) * (-(G v ω)
          - (-(∑ ω, p ω * G v ω)
            / (∑ ω, p ω * τ ω)) * τ ω))
        = fun ω => -(p ω * τ ω * G v ω)
          + ((∑ ω, p ω * G v ω) / (∑ ω, p ω * τ ω))
            * (p ω * τ ω * τ ω) from
        funext fun ω => by ring]
      rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
        ← Finset.mul_sum]
    have hE3 : ∑ ω, p ω * scoreS p τ G v ω ^ 2
        = ∑ ω, p ω * G v ω * G v ω
          + 2 * ((-(∑ ω, p ω * G v ω))
            / (∑ ω, p ω * τ ω))
            * ∑ ω, p ω * G v ω * τ ω
          + ((-(∑ ω, p ω * G v ω))
            / (∑ ω, p ω * τ ω)) ^ 2
            * ∑ ω, p ω * τ ω * τ ω := by
      rw [show (fun ω => p ω * scoreS p τ G v ω ^ 2)
        = fun ω => p ω * G v ω * G v ω
          + 2 * ((-(∑ ω, p ω * G v ω))
            / (∑ ω, p ω * τ ω)) * (p ω * G v ω * τ ω)
          + ((-(∑ ω, p ω * G v ω))
            / (∑ ω, p ω * τ ω)) ^ 2
            * (p ω * τ ω * τ ω) from
        funext fun ω => by
          unfold scoreS slopeVal
          ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hE1, hE2, hE3,
      show ∑ ω, p ω * τ ω * G v ω
        = ∑ ω, p ω * G v ω * τ ω from
      Finset.sum_congr rfl fun ω _ => by ring]
    field_simp
    ring
  rw [← hval]
  exact hquot

include hp hτ in
/-- The Hessian diagonal is nonnegative:
`τ̄⁻¹ 𝔼[(S_X v)²] ≥ 0`. -/
theorem pressure_second_deriv_nonneg :
    0 ≤ (∑ ω, p ω * τ ω)⁻¹
      * ∑ ω, p ω * scoreS p τ G v ω ^ 2 := by
  refine mul_nonneg (inv_nonneg.mpr
    (taubar_pos p τ hp hτ).le) ?_
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hp ω).le (sq_nonneg _)

end RewardPressureJet
end NCG
