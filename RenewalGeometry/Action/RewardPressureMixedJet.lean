/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.RewardPressureAnalytic
import RenewalGeometry.Action.RewardPressureJet

/-!
# Mixed pressure jets and the complete action Gram for the actual pressure
  (`cor:supp-pressure-jet`, `eq:supp-pressure-jet-a`, `eq:supp-pressure-jet-b`,
  emergent-spacetime manuscript)

For a finite faithful marked table (`p > 0`, `∑ p = 1`, `τ > 0`) and a linear reward synthesis
`G : E →ₗ (Ω → ℝ)` on a finite-dimensional `E`, the table-defined pressure `𝓟 = pressureFn`
is `C^ω` (`RewardPressureAnalytic.contDiff_pressure`), so its bilinear Hessian
`D²𝓟(0) = fderiv ℝ (fderiv ℝ 𝓟) 0` exists.  With `S_X` the score writer
(`RewardPressure.scoreS`, the Fréchet derivative of the tilted log-likelihood by
`RewardPressureAnalytic.fderiv_logTilt`), `π_X = D𝓟(0)`, the tilted mean duration
`τ̄_X(q) = 𝔼_{X,q} τ`, `δ_X = Dτ̄_X(0)` and `m₂ = 𝔼 τ²`:

* `RewardPressureMixedJet.hessian_line`: `D²𝓟(0)[v,v]` is the line second derivative
  `d²/dt² 𝓟(tv)|₀` (identified with `RewardPressureJet.pressure_second_deriv`);
* `RewardPressureMixedJet.pressure_hessian_eq` (`eq:supp-pressure-jet-a`, first identity):
  `D²𝓟(0)[u,v] = τ̄⁻¹ 𝔼[(S_X u)(S_X v)]` for **all** `u, v` (mixed blocks by symmetry of
  the analytic Hessian and polarization of the proved line jets);
* `RewardPressureMixedJet.duration_jet` (`eq:supp-pressure-jet-a`, second identity):
  `δ_X(v) = 𝔼[τ S_X v]`, i.e. `δ_X = T_X^* S_X` (via `RewardPressureJet.duration_slope`);
* `RewardPressureMixedJet.action_gram_reconstruction` (`eq:supp-pressure-jet-b`):
  `𝔼[g_u g_v] = τ̄ D²𝓟(0)[u,v] + δ_X(u) π_X(v) + π_X(u) δ_X(v) + m₂ π_X(u) π_X(v)`,
  for the actual pressure and duration objects (using `G = -S - Tπ` from
  `RewardPressure.slope_reconstruction` with `π = D𝓟(0)`), with no hypothesis on `G`.
-/

open Finset

namespace RenewalGeometry
namespace RewardPressureMixedJet

open RewardPressure RewardPressureAnalytic RewardPressureJet

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {p τ : Ω → ℝ} (G : E →ₗ[ℝ] (Ω → ℝ))

/-- The bilinear pressure Hessian `D²𝓟(0)`. -/
noncomputable def hessian (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (pressureFn p τ G hp hτ)) 0

/-- The tilted mean duration `τ̄_X(q) = 𝔼_{X,q} τ = ∑ p τ e^{-g_q - 𝓟(q) τ}`. -/
noncomputable def tiltedDuration (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (q : E) : ℝ :=
  ∑ ω, (p ω * τ ω) * Real.exp (-(G q ω) - pressureFn p τ G hp hτ q * τ ω)

/-- The duration cross-jet `δ_X = Dτ̄_X(0)`. -/
noncomputable def durationJet (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) : E →L[ℝ] ℝ :=
  fderiv ℝ (tiltedDuration G hp hτ) 0

theorem hasFDerivAt_fderiv_pressure (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (q : E) :
    HasFDerivAt (fderiv ℝ (pressureFn p τ G hp hτ))
      (fderiv ℝ (fderiv ℝ (pressureFn p τ G hp hτ)) q) q := by
  have h := (contDiff_pressure G hp hτ).fderiv_right (m := 1) (by exact_mod_cast le_top)
  exact (h.differentiable (by simp) q).hasFDerivAt

theorem hasDerivAt_pressure_line (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pressureFn p τ G hp hτ (s • v))
      (fderiv ℝ (pressureFn p τ G hp hτ) (t • v) v) t := by
  have hD : HasFDerivAt (pressureFn p τ G hp hτ)
      (fderiv ℝ (pressureFn p τ G hp hτ) (t • v)) (t • v) :=
    ((contDiffAt_pressure G hp hτ _).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  exact hD.comp_hasDerivAt t hl

/-- `D²𝓟(0)[v,v]` is the derivative at `0` of the line slope `t ↦ d/dt 𝓟(tv)`. -/
theorem hessian_line (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (v : E) :
    HasDerivAt (deriv (fLine p τ G v hp hτ)) (hessian G hp hτ v v) 0 := by
  have hderiv : deriv (fLine p τ G v hp hτ)
      = fun t => fderiv ℝ (pressureFn p τ G hp hτ) (t • v) v :=
    funext fun t => (hasDerivAt_pressure_line G hp hτ v t).deriv
  rw [hderiv]
  have hF : HasFDerivAt (fderiv ℝ (pressureFn p τ G hp hτ)) (hessian G hp hτ)
      ((0 : ℝ) • v) := by
    rw [zero_smul]; exact hasFDerivAt_fderiv_pressure G hp hτ 0
  have hl : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hc := hF.comp_hasDerivAt (0 : ℝ) hl
  exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hc

/-- Diagonal of `eq:supp-pressure-jet-a`: `D²𝓟(0)[v,v] = τ̄⁻¹ 𝔼[(S_X v)²]`. -/
theorem hessian_diag (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω) (v : E) :
    hessian G hp hτ v v = (∑ ω, p ω * τ ω)⁻¹ * ∑ ω, p ω * scoreS p τ G v ω ^ 2 :=
  (hessian_line G hp hτ v).unique (pressure_second_deriv p τ G v hp hp1 hτ)

/-- The analytic Hessian is symmetric. -/
theorem hessian_symm (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (u v : E) :
    hessian G hp hτ u v = hessian G hp hτ v u :=
  (contDiffAt_pressure G hp hτ 0).isSymmSndFDerivAt_of_omega u v

omit [Nonempty Ω] [FiniteDimensional ℝ E] in
theorem slopeVal_add (u v : E) :
    slopeVal p τ G (u + v) = slopeVal p τ G u + slopeVal p τ G v := by
  unfold slopeVal
  rw [map_add]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

omit [Nonempty Ω] [FiniteDimensional ℝ E] in
theorem scoreS_add (u v : E) (ω : Ω) :
    scoreS p τ G (u + v) ω = scoreS p τ G u ω + scoreS p τ G v ω := by
  unfold scoreS
  rw [slopeVal_add, map_add, Pi.add_apply]
  ring

/-- **`eq:supp-pressure-jet-a`, first identity, all mixed blocks**:
`D²𝓟(0)[u,v] = τ̄⁻¹ 𝔼[(S_X u)(S_X v)]`, i.e. `D²𝓟(0) = τ̄⁻¹ S_X^* S_X`. -/
theorem pressure_hessian_eq (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω)
    (u v : E) :
    hessian G hp hτ u v
      = (∑ ω, p ω * τ ω)⁻¹ * ∑ ω, p ω * (scoreS p τ G u ω * scoreS p τ G v ω) := by
  have hsum := hessian_diag G hp hp1 hτ (u + v)
  simp only [map_add, ContinuousLinearMap.add_apply] at hsum
  rw [hessian_diag G hp hp1 hτ u, hessian_diag G hp hp1 hτ v,
    hessian_symm G hp hτ v u] at hsum
  simp_rw [scoreS_add] at hsum
  have hexp : ∑ ω, p ω * (scoreS p τ G u ω + scoreS p τ G v ω) ^ 2
      = ∑ ω, p ω * scoreS p τ G u ω ^ 2 + ∑ ω, p ω * scoreS p τ G v ω ^ 2
        + 2 * ∑ ω, p ω * (scoreS p τ G u ω * scoreS p τ G v ω) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [hexp] at hsum
  linarith

/-- The pressure Hessian is positive semidefinite: `D²𝓟(0)[v,v] ≥ 0`. -/
theorem pressure_hessian_nonneg (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hτ : ∀ ω, 0 < τ ω) (v : E) : 0 ≤ hessian G hp hτ v v := by
  rw [hessian_diag G hp hp1 hτ]
  exact pressure_second_deriv_nonneg p τ G v hp hτ

theorem differentiableAt_tiltedDuration (hp : ∀ ω, 0 < p ω) (hτ : ∀ ω, 0 < τ ω) (q : E) :
    DifferentiableAt ℝ (tiltedDuration G hp hτ) q := by
  have hP : DifferentiableAt ℝ (pressureFn p τ G hp hτ) q :=
    (contDiffAt_pressure G hp hτ q).differentiableAt (by simp)
  unfold tiltedDuration
  refine DifferentiableAt.fun_sum fun ω _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.exp ?_
  have h1 : DifferentiableAt ℝ (fun q : E => G q ω) q :=
    (coordCLM G ω).differentiableAt
  exact h1.neg.sub (hP.mul_const _)

/-- **`eq:supp-pressure-jet-a`, second identity**: `δ_X(v) = Dτ̄_X(0)[v] = 𝔼[τ S_X v]`,
i.e. `δ_X = T_X^* S_X`. -/
theorem duration_jet (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1) (hτ : ∀ ω, 0 < τ ω) (v : E) :
    durationJet G hp hτ v = ∑ ω, (p ω * τ ω) * scoreS p τ G v ω := by
  have hD : HasFDerivAt (tiltedDuration G hp hτ) (durationJet G hp hτ) ((0 : ℝ) • v) := by
    rw [zero_smul]; exact (differentiableAt_tiltedDuration G hp hτ 0).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 := hD.comp_hasDerivAt (0 : ℝ) hl
  have heq : (tiltedDuration G hp hτ ∘ fun s : ℝ => s • v)
      = fun t => denFld p τ G v t (fLine p τ G v hp hτ t) := by
    funext t
    simp only [Function.comp_apply, tiltedDuration, denFld, fLine, map_smul, Pi.smul_apply,
      smul_eq_mul]
  rw [heq] at h1
  exact h1.unique (duration_slope p τ G v hp hp1 hτ)

/-- **`eq:supp-pressure-jet-b`** (`cor:supp-pressure-jet`), for the actual pressure and
duration objects: with `π_X = D𝓟(0)`, `δ_X = Dτ̄_X(0)`, `m₂ = 𝔼τ²`,
`𝔼[g_u g_v] = τ̄ D²𝓟(0)[u,v] + δ_X(u)π_X(v) + π_X(u)δ_X(v) + m₂ π_X(u)π_X(v)`. -/
theorem action_gram_reconstruction (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hτ : ∀ ω, 0 < τ ω) (u v : E) :
    ∑ ω, p ω * (G u ω * G v ω)
      = (∑ ω, p ω * τ ω) * hessian G hp hτ u v
        + durationJet G hp hτ u * fderiv ℝ (pressureFn p τ G hp hτ) 0 v
        + fderiv ℝ (pressureFn p τ G hp hτ) 0 u * durationJet G hp hτ v
        + (∑ ω, p ω * τ ω ^ 2) * fderiv ℝ (pressureFn p τ G hp hτ) 0 u
          * fderiv ℝ (pressureFn p τ G hp hτ) 0 v := by
  have hτb : (∑ ω, p ω * τ ω) ≠ 0 :=
    (Finset.sum_pos (fun ω _ => mul_pos (hp ω) (hτ ω)) Finset.univ_nonempty).ne'
  rw [pressure_hessian_eq G hp hp1 hτ, duration_jet G hp hp1 hτ, duration_jet G hp hp1 hτ,
    fderiv_pressure_zero G hp hp1 hτ, fderiv_pressure_zero G hp hp1 hτ,
    ← mul_assoc, mul_inv_cancel₀ hτb, one_mul]
  set x := slopeVal p τ G u
  set y := slopeVal p τ G v
  have hG : ∀ (w : E) (ω : Ω), G w ω = -(scoreS p τ G w ω) - slopeVal p τ G w * τ ω :=
    fun w ω => (RewardPressure.slope_reconstruction p τ G w).2 ω
  have hexp : ∀ ω, p ω * (G u ω * G v ω)
      = p ω * (scoreS p τ G u ω * scoreS p τ G v ω) + (p ω * τ ω * scoreS p τ G u ω) * y
        + x * (p ω * τ ω * scoreS p τ G v ω) + p ω * τ ω ^ 2 * x * y := by
    intro ω
    rw [hG u ω, hG v ω]
    ring
  rw [Finset.sum_congr rfl fun ω _ => hexp ω]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- The two-point reward synthesis `G q = (q, -q)` on `E = ℝ` (non-vacuity witness). -/
noncomputable def exampleSynthesis : ℝ →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i • LinearMap.id

/-- Non-vacuity: the two-point table `p = (1/2, 1/2)`, `τ = (1, 2)` (non-constant duration)
with the non-constant reward `G q = (q, -q)` satisfies every hypothesis of
`action_gram_reconstruction`. -/
example (u v : ℝ) :=
  action_gram_reconstruction (Ω := Fin 2) (p := fun _ => (1 / 2 : ℝ)) (τ := ![1, 2])
    exampleSynthesis (fun _ => by norm_num) (by simp) (fun i => by fin_cases i <;> norm_num)
    u v

end RewardPressureMixedJet
end RenewalGeometry
