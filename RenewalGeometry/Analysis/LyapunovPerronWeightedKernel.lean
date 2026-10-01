/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weighted kernel bounds for the Lyapunov–Perron operator

First layer of the Lyapunov–Perron construction of forward-invariant graphs
(`lem:supp-exact-graph-criterion`, emergent-spacetime manuscript).  For the integral operator
`(𝒯 y)(t) = ( -∫_{t}^{∞} P_u(t-r)[b_u + N_u(y(r))] dr ,
             P_n(t) n₀ + ∫_0^t P_n(t-r)[b_n + N_n(y(r))] dr )`
with propagator bounds `‖P_n(s)‖ ≤ M e^{αs}`, `‖P_u(-s)‖ ≤ M e^{-βs}` (`s ≥ 0`), `α < ν < β`,
`0 < ν`, and `L`-Lipschitz nonlinearities, we prove:

* `forward_kernel_le`: `∫_0^t M e^{α(t-r)} K e^{νr} dr ≤ M K e^{νt}/(ν - α)`;
* `backward_kernel_eq`: `∫_{t}^{∞} M e^{-β(r-t)} K e^{νr} dr = M K e^{νt}/(β - ν)`;
* `lpMap_sub_le`: **the weighted Lipschitz estimate** — if `‖y₁(r) - y₂(r)‖ ≤ δ e^{νr}` on
  `[0, ∞)` then `‖(𝒯y₁)(t) - (𝒯y₂)(t)‖ ≤ M L ((ν-α)⁻¹ + (β-ν)⁻¹) δ e^{νt}`, i.e. `𝒯` is a
  contraction in the weighted norm `sup_{t≥0} e^{-νt}|y(t)|` exactly under the `j = 1` case of
  `eq:supp-exact-graph-contraction`;
* `backward_integrable`: the improper backward integrand is integrable on `(t, ∞)` for continuous
  trajectories of weighted growth `‖y(r)‖ ≤ K e^{νr}`.

The same estimates at the weights `jν` are the kernel bounds of the higher-derivative
(fibre-contraction) equations.
-/

open Filter Set MeasureTheory intervalIntegral Real
open scoped Topology

namespace RenewalGeometry
namespace LyapunovPerron

/-! ### Scalar kernel integrals -/

/-- The forward kernel: `∫_0^t M e^{α(t-r)} K e^{νr} dr ≤ M K e^{νt}/(ν - α)` for `t ≥ 0`. -/
theorem forward_kernel_le {M K α ν t : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hαν : α < ν)
    (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, M * exp (α * (t - r)) * (K * exp (ν * r))
      ≤ M * K * exp (ν * t) / (ν - α) := by
  have hc : 0 < ν - α := sub_pos.mpr hαν
  have hfun : ∀ r, M * exp (α * (t - r)) * (K * exp (ν * r))
      = (M * K * exp (α * t)) * exp ((ν - α) * r) := by
    intro r
    have : exp (α * (t - r)) * exp (ν * r) = exp (α * t) * exp ((ν - α) * r) := by
      rw [← exp_add, ← exp_add]; ring_nf
    calc M * exp (α * (t - r)) * (K * exp (ν * r))
        = M * K * (exp (α * (t - r)) * exp (ν * r)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul]
  have hFTC : ∫ r in (0 : ℝ)..t, exp ((ν - α) * r)
      = exp ((ν - α) * t) / (ν - α) - exp ((ν - α) * 0) / (ν - α) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun r => exp ((ν - α) * r) / (ν - α))
      (fun x _ => ?_) ?_
    · have hne : ν - α ≠ 0 := ne_of_gt hc
      have h0 : HasDerivAt (fun r => (ν - α) * r) (ν - α) x := by
        simpa using (hasDerivAt_id x).const_mul (ν - α)
      have h := h0.exp.div_const (ν - α)
      rw [mul_div_assoc, div_self hne, mul_one] at h
      exact h
    · exact (continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [hFTC, mul_zero, exp_zero]
  have hA : 0 ≤ M * K * exp (α * t) := by positivity
  have hE : exp (α * t) * exp ((ν - α) * t) = exp (ν * t) := by
    rw [← exp_add]; ring_nf
  calc M * K * exp (α * t) * (exp ((ν - α) * t) / (ν - α) - 1 / (ν - α))
      ≤ M * K * exp (α * t) * (exp ((ν - α) * t) / (ν - α)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have : 0 ≤ 1 / (ν - α) := by positivity
        linarith
    _ = M * K * exp (ν * t) / (ν - α) := by rw [← hE]; ring

/-- The backward kernel: `∫_{(t,∞)} M e^{-β(r-t)} K e^{νr} dr = M K e^{νt}/(β - ν)`. -/
theorem backward_kernel_eq {M K β ν t : ℝ} (hνβ : ν < β) :
    ∫ r in Ioi t, M * exp (-β * (r - t)) * (K * exp (ν * r))
      = M * K * exp (ν * t) / (β - ν) := by
  have hfun : ∀ r, M * exp (-β * (r - t)) * (K * exp (ν * r))
      = (M * K * exp (β * t)) * exp ((ν - β) * r) := by
    intro r
    have : exp (-β * (r - t)) * exp (ν * r) = exp (β * t) * exp ((ν - β) * r) := by
      rw [← exp_add, ← exp_add]; ring_nf
    calc M * exp (-β * (r - t)) * (K * exp (ν * r))
        = M * K * (exp (-β * (r - t)) * exp (ν * r)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) t]
  have hE : exp (β * t) * exp ((ν - β) * t) = exp (ν * t) := by
    rw [← exp_add]; ring_nf
  have hne : ν - β ≠ 0 := by linarith
  have hne' : β - ν ≠ 0 := by linarith
  rw [← hE]
  field_simp
  ring

theorem backward_kernel_integrable {M K β ν t : ℝ} (hνβ : ν < β) :
    IntegrableOn (fun r => M * exp (-β * (r - t)) * (K * exp (ν * r))) (Ioi t) := by
  have hfun : (fun r => M * exp (-β * (r - t)) * (K * exp (ν * r)))
      = fun r => (M * K * exp (β * t)) * exp ((ν - β) * r) := by
    funext r
    have : exp (-β * (r - t)) * exp (ν * r) = exp (β * t) * exp ((ν - β) * r) := by
      rw [← exp_add, ← exp_add]; ring_nf
    calc M * exp (-β * (r - t)) * (K * exp (ν * r))
        = M * K * (exp (-β * (r - t)) * exp (ν * r)) := by ring
      _ = _ := by rw [this]; ring
  rw [hfun]
  exact (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _

/-! ### The Lyapunov–Perron operator -/

variable {U Nn : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]

/-- The Lyapunov–Perron operator of `eq:supp-exact-graph-field` with initial value `n₀`:
`(𝒯y)(t) = (-∫_{(t,∞)} P_u(t-r)[b_u + N_u(y r)] dr, P_n(t) n₀ + ∫_0^t P_n(t-r)[b_n + N_n(y r)] dr)`. -/
noncomputable def lpMap (Pu : ℝ → U →L[ℝ] U) (Pn : ℝ → Nn →L[ℝ] Nn) (bu : U) (bn : Nn)
    (Nu : U × Nn → U) (Nv : U × Nn → Nn) (n₀ : Nn) (y : ℝ → U × Nn) (t : ℝ) : U × Nn :=
  (-∫ r in Ioi t, Pu (t - r) (bu + Nu (y r)),
    Pn t n₀ + ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y r)))

/-- Integrability of the backward integrand for a continuous trajectory of weighted growth. -/
theorem backward_integrable {Pu : ℝ → U →L[ℝ] U} (hPuc : Continuous Pu) {M β ν L K t : ℝ}
    (hν : 0 < ν) (hνβ : ν < β) (hM : 0 ≤ M) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s)) (g : U × Nn → U)
    (hg : ∀ x x', ‖g x - g x'‖ ≤ L * ‖x - x'‖) {y : ℝ → U × Nn} (hy : Continuous y)
    (hyK : ∀ r, 0 ≤ r → ‖y r‖ ≤ K * exp (ν * r)) :
    IntegrableOn (fun r => Pu (t - r) (g (y r))) (Ioi t) := by
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun x' => hg x' x) ?_
    have : Tendsto (fun x' => L * ‖x' - x‖) (𝓝 x) (𝓝 (L * ‖x - x‖)) :=
      (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
    simpa using this
  have hmeas : AEStronglyMeasurable (fun r => Pu (t - r) (g (y r))) (volume.restrict (Ioi t)) :=
    ((hPuc.comp (continuous_const.sub continuous_id)).clm_apply
      (hgc.comp hy)).aestronglyMeasurable
  set C0 := ‖g 0‖
  -- domination by two decaying exponentials
  have hdom : ∀ r ∈ Ioi t, ‖Pu (t - r) (g (y r))‖
      ≤ M * exp (-β * (r - t)) * (C0 * exp (0 * r)) + M * exp (-β * (r - t)) *
        ((L * K) * exp (ν * r)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.le
    have hP : ‖Pu (t - r)‖ ≤ M * exp (-β * (r - t)) := by
      have := hPu (r - t) (by linarith [hr.out])
      rwa [show -(r - t) = t - r by ring] at this
    have hgy : ‖g (y r)‖ ≤ C0 + L * (K * exp (ν * r)) := by
      have := hg (y r) 0
      rw [sub_zero] at this
      calc ‖g (y r)‖ ≤ ‖g 0‖ + ‖g (y r) - g 0‖ := norm_le_insert' _ _
        _ ≤ C0 + L * (K * exp (ν * r)) :=
            add_le_add le_rfl (this.trans (mul_le_mul_of_nonneg_left (hyK r hr0) hL))
    calc ‖Pu (t - r) (g (y r))‖ ≤ ‖Pu (t - r)‖ * ‖g (y r)‖ := (Pu (t - r)).le_opNorm _
      _ ≤ M * exp (-β * (r - t)) * (C0 + L * (K * exp (ν * r))) :=
          mul_le_mul hP hgy (norm_nonneg _) (by positivity)
      _ = _ := by rw [zero_mul, exp_zero]; ring
  have hβ : (0 : ℝ) < β := hν.trans hνβ
  refine Integrable.mono' ((backward_kernel_integrable (M := M) (K := C0) (ν := 0) (t := t)
    hβ).add
    (backward_kernel_integrable (M := M) (K := L * K) (t := t) hνβ)) hmeas ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hdom)

/-- **Weighted Lipschitz estimate of the Lyapunov–Perron operator** (the `j = 1` case of
`eq:supp-exact-graph-contraction`): if `‖y₁(r) - y₂(r)‖ ≤ δ e^{νr}` for `r ≥ 0`, then for
`t ≥ 0`, `‖(𝒯y₁)(t) - (𝒯y₂)(t)‖ ≤ M L ((ν - α)⁻¹ + (β - ν)⁻¹) δ e^{νt}`. -/
theorem lpMap_sub_le {Pu : ℝ → U →L[ℝ] U} {Pn : ℝ → Nn →L[ℝ] Nn} (hPuc : Continuous Pu)
    (hPnc : Continuous Pn) {M α β ν L K δ : ℝ} (hν : 0 < ν) (hαν : α < ν) (hνβ : ν < β)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hPu : ∀ s, 0 ≤ s → ‖Pu (-s)‖ ≤ M * exp (-β * s))
    (hPn : ∀ s, 0 ≤ s → ‖Pn s‖ ≤ M * exp (α * s))
    (bu : U) (bn : Nn) (Nu : U × Nn → U) (Nv : U × Nn → Nn)
    (hNu : ∀ x x', ‖Nu x - Nu x'‖ ≤ L * ‖x - x'‖) (hNv : ∀ x x', ‖Nv x - Nv x'‖ ≤ L * ‖x - x'‖)
    (n₀ : Nn) {y₁ y₂ : ℝ → U × Nn} (hy₁ : Continuous y₁) (hy₂ : Continuous y₂)
    (hK₁ : ∀ r, 0 ≤ r → ‖y₁ r‖ ≤ K * exp (ν * r)) (hK₂ : ∀ r, 0 ≤ r → ‖y₂ r‖ ≤ K * exp (ν * r))
    (hδ : ∀ r, 0 ≤ r → ‖y₁ r - y₂ r‖ ≤ δ * exp (ν * r)) {t : ℝ} (ht : 0 ≤ t) :
    ‖lpMap Pu Pn bu bn Nu Nv n₀ y₁ t - lpMap Pu Pn bu bn Nu Nv n₀ y₂ t‖
      ≤ M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) * δ * exp (ν * t) := by
  have hδ0 : 0 ≤ δ := by
    have := (norm_nonneg _).trans (hδ 0 le_rfl)
    simpa using this
  -- the shifted nonlinearities `b + N` are `L`-Lipschitz
  have hgu : ∀ x x', ‖(bu + Nu x) - (bu + Nu x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact hNu x x'
  have hgv : ∀ x x', ‖(bn + Nv x) - (bn + Nv x')‖ ≤ L * ‖x - x'‖ := fun x x' => by
    rw [add_sub_add_left_eq_sub]; exact hNv x x'
  -- backward component
  have hI₁ := backward_integrable (t := t) hPuc hν hνβ hM hL ht hPu (fun x => bu + Nu x) hgu hy₁ hK₁
  have hI₂ := backward_integrable (t := t) hPuc hν hνβ hM hL ht hPu (fun x => bu + Nu x) hgu hy₂ hK₂
  have hB : ‖(∫ r in Ioi t, Pu (t - r) (bu + Nu (y₁ r))) - ∫ r in Ioi t, Pu (t - r) (bu + Nu (y₂ r))‖
      ≤ M * (L * δ) * exp (ν * t) / (β - ν) := by
    rw [← integral_sub hI₁ hI₂, ← backward_kernel_eq (M := M) (K := L * δ) hνβ]
    refine norm_integral_le_of_norm_le (backward_kernel_integrable hνβ) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 ≤ r := ht.trans hr.out.le
    have hP : ‖Pu (t - r)‖ ≤ M * exp (-β * (r - t)) := by
      have := hPu (r - t) (by linarith [hr.out])
      rwa [show -(r - t) = t - r by ring] at this
    rw [← map_sub]
    calc ‖Pu (t - r) ((bu + Nu (y₁ r)) - (bu + Nu (y₂ r)))‖
        ≤ ‖Pu (t - r)‖ * ‖(bu + Nu (y₁ r)) - (bu + Nu (y₂ r))‖ := (Pu (t - r)).le_opNorm _
      _ ≤ M * exp (-β * (r - t)) * (L * δ * exp (ν * r)) := by
          refine mul_le_mul hP ((hgu _ _).trans ?_) (norm_nonneg _) (by positivity)
          calc L * ‖y₁ r - y₂ r‖ ≤ L * (δ * exp (ν * r)) :=
                mul_le_mul_of_nonneg_left (hδ r hr0) hL
            _ = L * δ * exp (ν * r) := by ring
  -- forward component
  have hcontF : ∀ (y : ℝ → U × Nn), Continuous y →
      IntervalIntegrable (fun r => Pn (t - r) (bn + Nv (y r))) volume 0 t := by
    intro y hy
    have hgc : Continuous fun x : U × Nn => bn + Nv x := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun x' => hgv x' x) ?_
      have : Tendsto (fun x' => L * ‖x' - x‖) (𝓝 x) (𝓝 (L * ‖x - x‖)) :=
        (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
      simpa using this
    exact ((hPnc.comp (continuous_const.sub continuous_id)).clm_apply
      (hgc.comp hy)).intervalIntegrable _ _
  have hF : ‖(∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₁ r)))
      - ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₂ r))‖
      ≤ M * (L * δ) * exp (ν * t) / (ν - α) := by
    rw [← integral_sub (hcontF y₁ hy₁) (hcontF y₂ hy₂)]
    refine (norm_integral_le_of_norm_le ht ?_ ?_).trans
      (forward_kernel_le hM (by positivity) hαν ht)
    · refine Eventually.of_forall fun r hr => ?_
      have hr0 : 0 ≤ r := hr.1.le
      have hP : ‖Pn (t - r)‖ ≤ M * exp (α * (t - r)) := hPn (t - r) (by linarith [hr.2])
      rw [← map_sub]
      calc ‖Pn (t - r) ((bn + Nv (y₁ r)) - (bn + Nv (y₂ r)))‖
          ≤ ‖Pn (t - r)‖ * ‖(bn + Nv (y₁ r)) - (bn + Nv (y₂ r))‖ := (Pn (t - r)).le_opNorm _
        _ ≤ M * exp (α * (t - r)) * (L * δ * exp (ν * r)) := by
            refine mul_le_mul hP ((hgv _ _).trans ?_) (norm_nonneg _) (by positivity)
            calc L * ‖y₁ r - y₂ r‖ ≤ L * (δ * exp (ν * r)) :=
                  mul_le_mul_of_nonneg_left (hδ r hr0) hL
              _ = L * δ * exp (ν * r) := by ring
    · exact (by
        have : Continuous fun r : ℝ => M * exp (α * (t - r)) * (L * δ * exp (ν * r)) := by
          fun_prop
        exact this.intervalIntegrable _ _)
  -- combine the two components
  have hc1 : 0 < ν - α := sub_pos.mpr hαν
  have hc2 : 0 < β - ν := sub_pos.mpr hνβ
  simp only [lpMap]
  calc ‖((-∫ r in Ioi t, Pu (t - r) (bu + Nu (y₁ r))) - -∫ r in Ioi t, Pu (t - r) (bu + Nu (y₂ r)),
        (Pn t n₀ + ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₁ r)))
          - (Pn t n₀ + ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₂ r))))‖
      ≤ ‖(-∫ r in Ioi t, Pu (t - r) (bu + Nu (y₁ r))) - -∫ r in Ioi t, Pu (t - r) (bu + Nu (y₂ r))‖
        + ‖(Pn t n₀ + ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₁ r)))
          - (Pn t n₀ + ∫ r in (0 : ℝ)..t, Pn (t - r) (bn + Nv (y₂ r)))‖ := by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))
    _ ≤ M * (L * δ) * exp (ν * t) / (β - ν) + M * (L * δ) * exp (ν * t) / (ν - α) := by
        refine add_le_add ?_ ?_
        · rw [neg_sub_neg, norm_sub_rev]; exact hB
        · rw [add_sub_add_left_eq_sub]; exact hF
    _ = M * L * ((ν - α)⁻¹ + (β - ν)⁻¹) * δ * exp (ν * t) := by
        field_simp
        ring

end LyapunovPerron
end RenewalGeometry
