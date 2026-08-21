/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventBound

/-!
# Coercive bounds for weak operator-graph resolvents

If the graph energy has a lower floor `μ‖u‖²`, testing the positive-shift
resolvent equation against its solution improves the standard `1 / λ` bound
to `1 / (λ + μ)`.  For Fourier screens, `μ` is the high-mode quadratic
symbol bound, so this estimate turns symbol coercivity into uniform resolvent
tail decay.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- A coercive graph-energy floor improves the pointwise shifted-resolvent
bound from `1 / λ` to `1 / (λ + μ)`. -/
theorem OperatorGraphResolventEquation.norm_le_inv_add_mul
    {D : Submodule K E} {A : D →ₗ[K] F} {lam mu : ℝ} {f x : E}
    (h : OperatorGraphResolventEquation D A lam f x)
    (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoercive : ∀ y : D, mu * ‖(y : E)‖ ^ 2 ≤ ‖A y‖ ^ 2) :
    ‖x‖ ≤ (1 / (lam + mu)) * ‖f‖ := by
  have heuler := h.weakEuler ⟨x, h.mem⟩
  rw [← norm_sq_eq_re_inner (𝕜 := K) (A ⟨x, h.mem⟩),
    ← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  have henergy := hcoercive ⟨x, h.mem⟩
  have hquad : (lam + mu) * ‖x‖ ^ 2 ≤ ‖x‖ * ‖f‖ := by
    nlinarith
  have hshift : 0 < lam + mu := add_pos_of_pos_of_nonneg hlam hmu
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    positivity
  have hxPos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have hlinear : (lam + mu) * ‖x‖ ≤ ‖f‖ := by nlinarith
  calc
    ‖x‖ ≤ ‖f‖ / (lam + mu) :=
      (le_div_iff₀ hshift).2 (by simpa [mul_comm] using hlinear)
    _ = (1 / (lam + mu)) * ‖f‖ := by ring

/-- Operator-norm version of the coercive graph-resolvent estimate. -/
theorem operatorGraphResolvent_opNorm_le_inv_add
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoercive : ∀ y : D, mu * ‖(y : E)‖ ^ 2 ≤ ‖A y‖ ^ 2)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    ‖R‖ ≤ 1 / (lam + mu) := by
  apply R.opNorm_le_bound
  · positivity
  intro f
  exact (hR f).norm_le_inv_add_mul hlam hmu hcoercive

/-- A family of coercive floors diverging to infinity forces the corresponding
positive-shift resolvent norms to vanish. -/
theorem operatorGraphResolvent_opNorm_tendsto_zero_of_coercivity_atTop
    (D : ℕ → Submodule K E) (A : ∀ n, D n →ₗ[K] F)
    (R : ℕ → E →L[K] E) (lam : ℝ) (mu : ℕ → ℝ)
    (hlam : 0 < lam) (hmu : ∀ n, 0 ≤ mu n)
    (hcoercive : ∀ n (y : D n), mu n * ‖(y : E)‖ ^ 2 ≤ ‖A n y‖ ^ 2)
    (hR : ∀ n (f : E),
      OperatorGraphResolventEquation (D n) (A n) lam f (R n f))
    (hmuTop : Tendsto mu Filter.atTop Filter.atTop) :
    Tendsto (fun n => ‖R n‖) Filter.atTop (𝓝 0) := by
  have hbound : ∀ n, ‖R n‖ ≤ 1 / (lam + mu n) := fun n =>
    operatorGraphResolvent_opNorm_le_inv_add
      (D n) (A n) (R n) lam (mu n) hlam (hmu n) (hcoercive n) (hR n)
  have hdenom : Tendsto (fun n => lam + mu n) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left Filter.atTop lam hmuTop
  have hinv : Tendsto (fun n => 1 / (lam + mu n)) Filter.atTop (𝓝 0) := by
    simp only [one_div]
    change Tendsto ((fun r : ℝ => r⁻¹) ∘ (fun n => lam + mu n))
      Filter.atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp hdenom
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg (R n))
    (Filter.Eventually.of_forall hbound) hinv

end NCG.VaryingHilbert
