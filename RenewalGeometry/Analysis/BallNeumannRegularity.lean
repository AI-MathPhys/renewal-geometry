/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallGaffney

/-!
# Classical `H²` estimates for the Neumann problem on a ball
  (stage C4, a-priori part of the boundary regularity, ball rendering of Uhlenbeck's theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For a `C³` function `ξ` with **vanishing normal derivative** `(x - c)·∇ξ = 0` on `∂B_r(c)`, the
gradient `∇ξ` is a closed one-form with vanishing normal component, so Gaffney's identity
(`gaffney_ball`) applied to `∇ξ` gives the classical boundary `H²` estimate of the Neumann
problem, with the convexity term of the sphere:

* `neumann_hessian_identity`:
  `∫_B |∇²ξ|² + r^{n-1}(1/r) ∫_{S^{n-1}} |∇ξ(c + rω)|² dσ = ∫_B (Δξ)²`;
* `neumann_hessian_le`: `∫_B |∇²ξ|² ≤ ∫_B (Δξ)²`;
* `neumann_gradient_le` (Poincaré for the tangential form `∇ξ`):
  `(n - 1) ∫_B |∇ξ|² ≤ r² ∫_B (Δξ)²`.

These are the a-priori estimates behind `H²` regularity up to the boundary of the weak Neumann
solution (`neumann_weak_ball`); the passage from weak to strong solutions (difference quotients
along the rotation fields `x_i ∂_j - x_j ∂_i`, interior regularity) is not done here.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-- The gradient of `ξ` as a one-form. -/
def gradForm (ξ : (Fin n → ℝ) → ℝ) : Fin n → (Fin n → ℝ) → ℝ := fun ν => pd ξ ν

theorem contDiff_gradForm {ξ : (Fin n → ℝ) → ℝ} (hξ : ContDiff ℝ 3 ξ) (ν : Fin n) :
    ContDiff ℝ 2 (gradForm ξ ν) := by
  unfold gradForm pd
  exact (hξ.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

theorem curlSq_gradForm {ξ : (Fin n → ℝ) → ℝ} (hξ : ContDiff ℝ 3 ξ) (x : Fin n → ℝ) :
    curlSq (gradForm ξ) x = 0 := by
  unfold curlSq gradForm
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
  rw [pd_pd_symm (hξ.of_le (by norm_num)) μ ν x, sub_self]
  norm_num

/-- **The Neumann `H²` identity on a ball**: for `ξ ∈ C³` with `(x - c)·∇ξ = 0` on `∂B_r(c)`,
`∫_B |∇²ξ|² + r^{n-1}(1/r) ∫_{S^{n-1}} |∇ξ(c + rω)|² dσ = ∫_B (Δξ)²`. -/
theorem neumann_hessian_identity (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {ξ : (Fin n → ℝ) → ℝ}
    (hξ : ContDiff ℝ 3 ξ) (hN : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * pd ξ μ y = 0) :
    (∫ x in euclBall c r, gradSq (gradForm ξ) x) +
        r ^ (n - 1) / r * ∫ w, normSq (gradForm ξ) (c + r • w) ∂(sphereMeasure n) =
      ∫ x in euclBall c r, divF (gradForm ξ) x ^ 2 := by
  have h := gaffney_ball c hr (contDiff_gradForm hξ) hN
  rw [h]
  refine setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => ?_
  simp only [curlSq_gradForm hξ x, zero_div, zero_add]

/-- `∫_B |∇²ξ|² ≤ ∫_B (Δξ)²` for Neumann functions on a ball. -/
theorem neumann_hessian_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {ξ : (Fin n → ℝ) → ℝ}
    (hξ : ContDiff ℝ 3 ξ) (hN : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * pd ξ μ y = 0) :
    ∫ x in euclBall c r, gradSq (gradForm ξ) x ≤ ∫ x in euclBall c r, divF (gradForm ξ) x ^ 2 := by
  rw [← neumann_hessian_identity c hr hξ hN]
  have : 0 ≤ r ^ (n - 1) / r * ∫ w, normSq (gradForm ξ) (c + r • w) ∂(sphereMeasure n) :=
    mul_nonneg (by positivity) (integral_nonneg fun w => normSq_nonneg _ _)
  linarith

/-- `(n - 1) ∫_B |∇ξ|² ≤ r² ∫_B (Δξ)²` for Neumann functions on a ball. -/
theorem neumann_gradient_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {ξ : (Fin n → ℝ) → ℝ}
    (hξ : ContDiff ℝ 3 ξ) (hN : ∀ y, sqDist c y = r ^ 2 → ∑ μ, (y μ - c μ) * pd ξ μ y = 0) :
    ((n : ℝ) - 1) * ∫ x in euclBall c r, normSq (gradForm ξ) x ≤
      r ^ 2 * ∫ x in euclBall c r, divF (gradForm ξ) x ^ 2 := by
  have h := poincare_ball_tangential c hr (contDiff_gradForm hξ) hN
  have e : ∫ x in euclBall c r, (curlSq (gradForm ξ) x / 2 + divF (gradForm ξ) x ^ 2) =
      ∫ x in euclBall c r, divF (gradForm ξ) x ^ 2 :=
    setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => by
      simp only [curlSq_gradForm hξ x, zero_div, zero_add]
  rw [e] at h
  exact h

/-- Non-vacuity: the radial function `ξ = (|x|² - 1)²` has vanishing normal derivative on the
unit sphere. -/
example : ∀ y : Fin 4 → ℝ, sqDist 0 y = 1 ^ 2 →
    ∑ μ, (y μ - (0 : Fin 4 → ℝ) μ) * pd (fun x => (sqDist (0 : Fin 4 → ℝ) x - 1) ^ 2) μ y = 0 := by
  intro y hy
  have hd : ∀ μ, pd (fun x => (sqDist (0 : Fin 4 → ℝ) x - 1) ^ 2) μ y =
      2 * (sqDist 0 y - 1) * (2 * (y μ - 0)) := by
    intro μ
    have := pd_comp_real (h := fun s : ℝ => (s - 1) ^ 2) (q := sqDist (0 : Fin 4 → ℝ))
      (x := y) (by fun_prop) ((contDiff_sqDist (0 : Fin 4 → ℝ) (k := 1)).differentiable
        (by norm_num) y) μ
    rw [this, pd_sqDist]
    have hder : deriv (fun s : ℝ => (s - 1) ^ 2) (sqDist 0 y) = 2 * (sqDist 0 y - 1) := by
      have h1 : HasDerivAt (fun s : ℝ => (s - 1) ^ 2) (2 * (sqDist (0 : Fin 4 → ℝ) y - 1))
          (sqDist 0 y) := by
        have := ((hasDerivAt_id (sqDist (0 : Fin 4 → ℝ) y)).sub_const 1).pow 2
        exact this.congr_deriv (by simp)
      exact h1.deriv
    rw [hder]
    simp
  simp only [hd, hy]
  simp

end RenewalGeometry.BallAnalysis
