/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExtendedLegendreRateExact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Finite-rate points can be approximated by pressure derivatives

A positive quadratic penalty gives an interior minimizer of
`psi k - a*k + lambda*k^2`. Its derivative equation controls both the
distance to `a` and the tangent cost. This covers finite-rate endpoints
without assuming that the derivative range is open or strictly monotone.
-/

open Set
open scoped Topology

namespace NCG.LegendreDerivativeApproximation

noncomputable section

/-- Quadratic regularization produces a derivative slope with a controlled
cost and a quantitative displacement estimate. -/
theorem exists_regularized_tangent
    (psi : ℝ → ℝ) (hd : Differentiable ℝ psi) (a r lambda : ℝ)
    (hlambda : 0 < lambda) (hr : ExtendedLegendreRate.rate psi a ≤ (r : EReal)) :
    ∃ k : ℝ, deriv psi k - a = -2 * lambda * k ∧
      k * deriv psi k - psi k ≤ r ∧ lambda * k ^ 2 ≤ r + psi 0 := by
  have hb := (ExtendedLegendreRate.rate_le_coe_iff psi a r).mp hr
  have hC : 0 ≤ r + psi 0 := by have h := hb 0; linarith
  let R : ℝ := (r + psi 0) / lambda + 1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [div_nonneg hC hlambda.le]
  have hR : 0 < R := by linarith
  have hRmul : lambda * R = r + psi 0 + lambda := by
    dsimp [R]
    field_simp
    <;> ring
  have hRbig : r + psi 0 < lambda * R ^ 2 := by
    have hsq : R ≤ R ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq hlambda.le
    linarith
  let F : ℝ → ℝ := fun k => psi k - a * k + lambda * k ^ 2
  have hcont : Continuous F :=
    (hd.continuous.sub (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_id.pow 2))
  obtain ⟨k, hk, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩) hcont.continuousOn
  have hmin0 := hmin (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith)
  change F k ≤ F 0 at hmin0
  have hFk : F k ≤ psi 0 := by simpa only [F, mul_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, add_zero] using hmin0
  have hbound : lambda * k ^ 2 ≤ r + psi 0 := by
    have hb' := hb k
    dsimp [F] at hFk
    nlinarith
  have hleft : -R < k := by
    by_contra hn
    have heq : k = -R := le_antisymm (le_of_not_gt hn) hk.1
    rw [heq] at hbound
    nlinarith
  have hright : k < R := by
    by_contra hn
    have heq : k = R := le_antisymm hk.2 (le_of_not_gt hn)
    rw [heq] at hbound
    linarith
  have hlocal : IsLocalMin F k := hmin.isLocalMin (Icc_mem_nhds hleft hright)
  have hraw := ((hd k).hasDerivAt.sub ((hasDerivAt_id k).const_mul a)).add
    (((hasDerivAt_id k).pow 2).const_mul lambda)
  have hfun : ((psi - fun y => a * id y) + fun y => lambda * (id ^ 2) y) = F := by
    funext x
    simp [F, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  rw [hfun] at hraw
  have hderiv : deriv F k = deriv psi k - a + lambda * (2 * k) := by
    simpa using hraw.deriv
  have hz := hlocal.deriv_eq_zero
  rw [hderiv] at hz
  refine ⟨k, by linarith, ?_, hbound⟩
  have hb' := hb k
  have heq : k * (deriv psi k - a) = -2 * lambda * k ^ 2 := by
    have h := congrArg (fun x : ℝ => k * x) hz
    nlinarith [h]
  have hnonneg := mul_nonneg hlambda.le (sq_nonneg k)
  nlinarith

/-- Every point with a finite rate upper bound is approximated by derivative
slopes whose tangent cost satisfies the same upper bound. -/
theorem exists_derivative_near_with_cost_le
    (psi : ℝ → ℝ) (hd : Differentiable ℝ psi) (a r delta : ℝ)
    (hdelta : 0 < delta) (hr : ExtendedLegendreRate.rate psi a ≤ (r : EReal)) :
    ∃ k : ℝ, |deriv psi k - a| < delta ∧ k * deriv psi k - psi k ≤ r := by
  have hb := (ExtendedLegendreRate.rate_le_coe_iff psi a r).mp hr
  have hC : 0 ≤ r + psi 0 := by have h := hb 0; linarith
  let lambda : ℝ := delta ^ 2 / (8 * (r + psi 0 + 1))
  have hden : 0 < 8 * (r + psi 0 + 1) := by positivity
  have hlambda : 0 < lambda := div_pos (sq_pos_of_pos hdelta) hden
  have hid : 8 * (r + psi 0 + 1) * lambda = delta ^ 2 := by
    dsimp [lambda]
    field_simp
  obtain ⟨k, heq, hcost, hbound⟩ := exists_regularized_tangent psi hd a r lambda hlambda hr
  refine ⟨k, ?_, hcost⟩
  have hsq : (deriv psi k - a) ^ 2 = 4 * lambda * (lambda * k ^ 2) := by
    rw [heq]
    ring
  have hmult := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 4 * lambda by positivity)
  have hsmall : 4 * lambda * (r + psi 0) < delta ^ 2 := by
    nlinarith [mul_nonneg hlambda.le hC]
  apply abs_lt_of_sq_lt_sq _ hdelta.le
  rw [hsq]
  exact hmult.trans_lt hsmall

/-- Every open neighborhood of a finite-rate point contains a derivative
slope with no increase in the specified rate upper bound. -/
theorem exists_derivative_mem_open_with_cost_le
    (psi : ℝ → ℝ) (hd : Differentiable ℝ psi) (G : Set ℝ) (a r : ℝ)
    (hG : IsOpen G) (ha : a ∈ G)
    (hr : ExtendedLegendreRate.rate psi a ≤ (r : EReal)) :
    ∃ k : ℝ, deriv psi k ∈ G ∧ k * deriv psi k - psi k ≤ r := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hG a ha
  obtain ⟨k, hnear, hcost⟩ := exists_derivative_near_with_cost_le psi hd a r delta hdelta hr
  refine ⟨k, hball ?_, hcost⟩
  simpa only [Metric.mem_ball, Real.dist_eq] using hnear

end

end NCG.LegendreDerivativeApproximation
