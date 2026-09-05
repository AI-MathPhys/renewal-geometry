/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples

/-!
# Positive recurrent cost and nonlinear barycenter counterexamples

Faithful concrete models for `cth:GT-positive-cost-no-budget` and
`cth:GT-barycenter-not-solution`.
-/

open Finset

namespace NCG
namespace PositiveSelfLoopAndNonlinearBarycenter

/-! ## A positive self-loop has infinite history -/

/-- The unique infinite history on the one-vertex graph. -/
def selfLoopHistory (_n : ℕ) : Fin 1 := 0

/-- The unique edge is a self-loop of cost one. -/
def selfLoopCost (_source _target : Fin 1) : ℕ := 1

/-- `cth:GT-positive-cost-no-budget`: the path traverses the positive-cost
self-loop forever, its first `n` payments equal `n`, and hence no finite
source budget bounds every prefix. -/
theorem positive_self_loop_has_no_finite_budget :
    (∀ n, selfLoopHistory (n + 1) = selfLoopHistory n)
    ∧ 0 < selfLoopCost 0 0
    ∧ (∀ n, ∑ k ∈ range n,
        selfLoopCost (selfLoopHistory k) (selfLoopHistory (k + 1)) = n)
    ∧ ¬∃ B : ℕ, ∀ n, ∑ k ∈ range n,
        selfLoopCost (selfLoopHistory k) (selfLoopHistory (k + 1)) ≤ B := by
  refine ⟨fun _ ↦ rfl, by decide, ?_, ?_⟩
  · intro n
    simp [selfLoopCost]
  · rintro ⟨B, hB⟩
    have := hB (B + 1)
    simp [selfLoopCost] at this

/-! ## A mixture of exact nonlinear responses need not be exact -/

/-- The nonlinear vector field `2√(x₊)` in the manuscript. -/
noncomputable def nonlinearVectorField (x : ℝ) : ℝ :=
  2 * Real.sqrt (max x 0)

def zeroResponse (_t : ℝ) : ℝ := 0
def quadraticResponse (t : ℝ) : ℝ := t ^ 2
noncomputable def barycenterResponse (t : ℝ) : ℝ := t ^ 2 / 2

theorem zeroResponse_isSolution (t : ℝ) :
    HasDerivAt zeroResponse 0 t
      ∧ 0 = nonlinearVectorField (zeroResponse t) := by
  constructor
  · change HasDerivAt (fun _ : ℝ => 0) 0 t
    exact hasDerivAt_const (x := t) (c := (0 : ℝ))
  · simp [zeroResponse, nonlinearVectorField]

theorem quadraticResponse_isSolution {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt quadraticResponse (2 * t) t
      ∧ 2 * t = nonlinearVectorField (quadraticResponse t) := by
  constructor
  · change HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t
    have h := (hasDerivAt_id t).pow 2
    have hfun : (id ^ 2 : ℝ → ℝ) = fun x : ℝ => x ^ 2 := by
      funext x
      simp [Pi.pow_apply]
    rw [hfun] at h
    norm_num at h
    exact h
  · simp [quadraticResponse, nonlinearVectorField, max_eq_left (sq_nonneg t),
      Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

theorem nonlinearVectorField_barycenter {t : ℝ} (ht : 0 < t) :
    nonlinearVectorField (barycenterResponse t) = Real.sqrt 2 * t := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hs₀ : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hratio : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs₀).2
    nlinarith
  rw [nonlinearVectorField, barycenterResponse, max_eq_left (by positivity),
    Real.sqrt_div (sq_nonneg t) 2, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  calc
    2 * (t / Real.sqrt 2) = (2 / Real.sqrt 2) * t := by ring
    _ = Real.sqrt 2 * t := by rw [hratio]

/-- `cth:GT-barycenter-not-solution`: both atoms are exact solutions of the
displayed nonlinear ODE, while their equal barycenter has derivative `t` and
fails the same equation at every positive time. -/
theorem exact_responses_have_non_solution_barycenter {t : ℝ} (ht : 0 < t) :
    (HasDerivAt zeroResponse 0 t
      ∧ 0 = nonlinearVectorField (zeroResponse t))
    ∧ (HasDerivAt quadraticResponse (2 * t) t
      ∧ 2 * t = nonlinearVectorField (quadraticResponse t))
    ∧ HasDerivAt barycenterResponse t t
    ∧ t ≠ nonlinearVectorField (barycenterResponse t) := by
  refine ⟨zeroResponse_isSolution t, quadraticResponse_isSolution ht.le, ?_, ?_⟩
  · change HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t
    have hpow := (hasDerivAt_id t).pow 2
    have hpowfun : (id ^ 2 : ℝ → ℝ) = fun x : ℝ => x ^ 2 := by
      funext x
      simp [Pi.pow_apply]
    rw [hpowfun] at hpow
    norm_num at hpow
    have h := hpow.const_mul (1 / 2 : ℝ)
    have hfun : (fun y : ℝ => (1 / 2) * y ^ 2) =
        fun x : ℝ => x ^ 2 / 2 := by
      funext x
      ring
    rw [hfun] at h
    have hcoef : (1 / 2 : ℝ) * (2 * t) = t := by ring
    rw [hcoef] at h
    exact h
  · rw [nonlinearVectorField_barycenter ht]
    exact FiniteCalibrationAndDynamicalCounterexamples.nonlinear_barycenter_not_solution ht

end PositiveSelfLoopAndNonlinearBarycenter
end NCG
