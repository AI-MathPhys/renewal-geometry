/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-shell Hessian data do not determine a Wilsonian quadratic router

Two exact polynomial coefficient routers are attached only after the common microscopic law,
score Gram, and direct second-action Hessian have been acquired.  They agree to first order at the
base point but have opposite nonzero quadratic coefficients.  This supplies the finite witness in
`cth:SMFS-Hessian-not-beta` without replacing either the equilibrium packet or the router by a flag.
-/

namespace NCG.SMFSOneShellHessianWilsonianCounterexample

/-- The complete data acquired from one equilibrium shell, together with a subsequent router. -/
structure RoutedShell (Law Score Hessian : Type*) where
  law : Law
  scoreGram : Score
  directHessian : Hessian
  router : ℝ → ℝ

/-- Forgetting the later coarse-graining router leaves precisely the acquired one-shell data. -/
def acquiredData {Law Score Hessian : Type*} (P : RoutedShell Law Score Hessian) :
    Law × Score × Hessian :=
  (P.law, P.scoreGram, P.directHessian)

/-- The `+Q` coefficient router, here on the one-dimensional coefficient space with `Q(x,x)=x²`. -/
def routerPlus (x : ℝ) : ℝ := x + x ^ 2

/-- The `-Q` coefficient router on the same coefficient space. -/
def routerMinus (x : ℝ) : ℝ := x - x ^ 2

lemma hasDerivAt_routerPlus (x : ℝ) :
    HasDerivAt routerPlus (1 + 2 * x) x := by
  have hraw := (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2)
  have heq : routerPlus =ᶠ[nhds x] (id + id ^ 2 : ℝ → ℝ) :=
    Filter.Eventually.of_forall (by intro y; simp [routerPlus])
  have h := hraw.congr_of_eventuallyEq heq
  exact h.congr_deriv (by simp)

lemma hasDerivAt_routerMinus (x : ℝ) :
    HasDerivAt routerMinus (1 - 2 * x) x := by
  have hraw := (hasDerivAt_id x).sub ((hasDerivAt_id x).pow 2)
  have heq : routerMinus =ᶠ[nhds x] (id - id ^ 2 : ℝ → ℝ) :=
    Filter.Eventually.of_forall (by intro y; simp [routerMinus])
  have h := hraw.congr_of_eventuallyEq heq
  exact h.congr_deriv (by simp)

theorem router_first_order_agreement :
    routerPlus 0 = routerMinus 0 ∧
      deriv routerPlus 0 = 1 ∧ deriv routerMinus 0 = 1 := by
  constructor
  · norm_num [routerPlus, routerMinus]
  constructor
  · simpa using (hasDerivAt_routerPlus 0).deriv
  · simpa using (hasDerivAt_routerMinus 0).deriv

/-- The two Wilsonian quadratic coefficients are `+1` and `-1`. -/
theorem router_quadratic_coefficients_opposite :
    deriv (deriv routerPlus) 0 / 2 = 1 ∧
      deriv (deriv routerMinus) 0 / 2 = -1 := by
  have hplus : deriv routerPlus = fun x : ℝ => 1 + 2 * x := by
    funext x
    exact (hasDerivAt_routerPlus x).deriv
  have hminus : deriv routerMinus = fun x : ℝ => 1 - 2 * x := by
    funext x
    exact (hasDerivAt_routerMinus x).deriv
  rw [hplus, hminus]
  have hderPlus : HasDerivAt (fun x : ℝ => 1 + 2 * x) 2 0 := by
    have hraw := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul 2)
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp [mul_comm]))).congr_deriv (by norm_num)
  have hderMinus : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) 0 := by
    have hraw := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul 2)
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp [mul_comm]))).congr_deriv (by norm_num)
  constructor
  · rw [hderPlus.deriv]
    norm_num
  · rw [hderMinus.deriv]
    norm_num

/-- Exact finite counterexample: arbitrary common unnormalized law, complete score Gram, and direct
Hessian extend to two routed shells with identical acquired data and opposite quadratic Wilsonian
tensors. -/
theorem one_shell_equilibrium_data_do_not_determine_wilsonian_tensor
    {Law Score Hessian : Type*} (law : Law) (score : Score) (hessian : Hessian) :
    let Pplus : RoutedShell Law Score Hessian :=
      ⟨law, score, hessian, routerPlus⟩
    let Pminus : RoutedShell Law Score Hessian :=
      ⟨law, score, hessian, routerMinus⟩
    acquiredData Pplus = acquiredData Pminus ∧
      Pplus.router 0 = Pminus.router 0 ∧
      deriv Pplus.router 0 = deriv Pminus.router 0 ∧
      deriv (deriv Pplus.router) 0 / 2 = 1 ∧
      deriv (deriv Pminus.router) 0 / 2 = -1 := by
  dsimp
  refine ⟨rfl, router_first_order_agreement.1,
    router_first_order_agreement.2.1.trans router_first_order_agreement.2.2.symm,
    router_quadratic_coefficients_opposite.1,
    router_quadratic_coefficients_opposite.2⟩

end NCG.SMFSOneShellHessianWilsonianCounterexample
