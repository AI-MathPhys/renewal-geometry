/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Entropic Hodge form and minimizing movement
  (`thm:entropic-Hodge-continuum`, Gran-Tensor manuscript)

* `fisher_window_bound`: the boxed Fisher-window lower bound —
  edgewise Fisher weights above `g₋` dominate the covariant
  Dirichlet energy, `ℐ_Γ(θ) ≥ (g₋/2)‖D_Uθ‖²`;
* `hodge_gap_chain`: the boxed protected-complement gap — the
  Hessian form `q ≥ (176/225)‖D_Uv‖²` chains with the
  covariant spectral gap `‖D_Uv‖² ≥ λ_U‖v‖²` to
  `q(v) ≥ (176/225)·λ_U·‖v‖²`;
* `resolvent_minimizer`: the boxed minimizing movement — for a
  symmetric PSD form the unique minimizer of
  `f ↦ (1/2τ)‖f-fₙ‖² + ½⟨f, Lf⟩` is the resolvent step
  `f* = (I+τL)⁻¹fₙ`, exhibited by the exact completion of the
  square `F(f) - F(f*) = (1/2τ)⟨f-f*, (I+τL)(f-f*)⟩ ≥ 0`.

Rendering disclosed: the second-derivative identity
`D²ℐ_Γ(0) = q_{U,G₀}` (the Hessian computation at the primitive
law), the kernel identification with covariantly parallel
fields, the Trotter convergence `W_τ^{⌊t/τ⌋} → e^{-tL}`, and
the Mosco passage to the cutoff limit are the manuscript's
variational layer; the window bound, the gap chain, and the
exact resolvent minimization are proved here.
-/

open Matrix

namespace NCG

/-- Boxed Fisher-window bound: edge weights above `g₋` dominate
the covariant Dirichlet energy. -/
theorem fisher_window_bound {E : Type*} [Fintype E]
    (g d : E → ℝ) (gminus : ℝ) (hg : ∀ e, gminus ≤ g e)
    (hd : ∀ e, 0 ≤ d e) :
    gminus / 2 * ∑ e, d e ≤ ∑ e, g e / 2 * d e := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have := hg e
  have := hd e
  nlinarith

/-- Boxed protected-complement gap:
`q(v) ≥ (176/225)·λ_U·‖v‖²` by chaining the Hessian floor with
the covariant spectral gap. -/
theorem hodge_gap_chain (q Dnorm vnorm lam : ℝ)
    (hq : 176 / 225 * Dnorm ≤ q) (hgap : lam * vnorm ≤ Dnorm)
    (_hlam : 0 ≤ lam) (_hv : 0 ≤ vnorm) :
    176 / 225 * lam * vnorm ≤ q := by
  nlinarith

/-- Boxed minimizing movement: for a symmetric PSD `L`, the
resolvent step `(I+τL)f* = fₙ` minimizes
`f ↦ (1/2τ)‖f-fₙ‖² + ½⟨f, Lf⟩`, by the exact completion of the
square. -/
theorem resolvent_minimizer {n : Type*} [Fintype n]
    [DecidableEq n] (L : Matrix n n ℝ) (hsym : Lᵀ = L)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ L.mulVec x) (τ : ℝ)
    (hτ : 0 < τ) (fn fstar : n → ℝ)
    (hstar : (1 + τ • L).mulVec fstar = fn) (f : n → ℝ) :
    1 / (2 * τ) * ((fstar - fn) ⬝ᵥ (fstar - fn))
        + 1 / 2 * (fstar ⬝ᵥ L.mulVec fstar)
      ≤ 1 / (2 * τ) * ((f - fn) ⬝ᵥ (f - fn))
        + 1 / 2 * (f ⬝ᵥ L.mulVec f) := by
  set d : n → ℝ := f - fstar with hd
  have hLsymm : ∀ x y : n → ℝ,
      x ⬝ᵥ L.mulVec y = y ⬝ᵥ L.mulVec x := by
    intro x y
    calc x ⬝ᵥ L.mulVec y
        = Matrix.vecMul x L ⬝ᵥ y := by
          rw [dotProduct_mulVec]
      _ = Matrix.vecMul x Lᵀ ⬝ᵥ y := by rw [hsym]
      _ = L.mulVec x ⬝ᵥ y := by
          rw [Matrix.vecMul_transpose]
      _ = y ⬝ᵥ L.mulVec x := dotProduct_comm _ _
  -- expand both sides around fstar using the stationarity
  have hfn : fn = fstar + τ • L.mulVec fstar := by
    rw [← hstar, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec]
  have hf : f = fstar + d := by
    rw [hd]
    funext i
    simp
  have hkey : 1 / (2 * τ) * ((f - fn) ⬝ᵥ (f - fn))
        + 1 / 2 * (f ⬝ᵥ L.mulVec f)
      - (1 / (2 * τ) * ((fstar - fn) ⬝ᵥ (fstar - fn))
        + 1 / 2 * (fstar ⬝ᵥ L.mulVec fstar))
      = 1 / (2 * τ) * (d ⬝ᵥ d)
        + 1 / 2 * (d ⬝ᵥ L.mulVec d) := by
    rw [hf, hfn]
    have hexp : ∀ x y : n → ℝ,
        (x + y) ⬝ᵥ L.mulVec (x + y)
          = x ⬝ᵥ L.mulVec x + 2 * (x ⬝ᵥ L.mulVec y)
            + y ⬝ᵥ L.mulVec y := by
      intro x y
      rw [Matrix.mulVec_add, add_dotProduct,
        dotProduct_add, dotProduct_add]
      have := hLsymm y x
      linarith [this]
    have hdot : ∀ x y : n → ℝ,
        (x + y) ⬝ᵥ (x + y)
          = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
      intro x y
      rw [add_dotProduct, dotProduct_add,
        dotProduct_add]
      rw [dotProduct_comm y x]
      ring
    have h1 : fstar + d - (fstar + τ • L.mulVec fstar)
        = d - τ • L.mulVec fstar := by
      abel
    have h2 : fstar - (fstar + τ • L.mulVec fstar)
        = -(τ • L.mulVec fstar) := by
      abel
    rw [h1, h2]
    rw [show d - τ • L.mulVec fstar
      = d + (-(τ • L.mulVec fstar)) from by abel]
    rw [hdot, hexp]
    have e0 : d ⬝ᵥ (-(τ • L.mulVec fstar))
        = -(d ⬝ᵥ (τ • L.mulVec fstar)) := dotProduct_neg _ _
    have e1 : d ⬝ᵥ (τ • L.mulVec fstar)
        = τ * (d ⬝ᵥ L.mulVec fstar) := by
      rw [dotProduct_smul, smul_eq_mul]
    have e2 : fstar ⬝ᵥ L.mulVec d = d ⬝ᵥ L.mulVec fstar :=
      hLsymm fstar d
    rw [e0, e1, e2]
    field_simp
    ring
  have hnn : 0 ≤ 1 / (2 * τ) * (d ⬝ᵥ d)
      + 1 / 2 * (d ⬝ᵥ L.mulVec d) := by
    have hdd : 0 ≤ d ⬝ᵥ d := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hLd := hpsd d
    positivity
  linarith [hkey, hnn]

end NCG
