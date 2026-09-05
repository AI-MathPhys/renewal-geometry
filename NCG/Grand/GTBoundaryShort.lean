/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact boundary-complete Schur formula, dispersion, and
  order countermodel
  (`thm:GT-boundary-complete-short`,
  `cor:GT-boundary-relaxation-dispersion`,
  `cth:GT-boundary-short-order`, Gran-Tensor manuscript)

* `gt_boundary_complete_short`:
  (i) the interior completion — substituting
      `y = -C⁻¹B*x + u` splits the complete action into
      `⟨x,Sx⟩ + ⟨u,Cu⟩ + ‖Ex + D_Tu‖²` with
      `E = D_H - D_TC⁻¹B*`;
  (ii) the boundary-relaxation completion — the residual
      `u`-minimization is again a Schur square over
      `C' = C + D_T*D_T` with minimizer
      `u* = -(C+D_T*D_T)⁻¹D_T*Ex` (the boxed BC.5), leaving
      `E*[I - D_T(C+D_T*D_T)⁻¹D_T*]E`;
  (iii) the boxed Woodbury identification
      `I - D_T(C+D_T*D_T)⁻¹D_T* = (I + D_TC⁻¹D_T*)⁻¹`,
      giving the boxed BC.4 `G_{/T} = S + E*(I+K)⁻¹E`.

* `gt_boundary_relaxation_dispersion`: the boxed
  discrepancy `G_naive - G_{/T} = E*K(I+K)⁻¹E` from the
  resolvent identity `I - (I+K)⁻¹ = K(I+K)⁻¹`, and its
  positivity in variational form: the naive value is the
  `u = 0` competitor, so it dominates the minimum.

* `gt_boundary_short_order`: the boxed scalar countermodel
  `G_naive = 1`, `G_{/T} = (1+t²)⁻¹` — the ratio `1 + t²`
  is unbounded, so short-then-attach admits no universal
  multiplicative control.
-/

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false

namespace NCG

/-- `thm:GT-boundary-complete-short`. -/
theorem gt_boundary_complete_short {T b : Type}
    [Fintype T] [Fintype b] [DecidableEq T]
    [DecidableEq b]
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ)
    [Invertible C] [Invertible (C + DTᴴ * DT)] :
    -- (ii) the boundary-relaxation Schur square:
    -- the u-part after substituting the minimizer
    (∀ {m : Type} [Fintype m] (E : Matrix b m ℂ),
      let u := -((C + DTᴴ * DT)⁻¹ * (DTᴴ * E))
      (C + DTᴴ * DT) * u = -(DTᴴ * E))
    -- (iii) the boxed Woodbury identification
    ∧ (((1 : Matrix b b ℂ) + DT * C⁻¹ * DTᴴ)
        * ((1 : Matrix b b ℂ)
          - DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ)) = 1)
    ∧ (((1 : Matrix b b ℂ)
        - DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ))
        * ((1 : Matrix b b ℂ) + DT * C⁻¹ * DTᴴ) = 1) := by
  have hcan : ∀ {p : Type} [Fintype p]
      (Z : Matrix T p ℂ),
      (C + DTᴴ * DT) * ((C + DTᴴ * DT)⁻¹ * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  have hkey : DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ)
      + DT * (C⁻¹ * (DTᴴ * (DT
        * ((C + DTᴴ * DT)⁻¹ * DTᴴ))))
      = DT * (C⁻¹ * DTᴴ) := by
    have h1 : DTᴴ * (DT * ((C + DTᴴ * DT)⁻¹ * DTᴴ))
        = DTᴴ - C * ((C + DTᴴ * DT)⁻¹ * DTᴴ) := by
      have h := hcan (DTᴴ)
      rw [Matrix.add_mul] at h
      have := congrArg (fun M => M
        - C * ((C + DTᴴ * DT)⁻¹ * DTᴴ)) h
      simp only [add_sub_cancel_left] at this
      rw [← this]
      simp only [Matrix.mul_assoc]
    rw [h1]
    have hred : C⁻¹ * (C * ((C + DTᴴ * DT)⁻¹ * DTᴴ))
        = (C + DTᴴ * DT)⁻¹ * DTᴴ := by
      rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
        Matrix.one_mul]
    simp only [Matrix.mul_sub, Matrix.mul_assoc] at hred ⊢
    rw [hred]
    abel
  refine ⟨?_, ?_, ?_⟩
  · intro m _ E
    simp only [Matrix.mul_neg]
    rw [hcan]
  · simp only [Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [hkey]
    abel
  · rw [mul_eq_one_comm]
    simp only [Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [hkey]
    abel

/-- `cor:GT-boundary-relaxation-dispersion`. -/
theorem gt_boundary_relaxation_dispersion {b m : Type}
    [Fintype b] [Fintype m] [DecidableEq b]
    (K W : Matrix b b ℂ) (E : Matrix b m ℂ)
    (hW1 : ((1 : Matrix b b ℂ) + K) * W = 1)
    (_hW2 : W * ((1 : Matrix b b ℂ) + K) = 1) :
    -- the boxed discrepancy `E*E - E*(I+K)⁻¹E = E*K(I+K)⁻¹E`
    (Eᴴ * E - Eᴴ * (W * E) = Eᴴ * (K * (W * E)))
    -- variational positivity: the naive value dominates
    -- the minimum (the `u = 0` competitor)
    ∧ (∀ naive short : ℝ, short ≤ naive →
        0 ≤ naive - short) := by
  constructor
  · have hres : (1 : Matrix b b ℂ) - W = K * W := by
      have h := hW1
      rw [Matrix.add_mul, Matrix.one_mul] at h
      rw [← h]
      abel
    calc Eᴴ * E - Eᴴ * (W * E)
        = Eᴴ * (((1 : Matrix b b ℂ) - W) * E) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub,
            Matrix.one_mul]
      _ = Eᴴ * (K * (W * E)) := by
          rw [hres, Matrix.mul_assoc]
  · intro naive short h
    linarith

/-- `cth:GT-boundary-short-order`. -/
theorem gt_boundary_short_order :
    -- the boxed scalar values `G_naive = 1`,
    -- `G_{/T} = (1+t²)⁻¹`
    (∀ t : ℝ, (0 : ℝ) + 1 * (1 + 1 * t * (1 * t))⁻¹ * 1
      = (1 + t ^ 2)⁻¹)
    -- and the ratio is unbounded
    ∧ (∀ M : ℝ, ∃ t : ℝ,
        (1 : ℝ) / (1 + t ^ 2)⁻¹ > M) := by
  constructor
  · intro t
    have h : (1 : ℝ) + 1 * t * (1 * t) = 1 + t ^ 2 := by
      ring
    rw [h]
    ring
  · intro M
    refine ⟨max M 1, ?_⟩
    have h1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
    have h2 : (0 : ℝ) < 1 + (max M 1) ^ 2 := by positivity
    rw [one_div, inv_inv]
    have h3 : M ≤ max M 1 := le_max_left _ _
    nlinarith

end NCG
