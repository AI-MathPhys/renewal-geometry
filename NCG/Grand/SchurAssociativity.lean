/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Associativity of interface elimination
  (`thm:Schur-associativity`, Gran-Tensor manuscript)

* `schur_associativity`: the boxed quotient identity
  `(L/L_{I₁I₁})/(L/L_{I₁I₁})_{I₂I₂} = L/L_{II}` in solved form —
  for every interior solution `(u₁, u₂)` of the two internal
  balance equations, the iterated Schur complement applied to
  the exterior datum reproduces the full solved response
  `Ax + B₁u₁ + B₂u₂`.  Since the direct complement `L/L_{II}`
  has the same solve characterization (the interface-gluing
  theorem), a finite network response is independent of the
  order in which internal interfaces are eliminated.

Rendering disclosed: the matrix-level equality of the two
complements follows from this solve characterization by
running it on a basis of exterior data with the uniquely solved
interior (both internal blocks invertible); the displayed
existence proviso is the two `Invertible` hypotheses.
-/

open Matrix

namespace NCG

/-- `thm:Schur-associativity`: the iterated Schur complement
reproduces the full solved response — elimination order is
immaterial. -/
theorem schur_associativity {E I1 I2 : Type*} [Fintype E]
    [Fintype I1] [Fintype I2] [DecidableEq I1] [DecidableEq I2]
    (A : Matrix E E ℂ) (B1 : Matrix E I1 ℂ) (B2 : Matrix E I2 ℂ)
    (C1 : Matrix I1 E ℂ) (C2 : Matrix I2 E ℂ)
    (D11 : Matrix I1 I1 ℂ) (D12 : Matrix I1 I2 ℂ)
    (D21 : Matrix I2 I1 ℂ) (D22 : Matrix I2 I2 ℂ)
    [Invertible D11]
    [Invertible (D22 - D21 * D11⁻¹ * D12)]
    (x : E → ℂ) (u1 : I1 → ℂ) (u2 : I2 → ℂ)
    (h1 : D11 *ᵥ u1 + (D12 *ᵥ u2 + C1 *ᵥ x) = 0)
    (h2 : D21 *ᵥ u1 + (D22 *ᵥ u2 + C2 *ᵥ x) = 0) :
    ((A - B1 * D11⁻¹ * C1)
        - (B2 - B1 * D11⁻¹ * D12)
          * (D22 - D21 * D11⁻¹ * D12)⁻¹
          * (C2 - D21 * D11⁻¹ * C1)) *ᵥ x
      = A *ᵥ x + (B1 *ᵥ u1 + B2 *ᵥ u2) := by
  have hu1 : u1 = -(D11⁻¹ *ᵥ (D12 *ᵥ u2))
      - D11⁻¹ *ᵥ (C1 *ᵥ x) := by
    have h := congrArg (fun v => D11⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] at h
    funext j
    have hj := congrFun h j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  have hS : (D22 - D21 * D11⁻¹ * D12) *ᵥ u2
      + (C2 - D21 * D11⁻¹ * C1) *ᵥ x = 0 := by
    have h2' := h2
    rw [hu1] at h2'
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.mul_assoc] at h2' ⊢
    funext j
    have hj := congrFun h2' j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  have hu2 : u2 = -((D22 - D21 * D11⁻¹ * D12)⁻¹
      *ᵥ ((C2 - D21 * D11⁻¹ * C1) *ᵥ x)) := by
    have h := congrArg
      (fun v => (D22 - D21 * D11⁻¹ * D12)⁻¹ *ᵥ v) hS
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] at h
    funext j
    have hj := congrFun h j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hj ⊢
    linear_combination hj
  rw [hu2] at hu1
  rw [hu1, hu2]
  funext j
  simp only [Matrix.sub_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

end NCG
