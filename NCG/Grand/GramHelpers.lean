/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Right-associated Gram cancellation helpers

Small rewriting lemmas used throughout the Gran-Tensor batch
files: after `simp only [Matrix.mul_assoc]` normalizes a
product chain to right-associated form, these fire as simp
rules to collapse `A·B = 1` pairs, Gram factorizations
`SᴴS = Rp·Rp`, and projection cores `Zᴴ·Z·(ZᴴZ)⁻¹`.
-/

open Matrix

namespace NCG

/-- Collapse an inverse pair in prefix position. -/
theorem cancel_left {n p m : Type*} [Fintype n] [Fintype p]
    [DecidableEq n] {A : Matrix n p ℂ} {B : Matrix p n ℂ}
    (h : A * B = 1) (X : Matrix n m ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

/-- Swap a Gram `SᴴS` for its square-root factorization in
prefix position. -/
theorem gram_swap {H E m : Type*} [Fintype H] [Fintype E]
    {S : Matrix H E ℂ} {Rp : Matrix E E ℂ}
    (h : Sᴴ * S = Rp * Rp) (X : Matrix E m ℂ) :
    Sᴴ * (S * X) = Rp * (Rp * X) := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]

/-- Collapse the projection core `Zᴴ·Z·(ZᴴZ)⁻¹` in prefix
position. -/
theorem proj_cancel {H l m : Type*} [Fintype H] [Fintype l]
    [DecidableEq l] (Z : Matrix H l ℂ)
    [Invertible (Zᴴ * Z)] (X : Matrix l m ℂ) :
    Zᴴ * (Z * ((Zᴴ * Z)⁻¹ * X)) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible, Matrix.one_mul]

/-- Collapse the reversed projection core
`(ZᴴZ)⁻¹·Zᴴ·Z` in prefix position. -/
theorem proj_cancel' {H l m : Type*} [Fintype H] [Fintype l]
    [DecidableEq l] (Z : Matrix H l ℂ)
    [Invertible (Zᴴ * Z)] (X : Matrix l m ℂ) :
    (Zᴴ * Z)⁻¹ * (Zᴴ * (Z * X)) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (Zᴴ * Z)⁻¹ Zᴴ Z]
  rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]

end NCG
