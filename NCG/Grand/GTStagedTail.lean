/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Associativity of invariant-tail elimination
  (`thm:GT-staged-tail-elimination`, Gran-Tensor manuscript)

* `gt_staged_tail_elimination`: the boxed RT.3 — splitting
  the tail as `R = R₁ ⊕ R₂`, eliminating the second stratum
  first through its own aggregate `R₂⁰ = (1-D₂₂)⁻¹` and
  forming the staged data (RT.2)
  `Ã = A + B₂R₂⁰C₂`, `B̃ = B₁ + B₂R₂⁰D₂₁`,
  `C̃ = C₁ + D₁₂R₂⁰C₂`, `D̃ = D₁₁ + D₁₂R₂⁰D₂₁`,
  reproduces the one-shot aggregate exactly:
  `A + B(1-D)⁻¹C = Ã + B̃(1-D̃)⁻¹C̃`.

The proof solves the block system `(1-D)(x ⊕ y) = C`
explicitly: `x = (1-D̃)⁻¹C̃` and `y = R₂⁰(C₂ + D₂₁x)`, so
staged and one-shot elimination read off the same head
value.  The manuscript's `‖D‖ < 1` hypothesis guarantees
all three resolvents; here they are taken as invertibility
hypotheses.
-/

open Matrix

namespace NCG

/-- `thm:GT-staged-tail-elimination` (the boxed RT.3). -/
theorem gt_staged_tail_elimination {P m R1 R2 : Type}
    [Fintype R1] [Fintype R2] [DecidableEq R1]
    [DecidableEq R2]
    (A : Matrix P m ℂ) (B1 : Matrix P R1 ℂ)
    (B2 : Matrix P R2 ℂ)
    (C1 : Matrix R1 m ℂ) (C2 : Matrix R2 m ℂ)
    (D11 : Matrix R1 R1 ℂ) (D12 : Matrix R1 R2 ℂ)
    (D21 : Matrix R2 R1 ℂ) (D22 : Matrix R2 R2 ℂ)
    [Invertible (1 - D22)]
    [Invertible (1 - (D11 + D12 * (1 - D22)⁻¹ * D21))]
    [Invertible (1 - fromBlocks D11 D12 D21 D22)] :
    A + fromCols B1 B2
        * ((1 - fromBlocks D11 D12 D21 D22)⁻¹
            * fromRows C1 C2)
      = (A + B2 * ((1 - D22)⁻¹ * C2))
        + (B1 + B2 * ((1 - D22)⁻¹ * D21))
          * ((1 - (D11 + D12 * (1 - D22)⁻¹ * D21))⁻¹
              * (C1 + D12 * ((1 - D22)⁻¹ * C2))) := by
  set R20 := (1 - D22)⁻¹ with hR20
  set Dt := D11 + D12 * R20 * D21 with hDt
  set Ct := C1 + D12 * (R20 * C2) with hCt
  set x := (1 - Dt)⁻¹ * Ct with hx0
  set y := R20 * (C2 + D21 * x) with hy0
  have hx : (1 - Dt) * x = Ct := by
    rw [hx0, mul_inv_cancel_left_of_invertible]
  have hy : (1 - D22) * y = C2 + D21 * x := by
    rw [hy0, hR20, mul_inv_cancel_left_of_invertible]
  have hDiff : (1 : Matrix (R1 ⊕ R2) (R1 ⊕ R2) ℂ)
      - fromBlocks D11 D12 D21 D22
      = fromBlocks (1 - D11) (-D12) (-D21) (1 - D22) := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply,
        Matrix.neg_apply]
  have hkey : (1 - fromBlocks D11 D12 D21 D22)
      * fromRows x y = fromRows C1 C2 := by
    rw [hDiff, fromBlocks_mul_fromRows]
    congr 1
    · -- (1 - D11) * x + (-D12) * y = C1
      have hxx : x - (D11 * x + D12 * (R20 * (D21 * x)))
          = C1 + D12 * (R20 * C2) := by
        calc x - (D11 * x + D12 * (R20 * (D21 * x)))
            = (1 - Dt) * x := by
              simp only [hDt, Matrix.sub_mul,
                Matrix.add_mul, Matrix.one_mul,
                Matrix.mul_assoc]
          _ = Ct := hx
          _ = C1 + D12 * (R20 * C2) := hCt
      have hC1 : C1
          = x - (D11 * x + D12 * (R20 * (D21 * x)))
            - D12 * (R20 * C2) :=
        eq_sub_of_add_eq hxx.symm
      rw [hy0]
      simp only [Matrix.sub_mul, Matrix.one_mul,
        Matrix.neg_mul, Matrix.mul_add]
      rw [hC1]
      abel
    · -- (-D21) * x + (1 - D22) * y = C2
      rw [hy]
      simp only [Matrix.neg_mul]
      abel
  have hinv : (1 - fromBlocks D11 D12 D21 D22)⁻¹
      * fromRows C1 C2 = fromRows x y := by
    rw [← hkey, inv_mul_cancel_left_of_invertible]
  rw [hinv, fromCols_mul_fromRows, hy0]
  simp only [Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  abel

end NCG
