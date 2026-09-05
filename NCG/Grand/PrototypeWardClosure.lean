/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Prototype action to physical-time Ward closure
  (`cor:prototype-Ward-closure`, Gran-Tensor manuscript)

* `prototype_ward_closure` (l2 operator norm): the boxed
  finite dense-time comparison for the reconstructed
  prototype semigroup step `W` and the actual predictable
  mean step `K`:
  (i) `‖Kⁿ - Wⁿ‖ ≤ n·‖K - W‖` for contractions — so
      `‖K - W‖ = o(τ)` gives `‖K^{⌊t/τ⌋} - W^{⌊t/τ⌋}‖ → 0`
      uniformly on compact physical-time windows;
  (ii) the resolvent step `W = (1+τL)⁻¹` satisfies the exact
      defect identity `1 - W = τ·(L·W)` — the order-`τ`
      generator reading of the prototype action.

The Mosco-limit passage `K^{⌊t/τ⌋} → e^{-tL_∞}` is the
manuscript's continuum layer over these finite bounds.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `cor:prototype-Ward-closure`. -/
theorem prototype_ward_closure {E : Type*} [Fintype E]
    [DecidableEq E] (K W : Matrix E E ℂ)
    (hK : ‖K‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    -- (i) the dense-time comparison
    (∀ n : ℕ, ‖K ^ n - W ^ n‖ ≤ n * ‖K - W‖)
    -- (ii) the resolvent-step defect identity
    ∧ (∀ (τ : ℂ) (L : Matrix E E ℂ)
        (_ : Invertible (1 + τ • L)),
        1 - (1 + τ • L)⁻¹ = τ • (L * (1 + τ • L)⁻¹)) := by
  have hWj : ∀ j : ℕ, ‖W ^ j‖ ≤ 1 := by
    intro j
    induction j with
    | zero =>
        rcases isEmpty_or_nonempty E with hE | hE
        · rw [pow_zero,
            Subsingleton.elim (1 : Matrix E E ℂ) 0,
            norm_zero]
          norm_num
        · rw [pow_zero]
          exact le_of_eq CStarRing.norm_one
    | succ i ihi =>
        rw [pow_succ]
        calc ‖W ^ i * W‖ ≤ ‖W ^ i‖ * ‖W‖ :=
              Matrix.l2_opNorm_mul _ _
          _ ≤ 1 * 1 := mul_le_mul ihi hW
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
  constructor
  · intro n
    induction n with
    | zero => simp
    | succ j ih =>
        have hsplit : K ^ (j + 1) - W ^ (j + 1)
            = K * (K ^ j - W ^ j) + (K - W) * W ^ j := by
          rw [pow_succ' K, pow_succ' W]
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
        calc ‖K ^ (j + 1) - W ^ (j + 1)‖
            = ‖K * (K ^ j - W ^ j) + (K - W) * W ^ j‖ := by
              rw [hsplit]
          _ ≤ ‖K * (K ^ j - W ^ j)‖
              + ‖(K - W) * W ^ j‖ := norm_add_le _ _
          _ ≤ ‖K‖ * ‖K ^ j - W ^ j‖
              + ‖K - W‖ * ‖W ^ j‖ :=
              add_le_add (Matrix.l2_opNorm_mul _ _)
                (Matrix.l2_opNorm_mul _ _)
          _ ≤ 1 * (j * ‖K - W‖) + ‖K - W‖ * 1 := by
              apply add_le_add
              · exact mul_le_mul hK ih (norm_nonneg _)
                  zero_le_one
              · exact mul_le_mul_of_nonneg_left (hWj j)
                  (norm_nonneg _)
          _ = (j + 1 : ℕ) * ‖K - W‖ := by
              push_cast
              ring
  · intro τ L hinv
    have h1 : (1 + τ • L) * (1 + τ • L)⁻¹ = 1 :=
      Matrix.mul_inv_of_invertible _
    calc 1 - (1 + τ • L)⁻¹
        = (1 + τ • L) * (1 + τ • L)⁻¹
          - (1 + τ • L)⁻¹ := by rw [h1]
      _ = τ • (L * (1 + τ • L)⁻¹) := by
          rw [Matrix.add_mul, Matrix.one_mul,
            Matrix.smul_mul]
          abel

end NCG
