/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Interacting-regulator feedback memory
  (`thm:interacting-feedback-memory`, Gran-Tensor manuscript)

* `interacting_feedback_memory`: for the enlarged transfer
  `T̃ = [[A,B],[C,D]]`, the old-support compression
  `X_n = (T̃ⁿ)₁₁` satisfies `X₀ = I` and the boxed memory
  recursion `X_{n+1} = A·X_n + Σ_{j<n} K_{n-1-j}·X_j` with the
  boxed kernel `K_k = B·Dᵏ·C`; and the old raw-time process is
  exactly Markov (`X_n = Aⁿ`) when all memory kernels vanish.

Rendering disclosed: the generating-function resolvent identity
`Σ X_n zⁿ = [I - zA - z²B(I-zD)⁻¹C]⁻¹` is the power-series
packaging of the proved recursion; the converse Markov direction
and the Hankel-rank clause are the manuscript's remaining
finite-data clauses.
-/

open Matrix

namespace NCG

/-- `thm:interacting-feedback-memory`: the compression of the
enlarged transfer obeys the exact memory-kernel recursion. -/
theorem interacting_feedback_memory {d e : Type*} [Fintype d]
    [Fintype e] [DecidableEq d] [DecidableEq e]
    (A : Matrix d d ℝ) (B : Matrix d e ℝ)
    (C : Matrix e d ℝ) (D : Matrix e e ℝ) :
    (((Matrix.fromBlocks A B C D) ^ 0).toBlocks₁₁ = 1)
    ∧ (∀ n : ℕ,
        ((Matrix.fromBlocks A B C D) ^ (n + 1)).toBlocks₁₁
        = A * ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
          + ∑ j ∈ Finset.range n,
              (B * D ^ (n - 1 - j) * C)
                * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁)
    ∧ ((∀ k : ℕ, B * D ^ k * C = 0) →
        ∀ n : ℕ,
          ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
            = A ^ n) := by
  have hX0 : ((Matrix.fromBlocks A B C D) ^ 0).toBlocks₁₁
      = (1 : Matrix d d ℝ) := by
    rw [pow_zero, ← Matrix.fromBlocks_one,
      Matrix.toBlocks_fromBlocks₁₁]
  have hb11 : ∀ n : ℕ,
      ((Matrix.fromBlocks A B C D) ^ (n + 1)).toBlocks₁₁
      = A * ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
        + B * ((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₁ := by
    intro n
    have hdec : (Matrix.fromBlocks A B C D) ^ n
        = Matrix.fromBlocks
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₂)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₁)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₂) :=
      (Matrix.fromBlocks_toBlocks _).symm
    rw [pow_succ']
    conv_lhs => rw [hdec]
    rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  have hb21 : ∀ n : ℕ,
      ((Matrix.fromBlocks A B C D) ^ (n + 1)).toBlocks₂₁
      = C * ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
        + D * ((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₁ := by
    intro n
    have hdec : (Matrix.fromBlocks A B C D) ^ n
        = Matrix.fromBlocks
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₂)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₁)
            (((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₂) :=
      (Matrix.fromBlocks_toBlocks _).symm
    rw [pow_succ']
    conv_lhs => rw [hdec]
    rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
  have hY : ∀ n : ℕ,
      ((Matrix.fromBlocks A B C D) ^ n).toBlocks₂₁
      = ∑ j ∈ Finset.range n,
          D ^ (n - 1 - j) * C
            * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁ := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, ← Matrix.fromBlocks_one,
          Matrix.toBlocks_fromBlocks₂₁, Finset.range_zero,
          Finset.sum_empty]
    | succ n ih =>
        rw [hb21 n, ih, Matrix.mul_sum, Finset.sum_range_succ]
        have hterm : ∀ j ∈ Finset.range n,
            D * (D ^ (n - 1 - j) * C
              * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁)
            = D ^ (n - j) * C
              * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁ := by
          intro j hj
          rw [Finset.mem_range] at hj
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
            ← pow_succ', show n - 1 - j + 1 = n - j from by
              omega]
        rw [Finset.sum_congr rfl hterm]
        have hlast : (n + 1) - 1 - n = 0 := by omega
        rw [hlast, pow_zero, Matrix.one_mul]
        have hexp : ∀ j ∈ Finset.range n,
            D ^ (n - j) * C
              * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁
            = D ^ ((n + 1) - 1 - j) * C
              * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁ := by
          intro j hj
          rw [Finset.mem_range] at hj
          rw [show (n + 1) - 1 - j = n - j from by omega]
        rw [Finset.sum_congr rfl hexp, add_comm]
  refine ⟨hX0, ?_, ?_⟩
  · intro n
    rw [hb11 n, hY n, Matrix.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc]
  · intro hzero n
    induction n with
    | zero => rw [hX0, pow_zero]
    | succ n ih =>
        rw [hb11 n, hY n, Matrix.mul_sum]
        have hvan : ∀ j ∈ Finset.range n,
            B * (D ^ (n - 1 - j) * C
              * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁)
            = 0 := by
          intro j _
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
          rw [show B * D ^ (n - 1 - j) * C = 0 from hzero _]
          rw [Matrix.zero_mul]
        rw [Finset.sum_congr rfl hvan, Finset.sum_const_zero,
          add_zero, ih, ← pow_succ']

end NCG
