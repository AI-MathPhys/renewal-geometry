/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Visible recovery and exact no-return criterion
  (`thm:pre-renewal-visible-recovery`,
  Gran-Tensor manuscript)

* `pre_renewal_visible_recovery`: for the lift
  `T̃ = [[A,B],[C,D]]` with visible compressed powers
  `Xₙ = (T̃ⁿ)₁₁` and returned kernels `Kₙ = B·Dⁿ·C`:
  (i) `X₁ = A` (boxed);
  (ii) the boxed recursive recovery
      `X_{n+2} = A·X_{n+1} + Σ_{j≤n} K_{n-j}·X_j` — the
      visible powers determine every returned kernel;
  (iii) the exact no-return criterion: if every `Kₙ = 0`
      then `Xₙ = Aⁿ` for all `n` — an exact lift of the
      complete visible renewal cannot contain a hidden
      direction that leaves and later returns with active
      predictive information.
-/

open Matrix

namespace NCG

/-- `thm:pre-renewal-visible-recovery`. -/
theorem pre_renewal_visible_recovery {l e : Type*}
    [Fintype l] [Fintype e] [DecidableEq l] [DecidableEq e]
    (A : Matrix l l ℂ) (B : Matrix l e ℂ)
    (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    -- (i) the first visible power is `A`
    (fromBlocks A B C D ^ 1).toBlocks₁₁ = A
    -- (ii) the boxed recursive kernel recovery
    ∧ (∀ n : ℕ,
        (fromBlocks A B C D ^ (n + 2)).toBlocks₁₁
        = A * (fromBlocks A B C D ^ (n + 1)).toBlocks₁₁
          + ∑ j ∈ Finset.range (n + 1),
            B * D ^ (n - j) * C
              * (fromBlocks A B C D ^ j).toBlocks₁₁)
    -- (iii) exact no-return criterion
    ∧ ((∀ i : ℕ, B * D ^ i * C = 0) →
        ∀ n : ℕ,
          (fromBlocks A B C D ^ n).toBlocks₁₁ = A ^ n) := by
  -- block recursion for powers of the lift
  have hrec : ∀ n : ℕ,
      (fromBlocks A B C D ^ (n + 1)).toBlocks₁₁
        = A * (fromBlocks A B C D ^ n).toBlocks₁₁
          + B * (fromBlocks A B C D ^ n).toBlocks₂₁
      ∧ (fromBlocks A B C D ^ (n + 1)).toBlocks₂₁
        = C * (fromBlocks A B C D ^ n).toBlocks₁₁
          + D * (fromBlocks A B C D ^ n).toBlocks₂₁ := by
    intro n
    have h : fromBlocks A B C D ^ (n + 1)
        = fromBlocks A B C D * fromBlocks A B C D ^ n := by
      rw [pow_succ']
    constructor
    · rw [h, ← Matrix.fromBlocks_toBlocks
        (fromBlocks A B C D ^ n),
        Matrix.fromBlocks_multiply,
        Matrix.toBlocks_fromBlocks₁₁,
        Matrix.fromBlocks_toBlocks]
    · rw [h, ← Matrix.fromBlocks_toBlocks
        (fromBlocks A B C D ^ n),
        Matrix.fromBlocks_multiply,
        Matrix.toBlocks_fromBlocks₂₁,
        Matrix.fromBlocks_toBlocks]
  have hone : ((1 : Matrix (l ⊕ e) (l ⊕ e) ℂ)).toBlocks₁₁
      = 1 := by
    rw [← Matrix.fromBlocks_one,
      Matrix.toBlocks_fromBlocks₁₁]
  have honeZ : ((1 : Matrix (l ⊕ e) (l ⊕ e) ℂ)).toBlocks₂₁
      = 0 := by
    rw [← Matrix.fromBlocks_one,
      Matrix.toBlocks_fromBlocks₂₁]
  -- solve the lower-block recursion
  have hZ : ∀ n : ℕ,
      (fromBlocks A B C D ^ n).toBlocks₂₁
        = ∑ j ∈ Finset.range n,
          D ^ (n - 1 - j) * C
            * (fromBlocks A B C D ^ j).toBlocks₁₁ := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, honeZ, Finset.range_zero,
          Finset.sum_empty]
    | succ k ih =>
        rw [(hrec k).2, ih, Finset.sum_range_succ,
          Matrix.mul_sum]
        rw [add_comm
          (C * (fromBlocks A B C D ^ k).toBlocks₁₁)]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          have hjk : j < k := Finset.mem_range.mp hj
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
            show D * D ^ (k - 1 - j) = D ^ (k + 1 - 1 - j)
              from by
              rw [show k + 1 - 1 - j = (k - 1 - j) + 1 from
                by omega, pow_succ']]
        · rw [show k + 1 - 1 - k = 0 from by omega,
            pow_zero, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_one, Matrix.toBlocks_fromBlocks₁₁]
  · intro n
    rw [(hrec (n + 1)).1, hZ (n + 1)]
    congr 1
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [show n + 1 - 1 - j = n - j from by omega]
    simp only [Matrix.mul_assoc]
  · intro hK n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        match n with
        | 0 =>
            rw [pow_zero, hone, pow_zero]
        | 1 =>
            rw [pow_one, Matrix.toBlocks_fromBlocks₁₁,
              pow_one]
        | (m + 2) =>
            have hrec2 : (fromBlocks A B C D
                ^ (m + 2)).toBlocks₁₁
                = A * (fromBlocks A B C D
                    ^ (m + 1)).toBlocks₁₁
                  + ∑ j ∈ Finset.range (m + 1),
                    B * D ^ (m - j) * C
                      * (fromBlocks A B C D
                        ^ j).toBlocks₁₁ := by
              rw [(hrec (m + 1)).1, hZ (m + 1),
                Matrix.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [show m + 1 - 1 - j = m - j from by omega]
              simp only [Matrix.mul_assoc]
            rw [hrec2, ih (m + 1) (by omega)]
            rw [Finset.sum_eq_zero, add_zero, ← pow_succ']
            intro j _
            rw [hK (m - j), Matrix.zero_mul]

end NCG
