/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FeedbackMemory

/-!
# Universal feedback-memory theorem
  (`thm:universal-feedback-memory`, Gran-Tensor manuscript)

* `universal_feedback_memory`: the boxed exactness criterion —
  the compression is exactly the old process (`X_n = T₀ⁿ` for
  all `n`) **iff** `A = T₀` and every memory kernel
  `K_k = BDᵏC` vanishes.
* `feedback_kernel_reduction`: in finite external dimension it
  suffices to test `0 ≤ k < dim ℰ` (Cayley–Hamilton
  reduction).

Rendering disclosed: the memory recursion, `X₀ = I`, and the
sufficiency direction reuse `thm:interacting-feedback-memory`
(`NCG.interacting_feedback_memory`, proved); the Schur resolvent
series, the stabilized block-Hankel-rank minimality clause, and
the contraction norm estimate are the manuscript's power-series
and realization-theoretic packaging.
-/

open Matrix

namespace NCG

/-- Cayley–Hamilton reduction: kernels vanishing below the
external dimension vanish everywhere. -/
theorem feedback_kernel_reduction {d e : Type*}
    [Fintype e] [DecidableEq e]
    (B : Matrix d e ℝ) (C : Matrix e d ℝ) (D : Matrix e e ℝ)
    (hlow : ∀ k < Fintype.card e, B * D ^ k * C = 0) :
    ∀ k : ℕ, B * D ^ k * C = 0 := by
  set n := Fintype.card e with hn
  have hCH : D ^ n = ∑ i ∈ Finset.range n,
      (-(D.charpoly.coeff i)) • D ^ i := by
    have h0 := D.aeval_self_charpoly
    have hdeg : D.charpoly.natDegree = n :=
      D.charpoly_natDegree_eq_dim
    have hsum := Polynomial.aeval_eq_sum_range
      (S := Matrix e e ℝ) (p := D.charpoly) D
    rw [h0, hdeg, Finset.sum_range_succ] at hsum
    have hmonic : D.charpoly.coeff n = 1 := by
      have hm := D.charpoly_monic
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
        hdeg] at hm
      exact hm
    rw [hmonic, one_smul] at hsum
    have h1 : D ^ n
        = -(∑ i ∈ Finset.range n,
            D.charpoly.coeff i • D ^ i) := by
      linear_combination (norm := module) -hsum
    rw [h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_smul]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases hk : k < n
      · exact hlow k hk
      · have hk' : n ≤ k := le_of_not_gt hk
        have hkd : k = (k - n) + n := by omega
        rw [hkd, pow_add, hCH, Matrix.mul_sum, Matrix.mul_sum,
          Matrix.sum_mul]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
        rw [show B * (D ^ (k - n) * D ^ i) * C
            = B * D ^ (k - n + i) * C from by
          rw [← pow_add]]
        rw [ih (k - n + i) (by omega), smul_zero]

/-- `thm:universal-feedback-memory`: the exactness criterion
and its finite-dimension sufficiency. -/
theorem universal_feedback_memory {d e : Type*} [Fintype d]
    [Fintype e] [DecidableEq d] [DecidableEq e]
    (T0 A : Matrix d d ℝ) (B : Matrix d e ℝ)
    (C : Matrix e d ℝ) (D : Matrix e e ℝ) :
    ((∀ n : ℕ,
        ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁ = T0 ^ n)
      ↔ (A = T0 ∧ ∀ k : ℕ, B * D ^ k * C = 0))
    ∧ ((A = T0 ∧ ∀ k < Fintype.card e, B * D ^ k * C = 0) →
        ∀ n : ℕ,
          ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
            = T0 ^ n) := by
  have hfull : ∀ (hA : A = T0)
      (hker : ∀ k : ℕ, B * D ^ k * C = 0) (n : ℕ),
      ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁ = T0 ^ n := by
    rintro rfl hker n
    exact (interacting_feedback_memory A B C D).2.2 hker n
  constructor
  · constructor
    · intro hX
      obtain ⟨hX0, hrec, -⟩ :=
        interacting_feedback_memory A B C D
      have hA : A = T0 := by
        have h1 := hrec 0
        rw [hX0, Matrix.mul_one, Finset.range_zero,
          Finset.sum_empty, add_zero] at h1
        rw [← h1, hX 1, pow_one]
      subst hA
      refine ⟨rfl, ?_⟩
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
          have h2 := hrec (k + 1)
          have hsum : (∑ j ∈ Finset.range (k + 1),
              (B * D ^ (k + 1 - 1 - j) * C)
                * ((Matrix.fromBlocks A B C D) ^ j).toBlocks₁₁)
              = B * D ^ k * C := by
            rw [Finset.sum_eq_single 0
              (fun j hj hj0 => by
                rw [Finset.mem_range] at hj
                rw [show k + 1 - 1 - j = k - j from by omega,
                  ih (k - j) (by omega), Matrix.zero_mul])
              (fun h0 => absurd
                (Finset.mem_range.mpr (Nat.succ_pos k)) h0)]
            rw [show k + 1 - 1 - 0 = k from by omega, hX0,
              Matrix.mul_one]
          rw [hsum, hX (k + 2), hX (k + 1)] at h2
          have hpow : A * A ^ (k + 1) = A ^ (k + 2) :=
            (pow_succ' A (k + 1)).symm
          rw [hpow] at h2
          have h3 := congrArg (fun M => M - A ^ (k + 2)) h2
          simp only [sub_self, add_sub_cancel_left] at h3
          exact h3.symm
    · rintro ⟨rfl, hker⟩ n
      exact hfull rfl hker n
  · rintro ⟨rfl, hlow⟩ n
    exact hfull rfl (feedback_kernel_reduction B C D hlow) n

end NCG
