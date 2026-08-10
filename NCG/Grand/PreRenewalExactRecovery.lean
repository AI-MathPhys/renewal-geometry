/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PreRenewalRecovery
import NCG.Grand.UniversalFeedbackMemory

/-!
# Exact visible pre-renewal recovery

This module completes `thm:pre-renewal-visible-recovery`: the recursive
reconstruction from compressed block powers is upgraded to an if-and-only-if
no-return criterion, the infinite kernel test is reduced to the hidden
dimension by Cayley--Hamilton, and the analytic generating-function identity
is re-exported on its natural Neumann-series domain.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- Cayley--Hamilton reduces the complex returned-kernel test to the first
`dim E` powers. -/
theorem preRenewalKernelReduction {d e : Type*}
    [Fintype e] [DecidableEq e]
    (B : Matrix d e ℂ) (C : Matrix e d ℂ) (D : Matrix e e ℂ)
    (hlow : ∀ k < Fintype.card e, B * D ^ k * C = 0) :
    ∀ k : ℕ, B * D ^ k * C = 0 := by
  set n := Fintype.card e with hn
  have hCH : D ^ n = ∑ i ∈ Finset.range n,
      (-(D.charpoly.coeff i)) • D ^ i := by
    have h0 := D.aeval_self_charpoly
    have hdeg : D.charpoly.natDegree = n := D.charpoly_natDegree_eq_dim
    have hsum := Polynomial.aeval_eq_sum_range
      (S := Matrix e e ℂ) (p := D.charpoly) D
    rw [h0, hdeg, Finset.sum_range_succ] at hsum
    have hmonic : D.charpoly.coeff n = 1 := by
      have hm := D.charpoly_monic
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hdeg] at hm
      exact hm
    rw [hmonic, one_smul] at hsum
    have h1 : D ^ n = -(∑ i ∈ Finset.range n,
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
        rw [show B * (D ^ (k - n) * D ^ i) * C =
            B * D ^ (k - n + i) * C from by rw [← pow_add]]
        rw [ih (k - n + i) (by omega), smul_zero]

/-- Exact no-return criterion for complex block transfers, including the
finite hidden-dimension test. -/
theorem preRenewalNoReturnIff {d e : Type*} [Fintype d]
    [Fintype e] [DecidableEq d] [DecidableEq e]
    (T0 A : Matrix d d ℂ) (B : Matrix d e ℂ)
    (C : Matrix e d ℂ) (D : Matrix e e ℂ) :
    ((∀ n : ℕ,
        ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁ = T0 ^ n)
      ↔ (A = T0 ∧ ∀ k : ℕ, B * D ^ k * C = 0))
    ∧ ((A = T0 ∧ ∀ k < Fintype.card e, B * D ^ k * C = 0) →
        ∀ n : ℕ,
          ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁ = T0 ^ n) := by
  let X : ℕ → Matrix d d ℂ := fun n =>
    ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁
  have hrec := (pre_renewal_visible_recovery A B C D).2.1
  have hsuff := (pre_renewal_visible_recovery A B C D).2.2
  have hX0 : X 0 = 1 := by
    dsimp [X]
    rw [pow_zero, ← Matrix.fromBlocks_one,
      Matrix.toBlocks_fromBlocks₁₁]
  constructor
  · constructor
    · intro hX
      have hA : A = T0 := by
        calc
          A = X 1 := (pre_renewal_visible_recovery A B C D).1.symm
          _ = T0 := by simpa [X] using hX 1
      subst T0
      refine ⟨rfl, ?_⟩
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
          have hkrec := hrec k
          have hsum : (∑ j ∈ Finset.range (k + 1),
              B * D ^ (k - j) * C * X j) = B * D ^ k * C := by
            rw [Finset.sum_eq_single 0
              (fun j hj hj0 => by
                rw [Finset.mem_range] at hj
                rw [ih (k - j) (by omega), Matrix.zero_mul])
              (fun hzero => absurd
                (Finset.mem_range.mpr (Nat.succ_pos k)) hzero)]
            rw [Nat.sub_zero, hX0, Matrix.mul_one]
          change X (k + 2) = A * X (k + 1) +
            ∑ j ∈ Finset.range (k + 1),
              B * D ^ (k - j) * C * X j at hkrec
          rw [hsum] at hkrec
          have hx2 : X (k + 2) = A ^ (k + 2) := by
            simpa [X] using hX (k + 2)
          have hx1 : X (k + 1) = A ^ (k + 1) := by
            simpa [X] using hX (k + 1)
          rw [hx2, hx1] at hkrec
          have hpow : A * A ^ (k + 1) = A ^ (k + 2) :=
            (pow_succ' A (k + 1)).symm
          rw [hpow] at hkrec
          have hz := congrArg (fun M => M - A ^ (k + 2)) hkrec
          simp only [sub_self, add_sub_cancel_left] at hz
          exact hz.symm
    · rintro ⟨rfl, hker⟩ n
      exact hsuff hker n
  · rintro ⟨rfl, hlow⟩ n
    exact hsuff (preRenewalKernelReduction B C D hlow) n

/-- Analytic form of the manuscript's formal generating-function identity. -/
theorem preRenewalGeneratingFunction {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (A : Matrix d d ℂ) (B : Matrix d e ℂ)
    (C : Matrix e d ℂ) (D : Matrix e e ℂ) (z : ℂ)
    (hT : ‖z • Matrix.fromBlocks A B C D‖ < 1)
    (hD : ‖z • D‖ < 1) :
    (∑' n : ℕ, z ^ n •
        ((Matrix.fromBlocks A B C D) ^ n).toBlocks₁₁) =
      (1 - z • A - z ^ 2 • (B * (1 - z • D)⁻¹ * C))⁻¹ :=
  feedback_resolvent_series A B C D z hT hD

end NCG
