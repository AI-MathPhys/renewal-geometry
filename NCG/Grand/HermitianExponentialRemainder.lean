/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Sharp second-order remainder for Hermitian exponential lines

Along a skew-adjoint line the exponential is unitary, hence has norm one.
Integrating its derivative once gives the sharp Lipschitz bound and integrating
the resulting first-order error a second time gives the factor `1 / 2`.
-/

namespace NCG

open Set
open MeasureTheory
open scoped Interval

noncomputable section

section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

private lemma real_smul_mem_skewAdjoint (x : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    s • x ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff] at hx ⊢
  simp [hx]

private lemma norm_exp_real_smul_skewAdjoint (x : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    ‖NormedSpace.exp (s • x)‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary
    (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (real_smul_mem_skewAdjoint x hx s))

/-- The exponential of a skew-adjoint element is one-Lipschitz along its real
one-parameter group. -/
theorem norm_exp_real_smul_skew_sub_one_le
    (x : A) (hx : x ∈ skewAdjoint A) (q : ℝ) (hq : 0 ≤ q) :
    ‖NormedSpace.exp (q • x) - 1‖ ≤ q * ‖x‖ := by
  let f : ℝ → A := fun s => NormedSpace.exp (s • x)
  let f' : ℝ → A := fun s => NormedSpace.exp (s • x) * x
  have hderiv : ∀ s ∈ uIcc 0 q, HasDerivAt f (f' s) s := by
    intro s hs
    exact hasDerivAt_exp_smul_const x s
  have hint : IntervalIntegrable f' volume 0 q := by
    apply Continuous.intervalIntegrable
    dsimp [f']
    exact (differentiable_exp_smul_const ℝ x).continuous.mul continuous_const
  have hfund : (∫ s in 0..q, f' s) = f q - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ‖NormedSpace.exp (q • x) - 1‖ = ‖∫ s in 0..q, f' s‖ := by rw [hfund]; simp [f]
    _ ≤ ‖x‖ * |q - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      change ‖NormedSpace.exp (s • x) * x‖ ≤ ‖x‖
      calc
        ‖NormedSpace.exp (s • x) * x‖ ≤
            ‖NormedSpace.exp (s • x)‖ * ‖x‖ := norm_mul_le _ _
        _ = ‖x‖ := by rw [norm_exp_real_smul_skewAdjoint x hx s, one_mul]
    _ = q * ‖x‖ := by rw [sub_zero, abs_of_nonneg hq, mul_comm]

/-- Sharp second-order Taylor remainder on a nonnegative skew-adjoint
one-parameter group. -/
theorem norm_exp_real_smul_skew_sub_one_sub_le_of_nonneg
    (x : A) (hx : x ∈ skewAdjoint A) (q : ℝ) (hq : 0 ≤ q) :
    ‖NormedSpace.exp (q • x) - 1 - q • x‖ ≤ q ^ 2 * ‖x‖ ^ 2 / 2 := by
  let f : ℝ → A := fun s => NormedSpace.exp (s • x)
  let f' : ℝ → A := fun s => NormedSpace.exp (s • x) * x
  have hderiv : ∀ s ∈ uIcc 0 q, HasDerivAt f (f' s) s := by
    intro s hs
    exact hasDerivAt_exp_smul_const x s
  have hint : IntervalIntegrable f' volume 0 q := by
    apply Continuous.intervalIntegrable
    dsimp [f']
    exact (differentiable_exp_smul_const ℝ x).continuous.mul continuous_const
  have hfund : (∫ s in 0..q, f' s) = f q - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hconst : IntervalIntegrable (fun _ : ℝ => x) volume 0 q := by
    apply Continuous.intervalIntegrable
    exact continuous_const
  have heq : NormedSpace.exp (q • x) - 1 - q • x =
      ∫ s in 0..q, (NormedSpace.exp (s • x) - 1) * x := by
    calc
      NormedSpace.exp (q • x) - 1 - q • x =
          (∫ s in 0..q, f' s) - ∫ _s in 0..q, x := by rw [hfund]; simp [f]
      _ = ∫ s in 0..q, f' s - x := (intervalIntegral.integral_sub hint hconst).symm
      _ = ∫ s in 0..q, (NormedSpace.exp (s • x) - 1) * x := by
        apply intervalIntegral.integral_congr
        intro s hs
        simp [f', sub_mul]
  calc
    ‖NormedSpace.exp (q • x) - 1 - q • x‖ =
        ‖∫ s in 0..q, (NormedSpace.exp (s • x) - 1) * x‖ := congrArg norm heq
    _ ≤ ∫ s in 0..q, s * ‖x‖ ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le hq
      · filter_upwards with s hs
        change ‖(NormedSpace.exp (s • x) - 1) * x‖ ≤ s * ‖x‖ ^ 2
        have hs0 : 0 ≤ s := hs.1.le
        calc
          ‖(NormedSpace.exp (s • x) - 1) * x‖ ≤
              ‖NormedSpace.exp (s • x) - 1‖ * ‖x‖ := norm_mul_le _ _
          _ ≤ (s * ‖x‖) * ‖x‖ :=
            mul_le_mul_of_nonneg_right
              (norm_exp_real_smul_skew_sub_one_le x hx s hs0) (norm_nonneg x)
          _ = s * ‖x‖ ^ 2 := by ring
      · apply Continuous.intervalIntegrable
        change Continuous (fun t : ℝ => t * ‖x‖ ^ 2)
        fun_prop
    _ = q ^ 2 * ‖x‖ ^ 2 / 2 := by
      simp only [intervalIntegral.integral_mul_const]
      rw [integral_id]
      ring

/-- Sharp second-order Taylor remainder for every real time. -/
theorem norm_exp_real_smul_skew_sub_one_sub_le
    (x : A) (hx : x ∈ skewAdjoint A) (t : ℝ) :
    ‖NormedSpace.exp (t • x) - 1 - t • x‖ ≤ |t| ^ 2 * ‖x‖ ^ 2 / 2 := by
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using
      norm_exp_real_smul_skew_sub_one_sub_le_of_nonneg x hx t ht
  · have hq : 0 ≤ -t := neg_nonneg.mpr ht
    have hneg : -x ∈ skewAdjoint A := (skewAdjoint A).neg_mem hx
    have h := norm_exp_real_smul_skew_sub_one_sub_le_of_nonneg (-x) hneg (-t) hq
    simpa [abs_of_nonpos ht, norm_neg] using h

end

end

end NCG
