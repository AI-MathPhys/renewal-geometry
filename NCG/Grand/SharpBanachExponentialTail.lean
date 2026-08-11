/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp Banach-algebra exponential tail

The norm of the exponential tail after its constant and linear terms is
bounded by the corresponding scalar exponential tail.
-/

namespace NCG

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The exact nonlinear tail after the constant and linear terms of the
Banach-algebra exponential. -/
noncomputable def exponentialLinearRemainder (x : A) : A :=
  NormedSpace.exp x - 1 - x

set_option maxHeartbeats 200000 in
-- Normalizing both Banach-algebra and scalar exponential tails uses nested tsums.
/-- The sharp exponential Taylor-tail estimate, valid in every complex Banach
algebra. -/
theorem norm_exponentialLinearRemainder_le (x : A) :
    ‖exponentialLinearRemainder x‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ := by
  let f : ℕ → A := fun n => ((n.factorial : ℂ)⁻¹) • x ^ n
  let g : ℕ → ℝ := fun n => ‖x‖ ^ n / n.factorial
  have hf : Summable f := NormedSpace.expSeries_summable' x
  have hfnorm : Summable (fun n => ‖f n‖) :=
    NormedSpace.norm_expSeries_summable' x
  have hg : Summable g := Real.summable_pow_div_factorial ‖x‖
  have htail : exponentialLinearRemainder x = ∑' n, f (n + 2) := by
    have hsplit := hf.sum_add_tsum_nat_add 2
    have htotal : ∑' n, f n = NormedSpace.exp x :=
      (NormedSpace.exp_series_hasSum_exp' x).tsum_eq
    rw [htotal] at hsplit
    have hfirst : ∑ i ∈ Finset.range 2, f i = 1 + x := by
      simp [f, Finset.sum_range_succ]
    rw [hfirst] at hsplit
    unfold exponentialLinearRemainder
    rw [← hsplit]
    abel
  have htailNorm : Summable (fun n => ‖f (n + 2)‖) :=
    (summable_nat_add_iff 2).2 hfnorm
  have htailScalar : Summable (fun n => g (n + 2)) :=
    (summable_nat_add_iff 2).2 hg
  have hterm : ∀ n, ‖f (n + 2)‖ ≤ g (n + 2) := by
    intro n
    dsimp only [f, g]
    rw [norm_smul]
    simp only [norm_inv, Complex.norm_natCast]
    rw [div_eq_inv_mul]
    gcongr
    exact norm_pow_le x (n + 2)
  have hscalarSplit := hg.sum_add_tsum_nat_add 2
  have hscalarTotal : ∑' n, g n = Real.exp ‖x‖ := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [htail]
  calc
    ‖∑' n, f (n + 2)‖ ≤ ∑' n, ‖f (n + 2)‖ :=
      norm_tsum_le_tsum_norm htailNorm
    _ ≤ ∑' n, g (n + 2) :=
      htailNorm.tsum_le_tsum hterm htailScalar
    _ = Real.exp ‖x‖ - 1 - ‖x‖ := by
      have hfirst : ∑ i ∈ Finset.range 2, g i = 1 + ‖x‖ := by
        norm_num [g, Finset.sum_range_succ]
      rw [hfirst, hscalarTotal] at hscalarSplit
      linarith

end NCG
