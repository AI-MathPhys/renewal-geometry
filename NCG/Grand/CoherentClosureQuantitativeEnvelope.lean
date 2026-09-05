/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoherentClosure

/-!
# Quantitative envelope for reducing coherent closure

The exact coherent-source factorization lives in `CoherentClosure`.  This file
supplies the explicit entire-series estimate used by the quantitative clause of
`thm:SMST-reducing-coherent-closure`.
-/

open NormedSpace Matrix
open scoped Matrix

namespace NCG
namespace CoherentClosureQuantitativeEnvelope

/-- The scalar odd-factorial tail is bounded by the exponential majorant with
the manuscript's sharp elementary prefactor `x² / 6`. -/
theorem oddFactorialTail_le_expEnvelope (x : ℝ) (hx : 0 ≤ x) :
    ∑' k : ℕ, x ^ (2 * k + 2) / ((2 * k + 3).factorial : ℝ) ≤
      x ^ 2 * Real.exp x / 6 := by
  let f : ℕ → ℝ := fun n => x ^ n / (n.factorial : ℝ)
  let g : ℕ → ℝ := fun k => x ^ (2 * k + 2) /
    ((2 * k + 3).factorial : ℝ)
  have hf : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial x
  have hfi : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) hab
  have heven : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective hfi
  have hfac (k : ℕ) :
      (6 : ℝ) * ((2 * k).factorial : ℝ) ≤
        ((2 * k + 3).factorial : ℝ) := by
    norm_cast
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega,
      Nat.factorial_succ,
      show 2 * k + 2 = (2 * k + 1) + 1 by omega,
      Nat.factorial_succ,
      show 2 * k + 1 = 2 * k + 1 by rfl,
      Nat.factorial_succ]
    calc
      6 * (2 * k).factorial ≤
          ((2 * k + 3) * (2 * k + 2) * (2 * k + 1)) *
            (2 * k).factorial := by
        apply Nat.mul_le_mul_right
        calc
          6 = 3 * 2 * 1 := by norm_num
          _ ≤ (2 * k + 3) * (2 * k + 2) * (2 * k + 1) := by
            exact Nat.mul_le_mul
              (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = (2 * k + 3) * ((2 * k + 2) *
          ((2 * k + 1) * (2 * k).factorial)) := by ring
  have hterm (k : ℕ) :
      g k ≤ (x ^ 2 / 6) * f (2 * k) := by
    have hnum : 0 ≤ x ^ 2 * x ^ (2 * k) := by positivity
    have hden : (0 : ℝ) < 6 * ((2 * k).factorial : ℝ) := by positivity
    calc
      g k = (x ^ 2 * x ^ (2 * k)) /
          ((2 * k + 3).factorial : ℝ) := by
        simp [g, pow_add]
        ring
      _ ≤ (x ^ 2 * x ^ (2 * k)) /
          (6 * ((2 * k).factorial : ℝ)) :=
        div_le_div_of_nonneg_left hnum hden (hfac k)
      _ = (x ^ 2 / 6) * f (2 * k) := by
        simp [f]
        ring
  have hg_nonneg (k : ℕ) : 0 ≤ g k := by
    simp [g]
    positivity
  have hbound_nonneg (k : ℕ) : 0 ≤ (x ^ 2 / 6) * f (2 * k) := by
    simp [f]
    positivity
  have hbound : Summable (fun k : ℕ => (x ^ 2 / 6) * f (2 * k)) :=
    heven.mul_left _
  have hg : Summable g :=
    Summable.of_nonneg_of_le hg_nonneg hterm hbound
  calc
    ∑' k : ℕ, x ^ (2 * k + 2) / ((2 * k + 3).factorial : ℝ) =
        ∑' k, g k := by rfl
    _ ≤ ∑' k, (x ^ 2 / 6) * f (2 * k) :=
      hg.tsum_le_tsum hterm hbound
    _ = (x ^ 2 / 6) * ∑' k, f (2 * k) := by
      rw [tsum_mul_left]
    _ ≤ (x ^ 2 / 6) * ∑' n, f n := by
      exact mul_le_mul_of_nonneg_left
        (tsum_comp_le_tsum_of_inj hf (fun n => by
          simp [f]; positivity) hfi) (by positivity)
    _ = x ^ 2 * Real.exp x / 6 := by
      rw [show (∑' n, f n) = Real.exp x by
        rw [Real.exp_eq_exp_ℝ]
        simpa [f] using (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq]
      ring

/-- Explicit Banach-algebra estimate for the coherent writer
`W_t = Σ t²ᵏ a²ᵏ/(2k+1)!`:
`‖W_t-I‖ ≤ t² M² exp(tM)/6`. -/
theorem coherentWriter_sub_one_norm_le
    {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (a W : A) (t M : ℝ) (ht : 0 ≤ t) (ha : ‖a‖ ≤ M)
    (hW : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
        a ^ (2 * k)) W) :
    ‖W - 1‖ ≤ t ^ 2 * M ^ 2 * Real.exp (t * M) / 6 := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  let u : ℕ → A := fun k =>
    (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
      a ^ (2 * k)
  have hu0 : u 0 = 1 := by simp [u]
  have hdecomp := hW.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hdecomp
  have hWsub : W - 1 = ∑' k : ℕ, u (k + 1) := by
    have hdecompW := hdecomp.trans hW.tsum_eq
    rw [← hdecompW]
    simp [u]
  have hterm (k : ℕ) :
      ‖u (k + 1)‖ ≤
        (t * M) ^ (2 * k + 2) / ((2 * k + 3).factorial : ℝ) := by
    simp only [u, norm_smul, Real.norm_eq_abs]
    have hcoeff : 0 ≤
        t ^ (2 * (k + 1)) /
          (((2 * (k + 1) + 1).factorial : ℝ)) := by positivity
    rw [abs_of_nonneg hcoeff]
    have hpow : ‖a‖ ^ (2 * (k + 1)) ≤ M ^ (2 * (k + 1)) :=
      pow_le_pow_left₀ (norm_nonneg a) ha (2 * (k + 1))
    have hnormpow : ‖a ^ (2 * (k + 1))‖ ≤
        ‖a‖ ^ (2 * (k + 1)) := norm_pow_le _ _
    calc
      (t ^ (2 * (k + 1)) /
          (((2 * (k + 1) + 1).factorial : ℝ))) *
          ‖a ^ (2 * (k + 1))‖ ≤
        (t ^ (2 * (k + 1)) /
          (((2 * (k + 1) + 1).factorial : ℝ))) *
          ‖a‖ ^ (2 * (k + 1)) := by gcongr
      _ ≤
        (t ^ (2 * (k + 1)) /
          (((2 * (k + 1) + 1).factorial : ℝ))) *
          M ^ (2 * (k + 1)) := by gcongr
      _ = (t * M) ^ (2 * k + 2) /
          ((2 * k + 3).factorial : ℝ) := by
        have hn : 2 * (k + 1) = 2 * k + 2 := by omega
        have hfac : 2 * k + 2 + 1 = 2 * k + 3 := by omega
        rw [hn, hfac, mul_pow]
        ring
  have hscalar : Summable (fun k : ℕ =>
      (t * M) ^ (2 * k + 2) / ((2 * k + 3).factorial : ℝ)) := by
    have hfull := Real.summable_pow_div_factorial (t * M)
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 2) := by
      intro a b hab
      have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
      exact Nat.mul_left_cancel (by omega) hmul
    have hraw : Summable (fun k : ℕ =>
        (t * M) ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) := by
      simpa [Function.comp_def] using hfull.comp_injective hinj
    apply Summable.of_nonneg_of_le
      (fun k => by positivity)
      (fun k => ?_) hraw
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.factorial_le (by omega : 2 * k + 2 ≤ 2 * k + 3)
  have hunorm : Summable (fun k : ℕ => ‖u (k + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hscalar
  calc
    ‖W - 1‖ = ‖∑' k : ℕ, u (k + 1)‖ := by rw [hWsub]
    _ ≤ ∑' k : ℕ, ‖u (k + 1)‖ :=
      norm_tsum_le_tsum_norm hunorm
    _ ≤ ∑' k : ℕ,
        (t * M) ^ (2 * k + 2) / ((2 * k + 3).factorial : ℝ) :=
      hunorm.tsum_le_tsum hterm hscalar
    _ ≤ (t * M) ^ 2 * Real.exp (t * M) / 6 :=
      oddFactorialTail_le_expEnvelope (t * M) (mul_nonneg ht hM)
    _ = t ^ 2 * M ^ 2 * Real.exp (t * M) / 6 := by ring

/-- The residual factorization used in the Schur comparison is a genuine Gram
identity, not merely the distributive identity `BW - B = B(W-I)`. -/
theorem coherentSourceResidual_gram_factorization
    {h e : Type*} [Fintype h] [Fintype e] [DecidableEq e]
    (B : Matrix h e ℂ) (W : Matrix e e ℂ) :
    (B * W - B)ᴴ * (B * W - B) =
      (W - 1)ᴴ * (Bᴴ * B) * (W - 1) := by
  have hres : B * W - B = B * (W - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [hres, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end CoherentClosureQuantitativeEnvelope
end NCG
