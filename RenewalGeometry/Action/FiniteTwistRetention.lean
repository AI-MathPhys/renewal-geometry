/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact endpoint-twist retention under finite blocking
(`thm:main-no-blocking-attractor`, closing sentence, first half; `eq:supp-finite-twist-read`)

On a finite positive amplitude alphabet `F ⊂ (0, ∞)`, a twisted kernel
`L_C(x, y) = e^{C x²/ε} L₀(x, y) e^{-C y²/ε}` with symmetric positive untwisted kernel `L₀`
is diagonally similar to `L₀`: `L_C = D_C L₀ D_C⁻¹`, hence `L_Cⁿ = D_C L₀ⁿ D_C⁻¹` for every
number `n` of blocked intervals, and for `x ≠ y`
`ε/(2(x² - y²)) · log (L_Cⁿ(x, y) / L_Cⁿ(y, x)) = C`  (`finite_twist_retention`).
-/

open Matrix

namespace RenewalGeometry

namespace FiniteTwistRetention

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by a diagonal matrix with inverse diagonal commutes with powers. -/
theorem diag_conj_pow (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) (L : Matrix ι ι ℝ) (n : ℕ) :
    (diagonal d * L * diagonal (fun i => (d i)⁻¹)) ^ n
      = diagonal d * L ^ n * diagonal (fun i => (d i)⁻¹) := by
  have hinv : diagonal (fun i => (d i)⁻¹) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd i)
  have hinv' : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i)
  induction n with
  | zero => simp [hinv']
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc diagonal d * L ^ k * diagonal (fun i => (d i)⁻¹) *
          (diagonal d * L * diagonal (fun i => (d i)⁻¹))
        = diagonal d * L ^ k * (diagonal (fun i => (d i)⁻¹) * diagonal d) * L *
          diagonal (fun i => (d i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- Powers of an entrywise positive matrix are entrywise positive. -/
theorem pow_pos_entries [Nonempty ι] (L : Matrix ι ι ℝ) (hL : ∀ i j, 0 < L i j) (n : ℕ)
    (hn : 1 ≤ n) (i j : ι) : 0 < (L ^ n) i j := by
  induction n, hn using Nat.le_induction generalizing i j with
  | base => simpa using hL i j
  | succ k _ ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_pos (fun z _ => mul_pos (ih i z) (hL z j)) Finset.univ_nonempty

/-- **`eq:supp-finite-twist-read`.**  Let `F` be a finite set of positive amplitudes, `ε ≠ 0`,
`L₀` a symmetric kernel on `F` with positive entries, and `L_C = D_C L₀ D_C⁻¹` with
`D_C = diag(e^{C x²/ε})`.  Then for every `n ≥ 1` blocked intervals `L_Cⁿ = D_C L₀ⁿ D_C⁻¹`, and
for distinct amplitudes `x ≠ y` the measured endpoint twist is exactly `C`. -/
theorem finite_twist_retention (F : Finset ℝ) (hF : ∀ x ∈ F, 0 < x) (ε C : ℝ) (hε : ε ≠ 0)
    (L₀ : Matrix F F ℝ) (hsym : L₀ᵀ = L₀) (hpos : ∀ x y, 0 < L₀ x y) (n : ℕ) (hn : 1 ≤ n) :
    (diagonal (fun x : F => Real.exp (C * (x : ℝ) ^ 2 / ε)) * L₀ *
        diagonal (fun x : F => (Real.exp (C * (x : ℝ) ^ 2 / ε))⁻¹)) ^ n
      = diagonal (fun x : F => Real.exp (C * (x : ℝ) ^ 2 / ε)) * L₀ ^ n *
        diagonal (fun x : F => (Real.exp (C * (x : ℝ) ^ 2 / ε))⁻¹) ∧
    ∀ x y : F, x ≠ y →
      ε / (2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
        Real.log (((diagonal (fun x : F => Real.exp (C * (x : ℝ) ^ 2 / ε)) * L₀ *
            diagonal (fun x : F => (Real.exp (C * (x : ℝ) ^ 2 / ε))⁻¹)) ^ n) x y /
          ((diagonal (fun x : F => Real.exp (C * (x : ℝ) ^ 2 / ε)) * L₀ *
            diagonal (fun x : F => (Real.exp (C * (x : ℝ) ^ 2 / ε))⁻¹)) ^ n) y x) = C := by
  set d : F → ℝ := fun x => Real.exp (C * (x : ℝ) ^ 2 / ε)
  have hd : ∀ x, d x ≠ 0 := fun x => (Real.exp_pos _).ne'
  have hpow := diag_conj_pow d hd L₀ n
  refine ⟨hpow, fun x y hxy => ?_⟩
  have : Nonempty F := ⟨x⟩
  rw [hpow]
  have hPsym : (L₀ ^ n) y x = (L₀ ^ n) x y := by
    rw [← Matrix.transpose_apply (L₀ ^ n), Matrix.transpose_pow, hsym]
  have hP := pow_pos_entries L₀ hpos n hn x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hPsym]
  have hx2 : (x : ℝ) ^ 2 ≠ (y : ℝ) ^ 2 := by
    intro h
    apply hxy
    apply Subtype.ext
    have hx := hF x x.2
    have hy := hF y y.2
    nlinarith [sq_nonneg ((x : ℝ) - y), sq_nonneg ((x : ℝ) + y)]
  have hratio : d x * (L₀ ^ n) x y * (d y)⁻¹ / (d y * (L₀ ^ n) x y * (d x)⁻¹)
      = Real.exp (2 * C * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2) / ε) := by
    simp only [d]
    rw [← Real.exp_neg, ← Real.exp_neg]
    field_simp
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hratio, Real.log_exp]
  have hsub : (x : ℝ) ^ 2 - (y : ℝ) ^ 2 ≠ 0 := sub_ne_zero.2 hx2
  field_simp
