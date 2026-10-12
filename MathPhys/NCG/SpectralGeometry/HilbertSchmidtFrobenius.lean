/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The squared Hilbert–Schmidt (Frobenius) norm of a complex matrix

Split out of `MathPhys.Spectralization.NaimarkPhaseSharpness` (its helper lemmas):

* `hsFrobSq A = Σ_{i,j} |A_ij|²`, nonnegative and vanishing exactly at `A = 0`;
* `hsFrobSq_add_le`: `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`;
* `hsFrobSq_eq_re_trace`: `‖A‖² = re tr(AᴴA)`;
* `hsFrobSq_mul_isometry_le`: right multiplication by an isometry does not increase it.
-/

open Matrix

open scoped InnerProductSpace

namespace MathPhys

/-- Squared Hilbert–Schmidt (Frobenius) norm of a complex matrix:
the sum of the squared moduli of its entries. -/
def hsFrobSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The squared Hilbert–Schmidt norm is nonnegative. -/
theorem hsFrobSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : 0 ≤ hsFrobSq A :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The squared Hilbert–Schmidt norm vanishes only on the zero
matrix. -/
theorem hsFrobSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hsFrobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg
        fun j _ => Complex.normSq_nonneg (A i j))).mp h i
      (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (A i j))).mp h1 j
      (Finset.mem_univ j)
    simpa [Matrix.zero_apply] using Complex.normSq_eq_zero.mp h2
  · intro h
    simp [hsFrobSq, h]

/-- Two-two comparison for the squared Hilbert–Schmidt norm:
`‖X + Y‖² ≤ 2‖X‖² + 2‖Y‖²`. -/
theorem hsFrobSq_add_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    hsFrobSq (A + B) ≤ 2 * hsFrobSq A + 2 * hsFrobSq B := by
  have key : ∀ z w : ℂ, Complex.normSq (z + w)
      ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
    intro z w
    simp only [Complex.normSq_apply, Complex.add_re,
      Complex.add_im]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  have h1 : hsFrobSq (A + B)
      ≤ ∑ i, ∑ j, (2 * Complex.normSq (A i j)
        + 2 * Complex.normSq (B i j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum
      fun j _ => ?_
    rw [Matrix.add_apply]
    exact key _ _
  have h2 : ∑ i, ∑ j, (2 * Complex.normSq (A i j)
      + 2 * Complex.normSq (B i j))
      = 2 * hsFrobSq A + 2 * hsFrobSq B := by
    simp only [hsFrobSq, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [h1, h2.le, h2.ge]

/-- The squared Hilbert–Schmidt norm as the real part of the trace
of the Gram square: `‖A‖² = re tr(AᴴA)`. -/
theorem hsFrobSq_eq_re_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    hsFrobSq A = (Matrix.trace (Aᴴ * A)).re := by
  have h1 : Matrix.trace (Aᴴ * A)
      = ∑ j, ∑ i, star (A i j) * A i j := by
    simp [Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diag]
  calc hsFrobSq A
      = ∑ j, ∑ i, Complex.normSq (A i j) := Finset.sum_comm
    _ = ∑ j, ∑ i, (star (A i j) * A i j).re := by
        refine Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm,
          show star (A i j) = (starRingEnd ℂ) (A i j) from rfl,
          Complex.mul_conj, Complex.ofReal_re]
    _ = (∑ j, ∑ i, star (A i j) * A i j).re := by
        simp [Complex.re_sum]
    _ = (Matrix.trace (Aᴴ * A)).re := by rw [h1]

/-- Whitened contraction: right multiplication by an isometry
(`VᴴV = 1`) does not increase the squared Hilbert–Schmidt norm. -/
theorem hsFrobSq_mul_isometry_le {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p]
    (X : Matrix m m ℂ) (V : Matrix m p ℂ) (hV : Vᴴ * V = 1) :
    hsFrobSq (X * V) ≤ hsFrobSq X := by
  have hPH : (V * Vᴴ)ᴴ = V * Vᴴ := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hQH : ((1 : Matrix m m ℂ) - V * Vᴴ)ᴴ
      = 1 - V * Vᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQQ : ((1 : Matrix m m ℂ) - V * Vᴴ)
      * ((1 : Matrix m m ℂ) - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hPP, sub_self, sub_zero]
  -- `‖XV‖² = re tr(VVᴴ · XᴴX)`
  have hXV : hsFrobSq (X * V)
      = (Matrix.trace ((V * Vᴴ) * (Xᴴ * X))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have e1 : (X * V)ᴴ * (X * V) = (Vᴴ * (Xᴴ * X)) * V := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  -- `‖X(1 - VVᴴ)‖² = re tr((1 - VVᴴ) · XᴴX)`
  have hXQ : hsFrobSq (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
      = (Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
          * (Xᴴ * X))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have e1 : (X * ((1 : Matrix m m ℂ) - V * Vᴴ))ᴴ
        * (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
        = (((1 : Matrix m m ℂ) - V * Vᴴ) * (Xᴴ * X))
          * ((1 : Matrix m m ℂ) - V * Vᴴ) := by
      rw [Matrix.conjTranspose_mul, hQH]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    calc Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
          * (((1 : Matrix m m ℂ) - V * Vᴴ) * (Xᴴ * X)))
        = Matrix.trace ((((1 : Matrix m m ℂ) - V * Vᴴ)
            * ((1 : Matrix m m ℂ) - V * Vᴴ)) * (Xᴴ * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((1 : Matrix m m ℂ) - V * Vᴴ)
            * (Xᴴ * X)) := by rw [hQQ]
  -- Pythagoras: the two pieces sum to `‖X‖²`
  have hsum : hsFrobSq (X * V)
      + hsFrobSq (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
      = hsFrobSq X := by
    rw [hXV, hXQ, hsFrobSq_eq_re_trace, ← Complex.add_re,
      ← Matrix.trace_add, ← Matrix.add_mul]
    congr 2
    abel_nf
    rw [Matrix.one_mul]
  have hnn := hsFrobSq_nonneg
    (X * ((1 : Matrix m m ℂ) - V * Vᴴ))
  linarith [hsum]

end MathPhys
