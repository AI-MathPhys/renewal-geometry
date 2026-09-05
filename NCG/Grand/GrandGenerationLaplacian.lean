/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# The generation Laplacian and flavour rigidity
  (`thm:SM-generation-Laplacian`, Gran-Tensor manuscript)

* `sm_generation_laplacian`: for Hermitian residue squares
  `A, B`, the generation Laplacian
  `𝓛(X) = [A,[A,X]] + [B,[B,X]]` satisfies the energy identity
  `tr(X*𝓛X) = ‖[A,X]‖² + ‖[B,X]‖²` (so `𝓛 ⪰ 0`), and the boxed
  kernel identification `Ker 𝓛 = {A,B}'` — the zero eigenspace
  reconstructs the exact surviving generation algebra.

Rendering disclosed: the quantitative flavour-rigidity margin
(the first positive eigenvalue bound) reads off the energy
identity by the spectral gap of the positive superoperator and
is the manuscript's remaining bookkeeping.
-/

open Matrix

namespace NCG

/-- `thm:SM-generation-Laplacian`: energy identity and the
boxed kernel identification `Ker 𝓛 = {A,B}'`. -/
theorem sm_generation_laplacian {n : Type*} [Fintype n]
    (A B X : Matrix n n ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ((Xᴴ * ((A * (A * X - X * A) - (A * X - X * A) * A)
        + (B * (B * X - X * B) - (B * X - X * B) * B))).trace
      = ((A * X - X * A)ᴴ * (A * X - X * A)).trace
        + ((B * X - X * B)ᴴ * (B * X - X * B)).trace)
    ∧ ((A * (A * X - X * A) - (A * X - X * A) * A)
        + (B * (B * X - X * B) - (B * X - X * B) * B) = 0
      ↔ (A * X = X * A ∧ B * X = X * B)) := by
  have key : ∀ (C D : Matrix n n ℂ),
      Dᴴ = Xᴴ * C - C * Xᴴ →
      (Xᴴ * (C * D - D * C)).trace = (Dᴴ * D).trace := by
    intro C D hDH
    rw [hDH, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
      Matrix.trace_sub]
    congr 1
    · rw [← Matrix.mul_assoc]
    · rw [show Xᴴ * (D * C) = (Xᴴ * D) * C from by
        rw [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hmain : (Xᴴ * ((A * (A * X - X * A) - (A * X - X * A) * A)
      + (B * (B * X - X * B) - (B * X - X * B) * B))).trace
      = ((A * X - X * A)ᴴ * (A * X - X * A)).trace
        + ((B * X - X * B)ᴴ * (B * X - X * B)).trace := by
    rw [Matrix.mul_add, Matrix.trace_add,
      key A (A * X - X * A) (by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, hA]),
      key B (B * X - X * B) (by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, hB])]
  refine ⟨hmain, ?_, ?_⟩
  · intro h0
    have htr : (Xᴴ * ((A * (A * X - X * A) - (A * X - X * A) * A)
        + (B * (B * X - X * B) - (B * X - X * B) * B))).trace
        = 0 := by
      rw [h0, Matrix.mul_zero, Matrix.trace_zero]
    rw [hmain] at htr
    have hre := congrArg Complex.re htr
    rw [Complex.add_re, Complex.zero_re] at hre
    have hAnn : 0 ≤ (((A * X - X * A)ᴴ
        * (A * X - X * A)).trace).re := by
      rw [trace_conj_self_re]
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hBnn : 0 ≤ (((B * X - X * B)ᴴ
        * (B * X - X * B)).trace).re := by
      rw [trace_conj_self_re]
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : (((A * X - X * A)ᴴ
        * (A * X - X * A)).trace).re = 0 := by linarith
    have h2 : (((B * X - X * B)ᴴ
        * (B * X - X * B)).trace).re = 0 := by linarith
    exact ⟨sub_eq_zero.mp ((trace_conj_self_re_eq_zero _).mp h1),
      sub_eq_zero.mp ((trace_conj_self_re_eq_zero _).mp h2)⟩
  · rintro ⟨h1, h2⟩
    rw [show A * X - X * A = 0 from sub_eq_zero.mpr h1,
      show B * X - X * B = 0 from sub_eq_zero.mpr h2,
      Matrix.mul_zero, Matrix.zero_mul, sub_zero,
      Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero]

end NCG
