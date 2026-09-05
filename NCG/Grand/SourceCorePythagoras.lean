/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# Exact source-core Pythagorean comparison
  (`thm:source-core-Pythagoras`, Gran-Tensor manuscript)

* `source_core_pythagoras`: for an isometry `V` with range
  projection `P = VVᴴ` and the defect operators `R = NV - VA`,
  `L = (I-P)NV`, `C = VᴴNV - A`: the boxed orthogonal
  decomposition `R = L + VC` with `Ran L ⟂ Ran(VC)`, the boxed
  quadratic identity `RᴴR = LᴴL + CᴴC`, and the equivalence
  `R = 0 ↔ L = 0 ∧ C = 0` (zero leakage and zero compression
  mismatch iff exact intertwining).

Rendering disclosed: the comparison is rendered on finite
matrices (bounded operators); the unbounded graph-space
packaging `𝒟(A)_A` of the manuscript is its domain bookkeeping.
-/

open Matrix

namespace NCG

/-- `thm:source-core-Pythagoras`: the leakage/compression
splitting of the intertwining defect is exactly orthogonal. -/
theorem source_core_pythagoras {e h : Type*} [Fintype e]
    [Fintype h] [DecidableEq h] [DecidableEq e]
    (V : Matrix h e ℂ) (A : Matrix e e ℂ) (N : Matrix h h ℂ)
    (hV : Vᴴ * V = 1) :
    (N * V - V * A
      = (1 - V * Vᴴ) * (N * V) + V * (Vᴴ * N * V - A))
    ∧ ((1 - V * Vᴴ) * (N * V))ᴴ * (V * (Vᴴ * N * V - A)) = 0
    ∧ (N * V - V * A)ᴴ * (N * V - V * A)
      = ((1 - V * Vᴴ) * (N * V))ᴴ * ((1 - V * Vᴴ) * (N * V))
        + (Vᴴ * N * V - A)ᴴ * (Vᴴ * N * V - A)
    ∧ (N * V - V * A = 0
        ↔ (1 - V * Vᴴ) * (N * V) = 0
          ∧ Vᴴ * N * V - A = 0) := by
  have hPV : (1 - V * Vᴴ) * V = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV,
      Matrix.mul_one, sub_self]
  have hsplit : N * V - V * A
      = (1 - V * Vᴴ) * (N * V) + V * (Vᴴ * N * V - A) := by
    have hassoc : V * (Vᴴ * N * V) = V * Vᴴ * (N * V) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hassoc]
    abel
  have horth : ((1 - V * Vᴴ) * (N * V))ᴴ
      * (V * (Vᴴ * N * V - A)) = 0 := by
    have hherm : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    rw [Matrix.conjTranspose_mul, hherm]
    calc (N * V)ᴴ * (1 - V * Vᴴ) * (V * (Vᴴ * N * V - A))
        = (N * V)ᴴ * (((1 - V * Vᴴ) * V) * (Vᴴ * N * V - A))
          := by simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [hPV, Matrix.zero_mul, Matrix.mul_zero]
  have horth' : (V * (Vᴴ * N * V - A))ᴴ
      * ((1 - V * Vᴴ) * (N * V)) = 0 := by
    have hc := congrArg Matrix.conjTranspose horth
    simpa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using hc
  have hVC : (V * (Vᴴ * N * V - A))ᴴ * (V * (Vᴴ * N * V - A))
      = (Vᴴ * N * V - A)ᴴ * (Vᴴ * N * V - A) := by
    rw [Matrix.conjTranspose_mul]
    calc (Vᴴ * N * V - A)ᴴ * Vᴴ * (V * (Vᴴ * N * V - A))
        = (Vᴴ * N * V - A)ᴴ * (Vᴴ * V) * (Vᴴ * N * V - A)
          := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have hquad : (N * V - V * A)ᴴ * (N * V - V * A)
      = ((1 - V * Vᴴ) * (N * V))ᴴ * ((1 - V * Vᴴ) * (N * V))
        + (Vᴴ * N * V - A)ᴴ * (Vᴴ * N * V - A) := by
    conv_lhs => rw [hsplit]
    rw [Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, horth, horth', hVC]
    abel
  refine ⟨hsplit, horth, hquad, ?_, ?_⟩
  · intro h0
    have hzero : ((1 - V * Vᴴ) * (N * V))ᴴ
        * ((1 - V * Vᴴ) * (N * V))
        + (Vᴴ * N * V - A)ᴴ * (Vᴴ * N * V - A) = 0 := by
      rw [← hquad, h0, Matrix.conjTranspose_zero,
        Matrix.mul_zero]
    have htr := congrArg (fun M => (Matrix.trace M).re) hzero
    rw [Matrix.trace_add] at htr
    simp only [Complex.add_re, Matrix.trace_zero,
      Complex.zero_re] at htr
    have h1 : 0 ≤ ((((1 - V * Vᴴ) * (N * V))ᴴ
        * ((1 - V * Vᴴ) * (N * V))).trace).re := by
      rw [trace_conj_self_re]
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h2 : 0 ≤ (((Vᴴ * N * V - A)ᴴ
        * (Vᴴ * N * V - A)).trace).re := by
      rw [trace_conj_self_re]
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    constructor
    · exact (trace_conj_self_re_eq_zero _).mp (by linarith)
    · exact (trace_conj_self_re_eq_zero _).mp (by linarith)
  · rintro ⟨hL, hC⟩
    rw [hsplit, hL, hC, Matrix.mul_zero, add_zero]

end NCG
