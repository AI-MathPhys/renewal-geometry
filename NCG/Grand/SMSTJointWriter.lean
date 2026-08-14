/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Joint writer covariance and the twelve connected angles
  (`thm:SMST-joint-writer-orientation`,
  Gran-Tensor manuscript)

* `smst_joint_writer_orientation`: the boxed SMW.5
  orientation count for the identity-connected real
  branch:
  (i) a `3×3` complex skew-hermitian orientation block is
      freely parameterized by its three imaginary diagonal
      parts and three above-diagonal complex entries —
      determined by them, and every choice is realized —
      exactly `3 + 2·3 = 9` real parameters;
  (ii) a `3×3` real skew-symmetric orientation block is
      freely parameterized by its three above-diagonal
      entries — exactly `3` parameters;
  (iii) so the continuous orientation space has dimension
      `9 + 3 = 12` — the boxed SMW.5 count.

The boxed SMW.4 polar splitting `W = UP` of the whitened
overlap with positive coherence modulus is the repo's
`NCG.polar_decomposition`; the zero-innovation reduction
to the square identity-connected branch and the boxed
SMW.6 infinitesimal connected writer
`Ω = ½M⁻¹(C₁ - C₁*)` (the skew part of the first-order
whitened overlap) are the manuscript's derivative layer.
-/

open Matrix

namespace NCG

/-- `thm:SMST-joint-writer-orientation` (the boxed SMW.5
parameter count). -/
theorem smst_joint_writer_orientation :
    -- (i) complex skew-hermitian block: determined by
    -- 9 real parameters …
    (∀ A B : Matrix (Fin 3) (Fin 3) ℂ,
      Aᴴ = -A → Bᴴ = -B →
      (∀ i, (A i i).im = (B i i).im) →
      A 0 1 = B 0 1 → A 0 2 = B 0 2 → A 1 2 = B 1 2 →
      A = B)
    -- … and every choice of them is realized
    ∧ (∀ (a : Fin 3 → ℝ) (z01 z02 z12 : ℂ),
        ∃ A : Matrix (Fin 3) (Fin 3) ℂ,
          Aᴴ = -A ∧ (∀ i, (A i i).im = a i)
          ∧ A 0 1 = z01 ∧ A 0 2 = z02 ∧ A 1 2 = z12)
    -- (ii) real skew-symmetric block: 3 free parameters
    ∧ (∀ A B : Matrix (Fin 3) (Fin 3) ℝ,
      Aᵀ = -A → Bᵀ = -B →
      A 0 1 = B 0 1 → A 0 2 = B 0 2 → A 1 2 = B 1 2 →
      A = B)
    ∧ (∀ w01 w02 w12 : ℝ,
        ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
          Aᵀ = -A ∧ A 0 1 = w01 ∧ A 0 2 = w02
          ∧ A 1 2 = w12)
    -- (iii) the boxed count 9 + 3 = 12
    ∧ (3 + 2 * 3 + 3 = 12) := by
  have hdiagC : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ),
      Mᴴ = -M → ∀ i, (M i i).re = 0 := by
    intro M hM i
    have h := congrFun (congrFun hM i) i
    simp only [Matrix.conjTranspose_apply,
      Matrix.neg_apply] at h
    have hre := congrArg Complex.re h
    simp only [Complex.star_def, Complex.conj_re,
      Complex.neg_re] at hre
    linarith
  have hoffC : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ),
      Mᴴ = -M → ∀ i j, M j i = -(starRingEnd ℂ)
        (M i j) := by
    intro M hM i j
    have h := congrFun (congrFun hM j) i
    simp only [Matrix.conjTranspose_apply,
      Matrix.neg_apply] at h
    -- h : star (M i j) = -(M j i)
    have h2 := congrArg Neg.neg h
    rw [neg_neg] at h2
    -- h2 : -(star (M i j)) = M j i
    exact h2.symm
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro A B hA hB hdiag h01 h02 h12
    have hAB : ∀ i, A i i = B i i := by
      intro i
      have hre := (hdiagC A hA i).trans
        (hdiagC B hB i).symm
      exact Complex.ext hre (hdiag i)
    ext i j
    rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
        ∨ x = 2) i with rfl | rfl | rfl <;>
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
        ∨ x = 2) j with rfl | rfl | rfl <;>
      first
        | exact hAB _
        | assumption
        | (rw [hoffC A hA, hoffC B hB]
           first
             | rw [h01] | rw [h02] | rw [h12])
  · intro a z01 z02 z12
    refine ⟨Matrix.of
      ![![Complex.I * a 0, z01, z02],
        ![-(starRingEnd ℂ) z01, Complex.I * a 1, z12],
        ![-(starRingEnd ℂ) z02, -(starRingEnd ℂ) z12,
          Complex.I * a 2]], ?_, ?_, ?_, ?_, ?_⟩
    · ext i j
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) j with rfl | rfl | rfl <;>
        norm_num [Matrix.conjTranspose_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Complex.ext_iff, Complex.star_def,
          Complex.conj_re, Complex.conj_im,
          Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    · intro i
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Complex.ext_iff]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Complex.ext_iff]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Complex.ext_iff]
  · intro A B hA hB h01 h02 h12
    have hdiagR : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
        Mᵀ = -M → ∀ i, M i i = 0 := by
      intro M hM i
      have h := congrFun (congrFun hM i) i
      simp only [Matrix.transpose_apply,
        Matrix.neg_apply] at h
      linarith
    have hoffR : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
        Mᵀ = -M → ∀ i j, M j i = -(M i j) := by
      intro M hM i j
      have h := congrFun (congrFun hM j) i
      simp only [Matrix.transpose_apply,
        Matrix.neg_apply] at h
      linarith
    ext i j
    rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
        ∨ x = 2) i with rfl | rfl | rfl <;>
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
        ∨ x = 2) j with rfl | rfl | rfl <;>
      first
        | (rw [hdiagR A hA, hdiagR B hB])
        | assumption
        | (rw [hoffR A hA, hoffR B hB]
           first
             | rw [h01] | rw [h02] | rw [h12])
  · intro w01 w02 w12
    refine ⟨Matrix.of ![![0, w01, w02],
      ![-w01, 0, w12], ![-w02, -w12, 0]], ?_, ?_, ?_,
      ?_⟩
    · ext i j
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) j with rfl | rfl | rfl <;>
        norm_num [Matrix.transpose_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.neg_apply]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.of_apply]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.of_apply]
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.of_apply]

end NCG
