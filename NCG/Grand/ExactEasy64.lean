/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactEasy63

/-!
# Exact EASY 64: source-core Hamiltonian leakage

This file computes the compressed Hamiltonian derivative and the two
off-core commutator corners, then sums their matrix-unit Hilbert--Schmidt
weights to obtain the exact factor `2d`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Finset

namespace NCG

variable {d f : Type*} [Fintype d] [DecidableEq d]
  [Fintype f] [DecidableEq f]

lemma trace_isometry_sandwich (C : Matrix f d ℂ)
    (hC : Cᴴ * C = 1) (Z : Matrix d d ℂ) :
    Matrix.trace (C * Z * Cᴴ) = Matrix.trace Z := by
  calc
    Matrix.trace (C * Z * Cᴴ)
        = Matrix.trace (C * (Z * Cᴴ)) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace ((Z * Cᴴ) * C) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Z * (Cᴴ * C)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace Z := by rw [hC, Matrix.mul_one]

lemma trace_sandwich (B : Matrix f d ℂ) (Z : Matrix d d ℂ) :
    Matrix.trace (B * Z * Bᴴ) = Matrix.trace (Z * (Bᴴ * B)) := by
  calc
    Matrix.trace (B * Z * Bᴴ)
        = Matrix.trace (B * (Z * Bᴴ)) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace ((Z * Bᴴ) * B) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Z * (Bᴴ * B)) := by rw [Matrix.mul_assoc]

lemma corner_matrix_unit_hs (B C : Matrix f d ℂ)
    (hC : Cᴴ * C = 1) (hCB : Cᴴ * B = 0) (a b : d) :
    hsFrobSq
        (B * Matrix.single a b (1 : ℂ) * Cᴴ
          - C * Matrix.single a b (1 : ℂ) * Bᴴ)
      = ((Bᴴ * B) a a).re + ((Bᴴ * B) b b).re := by
  let Eab : Matrix d d ℂ := Matrix.single a b 1
  let Eba : Matrix d d ℂ := Matrix.single b a 1
  have hEstar : Eabᴴ = Eba := by simp [Eab, Eba, Matrix.conjTranspose_single]
  have hBC : Bᴴ * C = 0 := by
    have h := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul] using h
  have hXX : Matrix.trace ((B * Eab * Cᴴ)ᴴ * (B * Eab * Cᴴ))
      = (Bᴴ * B) a a := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hEstar]
    simp only [Matrix.mul_assoc]
    have hsand : Matrix.trace
        (C * (Eba * (Bᴴ * B) * Eab) * Cᴴ)
          = Matrix.trace (Eba * (Bᴴ * B) * Eab) :=
      trace_isometry_sandwich C hC _
    calc
      Matrix.trace (C * (Eba * (Bᴴ * (B * (Eab * Cᴴ)))))
          = Matrix.trace (C * (Eba * (Bᴴ * B) * Eab) * Cᴴ) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Eba * (Bᴴ * B) * Eab) := hsand
      _ = (Bᴴ * B) a a := by
        simp only [Eba, Eab]
        rw [Matrix.single_mul_mul_single]
        simp
  have hYY : Matrix.trace ((C * Eab * Bᴴ)ᴴ * (C * Eab * Bᴴ))
      = (Bᴴ * B) b b := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hEstar]
    simp only [Matrix.mul_assoc]
    calc
      Matrix.trace (B * (Eba * (Cᴴ * (C * (Eab * Bᴴ)))))
          = Matrix.trace (B * (Eba * Eab) * Bᴴ) := by
              congr 1
              rw [← Matrix.mul_assoc Cᴴ C (Eab * Bᴴ), hC]
              simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = Matrix.trace ((Eba * Eab) * (Bᴴ * B)) := trace_sandwich B _
      _ = (Bᴴ * B) b b := by
        simp only [Eba, Eab]
        rw [Matrix.single_mul_single_same]
        simp [Matrix.trace_single_mul]
  have hXY : Matrix.trace ((B * Eab * Cᴴ)ᴴ * (C * Eab * Bᴴ)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hEstar]
    calc
      Matrix.trace (C * (Eba * Bᴴ) * (C * Eab * Bᴴ))
          = Matrix.trace (C * Eba * (Bᴴ * C) * Eab * Bᴴ) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBC]; simp
  have hYX : Matrix.trace ((C * Eab * Bᴴ)ᴴ * (B * Eab * Cᴴ)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hEstar]
    calc
      Matrix.trace (B * (Eba * Cᴴ) * (B * Eab * Cᴴ))
          = Matrix.trace (B * Eba * (Cᴴ * B) * Eab * Cᴴ) := by
              congr 1
              simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCB]; simp
  rw [hsFrobSq_eq_re_trace]
  rw [Matrix.conjTranspose_sub]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hXX, hXY, hYX, hYY]
  simp

theorem corner_commutator_hs_sum (B C : Matrix f d ℂ)
    (hC : Cᴴ * C = 1) (hCB : Cᴴ * B = 0) :
    ∑ a : d, ∑ b : d, hsFrobSq
        (B * (Matrix.single a b (1 : ℂ) : Matrix d d ℂ) * Cᴴ
          - C * (Matrix.single a b (1 : ℂ) : Matrix d d ℂ) * Bᴴ)
      = 2 * Fintype.card d * hsFrobSq B := by
  simp_rw [corner_matrix_unit_hs (d := d) (f := f) B C hC hCB]
  have hdiag : ∑ a, ((Bᴴ * B) a a).re = hsFrobSq B := by
    rw [hsFrobSq_eq_re_trace]
    simp [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hdiag]
  ring

def sourceCoreIota (C : Matrix f d ℂ) (X : Matrix d d ℂ) : Matrix f f ℂ :=
  C * X * Cᴴ

def hamiltonianDerivative {n : Type*} [Fintype n]
    (H X : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • (H * X - X * H)

def sourceCoreK (H : Matrix f f ℂ) (C : Matrix f d ℂ) : Matrix d d ℂ :=
  Cᴴ * H * C

def sourceCoreB (H : Matrix f f ℂ) (C : Matrix f d ℂ) : Matrix f d ℂ :=
  (1 - C * Cᴴ) * H * C

def channelCoreResidual (H : Matrix f f ℂ) (C : Matrix f d ℂ)
    (X : Matrix d d ℂ) : Matrix f f ℂ :=
  hamiltonianDerivative H (sourceCoreIota C X)
    - sourceCoreIota C (hamiltonianDerivative (sourceCoreK H C) X)

def channelCoreDefectSq (H : Matrix f f ℂ) (C : Matrix f d ℂ) : ℝ :=
  ∑ a : d, ∑ b : d, hsFrobSq
    (channelCoreResidual H C (Matrix.single a b (1 : ℂ)))

lemma hsFrobSq_smul (z : ℂ) (A : Matrix f f ℂ) :
    hsFrobSq (z • A) = Complex.normSq z * hsFrobSq A := by
  simp [hsFrobSq, Complex.normSq_mul, Finset.mul_sum]

theorem compressed_hamiltonian_derivative (H : Matrix f f ℂ)
    (C : Matrix f d ℂ) (hC : Cᴴ * C = 1) (X : Matrix d d ℂ) :
    Cᴴ * hamiltonianDerivative H (sourceCoreIota C X) * C
      = hamiltonianDerivative (sourceCoreK H C) X := by
  simp only [hamiltonianDerivative, sourceCoreIota, sourceCoreK,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  simp [Matrix.mul_assoc, hC]
  rw [← Matrix.mul_assoc Cᴴ C (X * (Cᴴ * (H * C))), hC, Matrix.one_mul]

theorem sourceCoreB_orthogonal (H : Matrix f f ℂ) (C : Matrix f d ℂ)
    (hC : Cᴴ * C = 1) :
    Cᴴ * sourceCoreB H C = 0 := by
  simp only [sourceCoreB, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Cᴴ C (Cᴴ * (H * C)), hC, Matrix.one_mul, sub_self]

theorem channelCoreResidual_eq_corner (H : Matrix f f ℂ)
    (C : Matrix f d ℂ) (hC : Cᴴ * C = 1) (hH : Hᴴ = H)
    (X : Matrix d d ℂ) :
    channelCoreResidual H C X
      = (-Complex.I) •
          (sourceCoreB H C * X * Cᴴ - C * X * (sourceCoreB H C)ᴴ) := by
  have hBstar : (sourceCoreB H C)ᴴ
      = Cᴴ * H * (1 - C * Cᴴ) := by
    simp [sourceCoreB, Matrix.conjTranspose_mul, hH,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.mul_assoc]
  simp only [channelCoreResidual, hamiltonianDerivative, sourceCoreIota,
    sourceCoreK, hBstar, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub]
  congr 1
  simp only [sourceCoreB, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem channel_core_Pythagoras [Nonempty d]
    (H : Matrix f f ℂ) (C : Matrix f d ℂ)
    (hC : Cᴴ * C = 1) (hH : Hᴴ = H) :
    channelCoreDefectSq H C
      = 2 * Fintype.card d * hsFrobSq (sourceCoreB H C)
    ∧ (channelCoreDefectSq H C = 0 ↔ sourceCoreB H C = 0) := by
  have hCB := sourceCoreB_orthogonal H C hC
  have hsum := corner_commutator_hs_sum
    (sourceCoreB H C) C hC hCB
  have hformula : channelCoreDefectSq H C
      = 2 * Fintype.card d * hsFrobSq (sourceCoreB H C) := by
    rw [channelCoreDefectSq]
    simp_rw [channelCoreResidual_eq_corner H C hC hH]
    simp_rw [hsFrobSq_smul]
    simp only [Complex.normSq_neg, Complex.normSq_I, one_mul]
    exact hsum
  refine ⟨hformula, ?_⟩
  rw [hformula]
  constructor
  · intro hz
    have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
    have hhs : hsFrobSq (sourceCoreB H C) = 0 := by
      nlinarith [hsFrobSq_nonneg (sourceCoreB H C)]
    exact (hsFrobSq_eq_zero_iff _).mp hhs
  · intro hB
    simp [hB, hsFrobSq]

end NCG
