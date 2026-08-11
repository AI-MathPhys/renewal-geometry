/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordConcrete
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Concrete generator-level Schur certificate for the exceptional S4 panel

A transposition and a four-cycle generate `S₄`.  This file uses orthonormal
models of the `[31]`, `[211]`, and `[22]` irreducibles and solves the resulting
matrix intertwiner equations explicitly.  The sign twist exchanges `[4]` with
`[1⁴]`, exchanges `[31]` with `[211]`, and fixes `[22]` through `iJ`.
-/

open Matrix

namespace NCG
namespace ExceptionalS4GeneratorSchurCertificate

noncomputable section

open CommonOrigin

/-- A transposition on the tetrahedral standard triplet `[31]`. -/
def standardTransposition : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, 0, -1], ![0, -1, 0]]

/-- A four-cycle on the tetrahedral standard triplet `[31]`. -/
def standardFourCycle : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 1], ![0, -1, 0], ![-1, 0, 0]]

/-- A transposition on the two-dimensional pairing irrep `[22]`. -/
def pairingTransposition : Matrix (Fin 2) (Fin 2) ℂ :=
  -pauli3

/-- A four-cycle descends to a reflection on the three pairings. -/
def pairingFourCycle : Matrix (Fin 2) (Fin 2) ℂ :=
  ((2 : ℂ)⁻¹) • pauli3 - (Complex.sqrt 3 / 2) • pauli1

/-- Fixed Hermitian sign-twist intertwiner on `[22]`. -/
def pairingSignTwist : Matrix (Fin 2) (Fin 2) ℂ :=
  -pauli2

theorem pairingSignTwist_hermitian : pairingSignTwistᴴ = pairingSignTwist := by
  simp [pairingSignTwist, pauli2_herm]

theorem pairingSignTwist_sq : pairingSignTwist * pairingSignTwist = 1 := by
  simp [pairingSignTwist, pauli2_sq]

theorem pairingSignTwist_anticommutes_transposition :
    pairingTransposition * pairingSignTwist =
      -(pairingSignTwist * pairingTransposition) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num [pairingTransposition, pairingSignTwist, pauli2, pauli3,
    Matrix.neg_apply]

theorem pairingSignTwist_anticommutes_fourCycle :
    pairingFourCycle * pairingSignTwist =
      -(pairingSignTwist * pairingFourCycle) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [pairingFourCycle, pairingSignTwist, pauli1, pauli2, pauli3,
    Matrix.neg_apply]
  all_goals ring

private lemma matrixEntry {m n : Type*} (A B : Matrix m n ℂ)
    (h : A = B) (i : m) (j : n) : A i j = B i j :=
  congrFun (congrFun h i) j

private lemma sqrtThree_ne_zero : Complex.sqrt 3 ≠ 0 := by
  rw [sqrt_eq_exp (by norm_num : (3 : ℂ) ≠ 0)]
  exact Complex.exp_ne_zero _

/-- The standard triplet has no nonzero vector fixed by both generators. -/
theorem standard_fixedColumn_zero
    (A : Matrix (Fin 3) (Fin 1) ℂ)
    (_hS : standardTransposition * A = A)
    (hR : standardFourCycle * A = A) :
    A = 0 := by
  have h1 : A 1 0 = 0 := by
    have h := matrixEntry _ _ hR 1 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h20 : A 2 0 = A 0 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h02 : -A 0 0 = A 2 0 := by
    have h := matrixEntry _ _ hR 2 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h0 : A 0 0 = 0 := by
    linear_combination (-1 / 2 : ℂ) * h20 + (-1 / 2 : ℂ) * h02
  have h2 : A 2 0 = 0 := by linear_combination h20 + h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/-- The standard triplet has no nonzero covector fixed by both generators. -/
theorem standard_fixedRow_zero
    (A : Matrix (Fin 1) (Fin 3) ℂ)
    (_hS : A * standardTransposition = A)
    (hR : A * standardFourCycle = A) :
    A = 0 := by
  have h1 : A 0 1 = 0 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h20 : -A 0 2 = A 0 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h02 : A 0 0 = A 0 2 := by
    have h := matrixEntry _ _ hR 0 2
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h0 : A 0 0 = 0 := by
    linear_combination (-1 / 2 : ℂ) * h20 + (1 / 2 : ℂ) * h02
  have h2 : A 0 2 = 0 := by linear_combination -h02 + h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/-- The standard triplet has no common negative-eigenvalue vector. -/
theorem standard_antiFixedColumn_zero
    (A : Matrix (Fin 3) (Fin 1) ℂ)
    (hS : standardTransposition * A = -A)
    (hR : standardFourCycle * A = -A) :
    A = 0 := by
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination (1 / 2 : ℂ) * h
  have h2 : A 2 0 = 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two, h0] at h
    exact h
  have h1 : A 1 0 = 0 := by
    have h := matrixEntry _ _ hS 2 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two, h2] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/-- The standard triplet has no common negative-eigenvalue covector. -/
theorem standard_antiFixedRow_zero
    (A : Matrix (Fin 1) (Fin 3) ℂ)
    (hS : A * standardTransposition = -A)
    (hR : A * standardFourCycle = -A) :
    A = 0 := by
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination (1 / 2 : ℂ) * h
  have h2 : A 0 2 = 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two, h0] at h
    exact h
  have h1 : A 0 1 = 0 := by
    have h := matrixEntry _ _ hS 0 2
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two, h2] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/-- The pairing doublet has no nonzero vector fixed by both generators. -/
theorem pairing_fixedColumn_zero
    (A : Matrix (Fin 2) (Fin 1) ℂ)
    (hS : pairingTransposition * A = A)
    (hR : pairingFourCycle * A = A) :
    A = 0 := by
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h1 : A 1 0 = 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply, h0] at h
    exact h.resolve_left sqrtThree_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]

/-- The pairing doublet has no nonzero covector fixed by both generators. -/
theorem pairing_fixedRow_zero
    (A : Matrix (Fin 1) (Fin 2) ℂ)
    (hS : A * pairingTransposition = A)
    (hR : A * pairingFourCycle = A) :
    A = 0 := by
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h1 : A 0 1 = 0 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply, h0] at h
    exact h.resolve_right sqrtThree_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]

/-- The pairing doublet has no common negative-eigenvalue vector. -/
theorem pairing_antiFixedColumn_zero
    (A : Matrix (Fin 2) (Fin 1) ℂ)
    (hS : pairingTransposition * A = -A)
    (hR : pairingFourCycle * A = -A) :
    A = 0 := by
  have h1 : A 1 0 = 0 := by
    have h := matrixEntry _ _ hS 1 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (1 / 2 : ℂ) * h
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hR 1 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply, h1] at h
    exact h.resolve_left sqrtThree_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]

/-- The pairing doublet has no common negative-eigenvalue covector. -/
theorem pairing_antiFixedRow_zero
    (A : Matrix (Fin 1) (Fin 2) ℂ)
    (hS : A * pairingTransposition = -A)
    (hR : A * pairingFourCycle = -A) :
    A = 0 := by
  have h1 : A 0 1 = 0 := by
    have h := matrixEntry _ _ hS 0 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (1 / 2 : ℂ) * h
  have h0 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply, h1] at h
    exact h.resolve_right sqrtThree_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]

/-- There is no nonzero generator intertwiner from the standard triplet to
the pairing doublet. -/
theorem standard_to_pairing_intertwiner_zero
    (A : Matrix (Fin 2) (Fin 3) ℂ)
    (hS : pairingTransposition * A = A * standardTransposition)
    (hR : pairingFourCycle * A = A * standardFourCycle) :
    A = 0 := by
  have h00 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingTransposition, standardTransposition, pauli3,
      Matrix.cons_val_two] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hc : A 0 2 = A 0 1 := by
    have h := matrixEntry _ _ hS 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingTransposition, standardTransposition, pauli3,
      Matrix.cons_val_two] at h
    linear_combination -h
  have he : A 1 1 = -A 1 2 := by
    have h := matrixEntry _ _ hS 1 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingTransposition, standardTransposition, pauli3,
      Matrix.cons_val_two] at h
    exact h
  have hr0 : -(Complex.sqrt 3 / 2) * A 1 0 = -A 0 2 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingFourCycle, standardFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, h00] at h
    linear_combination -h
  have hr1 :
      (1 / 2 : ℂ) * A 0 1 + (Complex.sqrt 3 / 2) * A 1 2 =
        -A 0 1 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingFourCycle, standardFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, he] at h
    linear_combination h
  have hr2 :
      (1 / 2 : ℂ) * A 0 1 - (Complex.sqrt 3 / 2) * A 1 2 = 0 := by
    have h := matrixEntry _ _ hR 0 2
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at h
    norm_num [pairingFourCycle, standardFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, h00, hc] at h
    linear_combination h
  have hb : A 0 1 = 0 := by
    linear_combination (1 / 2 : ℂ) * hr1 + (1 / 2 : ℂ) * hr2
  have hf : A 1 2 = 0 := by
    apply (mul_left_cancel₀ sqrtThree_ne_zero)
    linear_combination -2 * hr2 + hb
  have hd : A 1 0 = 0 := by
    apply (mul_left_cancel₀ sqrtThree_ne_zero)
    linear_combination -2 * hr0 + 2 * hc + 2 * hb
  have hc0 : A 0 2 = 0 := by linear_combination hc + hb
  have he0 : A 1 1 = 0 := by linear_combination he - hf
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, hb, hc0, hd, he0, hf]

/-- There is no nonzero generator intertwiner from the pairing doublet to
the standard triplet. -/
theorem pairing_to_standard_intertwiner_zero
    (A : Matrix (Fin 3) (Fin 2) ℂ)
    (hS : standardTransposition * A = A * pairingTransposition)
    (hR : standardFourCycle * A = A * pairingFourCycle) :
    A = 0 := by
  have h00 : A 0 0 = 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardTransposition, pairingTransposition, pauli3,
      Matrix.cons_val_two] at h
    linear_combination (1 / 2 : ℂ) * h
  have he : A 2 0 = A 1 0 := by
    have h := matrixEntry _ _ hS 1 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardTransposition, pairingTransposition, pauli3,
      Matrix.cons_val_two] at h
    exact h
  have hd : A 1 1 = -A 2 1 := by
    have h := matrixEntry _ _ hS 1 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardTransposition, pairingTransposition, pauli3,
      Matrix.cons_val_two] at h
    exact h.symm
  have hr0 : A 2 0 = -(Complex.sqrt 3 / 2) * A 0 1 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardFourCycle, pairingFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, h00] at h
    linear_combination h
  have hr1 : A 2 1 = -(1 / 2 : ℂ) * A 0 1 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardFourCycle, pairingFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, h00] at h
    linear_combination h
  have hr10 :
      -A 1 0 = (1 / 2 : ℂ) * A 1 0 +
        (Complex.sqrt 3 / 2) * A 2 1 := by
    have h := matrixEntry _ _ hR 1 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] at h
    norm_num [standardFourCycle, pairingFourCycle, pauli1, pauli3,
      Matrix.smul_apply, Matrix.cons_val_two, hd] at h
    linear_combination h
  have hb : A 0 1 = 0 := by
    apply (mul_left_cancel₀ sqrtThree_ne_zero)
    linear_combination (-3 / 2 : ℂ) * he + (3 / 2 : ℂ) * hr0 +
      (Complex.sqrt 3 / 2) * hr1 + hr10
  have hc : A 1 0 = 0 := by
    linear_combination -he + hr0 - (Complex.sqrt 3 / 2) * hb
  have hd0 : A 1 1 = 0 := by
    linear_combination hd - hr1 + (1 / 2 : ℂ) * hb
  have he0 : A 2 0 = 0 := by
    linear_combination hr0 - (Complex.sqrt 3 / 2) * hb
  have hf : A 2 1 = 0 := by
    linear_combination hr1 - (1 / 2 : ℂ) * hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, hb, hc, hd0, he0, hf]

/-- The commutant of the two concrete `[31]` generators is the scalar line. -/
theorem standard_generator_commutant
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hS : standardTransposition * A = A * standardTransposition)
    (hR : standardFourCycle * A = A * standardFourCycle) :
    ∃ z : ℂ, A = z • 1 := by
  let z := A 0 0
  have s01 : A 0 1 = -A 0 2 := by
    have h := matrixEntry _ _ hS 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    exact h
  have s10 : -A 2 0 = A 1 0 := by
    have h := matrixEntry _ _ hS 1 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    exact h
  have s11 : A 2 1 = A 1 2 := by
    have h := matrixEntry _ _ hS 1 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    exact h
  have s12 : A 2 2 = A 1 1 := by
    have h := matrixEntry _ _ hS 1 2
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    exact h
  have r00 : A 2 0 = -A 0 2 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r01 : A 2 1 = -A 0 1 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r02 : A 2 2 = A 0 0 := by
    have h := matrixEntry _ _ hR 0 2
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r10 : A 1 0 = A 1 2 := by
    have h := matrixEntry _ _ hR 1 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r12 : -A 1 2 = A 1 0 := by
    have h := matrixEntry _ _ hR 1 2
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h12 : A 1 2 = 0 := by
    linear_combination (-1 / 2 : ℂ) * r10 + (-1 / 2 : ℂ) * r12
  have h21 : A 2 1 = 0 := by linear_combination s11 + h12
  have h10 : A 1 0 = 0 := by linear_combination r10 + h12
  have h20 : A 2 0 = 0 := by linear_combination -s10 - h10
  have h01 : A 0 1 = 0 := by linear_combination r01 - h21
  have h02 : A 0 2 = 0 := by linear_combination s01 - h01
  have h22 : A 2 2 = A 0 0 := r02
  have h11 : A 1 1 = A 0 0 := by linear_combination -s12 + h22
  refine ⟨z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [z, h12, h21, h10, h20, h01, h02, h22, h11]

/-- No nonzero endomorphism of the standard triplet intertwines its sign twist. -/
theorem standard_generator_anticommutant
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hS : standardTransposition * A = -(A * standardTransposition))
    (hR : standardFourCycle * A = -(A * standardFourCycle)) :
    A = 0 := by
  have s00 : A 0 0 = -A 0 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination h
  have s01 : A 0 1 = A 0 2 := by
    have h := matrixEntry _ _ hS 0 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination h
  have s10 : A 2 0 = A 1 0 := by
    have h := matrixEntry _ _ hS 1 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination h
  have s11 : A 2 1 = -A 1 2 := by
    have h := matrixEntry _ _ hS 1 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination -h
  have s12 : A 2 2 = -A 1 1 := by
    have h := matrixEntry _ _ hS 1 2
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardTransposition, Matrix.cons_val_two] at h
    linear_combination -h
  have r00 : A 2 0 = A 0 2 := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r01 : A 2 1 = A 0 1 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r02 : A 2 2 = -A 0 0 := by
    have h := matrixEntry _ _ hR 0 2
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have r10 : A 1 0 = -A 1 2 := by
    have h := matrixEntry _ _ hR 1 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    linear_combination -h
  have r12 : A 1 2 = A 1 0 := by
    have h := matrixEntry _ _ hR 1 2
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three] at h
    norm_num [standardFourCycle, Matrix.cons_val_two] at h
    exact h
  have h00 : A 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * s00
  have h10 : A 1 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * r10 - (1 / 2 : ℂ) * r12
  have h12 : A 1 2 = 0 := by linear_combination r12 + h10
  have h20 : A 2 0 = 0 := by linear_combination s10 + h10
  have h02 : A 0 2 = 0 := by linear_combination -r00 + h20
  have h01 : A 0 1 = 0 := by linear_combination s01 + h02
  have h21 : A 2 1 = 0 := by linear_combination r01 + h01
  have h22 : A 2 2 = 0 := by linear_combination r02 - h00
  have h11 : A 1 1 = 0 := by linear_combination s12 - h22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The sign-anticommutant of the pairing generators is exactly the iJ line. -/
theorem pairing_generator_anticommutant
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : pairingTransposition * A = -(A * pairingTransposition))
    (hR : pairingFourCycle * A = -(A * pairingFourCycle)) :
    ∃ z : ℂ, A = z • pairingSignTwist := by
  have s00 : -A 0 0 = A 0 0 := by
    have h := matrixEntry _ _ hS 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    exact h
  have s11 : A 1 1 = -A 1 1 := by
    have h := matrixEntry _ _ hS 1 1
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    exact h
  have r00 :
      (1 / 2 : ℂ) * A 0 0 - (Complex.sqrt 3 / 2) * A 1 0 =
        -((1 / 2 : ℂ) * A 0 0 - (Complex.sqrt 3 / 2) * A 0 1) := by
    have h := matrixEntry _ _ hR 0 0
    rw [Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply] at h
    linear_combination h
  have h00 : A 0 0 = 0 := by linear_combination (-1 / 2 : ℂ) * s00
  have h11 : A 1 1 = 0 := by linear_combination (1 / 2 : ℂ) * s11
  have hsqrt : Complex.sqrt 3 ≠ 0 := by
    rw [sqrt_eq_exp (by norm_num : (3 : ℂ) ≠ 0)]
    exact Complex.exp_ne_zero _
  have hsumScaled : (Complex.sqrt 3 / 2) * (A 1 0 + A 0 1) = 0 := by
    rw [h00] at r00
    linear_combination -r00
  have hscale : Complex.sqrt 3 / 2 ≠ 0 :=
    div_ne_zero hsqrt (by norm_num : (2 : ℂ) ≠ 0)
  have hsum : A 1 0 + A 0 1 = 0 :=
    (mul_eq_zero.mp hsumScaled).resolve_left hscale
  have h10 : A 1 0 = -A 0 1 := by exact eq_neg_of_add_eq_zero_left hsum
  have hI (x : ℂ) : Complex.I * x * Complex.I = -x := by
    calc
      Complex.I * x * Complex.I = (Complex.I * Complex.I) * x := by ring
      _ = -x := by rw [Complex.I_mul_I]; ring
  refine ⟨-Complex.I * A 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairingSignTwist, pauli2, Matrix.smul_apply,
      h00, h11, h10, hI]

/-- The commutant of the concrete pairing generators is the scalar line. -/
theorem pairing_generator_commutant
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : pairingTransposition * A = A * pairingTransposition)
    (hR : pairingFourCycle * A = A * pairingFourCycle) :
    ∃ z : ℂ, A = z • 1 := by
  have s01 : A 0 1 = 0 := by
    have h := matrixEntry _ _ hS 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (-1 / 2 : ℂ) * h
  have s10 : A 1 0 = 0 := by
    have h := matrixEntry _ _ hS 1 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two] at h
    norm_num [pairingTransposition, pauli3] at h
    linear_combination (1 / 2 : ℂ) * h
  have hsqrt : Complex.sqrt 3 ≠ 0 := by
    rw [sqrt_eq_exp (by norm_num : (3 : ℂ) ≠ 0)]
    exact Complex.exp_ne_zero _
  have r01 : A 0 0 = A 1 1 := by
    have h := matrixEntry _ _ hR 0 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two] at h
    norm_num [pairingFourCycle, pauli1, pauli3, Matrix.smul_apply,
      s01, s10] at h
    apply (mul_left_cancel₀ hsqrt)
    linear_combination -2 * h
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s01, s10, r01]

end
end ExceptionalS4GeneratorSchurCertificate
end NCG
