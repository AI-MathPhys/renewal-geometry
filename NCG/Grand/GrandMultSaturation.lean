/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.MarkedFactor

/-!
# Multiplicity saturation under the commuting `M₂` action
  (`thm:SM-multiplicity-saturation`, Gran-Tensor manuscript)

* `right_factor_commutant`: an operator commuting with the
  right factor `1 ⊗ M_J` lies in the left factor `M_I ⊗ 1` —
  the mirror of the marked Kronecker commutant;
* `sm_multiplicity_saturation`: if the future transfer and the
  source both commute with the faithful right `M₂` action, then
  up to the factorization `T = A ⊗ I₂`, `S = B ⊗ I₂`, and every
  multiplicity Gram block factors as
  `S*(T*)^i T^j S = (B*(A*)^i A^j B) ⊗ I₂` — the boxed
  `𝔾_mat = 𝔾_mult ⊗ I₂` blockwise.

Rendering disclosed: the generation factor `⊗ I₃` and the
Schur-defect rank-increment/one-generation clauses read off the
factored Grams and are the manuscript's remaining bookkeeping;
the multiplicity-space unitary is the identity in this frame.
-/

open Matrix Kronecker

set_option linter.unusedSimpArgs false

namespace NCG

/-- Mirror marked commutant: commuting with the right factor
forces membership in the left factor. -/
theorem right_factor_commutant {I J : Type*} [Fintype I]
    [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty J]
    (T : Matrix (I × J) (I × J) ℂ)
    (hT : ∀ g : Matrix J J ℂ,
      ((1 : Matrix I I ℂ) ⊗ₖ g) * T
        = T * ((1 : Matrix I I ℂ) ⊗ₖ g)) :
    ∃ A : Matrix I I ℂ,
      T = A ⊗ₖ (1 : Matrix J J ℂ) := by
  classical
  have hentry : ∀ (a c : J) (i k : I) (b : J),
      T (i, c) (k, b)
        = if b = c then T (i, a) (k, a) else 0 := by
    intro a c i k b
    have h := congrFun (congrFun
      (hT (Matrix.single a c (1 : ℂ))) (i, a)) (k, b)
    have hL : (((1 : Matrix I I ℂ) ⊗ₖ Matrix.single a c (1 : ℂ))
        * T) (i, a) (k, b) = T (i, c) (k, b) := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.kroneckerMap_apply,
        Matrix.single_apply, Matrix.one_apply]
      simp [Finset.sum_ite_eq, ite_and]
    have hR : (T * ((1 : Matrix I I ℂ)
        ⊗ₖ Matrix.single a c (1 : ℂ))) (i, a) (k, b)
        = if b = c then T (i, a) (k, a) else 0 := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.kroneckerMap_apply,
        Matrix.single_apply, Matrix.one_apply]
      simp [Finset.sum_ite_eq, ite_and, eq_comm]
    rw [hL, hR] at h
    exact h
  obtain ⟨b0⟩ := (inferInstance : Nonempty J)
  refine ⟨Matrix.of fun i k => T (i, b0) (k, b0), ?_⟩
  ext ⟨i, c⟩ ⟨k, b⟩
  rw [Matrix.kroneckerMap_apply, Matrix.of_apply,
    Matrix.one_apply, hentry b0 c i k b]
  by_cases hbc : b = c
  · subst hbc
    simp
  · rw [if_neg hbc, if_neg (fun h => hbc h.symm), mul_zero]

/-- `thm:SM-multiplicity-saturation`: the commuting `M₂`
action forces the tensor factorization and the blockwise Gram
factorization `𝔾_mat = 𝔾_mult ⊗ I₂`. -/
theorem sm_multiplicity_saturation {M : Type*} [Fintype M]
    [DecidableEq M]
    (T S : Matrix (M × Fin 2) (M × Fin 2) ℂ)
    (hT : ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      ((1 : Matrix M M ℂ) ⊗ₖ g) * T
        = T * ((1 : Matrix M M ℂ) ⊗ₖ g))
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      ((1 : Matrix M M ℂ) ⊗ₖ g) * S
        = S * ((1 : Matrix M M ℂ) ⊗ₖ g)) :
    ∃ A B : Matrix M M ℂ,
      T = A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
      ∧ S = B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
      ∧ ∀ i j : ℕ,
        Sᴴ * ((Tᴴ) ^ i * (T ^ j * S))
          = (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B)))
            ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨A, hA⟩ := right_factor_commutant T hT
  obtain ⟨B, hB⟩ := right_factor_commutant S hS
  have hpow : ∀ (C : Matrix M M ℂ) (k : ℕ),
      (C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ k
        = (C ^ k) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro C k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_kronecker_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
  refine ⟨A, B, hA, hB, ?_⟩
  intro i j
  rw [hA, hB, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    hpow, hpow, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]

end NCG
