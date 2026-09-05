/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MultiplicityGenerationSaturation
import NCG.Grand.SMSTCommutant

/-!
# Writer--Casimir Gram and multiplicity saturation

This file removes the former all-matrices commutation interface.  The
writer--Casimir defect is the finite sum of Hilbert--Schmidt squares of the
commutators with the matrix-unit generators of the faithful right M2 action.
Its vanishing is proved equivalent to commutation with the whole action.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace NCG
namespace MultiplicityCasimirSaturationAssembly

/-- Finite writer--Casimir commutator Gram for the right M2 action. -/
noncomputable def writerCasimirGram
    {M : Type*} [Fintype M] [DecidableEq M]
    (T : Matrix (M × Fin 2) (M × Fin 2) ℂ) : ℝ :=
  ∑ p : Fin 2, ∑ q : Fin 2,
    quiverHSSq
      (((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1) * T -
        T * ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1))

/-- Vanishing of the positive writer--Casimir Gram is exactly commutation
with every matrix-unit generator. -/
theorem writerCasimirGram_eq_zero_iff_matrixUnits
    {M : Type*} [Fintype M] [DecidableEq M]
    (T : Matrix (M × Fin 2) (M × Fin 2) ℂ) :
    writerCasimirGram T = 0 ↔
      ∀ p q : Fin 2,
        ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1) * T =
          T * ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1) := by
  constructor
  · intro h p q
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => Finset.sum_nonneg fun q _ =>
        quiverHSSq_nonneg _)).mp h p (Finset.mem_univ p)
    have hq := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => quiverHSSq_nonneg _)).mp hp q (Finset.mem_univ q)
    exact sub_eq_zero.mp ((quiverHSSq_eq_zero_iff _).mp hq)
  · intro h
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro q _
    rw [h p q, sub_self]
    simp [quiverHSSq]

/-- Matrix-unit commutation extends linearly to the complete right M2
action. -/
theorem commutes_full_right_action_of_matrixUnits
    {M : Type*} [Fintype M] [DecidableEq M]
    (T : Matrix (M × Fin 2) (M × Fin 2) ℂ)
    (hunit : ∀ p q : Fin 2,
      ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1) * T =
        T * ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single p q 1)) :
    ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      ((1 : Matrix M M ℂ) ⊗ₖ g) * T =
        T * ((1 : Matrix M M ℂ) ⊗ₖ g) := by
  intro g
  have hg : g =
      g 0 0 • Matrix.single 0 0 (1 : ℂ) +
      g 0 1 • Matrix.single 0 1 (1 : ℂ) +
      g 1 0 • Matrix.single 1 0 (1 : ℂ) +
      g 1 1 • Matrix.single 1 1 (1 : ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hg]
  simp only [Matrix.kronecker_add, Matrix.kronecker_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [hunit 0 0, hunit 0 1, hunit 1 0, hunit 1 1]

/-- Zero writer--Casimir Gram is equivalent to commutation with the complete
faithful right M2 action. -/
theorem writerCasimirGram_eq_zero_iff
    {M : Type*} [Fintype M] [DecidableEq M]
    (T : Matrix (M × Fin 2) (M × Fin 2) ℂ) :
    writerCasimirGram T = 0 ↔
      ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
        ((1 : Matrix M M ℂ) ⊗ₖ g) * T =
          T * ((1 : Matrix M M ℂ) ⊗ₖ g) := by
  constructor
  · intro h
    exact commutes_full_right_action_of_matrixUnits T
      ((writerCasimirGram_eq_zero_iff_matrixUnits T).mp h)
  · intro h
    apply (writerCasimirGram_eq_zero_iff_matrixUnits T).mpr
    intro p q
    exact h (Matrix.single p q 1)

/-- Complete copy--deformation separation and saturation, now derived from
the displayed positive writer--Casimir residual. -/
theorem multiplicity_saturation_from_writerCasimir
    {M : Type*} [Fintype M] [DecidableEq M]
    (T S : Matrix (M × Fin 2) (M × Fin 2) ℂ)
    (hT : writerCasimirGram T = 0)
    (hS : writerCasimirGram S = 0) :
    (∃ A B : Matrix M M ℂ,
      T = A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      S = B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ i j : ℕ,
        Sᴴ * ((Tᴴ) ^ i * (T ^ j * S)) =
          (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B))) ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∀ i j : ℕ,
        let A3 := A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
        let B3 := B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
        B3ᴴ * ((A3ᴴ) ^ i * (A3 ^ j * B3)) =
          (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B))) ⊗ₖ
            (1 : Matrix (Fin 3) (Fin 3) ℂ)))
    ∧ (∀ {h e1 e2 : ℕ}
      (S1 : Matrix (Fin h) (Fin e1) ℂ)
      (S2 : Matrix (Fin h) (Fin e2) ℂ),
      (S1ᴴ * S1).rank = 1 →
      (multiplicitySchurDefect S1 S2 = 0 ↔
        (Matrix.fromBlocks (S1ᴴ * S1) (S1ᴴ * S2)
          ((S1ᴴ * S2)ᴴ) (S2ᴴ * S2)).rank = 1)) := by
  refine ⟨multiplicityMatterGeneration_factorization T S
      ((writerCasimirGram_eq_zero_iff T).mp hT)
      ((writerCasimirGram_eq_zero_iff S).mp hS), ?_⟩
  intro h e1 e2 S1 S2 hrank
  exact oneGeneration_iff_rankOne_and_zeroSchurDefect S1 S2 hrank

end MultiplicityCasimirSaturationAssembly
end NCG
