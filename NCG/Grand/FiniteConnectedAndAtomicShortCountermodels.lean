/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite connected-interaction and atomic-shorting countermodels

Structural matrix witnesses for `cth:GT-negative-connected-generator` and
`cth:GRH-atomic-short`.
-/

open Matrix

namespace NCG
namespace FiniteConnectedAndAtomicShortCountermodels

/-! ## A positive graded family with negative Möbius interaction -/

def firstSiteExcitation : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.diagonal (fun p ↦ if p.1 = 0 then 1 else 0)

def secondSiteExcitation : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.diagonal (fun p ↦ if p.2 = 0 then 1 else 0)

def twoSiteAction : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  firstSiteExcitation + secondSiteExcitation
    - firstSiteExcitation * secondSiteExcitation

def connectedInteraction : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  twoSiteAction - firstSiteExcitation - secondSiteExcitation

theorem graded_actions_posSemidef :
    firstSiteExcitation.PosSemidef ∧ secondSiteExcitation.PosSemidef
      ∧ twoSiteAction.PosSemidef := by
  refine ⟨Matrix.posSemidef_diagonal_iff.mpr ?_,
    Matrix.posSemidef_diagonal_iff.mpr ?_, ?_⟩
  · intro p
    split_ifs <;> norm_num
  · intro p
    split_ifs <;> norm_num
  · have hdiag : twoSiteAction = Matrix.diagonal (fun p : Fin 2 × Fin 2 ↦
        (if p.1 = 0 then 1 else 0) + (if p.2 = 0 then 1 else 0)
          - (if p.1 = 0 then 1 else 0) * (if p.2 = 0 then 1 else 0)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [twoSiteAction, firstSiteExcitation, secondSiteExcitation,
          Matrix.diagonal_apply]
      · simp [twoSiteAction, firstSiteExcitation, secondSiteExcitation,
          Matrix.diagonal_apply_ne _ hij]
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> norm_num

/-- `cth:GT-negative-connected-generator`, including the actual Boolean
Möbius subtraction and its Loewner sign. -/
theorem mobius_connected_interaction_is_negative :
    connectedInteraction = -(firstSiteExcitation * secondSiteExcitation)
      ∧ (-connectedInteraction).PosSemidef
      ∧ connectedInteraction ≠ 0 := by
  have heq : connectedInteraction = -(firstSiteExcitation * secondSiteExcitation) := by
    unfold connectedInteraction twoSiteAction
    abel
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, neg_neg]
    have hprod : firstSiteExcitation * secondSiteExcitation =
        Matrix.diagonal (fun p : Fin 2 × Fin 2 ↦
          (if p.1 = 0 then 1 else 0) * (if p.2 = 0 then 1 else 0)) := by
      unfold firstSiteExcitation secondSiteExcitation
      rw [Matrix.diagonal_mul_diagonal]
    rw [hprod, Matrix.posSemidef_diagonal_iff]
    intro p
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> norm_num
  · intro hzero
    have hentry := congrFun (congrFun hzero (0, 0)) (0, 0)
    norm_num [connectedInteraction, twoSiteAction, firstSiteExcitation,
      secondSiteExcitation, Matrix.mul_apply, Finset.sum_product,
      Fin.sum_univ_two, Matrix.diagonal_apply] at hentry

/-! ## Atomic shorting can erase each local direction -/

def firstAtomGram : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
def secondAtomGram : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- Scalar protected short of a `2×2` complete Gram, with the first
coordinate the nuisance/total column and the second the protected column. -/
noncomputable def protectedScalarShort (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 1 1 - M 1 0 * (M 0 0)⁻¹ * M 0 1

theorem atomGrams_posSemidef :
    firstAtomGram.PosSemidef ∧ secondAtomGram.PosSemidef := by
  constructor
  · have h : firstAtomGram =
        (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)
          * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [firstAtomGram, Matrix.mul_apply, Fin.sum_univ_one]
    rw [h]
    simpa using Matrix.PosSemidef.one.mul_mul_conjTranspose_same
      (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)
  · have h : secondAtomGram =
        (!![1; -1] : Matrix (Fin 2) (Fin 1) ℝ)
          * (!![1; -1] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [secondAtomGram, Matrix.mul_apply, Fin.sum_univ_one]
    rw [h]
    simpa using Matrix.PosSemidef.one.mul_mul_conjTranspose_same
      (!![1; -1] : Matrix (Fin 2) (Fin 1) ℝ)

/-- `cth:GRH-atomic-short`, with the two complete atom Grams, their
positivity, local shorts, assembled Gram, and assembled short all explicit. -/
theorem atomic_shorts_zero_but_assembled_short_positive :
    firstAtomGram.PosSemidef ∧ secondAtomGram.PosSemidef
      ∧ protectedScalarShort firstAtomGram = 0
      ∧ protectedScalarShort secondAtomGram = 0
      ∧ firstAtomGram + secondAtomGram = 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      ∧ protectedScalarShort (firstAtomGram + secondAtomGram) = 2
      ∧ 0 < protectedScalarShort (firstAtomGram + secondAtomGram) := by
  refine ⟨atomGrams_posSemidef.1, atomGrams_posSemidef.2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [protectedScalarShort, firstAtomGram]
  · norm_num [protectedScalarShort, secondAtomGram]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [firstAtomGram, secondAtomGram]
  · norm_num [protectedScalarShort, firstAtomGram, secondAtomGram]
  · norm_num [protectedScalarShort, firstAtomGram, secondAtomGram]

end FiniteConnectedAndAtomicShortCountermodels
end NCG
