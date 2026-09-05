/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HoeffdingGramIdentification
import NCG.Grand.S4SupportGramCovariance

/-!
# Conditional Möbius reconstruction of support Grams

This file supplies the Boolean-lattice inversion missing from
`thm:conditional-Mobius-support`.  Conditional panels are sums of the exact
Hoeffding support blocks below a retained coordinate set.  Möbius inversion
recovers each exact block, conjugation gives the matrix/Fisher formula, and
the four-cell orbit counts give the pair/triple/four-body prototype energies.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Boolean masks for the sixteen supports of four cells. -/
abbrev FourCellMask := Bool × Bool × Bool × Bool

/-- Inclusion of four-cell support masks. -/
def fourCellMaskLE (A B : FourCellMask) : Prop :=
  A.1 ≤ B.1 ∧ A.2.1 ≤ B.2.1 ∧ A.2.2.1 ≤ B.2.2.1 ∧
    A.2.2.2 ≤ B.2.2.2

instance fourCellMaskLE_decidable (A B : FourCellMask) :
    Decidable (fourCellMaskLE A B) := by
  unfold fourCellMaskLE
  infer_instance

/-- Conditional block obtained by retaining every exact support contained in
`B`. -/
def conditionalSupportSum {E : Type*} [AddCommMonoid E]
    (P : FourCellMask → E) (B : FourCellMask) : E :=
  ∑ A, if fourCellMaskLE A B then P A else 0

set_option maxHeartbeats 800000 in
-- Exhaustive normalization of all sixteen Boolean support masks.
/-- Möbius inversion on the complete four-cell Boolean lattice. -/
theorem fourCell_conditionalSupport_mobius
    {h : Type*}
    (P : FourCellMask → Matrix h h ℂ) (A : FourCellMask) :
    P A = ∑ B, if fourCellMaskLE B A then
      ((-1 : ℂ) ^ (hoeffCount A - hoeffCount B)) •
        conditionalSupportSum P B else 0 := by
  classical
  ext i j
  have hTF : ¬(true ≤ false) := by decide
  rcases A with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [conditionalSupportSum, fourCellMaskLE, hoeffCount,
      Fintype.sum_prod_type, hTF] <;> ring

/-- Conjugating the Boolean inversion by a synthesis gives the exact-support
Gram as the alternating sum of conditional Gram/Fisher panels. -/
theorem conditionalSupportGram_mobius
    {h k : Type*} [Fintype h]
    (P : FourCellMask → Matrix h h ℂ) (F : Matrix h k ℂ)
    (A : FourCellMask) :
    Fᴴ * P A * F = ∑ B, if fourCellMaskLE B A then
      ((-1 : ℂ) ^ (hoeffCount A - hoeffCount B)) •
        (Fᴴ * conditionalSupportSum P B * F) else 0 := by
  classical
  rw [fourCell_conditionalSupport_mobius P A]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hBA : fourCellMaskLE B A
  · simp [hBA, Matrix.mul_smul, Matrix.smul_mul]
  · simp [hBA]

/-- Exact support Grams are positive and vanish precisely when their projected
support synthesis vanishes. -/
theorem exactSupportGram_positive_and_zero_iff
    {h k : Type*} [Fintype h] [Fintype k]
    (P : FourCellMask → Matrix h h ℂ) (F : Matrix h k ℂ)
    (hPH : ∀ A, (P A)ᴴ = P A) (hP2 : ∀ A, P A * P A = P A)
    (A : FourCellMask) :
    (Fᴴ * P A * F).PosSemidef ∧
      (Fᴴ * P A * F = 0 ↔ P A * F = 0) := by
  have hgram : Fᴴ * P A * F = (P A * F)ᴴ * (P A * F) := by
    rw [Matrix.conjTranspose_mul, hPH A]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P A) (P A) F, hP2 A]
  rw [hgram]
  exact ⟨Matrix.posSemidef_conjTranspose_mul_self _,
    Matrix.conjTranspose_mul_self_eq_zero⟩

/-- Scalar conditional energy after constants and one-cell supports have been
shorted.  Exact `S₄` covariance makes the remaining scalarization depend only
on support cardinality. -/
def fourCellConditionalEnergy
    (c : FourCellMask → ℝ) (B : FourCellMask) : ℝ :=
  ∑ A, if fourCellMaskLE A B then c A else 0

/-- The cardinality-orbit reduction gives the manuscript's three triangular
prototype formulas, their Möbius inverse, and positivity. -/
theorem fourCell_prototypeSupportEnergies
    (c : FourCellMask → ℝ) (c₂ c₃ c₄ : ℝ)
    (hc : ∀ A : FourCellMask, c A =
      if hoeffCount A = 2 then c₂ else if hoeffCount A = 3 then c₃ else
      if hoeffCount A = 4 then c₄ else 0)
    (hnonneg : ∀ A, 0 ≤ c A) :
    let m₂ := fourCellConditionalEnergy c (true, true, false, false)
    let m₃ := fourCellConditionalEnergy c (true, true, true, false)
    let m₄ := fourCellConditionalEnergy c (true, true, true, true)
    m₂ = c₂ ∧ m₃ = 3 * c₂ + c₃ ∧
      m₄ = 6 * c₂ + 4 * c₃ + c₄ ∧
      c₂ = m₂ ∧ c₃ = m₃ - 3 * m₂ ∧
      c₄ = m₄ - 4 * m₃ + 6 * m₂ ∧
      0 ≤ c₂ ∧ 0 ≤ c₃ ∧ 0 ≤ c₄ := by
  dsimp only
  have hTF : ¬(true ≤ false) := by decide
  have hm₂ : fourCellConditionalEnergy c (true, true, false, false) = c₂ := by
    simp [fourCellConditionalEnergy, fourCellMaskLE, hc, hoeffCount,
      Fintype.sum_prod_type, hTF]
  have hm₃ : fourCellConditionalEnergy c (true, true, true, false) =
      3 * c₂ + c₃ := by
    simp [fourCellConditionalEnergy, fourCellMaskLE, hc, hoeffCount,
      Fintype.sum_prod_type, hTF]
    ring
  have hm₄ : fourCellConditionalEnergy c (true, true, true, true) =
      6 * c₂ + 4 * c₃ + c₄ := by
    simp [fourCellConditionalEnergy, fourCellMaskLE, hc, hoeffCount,
      Fintype.sum_prod_type]
    ring
  have hc₂ : 0 ≤ c₂ := by
    simpa [hc, hoeffCount] using
      hnonneg (true, true, false, false)
  have hc₃ : 0 ≤ c₃ := by
    simpa [hc, hoeffCount] using
      hnonneg (true, true, true, false)
  have hc₄ : 0 ≤ c₄ := by
    simpa [hc, hoeffCount] using
      hnonneg (true, true, true, true)
  refine ⟨hm₂, hm₃, hm₄, hm₂.symm, ?_, ?_, hc₂, hc₃, hc₄⟩
  · rw [hm₂, hm₃]
    ring
  · rw [hm₂, hm₃, hm₄]
    ring

end NCG
