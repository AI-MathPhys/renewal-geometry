/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConditionalMobiusSupportReconstruction

/-!
# Conditional expectations as sums of Hoeffding support masks

This supplies the missing concrete layer of
`thm:conditional-Mobius-support`.  A retained coordinate uses the identity
operator and an omitted coordinate uses the constant conditional
expectation.  Their fourfold tensor product is proved to equal the sum of all
exact Hoeffding projections supported inside the retained mask.  Positivity
of the scalar prototype energies is then derived from their exact support
Grams.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG
namespace ConditionalExpectationHoeffdingMask

/-- One-cell conditional expectation: retain the coordinate (`I`) or forget
it (`E`, projection onto constants). -/
def conditionalPick {d : Type*} [Fintype d] [DecidableEq d] (E : Matrix d d ℂ) : Bool → Matrix d d ℂ :=
  fun b => bif b then 1 else E

/-- Conditional expectation onto the coordinates selected by a four-cell
mask. -/
def fourCellConditionalExpectation {d : Type*} [Fintype d] [DecidableEq d] (E : Matrix d d ℂ)
    (B : FourCellMask) : Matrix (d × d × d × d) (d × d × d × d) ℂ :=
  conditionalPick E B.1 ⊗ₖ (conditionalPick E B.2.1 ⊗ₖ
    (conditionalPick E B.2.2.1 ⊗ₖ conditionalPick E B.2.2.2))

set_option maxHeartbeats 800000 in
-- Exhaustive Boolean normalization expands each retained identity as E+Q.
/-- The actual primitive conditional expectation is the sum of precisely the
Hoeffding support projections contained in the retained mask. -/
theorem primitive_conditionalExpectation_eq_supportSum (B : FourCellMask) :
    fourCellConditionalExpectation primitiveConstant B =
      conditionalSupportSum
        (hoeffP primitiveConstant primitiveScoreProjection) B := by
  classical
  have hTF : ¬(true ≤ false) := by decide
  unfold fourCellConditionalExpectation conditionalPick
  rw [show (1 : Matrix (Fin 4) (Fin 4) ℂ) =
    primitiveConstant + primitiveScoreProjection from
      primitive_projection_relations.1.symm]
  rcases B with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [
      conditionalSupportSum, fourCellMaskLE, hoeffP, hoeffPick,
      Fintype.sum_prod_type, hTF, Matrix.add_kronecker,
      Matrix.kronecker_add] <;> abel

/-- Conditional Gram panels are therefore literal conditional-expectation
Grams, not merely abstract mask sums. -/
theorem primitive_conditionalGram_eq_supportSumGram
    {k : Type*} [Fintype k]
    (F : Matrix PrimitiveFourCarrier k ℂ) (B : FourCellMask) :
    Fᴴ * fourCellConditionalExpectation primitiveConstant B * F =
      Fᴴ * conditionalSupportSum
        (hoeffP primitiveConstant primitiveScoreProjection) B * F := by
  rw [primitive_conditionalExpectation_eq_supportSum]

/-- Trace scalarization of an exact support Gram. -/
def supportTraceEnergy {h k : Type*} [Fintype h] [Fintype k]
    (P : FourCellMask → Matrix h h ℂ) (F : Matrix h k ℂ)
    (A : FourCellMask) : ℝ := (Fᴴ * P A * F).trace.re

/-- Exact support trace energies are automatically nonnegative. -/
theorem supportTraceEnergy_nonneg
    {h k : Type*} [Fintype h] [Fintype k]
    (P : FourCellMask → Matrix h h ℂ) (F : Matrix h k ℂ)
    (hPH : ∀ A, (P A)ᴴ = P A) (hP2 : ∀ A, P A * P A = P A)
    (A : FourCellMask) : 0 ≤ supportTraceEnergy P F A := by
  have hpos := (exactSupportGram_positive_and_zero_iff P F hPH hP2 A).1
  change 0 ≤ (Fᴴ * P A * F).trace.re
  exact (Complex.le_def.mp hpos.trace_nonneg).1

/-- The pair/triple/four-body prototype formulas with nonnegativity derived
from the PSD exact-support Grams.  No separate `c ≥ 0` hypothesis remains. -/
theorem fourCell_prototypeSupportEnergies_of_exactGrams
    {h k : Type*} [Fintype h] [Fintype k]
    (P : FourCellMask → Matrix h h ℂ) (F : Matrix h k ℂ)
    (hPH : ∀ A, (P A)ᴴ = P A) (hP2 : ∀ A, P A * P A = P A)
    (c₂ c₃ c₄ : ℝ)
    (horbit : ∀ A : FourCellMask, supportTraceEnergy P F A =
      if hoeffCount A = 2 then c₂ else if hoeffCount A = 3 then c₃ else
      if hoeffCount A = 4 then c₄ else 0) :
    let c := supportTraceEnergy P F
    let m₂ := fourCellConditionalEnergy c (true, true, false, false)
    let m₃ := fourCellConditionalEnergy c (true, true, true, false)
    let m₄ := fourCellConditionalEnergy c (true, true, true, true)
    m₂ = c₂ ∧ m₃ = 3 * c₂ + c₃ ∧
      m₄ = 6 * c₂ + 4 * c₃ + c₄ ∧
      c₂ = m₂ ∧ c₃ = m₃ - 3 * m₂ ∧
      c₄ = m₄ - 4 * m₃ + 6 * m₂ ∧
      0 ≤ c₂ ∧ 0 ≤ c₃ ∧ 0 ≤ c₄ := by
  exact fourCell_prototypeSupportEnergies
    (supportTraceEnergy P F) c₂ c₃ c₄ horbit
    (supportTraceEnergy_nonneg P F hPH hP2)

end ConditionalExpectationHoeffdingMask
end NCG
