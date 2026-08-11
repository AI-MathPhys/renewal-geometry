/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExceptionalS4IsotypicBlockClassification
import NCG.Grand.ExceptionalS4ThreeMatrixPanel

/-!
# Multiplicity-matrix assembly for the exceptional S4 panel

After the isotypic Schur classification, self-adjointness identifies the two
directions of each paired block.  The remaining data are precisely two
rectangular contractions and one Hermitian contraction.  This module packages
that reduction and attaches the exact exceptional contribution and zero
branch.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ExceptionalS4MultiplicityMatrixAssembly

noncomputable section

open ExceptionalS4ThreeMatrixPanel

variable {m1 msgn m31 m211 m22 : Type*}
  [Fintype m1] [Fintype msgn] [Fintype m31] [Fintype m211] [Fintype m22]
  [DecidableEq m1] [DecidableEq msgn] [DecidableEq m31]
  [DecidableEq m211] [DecidableEq m22]

/-- The five directed multiplicity coefficient families left by the isotypic
classification, with self-adjointness and contraction certificates. -/
structure SelfAdjointCovariantMultiplicityData where
  oneToSign : Matrix msgn m1 ℂ
  signToOne : Matrix m1 msgn ℂ
  standardToSignStandard : Matrix m211 m31 ℂ
  signStandardToStandard : Matrix m31 m211 ℂ
  pairing : Matrix m22 m22 ℂ
  signToOne_eq_adjoint : signToOne = oneToSignᴴ
  signStandardToStandard_eq_adjoint :
    signStandardToStandard = standardToSignStandardᴴ
  pairing_hermitian : pairingᴴ = pairing
  oneToSign_domain_contraction :
    (1 - oneToSignᴴ * oneToSign).PosSemidef
  oneToSign_codomain_contraction :
    (1 - oneToSign * oneToSignᴴ).PosSemidef
  standardToSignStandard_domain_contraction :
    (1 - standardToSignStandardᴴ * standardToSignStandard).PosSemidef
  standardToSignStandard_codomain_contraction :
    (1 - standardToSignStandard * standardToSignStandardᴴ).PosSemidef
  pairing_contraction : (1 - pairing * pairing).PosSemidef

/-- The three independent matrices obtained from the five directed families. -/
def SelfAdjointCovariantMultiplicityData.toExceptionalPanel
    (D : SelfAdjointCovariantMultiplicityData
      (m1 := m1) (msgn := msgn) (m31 := m31) (m211 := m211) (m22 := m22)) :
    ExceptionalPanel (m1 := m1) (msgn := msgn) (m31 := m31)
      (m211 := m211) (m22 := m22) where
  A1 := D.oneToSign
  A3 := D.standardToSignStandard
  A2 := D.pairing
  A2_hermitian := D.pairing_hermitian
  A1_domain_contraction := D.oneToSign_domain_contraction
  A1_codomain_contraction := D.oneToSign_codomain_contraction
  A3_domain_contraction := D.standardToSignStandard_domain_contraction
  A3_codomain_contraction := D.standardToSignStandard_codomain_contraction
  A2_contraction := D.pairing_contraction

/-- Self-adjoint orientation covariance leaves exactly the three manuscript
matrices, and reconstructs both reverse paired blocks. -/
theorem exactlyThreeMultiplicityMatrices
    (D : SelfAdjointCovariantMultiplicityData
      (m1 := m1) (msgn := msgn) (m31 := m31) (m211 := m211) (m22 := m22)) :
    ∃ A1 : Matrix msgn m1 ℂ,
      ∃ A3 : Matrix m211 m31 ℂ,
      ∃ A2 : Matrix m22 m22 ℂ,
        A2ᴴ = A2 ∧
        D.oneToSign = A1 ∧ D.signToOne = A1ᴴ ∧
        D.standardToSignStandard = A3 ∧
        D.signStandardToStandard = A3ᴴ ∧
        D.pairing = A2 := by
  exact ⟨D.oneToSign, D.standardToSignStandard, D.pairing,
    D.pairing_hermitian, rfl, D.signToOne_eq_adjoint,
    rfl, D.signStandardToStandard_eq_adjoint, rfl⟩

/-- Full exact exceptional theorem after the concrete Schur reduction:
three matrices, the displayed contribution, nonnegativity, and the simultaneous
zero branch. -/
theorem exceptionalThreeMatrixContribution_and_zeroBranch
    (D : SelfAdjointCovariantMultiplicityData
      (m1 := m1) (msgn := msgn) (m31 := m31) (m211 := m211) (m22 := m22))
    (dN : ℝ) (hdN : 0 < dN) :
    let P := D.toExceptionalPanel
    exceptionalContribution dN P = dN *
      ((Fintype.card m1 + Fintype.card msgn -
          2 * hilbertSchmidtSquare P.A1) +
       3 * (Fintype.card m31 + Fintype.card m211 -
          2 * hilbertSchmidtSquare P.A3) +
       2 * (Fintype.card m22 - (Matrix.trace (P.A2 * P.A2)).re)) ∧
    0 ≤ exceptionalContribution dN P ∧
    (exceptionalContribution dN P = 0 ↔
      Fintype.card m1 = Fintype.card msgn ∧
      Fintype.card m31 = Fintype.card m211 ∧
      P.A1ᴴ * P.A1 = 1 ∧ P.A1 * P.A1ᴴ = 1 ∧
      P.A3ᴴ * P.A3 = 1 ∧ P.A3 * P.A3ᴴ = 1 ∧
      P.A2 * P.A2 = 1) := by
  dsimp only
  refine ⟨exceptionalContribution_expanded dN D.toExceptionalPanel,
    exceptionalContribution_nonnegative dN (le_of_lt hdN)
      D.toExceptionalPanel, ?_⟩
  exact exceptionalContribution_eq_zero_iff dN hdN D.toExceptionalPanel

end
end ExceptionalS4MultiplicityMatrixAssembly
end NCG
