/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AutonomousTest

/-!
# Autonomous first-return channel identification

This module supplies the channel-level objects omitted by the original
`sm_autonomous_test` theorem: literal first-return operators, the lossless
trivial/sign/off-diagonal normalizer packet, the coarse score-square channel,
and a finite Stinespring-record intertwining residual.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace AutonomousFirstReturnChannelIdentification

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Block (n : Type*) := Matrix n n ℂ

/-- The literal Schur first return
`PTP + PTQ (I-QTQ)⁻¹ QTP`. -/
noncomputable def firstReturnOperator (P Q T : Block n) : Block n :=
  P * T * P + P * T * Q * ((1 : Block n) - Q * T * Q)⁻¹ * Q * T * P

/-- The two-by-two off-diagonal normalizer return, stored in its four coarse
grading blocks. -/
structure OffDiagonalReturn (n : Type*) where
  C0minus : Block n
  C2plus : Block n
  C2minus : Block n
  C0plus : Block n

/-- The three twisted first returns: trivial, parity-sign, and the
two-dimensional off-diagonal normalizer return. -/
structure NormalizerReturnPacket (n : Type*) where
  trivial : Block n
  sign : Block n
  off : OffDiagonalReturn n

/-- The complete coarse autonomous grading channel in normalizer-isotypic
coordinates. -/
structure CoarseGradingChannel (n : Type*) where
  even : Block n
  odd : Block n
  C0minus : Block n
  C2plus : Block n
  C2minus : Block n
  C0plus : Block n

/-- Reading the three returns loses no coarse channel block. -/
def packetToCoarseChannel : NormalizerReturnPacket (n := n) ≃
    CoarseGradingChannel (n := n) where
  toFun F := ⟨F.trivial, F.sign, F.off.C0minus, F.off.C2plus,
    F.off.C2minus, F.off.C0plus⟩
  invFun C := ⟨C.even, C.odd,
    ⟨C.C0minus, C.C2plus, C.C2minus, C.C0plus⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem threeTwistedReturns_determine_completeCoarseChannel :
    Function.Bijective
      (packetToCoarseChannel (n := n) :
        NormalizerReturnPacket (n := n) → CoarseGradingChannel (n := n)) :=
  (packetToCoarseChannel (n := n)).bijective

/-- The score-square normalizer packet associated with the unsigned block. -/
def scoreSquarePacket (B : Block n) : NormalizerReturnPacket (n := n) where
  trivial := B
  sign := 0
  off := ⟨(2⁻¹ : ℂ) • B, 0, 0, (2⁻¹ : ℂ) • Bᴴ⟩

/-- The autonomous first-return residual, in its exact expanded form. -/
def firstReturnResidual (F : NormalizerReturnPacket (n := n)) : ℂ :=
  (F.signᴴ * F.sign).trace
    + 2 * ((F.off.C0minus - (2⁻¹ : ℂ) • F.trivial)ᴴ *
      (F.off.C0minus - (2⁻¹ : ℂ) • F.trivial)).trace
    + 2 * (F.off.C2plusᴴ * F.off.C2plus).trace

theorem firstReturnResidual_nonneg (F : NormalizerReturnPacket (n := n)) :
    (0 : ℂ) ≤ firstReturnResidual F := by
  unfold firstReturnResidual
  have htr : ∀ M : Block n, (0 : ℂ) ≤ (Mᴴ * M).trace :=
    fun M => (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg
  have htwo : (0 : ℂ) ≤ 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast]
    exact Complex.zero_le_real.mpr (by norm_num)
  exact add_nonneg (add_nonneg (htr _) (mul_nonneg htwo (htr _)))
    (mul_nonneg htwo (htr _))

theorem firstReturnResidual_eq_zero_iff
    (F : NormalizerReturnPacket (n := n)) :
    firstReturnResidual F = 0 ↔
      F.sign = 0 ∧ F.off.C0minus = (2⁻¹ : ℂ) • F.trivial ∧
        F.off.C2plus = 0 := by
  exact (NCG.sm_autonomous_test (n := n)).1
    F.sign F.off.C0minus F.off.C2plus F.trivial

/-- On packets obeying the adjoint/reversal relations, the residual vanishes
exactly when the whole coarse packet equals the score-square packet. -/
theorem firstReturnResidual_eq_zero_iff_scoreSquare
    (F : NormalizerReturnPacket (n := n))
    (hC2 : F.off.C2minus = F.off.C2plusᴴ)
    (hC0 : F.off.C0plus = F.off.C0minusᴴ) :
    firstReturnResidual F = 0 ↔ F = scoreSquarePacket F.trivial := by
  rw [firstReturnResidual_eq_zero_iff]
  constructor
  · rintro ⟨hS, h0, h2⟩
    cases F with
    | mk trivial sign off =>
      cases off with
      | mk C0minus C2plus C2minus C0plus =>
        simp_all [scoreSquarePacket]
  · intro h
    have hS := congrArg NormalizerReturnPacket.sign h
    have h0 := congrArg (fun G => G.off.C0minus) h
    have h2 := congrArg (fun G => G.off.C2plus) h
    simpa [scoreSquarePacket] using And.intro hS (And.intro h0 h2)

/-- A finite protected record representation and its score-square target,
compared through one proposed record-space unitary. -/
structure RecordIntertwiningProblem (n : Type*) where
  protectedRecord : Block n
  scoreSquareRecord : Block n

def recordResidual (R : RecordIntertwiningProblem (n := n)) (U : Block n) : ℂ :=
  let E := U * R.protectedRecord - R.scoreSquareRecord * U
  (Eᴴ * E).trace

def IsUnitaryMatrix (U : Block n) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

def RecordEquivalent (R : RecordIntertwiningProblem (n := n)) : Prop :=
  ∃ U : Block n, IsUnitaryMatrix U ∧
    U * R.protectedRecord = R.scoreSquareRecord * U

theorem recordResidual_eq_zero_iff (R : RecordIntertwiningProblem (n := n))
    (U : Block n) :
    recordResidual R U = 0 ↔
      U * R.protectedRecord = R.scoreSquareRecord * U := by
  unfold recordResidual
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]

theorem exists_unitary_recordResidual_eq_zero_iff
    (R : RecordIntertwiningProblem (n := n)) :
    (∃ U : Block n, IsUnitaryMatrix U ∧ recordResidual R U = 0) ↔
      RecordEquivalent R := by
  simp only [RecordEquivalent, recordResidual_eq_zero_iff]

/-- Exact terminating test for a fixed unitary record comparison. -/
theorem combinedResidual_eq_zero_iff
    (F : NormalizerReturnPacket (n := n))
    (R : RecordIntertwiningProblem (n := n)) (U : Block n)
    (hU : IsUnitaryMatrix U) :
    firstReturnResidual F + recordResidual R U = 0 ↔
      (F.sign = 0 ∧ F.off.C0minus = (2⁻¹ : ℂ) • F.trivial ∧
        F.off.C2plus = 0)
      ∧ U * R.protectedRecord = R.scoreSquareRecord * U := by
  have hFR : (0 : ℂ) ≤ firstReturnResidual F := firstReturnResidual_nonneg F
  have hrec : (0 : ℂ) ≤ recordResidual R U := by
    unfold recordResidual
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  rw [add_eq_zero_iff_of_nonneg hFR hrec,
    firstReturnResidual_eq_zero_iff, recordResidual_eq_zero_iff]

/-- The unchanged reset has a unitary record intertwiner exactly when one
unitary makes the sum of the two nonnegative residuals vanish. -/
theorem exists_unitary_combinedResidual_eq_zero_iff
    (F : NormalizerReturnPacket (n := n))
    (R : RecordIntertwiningProblem (n := n)) :
    (∃ U : Block n, IsUnitaryMatrix U ∧
      firstReturnResidual F + recordResidual R U = 0) ↔
      (F.sign = 0 ∧ F.off.C0minus = (2⁻¹ : ℂ) • F.trivial ∧
        F.off.C2plus = 0) ∧ RecordEquivalent R := by
  constructor
  · rintro ⟨U, hU, hzero⟩
    have h := (combinedResidual_eq_zero_iff F R U hU).mp hzero
    exact ⟨h.1, ⟨U, hU, h.2⟩⟩
  · rintro ⟨hF, U, hU, hrecord⟩
    refine ⟨U, hU, ?_⟩
    exact (combinedResidual_eq_zero_iff F R U hU).mpr ⟨hF, hrecord⟩

/-- Cayley–Hamilton gives an explicit polynomial formula for every invertible
finite matrix, with degree strictly below the carrier dimension. -/
theorem matrixInverse_degreeBoundedPolynomial (M : Block n) (hM : IsUnit M) :
    ∃ c : ℂ, ∃ q : Polynomial ℂ,
      M⁻¹ = c • Polynomial.aeval M q ∧
        q.degree < Fintype.card n := by
  let p := M.charpoly
  have hsplit : Polynomial.X * p.divX + Polynomial.C (p.coeff 0) = p :=
    Polynomial.X_mul_divX_add p
  have haeval : M * Polynomial.aeval M p.divX
      + (p.coeff 0) • (1 : Block n) = 0 := by
    have h := congrArg (Polynomial.aeval M) hsplit
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Matrix.aeval_self_charpoly] at h
    rw [← h]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
  have hc0 : p.coeff 0 ≠ 0 := by
    intro h0
    have hdet : M.det = (-1) ^ (Fintype.card n) * p.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff M
    rw [h0, mul_zero] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero hdet
  let c : ℂ := -(p.coeff 0)⁻¹
  have hMq : M * (c • Polynomial.aeval M p.divX) = 1 := by
    rw [mul_smul_comm]
    have h1 : M * Polynomial.aeval M p.divX =
        -((p.coeff 0) • (1 : Block n)) :=
      eq_neg_of_add_eq_zero_left haeval
    rw [h1, smul_neg, smul_smul]
    dsimp [c]
    rw [neg_mul, inv_mul_cancel₀ hc0]
    simp
  refine ⟨c, p.divX, Matrix.inv_eq_right_inv hMq, ?_⟩
  rw [← Matrix.charpoly_degree_eq_dim M]
  exact Polynomial.degree_divX_lt (Matrix.charpoly_monic M).ne_zero

/-- The first return is a finite loaded panel: it belongs to the unital
algebra generated by `P,Q,T` whenever the transient resolvent exists. -/
theorem firstReturnOperator_mem_generatedAlgebra (P Q T : Block n)
    (hres : IsUnit ((1 : Block n) - Q * T * Q)) :
    firstReturnOperator P Q T ∈ Algebra.adjoin ℂ {P, Q, T} := by
  let A := Algebra.adjoin ℂ ({P, Q, T} : Set (Block n))
  have hP : P ∈ A := Algebra.subset_adjoin (by simp)
  have hQ : Q ∈ A := Algebra.subset_adjoin (by simp)
  have hT : T ∈ A := Algebra.subset_adjoin (by simp)
  have htrans : (1 : Block n) - Q * T * Q ∈ A := by
    exact sub_mem (Subalgebra.one_mem A) (mul_mem (mul_mem hQ hT) hQ)
  have hinv : ((1 : Block n) - Q * T * Q)⁻¹ ∈ A :=
    inv_mem_of_isUnit htrans hres
  exact add_mem (mul_mem (mul_mem hP hT) hP)
    (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hP hT) hQ)
      hinv) hQ) hT) hP)

/-- A grading-preserving source has signed return equal to its unsigned
return; if that return is nonzero, the autonomous residual cannot vanish. -/
theorem gradingPreserving_nonzeroReturn_obstruction
    (F : NormalizerReturnPacket (n := n))
    (hSB : F.sign = F.trivial) (hB : F.trivial ≠ 0) :
    firstReturnResidual F ≠ 0 := by
  intro hzero
  have hS0 := (firstReturnResidual_eq_zero_iff F).mp hzero |>.1
  exact hB (hSB ▸ hS0)

theorem gradingPreserving_nonzeroReturn_strictlyPositive
    (F : NormalizerReturnPacket (n := n))
    (hSB : F.sign = F.trivial) (hB : F.trivial ≠ 0) :
    (0 : ℂ) < firstReturnResidual F :=
  lt_of_le_of_ne (firstReturnResidual_nonneg F)
    (Ne.symm (gradingPreserving_nonzeroReturn_obstruction F hSB hB))

/-- Complete channel-level form of `thm:SM-autonomous-test`. -/
theorem terminatingAutonomousIdentification :
    Function.Bijective
      (packetToCoarseChannel (n := n) :
        NormalizerReturnPacket (n := n) → CoarseGradingChannel (n := n))
    ∧ (∀ F : NormalizerReturnPacket (n := n),
      firstReturnResidual F = 0 ↔
        F.sign = 0 ∧ F.off.C0minus = (2⁻¹ : ℂ) • F.trivial ∧
          F.off.C2plus = 0)
    ∧ (∀ R : RecordIntertwiningProblem (n := n),
      (∃ U : Block n, IsUnitaryMatrix U ∧ recordResidual R U = 0) ↔
        RecordEquivalent R)
    ∧ (∀ P Q T : Block n, IsUnit ((1 : Block n) - Q * T * Q) →
      firstReturnOperator P Q T ∈ Algebra.adjoin ℂ {P, Q, T}) := by
  exact ⟨threeTwistedReturns_determine_completeCoarseChannel,
    firstReturnResidual_eq_zero_iff,
    exists_unitary_recordResidual_eq_zero_iff,
    firstReturnOperator_mem_generatedAlgebra⟩

end
end AutonomousFirstReturnChannelIdentification
end NCG
