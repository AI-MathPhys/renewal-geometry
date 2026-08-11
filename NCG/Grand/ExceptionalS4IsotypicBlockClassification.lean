/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExceptionalS4GeneratorSchurCertificate

/-!
# Complete isotypic block classification for the exceptional S4 panel

The five isotypes are ordered as the trivial line, sign line, standard
triplet, sign-standard triplet, and pairing doublet.  This module packages the
twenty-five reduced generator equations for one multiplicity slice and proves
that exactly five directed blocks survive.
-/

open Matrix

namespace NCG
namespace ExceptionalS4IsotypicBlockClassification

noncomputable section

open ExceptionalS4GeneratorSchurCertificate

/-- One multiplicity slice of all twenty-five exceptional isotype blocks,
together with the reduced orientation-covariance equations. -/
structure CovariantIsotypeSlice where
  oneOne : Matrix (Fin 1) (Fin 1) ℂ
  oneSign : Matrix (Fin 1) (Fin 1) ℂ
  oneStandard : Matrix (Fin 1) (Fin 3) ℂ
  oneSignStandard : Matrix (Fin 1) (Fin 3) ℂ
  onePairing : Matrix (Fin 1) (Fin 2) ℂ
  signOne : Matrix (Fin 1) (Fin 1) ℂ
  signSign : Matrix (Fin 1) (Fin 1) ℂ
  signStandard : Matrix (Fin 1) (Fin 3) ℂ
  signSignStandard : Matrix (Fin 1) (Fin 3) ℂ
  signPairing : Matrix (Fin 1) (Fin 2) ℂ
  standardOne : Matrix (Fin 3) (Fin 1) ℂ
  standardSign : Matrix (Fin 3) (Fin 1) ℂ
  standardStandard : Matrix (Fin 3) (Fin 3) ℂ
  standardSignStandard : Matrix (Fin 3) (Fin 3) ℂ
  standardPairing : Matrix (Fin 3) (Fin 2) ℂ
  signStandardOne : Matrix (Fin 3) (Fin 1) ℂ
  signStandardSign : Matrix (Fin 3) (Fin 1) ℂ
  signStandardStandard : Matrix (Fin 3) (Fin 3) ℂ
  signStandardSignStandard : Matrix (Fin 3) (Fin 3) ℂ
  signStandardPairing : Matrix (Fin 3) (Fin 2) ℂ
  pairingOne : Matrix (Fin 2) (Fin 1) ℂ
  pairingSign : Matrix (Fin 2) (Fin 1) ℂ
  pairingStandard : Matrix (Fin 2) (Fin 3) ℂ
  pairingSignStandard : Matrix (Fin 2) (Fin 3) ℂ
  pairingPairing : Matrix (Fin 2) (Fin 2) ℂ
  oneOne_cov : oneOne = -oneOne
  oneStandard_covS : oneStandard * standardTransposition = -oneStandard
  oneStandard_covR : oneStandard * standardFourCycle = -oneStandard
  oneSignStandard_covS : oneSignStandard * standardTransposition = oneSignStandard
  oneSignStandard_covR : oneSignStandard * standardFourCycle = oneSignStandard
  onePairing_covS : onePairing * pairingTransposition = -onePairing
  onePairing_covR : onePairing * pairingFourCycle = -onePairing
  signSign_cov : signSign = -signSign
  signStandard_covS : signStandard * standardTransposition = signStandard
  signStandard_covR : signStandard * standardFourCycle = signStandard
  signSignStandard_covS :
    signSignStandard * standardTransposition = -signSignStandard
  signSignStandard_covR :
    signSignStandard * standardFourCycle = -signSignStandard
  signPairing_covS : signPairing * pairingTransposition = signPairing
  signPairing_covR : signPairing * pairingFourCycle = signPairing
  standardOne_covS : standardTransposition * standardOne = -standardOne
  standardOne_covR : standardFourCycle * standardOne = -standardOne
  standardSign_covS : standardTransposition * standardSign = standardSign
  standardSign_covR : standardFourCycle * standardSign = standardSign
  standardStandard_covS :
    standardTransposition * standardStandard =
      -(standardStandard * standardTransposition)
  standardStandard_covR :
    standardFourCycle * standardStandard =
      -(standardStandard * standardFourCycle)
  standardSignStandard_covS :
    standardTransposition * standardSignStandard =
      standardSignStandard * standardTransposition
  standardSignStandard_covR :
    standardFourCycle * standardSignStandard =
      standardSignStandard * standardFourCycle
  standardPairing_covS :
    standardTransposition * standardPairing =
      -(standardPairing * pairingTransposition)
  standardPairing_covR :
    standardFourCycle * standardPairing =
      -(standardPairing * pairingFourCycle)
  signStandardOne_covS :
    standardTransposition * signStandardOne = signStandardOne
  signStandardOne_covR :
    standardFourCycle * signStandardOne = signStandardOne
  signStandardSign_covS :
    standardTransposition * signStandardSign = -signStandardSign
  signStandardSign_covR :
    standardFourCycle * signStandardSign = -signStandardSign
  signStandardStandard_covS :
    standardTransposition * signStandardStandard =
      signStandardStandard * standardTransposition
  signStandardStandard_covR :
    standardFourCycle * signStandardStandard =
      signStandardStandard * standardFourCycle
  signStandardSignStandard_covS :
    standardTransposition * signStandardSignStandard =
      -(signStandardSignStandard * standardTransposition)
  signStandardSignStandard_covR :
    standardFourCycle * signStandardSignStandard =
      -(signStandardSignStandard * standardFourCycle)
  signStandardPairing_covS :
    standardTransposition * signStandardPairing =
      signStandardPairing * pairingTransposition
  signStandardPairing_covR :
    standardFourCycle * signStandardPairing =
      signStandardPairing * pairingFourCycle
  pairingOne_covS : pairingTransposition * pairingOne = -pairingOne
  pairingOne_covR : pairingFourCycle * pairingOne = -pairingOne
  pairingSign_covS : pairingTransposition * pairingSign = pairingSign
  pairingSign_covR : pairingFourCycle * pairingSign = pairingSign
  pairingStandard_covS :
    pairingTransposition * pairingStandard =
      -(pairingStandard * standardTransposition)
  pairingStandard_covR :
    pairingFourCycle * pairingStandard =
      -(pairingStandard * standardFourCycle)
  pairingSignStandard_covS :
    pairingTransposition * pairingSignStandard =
      pairingSignStandard * standardTransposition
  pairingSignStandard_covR :
    pairingFourCycle * pairingSignStandard =
      pairingSignStandard * standardFourCycle
  pairingPairing_covS :
    pairingTransposition * pairingPairing =
      -(pairingPairing * pairingTransposition)
  pairingPairing_covR :
    pairingFourCycle * pairingPairing =
      -(pairingPairing * pairingFourCycle)

/-- The exact output of the isotypic Schur classification: twenty forbidden
blocks vanish and the five sign-twist blocks lie on their unique lines. -/
structure IsotypicSliceNormalForm (B : CovariantIsotypeSlice) where
  oneSign_scalar : ∃ z : ℂ, B.oneSign = z • 1
  signOne_scalar : ∃ z : ℂ, B.signOne = z • 1
  standardSignStandard_scalar :
    ∃ z : ℂ, B.standardSignStandard = z • 1
  signStandardStandard_scalar :
    ∃ z : ℂ, B.signStandardStandard = z • 1
  pairingPairing_scalar :
    ∃ z : ℂ, B.pairingPairing = z • pairingSignTwist
  oneOne_zero : B.oneOne = 0
  oneStandard_zero : B.oneStandard = 0
  oneSignStandard_zero : B.oneSignStandard = 0
  onePairing_zero : B.onePairing = 0
  signSign_zero : B.signSign = 0
  signStandard_zero : B.signStandard = 0
  signSignStandard_zero : B.signSignStandard = 0
  signPairing_zero : B.signPairing = 0
  standardOne_zero : B.standardOne = 0
  standardSign_zero : B.standardSign = 0
  standardStandard_zero : B.standardStandard = 0
  standardPairing_zero : B.standardPairing = 0
  signStandardOne_zero : B.signStandardOne = 0
  signStandardSign_zero : B.signStandardSign = 0
  signStandardSignStandard_zero : B.signStandardSignStandard = 0
  signStandardPairing_zero : B.signStandardPairing = 0
  pairingOne_zero : B.pairingOne = 0
  pairingSign_zero : B.pairingSign = 0
  pairingStandard_zero : B.pairingStandard = 0
  pairingSignStandard_zero : B.pairingSignStandard = 0

private theorem oneByOne_scalar (A : Matrix (Fin 1) (Fin 1) ℂ) :
    ∃ z : ℂ, A = z • 1 := by
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp

private theorem oneByOne_zero (A : Matrix (Fin 1) (Fin 1) ℂ)
    (h : A = -A) : A = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  change A 0 0 = 0
  have hij := congrFun (congrFun h 0) 0
  simp only [Matrix.neg_apply] at hij
  linear_combination (1 / 2 : ℂ) * hij

/-- All twenty-five block positions are classified, with no abstract Schur
interface left as a hypothesis. -/
theorem covariantIsotypeSlice_normalForm (B : CovariantIsotypeSlice) :
    IsotypicSliceNormalForm B where
  oneSign_scalar := oneByOne_scalar B.oneSign
  signOne_scalar := oneByOne_scalar B.signOne
  standardSignStandard_scalar :=
    standard_generator_commutant B.standardSignStandard
      B.standardSignStandard_covS B.standardSignStandard_covR
  signStandardStandard_scalar :=
    standard_generator_commutant B.signStandardStandard
      B.signStandardStandard_covS B.signStandardStandard_covR
  pairingPairing_scalar :=
    pairing_generator_anticommutant B.pairingPairing
      B.pairingPairing_covS B.pairingPairing_covR
  oneOne_zero := oneByOne_zero B.oneOne B.oneOne_cov
  oneStandard_zero := standard_antiFixedRow_zero B.oneStandard
    B.oneStandard_covS B.oneStandard_covR
  oneSignStandard_zero := standard_fixedRow_zero B.oneSignStandard
    B.oneSignStandard_covS B.oneSignStandard_covR
  onePairing_zero := pairing_antiFixedRow_zero B.onePairing
    B.onePairing_covS B.onePairing_covR
  signSign_zero := oneByOne_zero B.signSign B.signSign_cov
  signStandard_zero := standard_fixedRow_zero B.signStandard
    B.signStandard_covS B.signStandard_covR
  signSignStandard_zero := standard_antiFixedRow_zero B.signSignStandard
    B.signSignStandard_covS B.signSignStandard_covR
  signPairing_zero := pairing_fixedRow_zero B.signPairing
    B.signPairing_covS B.signPairing_covR
  standardOne_zero := standard_antiFixedColumn_zero B.standardOne
    B.standardOne_covS B.standardOne_covR
  standardSign_zero := standard_fixedColumn_zero B.standardSign
    B.standardSign_covS B.standardSign_covR
  standardStandard_zero := standard_generator_anticommutant B.standardStandard
    B.standardStandard_covS B.standardStandard_covR
  standardPairing_zero := by
    let C := B.standardPairing * pairingSignTwist
    have hCS : standardTransposition * C = C * pairingTransposition := by
      dsimp [C]
      calc
        standardTransposition * (B.standardPairing * pairingSignTwist) =
            (standardTransposition * B.standardPairing) * pairingSignTwist := by
              rw [Matrix.mul_assoc]
        _ = (-(B.standardPairing * pairingTransposition)) *
            pairingSignTwist := by rw [B.standardPairing_covS]
        _ = B.standardPairing *
            (pairingSignTwist * pairingTransposition) := by
              have h := congrArg Neg.neg
                pairingSignTwist_anticommutes_transposition
              have ht : pairingSignTwist * pairingTransposition =
                  -(pairingTransposition * pairingSignTwist) := by
                simpa using h.symm
              rw [ht]
              simp [Matrix.mul_assoc]
        _ = (B.standardPairing * pairingSignTwist) *
            pairingTransposition := by rw [Matrix.mul_assoc]
    have hCR : standardFourCycle * C = C * pairingFourCycle := by
      dsimp [C]
      calc
        standardFourCycle * (B.standardPairing * pairingSignTwist) =
            (standardFourCycle * B.standardPairing) * pairingSignTwist := by
              rw [Matrix.mul_assoc]
        _ = (-(B.standardPairing * pairingFourCycle)) *
            pairingSignTwist := by rw [B.standardPairing_covR]
        _ = B.standardPairing *
            (pairingSignTwist * pairingFourCycle) := by
              have h := congrArg Neg.neg
                pairingSignTwist_anticommutes_fourCycle
              have ht : pairingSignTwist * pairingFourCycle =
                  -(pairingFourCycle * pairingSignTwist) := by
                simpa using h.symm
              rw [ht]
              simp [Matrix.mul_assoc]
        _ = (B.standardPairing * pairingSignTwist) *
            pairingFourCycle := by rw [Matrix.mul_assoc]
    have hC := pairing_to_standard_intertwiner_zero C hCS hCR
    calc
      B.standardPairing =
          B.standardPairing * (pairingSignTwist * pairingSignTwist) := by
            rw [pairingSignTwist_sq]
            simp
      _ = C * pairingSignTwist := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hC]; simp
  signStandardOne_zero := standard_fixedColumn_zero B.signStandardOne
    B.signStandardOne_covS B.signStandardOne_covR
  signStandardSign_zero := standard_antiFixedColumn_zero B.signStandardSign
    B.signStandardSign_covS B.signStandardSign_covR
  signStandardSignStandard_zero :=
    standard_generator_anticommutant B.signStandardSignStandard
      B.signStandardSignStandard_covS B.signStandardSignStandard_covR
  signStandardPairing_zero :=
    pairing_to_standard_intertwiner_zero B.signStandardPairing
      B.signStandardPairing_covS B.signStandardPairing_covR
  pairingOne_zero := pairing_antiFixedColumn_zero B.pairingOne
    B.pairingOne_covS B.pairingOne_covR
  pairingSign_zero := pairing_fixedColumn_zero B.pairingSign
    B.pairingSign_covS B.pairingSign_covR
  pairingStandard_zero := by
    let C := pairingSignTwist * B.pairingStandard
    have hCS : pairingTransposition * C = C * standardTransposition := by
      dsimp [C]
      calc
        pairingTransposition * (pairingSignTwist * B.pairingStandard) =
            (pairingTransposition * pairingSignTwist) *
              B.pairingStandard := by rw [Matrix.mul_assoc]
        _ = (-(pairingSignTwist * pairingTransposition)) *
              B.pairingStandard := by
                rw [pairingSignTwist_anticommutes_transposition]
        _ = pairingSignTwist *
              (-(pairingTransposition * B.pairingStandard)) := by
                simp [Matrix.mul_assoc]
        _ = pairingSignTwist *
              (B.pairingStandard * standardTransposition) := by
                rw [B.pairingStandard_covS]
                simp
        _ = (pairingSignTwist * B.pairingStandard) *
              standardTransposition := by rw [Matrix.mul_assoc]
    have hCR : pairingFourCycle * C = C * standardFourCycle := by
      dsimp [C]
      calc
        pairingFourCycle * (pairingSignTwist * B.pairingStandard) =
            (pairingFourCycle * pairingSignTwist) *
              B.pairingStandard := by rw [Matrix.mul_assoc]
        _ = (-(pairingSignTwist * pairingFourCycle)) *
              B.pairingStandard := by
                rw [pairingSignTwist_anticommutes_fourCycle]
        _ = pairingSignTwist *
              (-(pairingFourCycle * B.pairingStandard)) := by
                simp [Matrix.mul_assoc]
        _ = pairingSignTwist *
              (B.pairingStandard * standardFourCycle) := by
                rw [B.pairingStandard_covR]
                simp
        _ = (pairingSignTwist * B.pairingStandard) *
              standardFourCycle := by rw [Matrix.mul_assoc]
    have hC := standard_to_pairing_intertwiner_zero C hCS hCR
    calc
      B.pairingStandard =
          (pairingSignTwist * pairingSignTwist) * B.pairingStandard := by
            rw [pairingSignTwist_sq]
            simp
      _ = pairingSignTwist * C := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hC]; simp
  pairingSignStandard_zero :=
    standard_to_pairing_intertwiner_zero B.pairingSignStandard
      B.pairingSignStandard_covS B.pairingSignStandard_covR

end
end ExceptionalS4IsotypicBlockClassification
end NCG
