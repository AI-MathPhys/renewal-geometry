/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FiniteRealEvenSpectralizationExact

/-!
# Exact grading and conjugate-port operations of a finite spectral packet

The coordinate grading and real matrix of the canonical finite
spectralization are promoted here to their actual operations on the finite
Hilbert carrier.  The grading is a self-adjoint unitary involution.  The
conjugate port is conjugate-linear, involutive, commutes with the Dirac and
grading operations, and implements the opposite representation.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace NCG.FiniteSpectralPacketGradingRealOperationsExact

noncomputable section

open FiniteRealEvenSpectralizationExact

variable {A I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

namespace Packet

variable (P : Packet (A := A) (I := I) (J := J))

/-- The grading is self-adjoint. -/
theorem grading_isHermitian : P.grading.IsHermitian := by
  unfold Packet.grading Matrix.IsHermitian
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- The grading is an involution. -/
theorem grading_sq : P.grading * P.grading = 1 := by
  unfold Packet.grading
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp

/-- Consequently the grading is a two-sided unitary operation. -/
theorem grading_unitary :
    P.gradingᴴ * P.grading = 1 ∧ P.grading * P.gradingᴴ = 1 := by
  rw [(grading_isHermitian P).eq]
  exact ⟨grading_sq P, grading_sq P⟩

/-- Coordinatewise conjugation on the finite Hilbert carrier. -/
def conjugateVector (x : P.HIndex → ℂ) : P.HIndex → ℂ :=
  fun i => star (x i)

/-- The conjugate-port operation `x ↦ j * conjugate(x)`. -/
def realOperation (x : P.HIndex → ℂ) : P.HIndex → ℂ :=
  P.realMatrix *ᵥ conjugateVector P x

@[simp]
theorem conjugateVector_conjugateVector (x : P.HIndex → ℂ) :
    conjugateVector P (conjugateVector P x) = x := by
  ext i
  simp [conjugateVector]

theorem conjugateVector_smul (z : ℂ) (x : P.HIndex → ℂ) :
    conjugateVector P (z • x) = star z • conjugateVector P x := by
  ext i
  simp [conjugateVector]

theorem conjugateVector_mulVec
    (M : Matrix P.HIndex P.HIndex ℂ) (x : P.HIndex → ℂ) :
    conjugateVector P (M *ᵥ x) =
      M.map star *ᵥ conjugateVector P x := by
  ext i
  simp [conjugateVector, Matrix.mulVec, dotProduct,
    map_sum, star_mul, mul_comm]

/-- The conjugate port is conjugate-linear. -/
theorem realOperation_smul (z : ℂ) (x : P.HIndex → ℂ) :
    realOperation P (z • x) = star z • realOperation P x := by
  simp [realOperation, conjugateVector_smul P,
    Matrix.mulVec_smul]

/-- The conjugate port squares exactly to the identity. -/
theorem realOperation_involutive (x : P.HIndex → ℂ) :
    realOperation P (realOperation P x) = x := by
  rw [realOperation, realOperation, conjugateVector_mulVec P]
  rw [conjugateVector_conjugateVector P]
  rw [Matrix.mulVec_mulVec, P.realMatrix_sq, Matrix.one_mulVec]

/-- The conjugate port commutes with the finite Dirac operation. -/
theorem realOperation_dirac (x : P.HIndex → ℂ) :
    realOperation P (P.dirac *ᵥ x) =
      P.dirac *ᵥ realOperation P x := by
  rw [realOperation, conjugateVector_mulVec P]
  rw [realOperation, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    P.realMatrix_intertwines_dirac]

/-- The conjugate port commutes with the grading operation. -/
theorem realOperation_grading (x : P.HIndex → ℂ) :
    realOperation P (P.grading *ᵥ x) =
      P.grading *ᵥ realOperation P x := by
  rw [realOperation, conjugateVector_mulVec P]
  rw [realOperation, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    P.realMatrix_commutes_grading]

/-- Conjugating a represented algebra element through the real port gives
the declared opposite representation. -/
theorem realOperation_representation (b : A) (x : P.HIndex → ℂ) :
    realOperation P
        (P.representation (star b) *ᵥ realOperation P x) =
      P.oppositeRepresentation b *ᵥ x := by
  rw [realOperation, realOperation, conjugateVector_mulVec P]
  rw [conjugateVector_mulVec P, conjugateVector_conjugateVector P]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [P.realMatrix_implements_opposite]

/-- Complete controlled grading/conjugate-port certificate used in the
finite marked realization. -/
theorem finiteSpectralization_grading_real_operations_exact :
    (P.gradingᴴ * P.grading = 1 ∧ P.grading * P.gradingᴴ = 1) ∧
    (∀ (z : ℂ) (x : P.HIndex → ℂ), realOperation P (z • x) =
      star z • realOperation P x) ∧
    (∀ x : P.HIndex → ℂ, realOperation P (realOperation P x) = x) ∧
    (∀ x : P.HIndex → ℂ, realOperation P (P.dirac *ᵥ x) =
      P.dirac *ᵥ realOperation P x) ∧
    (∀ x : P.HIndex → ℂ, realOperation P (P.grading *ᵥ x) =
      P.grading *ᵥ realOperation P x) ∧
    (∀ (b : A) (x : P.HIndex → ℂ), realOperation P
        (P.representation (star b) *ᵥ realOperation P x) =
      P.oppositeRepresentation b *ᵥ x) := by
  exact ⟨grading_unitary P, realOperation_smul P,
    realOperation_involutive P, realOperation_dirac P,
    realOperation_grading P, realOperation_representation P⟩

end Packet

end

end NCG.FiniteSpectralPacketGradingRealOperationsExact
