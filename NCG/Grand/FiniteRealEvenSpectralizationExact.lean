/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteDifferentialOccurrenceCompiler
import NCG.Grand.FiniteSpectralizationBlockNormExact

/-!
# Canonical finite real even spectralization

This is a coordinate model of an admissible source-minimal differential
packet.  The two finite Hilbert carriers are given orthonormal coordinates;
all operators below are genuine matrices equipped with the Euclidean
operator norm.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace NCG.FiniteRealEvenSpectralizationExact

noncomputable section

variable {A I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- Coordinate form of the admissible differential packet after quotienting
universal one-forms by the Gram null space. -/
structure Packet where
  left0 : A → Matrix I I ℂ
  left1 : A → Matrix J J ℂ
  right0 : A → Matrix I I ℂ
  right1 : A → Matrix J J ℂ
  differential : Matrix J I ℂ
  B : A → Matrix J I ℂ
  B_real_smul : ∀ (r : ℝ) a,
    B ((r : ℂ) • a) = (r : ℂ) • B a
  partialVector : A → (J → ℂ)
  unitVector : I → ℂ
  left0_star : ∀ a, (left0 a)ᴴ = left0 (star a)
  left1_star : ∀ a, (left1 a)ᴴ = left1 (star a)
  right0_star : ∀ a, (right0 a)ᴴ = right0 (star a)
  right1_star : ∀ a, (right1 a)ᴴ = right1 (star a)
  commute0 : ∀ a b, left0 a * right0 b = right0 b * left0 a
  commute1 : ∀ a b, left1 a * right1 b = right1 b * left1 a
  leibniz : ∀ a,
    differential * left0 a - left1 a * differential = B a
  B_right : ∀ a b, B a * right0 b = right1 b * B a
  B_unit : ∀ a, B a *ᵥ unitVector = partialVector a
  B_zero_of_partial_zero : ∀ a, partialVector a = 0 → B a = 0
  j0 : Matrix I I ℂ
  j1 : Matrix J J ℂ
  j0_sq : j0 * j0.map star = 1
  j1_sq : j1 * j1.map star = 1
  j0_left : ∀ a, j0 * (left0 a).map star =
    right0 (star a) * j0
  j1_left : ∀ a, j1 * (left1 a).map star =
    right1 (star a) * j1
  j_differential :
    j1 * differential.map star = differential * j0
  j_differentialAdjoint :
    j0 * (differentialᴴ).map star = differentialᴴ * j1

namespace Packet

variable (P : Packet (A := A) (I := I) (J := J))

abbrev HIndex (_P : Packet (A := A) (I := I) (J := J)) := I ⊕ J

@[simp] theorem map_star_zero {M N : Type*} :
    (0 : Matrix M N ℂ).map star = 0 := by
  ext i j
  simp

/-- SP.8: the finite Hodge--Dirac matrix. -/
def dirac : Matrix P.HIndex P.HIndex ℂ :=
  Matrix.fromBlocks 0 P.differentialᴴ P.differential 0

/-- SP.8: the even grading. -/
def grading : Matrix P.HIndex P.HIndex ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- SP.7: left representation on zero- and one-forms. -/
def representation (a : A) : Matrix P.HIndex P.HIndex ℂ :=
  Matrix.fromBlocks (P.left0 a) 0 0 (P.left1 a)

/-- SP.12: the commuting opposite representation. -/
def oppositeRepresentation (b : A) : Matrix P.HIndex P.HIndex ℂ :=
  Matrix.fromBlocks (P.right0 b) 0 0 (P.right1 b)

/-- Matrix commutator. -/
def commutator (X Y : Matrix P.HIndex P.HIndex ℂ) : Matrix P.HIndex P.HIndex ℂ :=
  X * Y - Y * X

/-- The coordinate antiunitary is x maps to j * conjugate(x). -/
def realMatrix : Matrix P.HIndex P.HIndex ℂ :=
  Matrix.fromBlocks P.j0 0 0 P.j1

theorem dirac_isHermitian : P.dirac.IsHermitian := by
  unfold dirac
  rw [Matrix.isHermitian_fromBlocks_iff]
  simp

theorem dirac_odd :
    P.dirac * P.grading + P.grading * P.dirac = 0 := by
  simp only [dirac, grading, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  rw [Matrix.fromBlocks_add]
  simp

theorem top_commutator_block (a : A) :
    P.differentialᴴ * P.left1 a - P.left0 a * P.differentialᴴ =
      -(P.B (star a))ᴴ := by
  have h := congrArg Matrix.conjTranspose (P.leibniz (star a))
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul] at h
  rw [P.left0_star, P.left1_star, star_star] at h
  calc
    P.differentialᴴ * P.left1 a - P.left0 a * P.differentialᴴ =
        -(P.left0 a * P.differentialᴴ -
          P.differentialᴴ * P.left1 a) := by abel
    _ = -(P.B (star a))ᴴ := congrArg Neg.neg h

/-- SP.9, derived from the Leibniz rule and adjoint compatibility. -/
theorem dirac_commutator_formula (a : A) :
    P.commutator P.dirac (P.representation a) =
      Matrix.fromBlocks 0 (-(P.B (star a))ᴴ) (P.B a) 0 := by
  simp only [commutator, dirac, representation,
    Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, sub_eq_add_neg]
  rw [Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  rw [Matrix.fromBlocks_inj]
  exact ⟨by simp,
    by simpa [sub_eq_add_neg] using P.top_commutator_block a,
    by simpa [sub_eq_add_neg] using P.leibniz a,
    by simp⟩

/-- SP.10: for a self-adjoint algebra element the commutator norm is exactly
the differential block norm. -/
theorem commutator_norm_eq_B {a : A} (ha : star a = a) :
    ‖P.commutator P.dirac (P.representation a)‖ = ‖P.B a‖ := by
  rw [P.dirac_commutator_formula, ha]
  exact NCG.FiniteSpectralizationBlockNormExact.norm_offDiagonal (P.B a)

/-- Vanishing of the Lipschitz block is equivalent to vanishing of the
source-minimal differential vector. -/
theorem B_eq_zero_iff_partialVector_eq_zero (a : A) :
    P.B a = 0 ↔ P.partialVector a = 0 := by
  constructor
  · intro h
    rw [← P.B_unit a, h, Matrix.zero_mulVec]
  · exact P.B_zero_of_partial_zero a

def KernelConstants : Prop :=
  ∀ a : A, P.partialVector a = 0 ↔ ∃ z : ℂ, a = z • (1 : A)

def ConnesMetricFinite : Prop :=
  ∀ a : A, P.B a = 0 ↔ ∃ z : ℂ, a = z • (1 : A)

/-- The finite Connes metric criterion in SP.10. -/
theorem connesMetricFinite_iff_kernelConstants :
    P.ConnesMetricFinite ↔ P.KernelConstants := by
  simp only [ConnesMetricFinite, KernelConstants]
  constructor <;> intro h a
  · rw [← P.B_eq_zero_iff_partialVector_eq_zero]
    exact h a
  · rw [P.B_eq_zero_iff_partialVector_eq_zero]
    exact h a

/-- Order zero in SP.13. -/
theorem order_zero (a b : A) :
    P.commutator (P.representation a) (P.oppositeRepresentation b) = 0 := by
  simp [commutator, representation, oppositeRepresentation,
    Matrix.fromBlocks_multiply, P.commute0, P.commute1]

theorem top_first_order_block (a b : A) :
    (-(P.B (star a))ᴴ) * P.right1 b =
      P.right0 b * (-(P.B (star a))ᴴ) := by
  have h := congrArg Matrix.conjTranspose (P.B_right (star a) (star b))
  simp only [Matrix.conjTranspose_mul] at h
  rw [P.right0_star, P.right1_star, star_star] at h
  ext i j
  have hij := congrArg
    (fun M : Matrix I J ℂ => -(M i j)) h.symm
  simpa [Matrix.mul_apply] using hij

/-- First order in SP.13. -/
theorem first_order (a b : A) :
    P.commutator
      (P.commutator P.dirac (P.representation a))
      (P.oppositeRepresentation b) = 0 := by
  rw [P.dirac_commutator_formula]
  simp [commutator, oppositeRepresentation, Matrix.fromBlocks_multiply,
    P.B_right, P.top_first_order_block]

theorem realMatrix_sq :
    P.realMatrix * P.realMatrix.map star = 1 := by
  unfold realMatrix
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  exact ⟨by simpa using P.j0_sq, by simp, by simp,
    by simpa using P.j1_sq⟩

theorem realMatrix_intertwines_dirac :
    P.realMatrix * P.dirac.map star = P.dirac * P.realMatrix := by
  unfold realMatrix dirac
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  exact ⟨by simp, by simpa using P.j_differentialAdjoint,
    by simpa using P.j_differential, by simp⟩

theorem realMatrix_commutes_grading :
    P.realMatrix * P.grading.map star = P.grading * P.realMatrix := by
  have hneg : ((-1 : Matrix J J ℂ).map star) = -1 := by
    ext i j
    simp [Matrix.one_apply]
  unfold realMatrix grading
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  rw [hneg]
  simp

theorem realMatrix_implements_opposite (b : A) :
    P.realMatrix * (P.representation (star b)).map star *
        P.realMatrix.map star =
      P.oppositeRepresentation b := by
  simp only [realMatrix, representation, oppositeRepresentation,
    Matrix.fromBlocks_map, map_star_zero, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [P.j0_left, P.j1_left, star_star]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rw [mul_assoc, P.j0_sq, mul_one]
  · exact ⟨by simp, by simp, by rw [mul_assoc, P.j1_sq, mul_one]⟩

/-- Complete coordinate certificate for the canonical real even finite
spectralization. -/
theorem canonical_finite_real_even_spectralization :
    P.dirac.IsHermitian ∧
    (P.dirac * P.grading + P.grading * P.dirac = 0) ∧
    (∀ a, P.commutator P.dirac (P.representation a) =
      Matrix.fromBlocks 0 (-(P.B (star a))ᴴ) (P.B a) 0) ∧
    (∀ a, star a = a →
      ‖P.commutator P.dirac (P.representation a)‖ = ‖P.B a‖) ∧
    (P.ConnesMetricFinite ↔ P.KernelConstants) ∧
    (∀ a b, P.commutator (P.representation a)
      (P.oppositeRepresentation b) = 0) ∧
    (∀ a b, P.commutator
      (P.commutator P.dirac (P.representation a))
      (P.oppositeRepresentation b) = 0) ∧
    P.realMatrix * P.realMatrix.map star = 1 ∧
    P.realMatrix * P.dirac.map star = P.dirac * P.realMatrix ∧
    P.realMatrix * P.grading.map star = P.grading * P.realMatrix := by
  exact ⟨P.dirac_isHermitian, P.dirac_odd,
    P.dirac_commutator_formula, fun a => P.commutator_norm_eq_B,
    P.connesMetricFinite_iff_kernelConstants, P.order_zero, P.first_order,
    P.realMatrix_sq, P.realMatrix_intertwines_dirac,
    P.realMatrix_commutes_grading⟩

end Packet

end

end NCG.FiniteRealEvenSpectralizationExact
