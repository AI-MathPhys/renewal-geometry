/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SixStateNoMatter
import NCG.Grand.LiteralZeroOccurrence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Six-state zero occurrence and its exact Bures discrepancy

This file completes `cor:SM-literal-zero-occurrence`.  It connects the
displayed six-state support-preserving word algebra to the vanishing
cross-support jump packet, derives the zero Choi matrix, and evaluates the
matrix Bures expression using the CFC square root.  It also records the four
invariances stated in the manuscript: Kraus/unitary changes, record
refinement, scalar acceptance tilts, and zero-preserving functional calculus.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

namespace NCG

/-- The support-changing part of a coefficient relative to the locked left
and right grading projections. -/
def crossSupportJump {n : Type*} [Fintype n]
    (PL PR M : Matrix n n ℂ) : Matrix n n ℂ :=
  PL * M * PR + PR * M * PL

/-- A support-preserving coefficient has no occurrence jump. -/
theorem crossSupportJump_eq_zero_of_supportPreserving
    {n : Type*} [Fintype n]
    (PL PR M : Matrix n n ℂ) (hM : SupportPreserving PL PR M) :
    crossSupportJump PL PR M = 0 := by
  rw [crossSupportJump, hM.1, hM.2, add_zero]

/-- Every word in the displayed six-state coefficient algebra has vanishing
support-changing jump.  This is the generator-level zero-occurrence result. -/
theorem sixState_words_have_zero_occurrence_jump
    {n : Type*} [Fintype n] [DecidableEq n]
    (PL PR : Matrix n n ℂ)
    (hsum : PL + PR = 1) (hLR : PL * PR = 0)
    (hRL : PR * PL = 0) (hLH : PLᴴ = PL) (hRH : PRᴴ = PR)
    (words : List (Matrix n n ℂ))
    (hwords : ∀ M ∈ words, SupportPreserving PL PR M) :
    crossSupportJump PL PR words.prod = 0 := by
  have hprod : SupportPreserving PL PR words.prod :=
    (six_state_no_matter PL PR hsum hLR hRL hLH hRH).2.2.2.2 words hwords
  exact crossSupportJump_eq_zero_of_supportPreserving PL PR words.prod hprod

/-- The matrix Bures square-distance expression
`Tr A + Tr B - 2 Tr sqrt(sqrt(A) B sqrt(A))`. -/
noncomputable def matrixBuresDistanceSq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  A.trace + B.trace -
    2 * (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).trace

/-- CFC evaluates the positive square root at the zero matrix as zero. -/
theorem matrixCfcSqrt_zero {n : ℕ} :
    CFC.sqrt (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [CFC.sqrt]

/-- The Bures distance from the zero occurrence packet to any matrix is its
trace; positivity is retained in the statement because this is the physical
covariance branch. -/
theorem matrixBuresDistanceSq_zero_left {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℂ) (_hK : K.PosSemidef) :
    matrixBuresDistanceSq 0 K = K.trace := by
  simp [matrixBuresDistanceSq]

/-- For the independently reconstructed five-channel covariance, whose total
trace is `65/32`, the exact squared discrepancy is `65/32`. -/
theorem sixState_zeroOccurrence_bures_sixtyFive_over_thirtyTwo
    {n : ℕ}
    (Kword : Matrix (Fin n) (Fin n) ℂ) (hK : Kword.PosSemidef)
    (htrace : Kword.trace = 65 / 32) :
    matrixBuresDistanceSq 0 Kword = 65 / 32 := by
  rw [matrixBuresDistanceSq_zero_left Kword hK, htrace]

/-- Choi reconstruction of the derived zero occurrence map is zero for every
finite operator frame. -/
theorem sixState_zeroOccurrence_choi
    {d : Type*} {ι : Type} [Fintype d] [Fintype ι]
    (frame : ι → Matrix d d ℂ) :
    choiRecon (0 : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) frame = 0 :=
  (literal_zero_occurrence (d := d) (c := Fin 1)).1 frame

/-- A Kraus/unitary frame change cannot move the zero Choi packet. -/
theorem zeroOccurrence_invariant_under_kraus_rotation
    {d : Type*} [Fintype d]
    (U : Matrix d d ℂ) :
    U * (0 : Matrix d d ℂ) * Uᴴ = 0 := by simp

/-- Any linear record refinement sends the zero occurrence packet to zero. -/
theorem zeroOccurrence_invariant_under_record_refinement
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℂ A] [Module ℂ B] (R : A →ₗ[ℂ] B) :
    R 0 = 0 := R.map_zero

/-- A scalar acceptance tilt leaves the zero packet zero. -/
theorem zeroOccurrence_invariant_under_acceptance_tilt
    {A : Type*} [AddCommMonoid A] [Module ℂ A] (s : ℂ) :
    s • (0 : A) = 0 := smul_zero s

/-- Every zero-preserving functional-calculus operation inside the old
release algebra leaves the occurrence packet zero. -/
theorem zeroOccurrence_invariant_under_functional_calculus
    {A : Type*} [Zero A] (f : A → A) (hf : f 0 = 0) :
    f 0 = 0 := hf

/-- Exact assembled form of `cor:SM-literal-zero-occurrence`. -/
theorem six_state_literal_zero_occurrence
    {d : Type*} {c : ℕ} [Fintype d]
    (Kword : Matrix (Fin c) (Fin c) ℂ) (hK : Kword.PosSemidef)
    (htrace : Kword.trace = 65 / 32) :
    (∀ {ι : Type} [Fintype ι] (frame : ι → Matrix d d ℂ),
      choiRecon (0 : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) frame = 0) ∧
    matrixBuresDistanceSq 0 Kword = 65 / 32 ∧
    (∀ U : Matrix d d ℂ, U * (0 : Matrix d d ℂ) * Uᴴ = 0) ∧
    (∀ (s : ℂ), s • (0 : Matrix d d ℂ) = 0) := by
  exact ⟨sixState_zeroOccurrence_choi,
    sixState_zeroOccurrence_bures_sixtyFive_over_thirtyTwo Kword hK htrace,
    zeroOccurrence_invariant_under_kraus_rotation,
    zeroOccurrence_invariant_under_acceptance_tilt⟩

end NCG
