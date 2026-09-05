/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FiniteResetRecordAudit
import NCG.Grand.FreshEndpointRetainedRecord

/-!
# Counterexamples separating mixing, freshness, and renewal from reset

The final sentence of `thm:reset-record-audit` is witnessed here by explicit
binary systems.  Reference renewal can be the identity branch; target mixing
can be strict contraction toward the maximally mixed state while retaining a
nonzero fraction of every traceless record; and a fresh hub endpoint can
coexist with two distinct private output records.
-/

open Matrix
open scoped ComplexOrder MatrixOrder ComplexStarModule Kronecker

namespace NCG

/-- The two computational-basis density matrices. -/
noncomputable def binaryStateZero : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, 0]

noncomputable def binaryStateOne : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![0, 1]

/-- The maximally mixed binary state. -/
noncomputable def binaryMaximallyMixed : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem binaryStateZero_posSemidef : binaryStateZero.PosSemidef := by
  rw [binaryStateZero, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem binaryStateOne_posSemidef : binaryStateOne.PosSemidef := by
  rw [binaryStateOne, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem binaryMaximallyMixed_posSemidef :
    binaryMaximallyMixed.PosSemidef := by
  rw [binaryMaximallyMixed]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
    norm_num [Complex.nonneg_iff])

theorem binaryState_traces :
    binaryStateZero.trace = 1 ∧ binaryStateOne.trace = 1 ∧
      binaryMaximallyMixed.trace = 1 := by
  norm_num [binaryStateZero, binaryStateOne, binaryMaximallyMixed,
    Matrix.trace_fin_two]

theorem binaryStateZero_ne_binaryStateOne :
    binaryStateZero ≠ binaryStateOne := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [binaryStateZero, binaryStateOne, Matrix.diagonal_apply] at h00

/-! ## Reference renewal -/

/-- The identity branch: it renews every chosen reference state but erases
nothing. -/
def binaryIdentityBranch :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.id

theorem binaryIdentityBranch_positive :
    IsPositiveMatrixBranch binaryIdentityBranch := by
  intro X hX
  exact hX

/-- Reference renewal alone neither forces complete reset nor erases a
distinguishing record. -/
theorem referenceRenewal_does_not_imply_reset_or_erasure :
    binaryIdentityBranch binaryMaximallyMixed = binaryMaximallyMixed
    ∧ ¬ IsCompleteAtomicReset binaryIdentityBranch
        binaryIdentityBranch_positive
    ∧ binaryIdentityBranch binaryStateZero ≠
        binaryIdentityBranch binaryStateOne := by
  refine ⟨rfl, ?_, ?_⟩
  · exact not_completeAtomicReset_of_distinct_normalized_outputs
      binaryIdentityBranch binaryIdentityBranch_positive
      binaryStateZero binaryStateOne binaryStateZero_posSemidef
      binaryStateOne_posSemidef binaryState_traces.1
      binaryState_traces.2.1 binaryStateZero_ne_binaryStateOne
  · exact binaryStateZero_ne_binaryStateOne

/-! ## Strict target mixing -/

/-- A half-depolarizing branch: one half of the input is retained and one
half is replaced by the maximally mixed state. -/
noncomputable def binaryHalfDepolarizing :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • LinearMap.id +
    (2 : ℂ)⁻¹ • matrixAtomicReset (1 : Matrix (Fin 2) (Fin 2) ℂ)
      binaryMaximallyMixed

theorem binaryHalfDepolarizing_apply
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    binaryHalfDepolarizing X =
      (2 : ℂ)⁻¹ • X + (2 : ℂ)⁻¹ • (X.trace • binaryMaximallyMixed) := by
  simp [binaryHalfDepolarizing, matrixAtomicReset_apply]

theorem binaryHalfDepolarizing_positive :
    IsPositiveMatrixBranch binaryHalfDepolarizing := by
  intro X hX
  rw [binaryHalfDepolarizing_apply]
  exact (hX.smul (by norm_num [Complex.nonneg_iff])).add
    ((binaryMaximallyMixed_posSemidef.smul hX.trace_nonneg).smul
      (by norm_num [Complex.nonneg_iff]))

theorem binaryHalfDepolarizing_trace
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (binaryHalfDepolarizing X).trace = X.trace := by
  rw [binaryHalfDepolarizing_apply, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    binaryState_traces.2.2]
  ring

/-- On the trace-one affine hyperplane the displacement from the target is
contracted exactly by `1/2`. -/
theorem binaryHalfDepolarizing_target_contraction
    (X : Matrix (Fin 2) (Fin 2) ℂ) (htr : X.trace = 1) :
    binaryHalfDepolarizing X - binaryMaximallyMixed =
      (2 : ℂ)⁻¹ • (X - binaryMaximallyMixed) := by
  rw [binaryHalfDepolarizing_apply, htr]
  ext i j
  simp [Matrix.sub_apply]
  ring

theorem binaryHalfDepolarizing_distinguishes_basis_states :
    binaryHalfDepolarizing binaryStateZero ≠
      binaryHalfDepolarizing binaryStateOne := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [binaryHalfDepolarizing_apply, binaryStateZero, binaryStateOne,
    binaryMaximallyMixed, Matrix.trace_fin_two, Matrix.diagonal_apply] at h00

/-- Exact target contraction does not imply one-step atomic reset or global
record erasure. -/
theorem targetMixing_does_not_imply_reset_or_erasure :
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, X.trace = 1 →
      binaryHalfDepolarizing X - binaryMaximallyMixed =
        (2 : ℂ)⁻¹ • (X - binaryMaximallyMixed))
    ∧ ¬ IsCompleteAtomicReset binaryHalfDepolarizing
        binaryHalfDepolarizing_positive
    ∧ binaryHalfDepolarizing binaryStateZero ≠
        binaryHalfDepolarizing binaryStateOne := by
  refine ⟨binaryHalfDepolarizing_target_contraction, ?_,
    binaryHalfDepolarizing_distinguishes_basis_states⟩
  exact not_completeAtomicReset_of_distinct_normalized_outputs
    binaryHalfDepolarizing binaryHalfDepolarizing_positive
    binaryStateZero binaryStateOne binaryStateZero_posSemidef
    binaryStateOne_posSemidef
    (binaryHalfDepolarizing_trace _ |>.trans binaryState_traces.1)
    (binaryHalfDepolarizing_trace _ |>.trans binaryState_traces.2.1)
    binaryHalfDepolarizing_distinguishes_basis_states

/-! ## Fresh endpoint -/

/-- A fresh maximally mixed hub marginal coexists with unequal full outputs
and unequal retained private states. -/
theorem freshEndpoint_does_not_imply_reset_or_erasure :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      partialTraceRight (retainedRecordHubChannel ρ) =
        ρ.trace • binaryMaximallyMixed)
    ∧ retainedRecordHubChannel binaryStateZero ≠
        retainedRecordHubChannel binaryStateOne
    ∧ privateRecordState hubR0 ≠ privateRecordState hubR1 := by
  refine ⟨?_, ?_, retained_private_record_states_ne⟩
  · simpa [binaryMaximallyMixed] using retained_record_hub_marginal
  · intro h
    have hr0 : privateRecordState hubR0 0 0 = 1 := by
      norm_num [privateRecordState, Matrix.vecMulVec_apply, hubR0,
        Pi.star_apply, RCLike.star_def]
    have hr1 : privateRecordState hubR1 0 0 = (1 / 25 : ℂ) := by
      norm_num [privateRecordState, Matrix.vecMulVec_apply, hubR1,
        Pi.star_apply, RCLike.star_def]
    have hz : retainedRecordHubChannel binaryStateZero (0, 0) (0, 0)
        = (1 / 2 : ℂ) := by
      norm_num [retainedRecordHubChannel, binaryStateZero,
        Matrix.diagonal_apply, Matrix.kronecker_apply, hr0, hr1]
    have ho : retainedRecordHubChannel binaryStateOne (0, 0) (0, 0)
        = (1 / 50 : ℂ) := by
      norm_num [retainedRecordHubChannel, binaryStateOne,
        Matrix.diagonal_apply, Matrix.kronecker_apply, hr0, hr1]
    have hentry := congrFun (congrFun h (0, 0)) (0, 0)
    rw [hz, ho] at hentry
    norm_num at hentry

/-- All three manuscript non-implications, assembled as explicit finite
witnesses. -/
theorem reset_nonimplication_counterexamples :
    (binaryIdentityBranch binaryMaximallyMixed = binaryMaximallyMixed
      ∧ ¬ IsCompleteAtomicReset binaryIdentityBranch
          binaryIdentityBranch_positive
      ∧ binaryIdentityBranch binaryStateZero ≠
          binaryIdentityBranch binaryStateOne)
    ∧ ((∀ X : Matrix (Fin 2) (Fin 2) ℂ, X.trace = 1 →
          binaryHalfDepolarizing X - binaryMaximallyMixed =
            (2 : ℂ)⁻¹ • (X - binaryMaximallyMixed))
      ∧ ¬ IsCompleteAtomicReset binaryHalfDepolarizing
          binaryHalfDepolarizing_positive
      ∧ binaryHalfDepolarizing binaryStateZero ≠
          binaryHalfDepolarizing binaryStateOne)
    ∧ ((∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
          partialTraceRight (retainedRecordHubChannel ρ) =
            ρ.trace • binaryMaximallyMixed)
      ∧ retainedRecordHubChannel binaryStateZero ≠
          retainedRecordHubChannel binaryStateOne
      ∧ privateRecordState hubR0 ≠ privateRecordState hubR1) :=
  ⟨referenceRenewal_does_not_imply_reset_or_erasure,
    targetMixing_does_not_imply_reset_or_erasure,
    freshEndpoint_does_not_imply_reset_or_erasure⟩

end NCG
