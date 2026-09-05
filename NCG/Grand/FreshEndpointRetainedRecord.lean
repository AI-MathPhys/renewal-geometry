/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FreshEndpoint

/-!
# Fresh endpoint with a retained non-orthogonal record

This module gives the faithful channel from
`thm:fresh-endpoint-retained-record` in the Gran-Tensor manuscript.  Unlike the
older computational-basis model, the private factor here is built from the
same non-orthogonal record vectors whose overlap enters the discrimination
probability.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- The pure density matrix associated with a private record vector. -/
noncomputable def privateRecordState (r : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec r (star r)

/-- The manuscript's completed-private reset channel: a fresh maximally mixed
hub together with the retained, generally non-orthogonal, private record. -/
noncomputable def retainedRecordHubChannel
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
    (ρ 0 0 • privateRecordState hubR0
      + ρ 1 1 • privateRecordState hubR1)

/-- Both concrete private record vectors are normalized. -/
theorem retained_private_records_normalized :
    star hubR0 ⬝ᵥ hubR0 = 1 ∧ star hubR1 ⬝ᵥ hubR1 = 1 :=
  ⟨fresh_endpoint_retained_record.2.2.1.1,
    fresh_endpoint_retained_record.2.2.1.2.1⟩

/-- The retained private states are genuinely different, so the old private
record has not been erased. -/
theorem retained_private_record_states_ne :
    privateRecordState hubR0 ≠ privateRecordState hubR1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [privateRecordState, Matrix.vecMulVec_apply, hubR0, hubR1] at h00
  norm_num at h00

/-- The private factor in the reset channel has the same trace as the input. -/
theorem retained_private_factor_trace
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (ρ 0 0 • privateRecordState hubR0
      + ρ 1 1 • privateRecordState hubR1).trace = ρ.trace := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  simp only [privateRecordState]
  rw [show (Matrix.vecMulVec hubR0 (star hubR0)).trace =
      star hubR0 ⬝ᵥ hubR0 by
        simp [Matrix.trace, dotProduct, Matrix.vecMulVec_apply]
        ring]
  rw [show (Matrix.vecMulVec hubR1 (star hubR1)).trace =
      star hubR1 ⬝ᵥ hubR1 by
        simp [Matrix.trace, dotProduct, Matrix.vecMulVec_apply]
        ring]
  rw [retained_private_records_normalized.1,
    retained_private_records_normalized.2]
  simp [Matrix.trace_fin_two]

/-- The faithful retained-record reset channel preserves trace. -/
theorem retained_record_hub_channel_trace
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (retainedRecordHubChannel ρ).trace = ρ.trace := by
  unfold retainedRecordHubChannel
  rw [Matrix.trace_kronecker, retained_private_factor_trace,
    Matrix.trace_smul, Matrix.trace_one]
  simp

/-- Tracing out the private factor leaves a fresh maximally mixed hub.  In
particular, for trace-one inputs this marginal is exactly `I₂ / 2`, independent
of the accessible old private record. -/
theorem retained_record_hub_marginal
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    partialTraceRight (retainedRecordHubChannel ρ)
      = ρ.trace • ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hcollapse : ∀ (A B : Matrix (Fin 2) (Fin 2) ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A :=
    (renewal_spectator_product LinearMap.id LinearMap.id
      (fun _ => rfl)).1
  unfold retainedRecordHubChannel
  rw [hcollapse, retained_private_factor_trace]

/-- The overlap used in the discrimination formula is the overlap of the
actual private states written by `retainedRecordHubChannel`. -/
theorem retained_private_record_overlap :
    star hubR0 ⬝ᵥ hubR1 = (1 / 5 : ℂ) :=
  fresh_endpoint_retained_record.2.2.1.2.2

/-- The equal-prior pure-state Helstrom expression for the two private states
written by the channel has the manuscript's exact value. -/
theorem retained_private_record_helstrom_value :
    (1 / 2 : ℝ) *
        (1 + Real.sqrt (1 - Complex.normSq (star hubR0 ⬝ᵥ hubR1)))
      = (5 + 2 * Real.sqrt 6) / 10 := by
  rw [retained_private_record_overlap]
  convert fresh_endpoint_retained_record.2.2.2 using 1
  norm_num [Complex.normSq_apply]

/-- `thm:fresh-endpoint-retained-record`: the exact non-orthogonal-record
channel, its independent fresh hub marginal, retention of distinct private
states, and the resulting equal-prior discrimination value. -/
theorem fresh_endpoint_retained_record_exact :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (retainedRecordHubChannel ρ).trace = ρ.trace)
    ∧ (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        partialTraceRight (retainedRecordHubChannel ρ)
          = ρ.trace • ((2 : ℂ)⁻¹ • 1))
    ∧ privateRecordState hubR0 ≠ privateRecordState hubR1
    ∧ star hubR0 ⬝ᵥ hubR1 = (1 / 5 : ℂ)
    ∧ ((1 / 2 : ℝ) *
          (1 + Real.sqrt (1 - Complex.normSq (star hubR0 ⬝ᵥ hubR1)))
        = (5 + 2 * Real.sqrt 6) / 10) := by
  exact ⟨retained_record_hub_channel_trace,
    retained_record_hub_marginal,
    retained_private_record_states_ne,
    retained_private_record_overlap,
    retained_private_record_helstrom_value⟩

end NCG
