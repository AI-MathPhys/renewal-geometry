/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ActiveNoRouting
import NCG.Grand.FreshEndpointRetainedRecord

/-!
# Concrete retained-private no-routing

This instantiates `thm:active-private-no-routing` on the actual two retained
private record states.  Later active Reads are defined on the fresh hub
marginal (the manuscript's discard wiring), so no separate factorization
hypothesis is exposed.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- The old-private contrast retained across the completed reset. -/
noncomputable def retainedPrivateContrast : Matrix (Fin 2) (Fin 2) ℂ :=
  privateRecordState hubR0 - privateRecordState hubR1

/-- The retained old-private contrast is traceless. -/
theorem retainedPrivateContrast_trace : retainedPrivateContrast.trace = 0 := by
  rw [retainedPrivateContrast, Matrix.trace_sub]
  have h0 : (privateRecordState hubR0).trace = 1 := by
    change (Matrix.vecMulVec hubR0 (star hubR0)).trace = 1
    rw [show (Matrix.vecMulVec hubR0 (star hubR0)).trace =
        star hubR0 ⬝ᵥ hubR0 by
      simp [Matrix.trace, dotProduct, Matrix.vecMulVec_apply]
      ring]
    exact retained_private_records_normalized.1
  have h1 : (privateRecordState hubR1).trace = 1 := by
    change (Matrix.vecMulVec hubR1 (star hubR1)).trace = 1
    rw [show (Matrix.vecMulVec hubR1 (star hubR1)).trace =
        star hubR1 ⬝ᵥ hubR1 by
      simp [Matrix.trace, dotProduct, Matrix.vecMulVec_apply]
      ring]
    exact retained_private_records_normalized.2
  rw [h0, h1, sub_self]

/-- The fresh hub state written at the completed-private cut. -/
noncomputable def completedPrivateFreshHub : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • 1

/-- `thm:active-private-no-routing` for the concrete renewal source.  Every
active recurrent Read is applied after discarding the old private factor;
hence the retained contrast contributes neither an active coordinate nor an
active Gram entry. -/
theorem concrete_active_private_no_routing
    {y : Type*} [Fintype y]
    (Cact : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix y y ℂ) :
    (∀ z : ℂ, Cact (partialTraceRight
      (completedPrivateFreshHub ⊗ₖ (z • retainedPrivateContrast))) = 0)
    ∧ (∀ z w : ℂ,
      ((Cact (partialTraceRight
          (completedPrivateFreshHub ⊗ₖ (z • retainedPrivateContrast))))ᴴ *
        Cact (partialTraceRight
          (completedPrivateFreshHub ⊗ₖ (w • retainedPrivateContrast)))).trace = 0) := by
  let Jp : ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun z => z • retainedPrivateContrast
  have htr : ∀ z, (Jp z).trace = 0 := by
    intro z
    simp [Jp, Matrix.trace_smul, retainedPrivateContrast_trace]
  have h := active_private_no_routing
    (W := Matrix y y ℂ) completedPrivateFreshHub Jp htr
  refine ⟨?_, ?_⟩
  · exact h.2.1 Cact
  · intro z w
    rw [h.2.1 Cact z, h.2.1 Cact w, Matrix.conjTranspose_zero,
      Matrix.zero_mul, Matrix.trace_zero]

end NCG
