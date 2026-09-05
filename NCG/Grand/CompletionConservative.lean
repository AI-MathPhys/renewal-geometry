/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# Compatibility with the operationally complete Grand Tensor
  (`thm:SM-completion-conservative`, Gran-Tensor manuscript)

* `sm_completion_conservative`:
  (i) record discard recovers the old process exactly: the
      partial trace over the new record leg of `A ⊗ W` with a
      normalized writer state (`Tr W = 1`) is `A`;
  (ii) the old history algebra embeds by a unital
      `*`-monomorphism `a ↦ a ⊗ I`: multiplicative, unital,
      star-preserving, and injective — all old word relations,
      multiplication, involution, and null classes are
      preserved.

Rendering disclosed: (iii) the isometric physical-metric
clause and (iv) the central-density regular-trace transport
cite `thm:cutoff-compatibility` (its finite content is the
proved regular-trace and cutoff records); (v) record survival
and transient forgetting are the proved `record_survival` and
`record_sink_nullity` layers. The concrete completed Kraus
operators (`2⁻¹U_{ab}` with deterministic writers) instantiate
the embedding.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:SM-completion-conservative`. -/
theorem sm_completion_conservative
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    [DecidableEq r] [Nonempty r] :
    -- (i) record discard recovers the old branch
    (∀ (A : Matrix d d ℂ) (W : Matrix r r ℂ),
      W.trace = 1 →
      partialTraceRight (dA := d) (dK := r) (A ⊗ₖ W) = A)
    -- (ii) unital *-monomorphism a ↦ a ⊗ I
    ∧ (∀ a b : Matrix d d ℂ,
        (a * b) ⊗ₖ (1 : Matrix r r ℂ)
          = (a ⊗ₖ (1 : Matrix r r ℂ))
            * (b ⊗ₖ (1 : Matrix r r ℂ)))
    ∧ ((1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix r r ℂ)
        = (1 : Matrix (d × r) (d × r) ℂ))
    ∧ (∀ a : Matrix d d ℂ,
        aᴴ ⊗ₖ (1 : Matrix r r ℂ)
          = (a ⊗ₖ (1 : Matrix r r ℂ))ᴴ)
    ∧ (∀ a b : Matrix d d ℂ,
        a ⊗ₖ (1 : Matrix r r ℂ) = b ⊗ₖ (1 : Matrix r r ℂ) →
        a = b) := by
  refine ⟨?_, ?_, Matrix.one_kronecker_one, ?_, ?_⟩
  · intro A W hW
    ext i j
    simp only [partialTraceRight, Matrix.of_apply,
      Matrix.kroneckerMap_apply]
    rw [← Finset.mul_sum,
      show ∑ k, W k k = W.trace from rfl, hW, mul_one]
  · intro a b
    rw [show (a * b) ⊗ₖ (1 : Matrix r r ℂ)
        = (a * b) ⊗ₖ ((1 : Matrix r r ℂ)
          * (1 : Matrix r r ℂ)) from by
      rw [Matrix.one_mul]]
    rw [Matrix.mul_kronecker_mul]
  · intro a
    rw [Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
  · intro a b hab
    obtain ⟨k⟩ := (inferInstance : Nonempty r)
    ext i j
    have h := Matrix.ext_iff.mpr hab (i, k) (j, k)
    simpa [Matrix.kroneckerMap_apply, Matrix.one_apply]
      using h

end NCG
