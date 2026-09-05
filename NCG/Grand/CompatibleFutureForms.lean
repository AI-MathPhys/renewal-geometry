/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HilbertLimitBoundedAction
import NCG.Grand.AFInductiveLimitState
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Compatible future forms

This file supplies the construction layer of
`thm:compatible-future-forms` from the Gran-Tensor manuscript.

The algebraic direct limit, equipped with the positive-definite inner product
induced by a compatible faithful family, is represented by a pre-Hilbert space
`V`.  Its Hilbert direct limit is its canonical uniform completion.  For an
increasing family of finite-stage subspaces covering `V), a compatible
algebraic action extends to the Hilbert direct limit exactly when its
finite-stage operator bounds admit one common constant.  The extension is
unique.

Compatible GNS forms provide the required common constant by
`CompatibleState.norm_completionGNSRepresentation_apply_le`.
-/

noncomputable section

open Filter

namespace NCG
namespace CompatibleFutureForms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The Hilbert direct limit of the algebraic compatible-form union. -/
abbrev HilbertDirectLimit (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] :=
  UniformSpace.Completion V

/-- Every algebraic vector embeds isometrically in the compatible-form Hilbert
direct limit. -/
theorem algebraicInclusion_isometry :
    Isometry ((↑) : V → HilbertDirectLimit V) :=
  UniformSpace.Completion.isometry_coe

/-- The algebraic compatible-form union is dense in its Hilbert direct limit. -/
theorem algebraicInclusion_dense :
    DenseRange ((↑) : V → HilbertDirectLimit V) :=
  UniformSpace.Completion.denseRange_coe

/-- Exact compatible-future-forms theorem on the canonical Hilbert completion.

The equality `⨆ n, S n = ⊤` says that the stage spaces exhaust the algebraic
direct limit.  The displayed iff is the manuscript's
`β_g(a) < ∞` criterion, with a common real bound in place of an extended-real
supremum. -/
theorem boundedAction_iff_uniformStageBound
    (S : ℕ → Submodule ℂ V) (hmono : Monotone S)
    (hcover : ⨆ n, S n = ⊤)
    (T₀ : V →ₗ[ℂ] V) :
    ((∃ T : HilbertDirectLimit V →L[ℂ] HilbertDirectLimit V,
        ∀ x : V, T (x : HilbertDirectLimit V) =
          (T₀ x : HilbertDirectLimit V)) ↔
      (∃ C : ℝ, ∀ n, ∀ (x : V), x ∈ S n →
        ‖T₀ x‖ ≤ C * ‖x‖))
    ∧ (∀ T T' : HilbertDirectLimit V →L[ℂ] HilbertDirectLimit V,
        (∀ x : V, T (x : HilbertDirectLimit V) =
          (T₀ x : HilbertDirectLimit V)) →
        (∀ x : V, T' (x : HilbertDirectLimit V) =
          (T₀ x : HilbertDirectLimit V)) →
        T = T') := by
  have hmem : ∀ x : V, ∃ n, x ∈ S n := by
    intro x
    have hx : x ∈ (⨆ n, S n : Submodule ℂ V) := by
      rw [hcover]
      trivial
    exact (Submodule.mem_iSup_of_directed S hmono.directed_le).mp hx
  constructor
  · constructor
    · rintro ⟨T, hT⟩
      refine ⟨‖T‖, fun n x hx => ?_⟩
      have hbound := T.le_opNorm (x : HilbertDirectLimit V)
      rw [hT x] at hbound
      simpa using hbound
    · rintro ⟨C, hC⟩
      have hbound : ∀ x : V, ‖T₀ x‖ ≤ C * ‖x‖ := by
        intro x
        obtain ⟨n, hx⟩ := hmem x
        exact hC n x hx
      let Tpre : V →L[ℂ] V := T₀.mkContinuous C hbound
      refine ⟨Tpre.completion, ?_⟩
      intro x
      exact Tpre.completion_apply_coe x
  · intro T T' hT hT'
    ext z
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_eq T.continuous T'.continuous
    | ih x =>
        rw [hT x, hT' x]

end CompatibleFutureForms
end NCG
