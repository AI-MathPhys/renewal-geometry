/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PredictiveActionCarriersExact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Closed predictive and reducing carriers on Hilbert space

This file removes the finite-dimensional restriction from the carrier layer of
`thm:GT-predictive-action-carriers`.  Algebraic word spans are replaced by
their Hilbert closures, primitive branches are continuous, and the projection
criterion is stated as the literal bounded-operator identity
`(I-P₊) Uₐ† P₊ = 0`.
-/

open Submodule NCG.AdaptiveWordLocalizerStop

noncomputable section

namespace NCG
namespace PredictiveActionCarriersHilbert

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The closed span of all forward words applied to the source. -/
def forwardCarrier (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    ClosedSubmodule ℂ E where
  toSubmodule := (generatedCarrier (fun a => (U a : E →ₗ[ℂ] E)) V).topologicalClosure
  isClosed' := Submodule.isClosed_topologicalClosure _

/-- A branch or its Hilbert adjoint, as a continuous star-letter. -/
def starLetters (U : ι → E →L[ℂ] E) : ι ⊕ ι → E →L[ℂ] E
  | Sum.inl a => U a
  | Sum.inr a => (U a).adjoint

/-- The closed span of all words in the branches and their adjoints. -/
def twoSidedCarrier (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    ClosedSubmodule ℂ E where
  toSubmodule :=
    (generatedCarrier (fun a => (starLetters U a : E →ₗ[ℂ] E)) V).topologicalClosure
  isClosed' := Submodule.isClosed_topologicalClosure _

/-- A closed subspace reduces the branch family when it is invariant under
each branch and each Hilbert adjoint. -/
def Reduces (U : ι → E →L[ℂ] E) (M : Submodule ℂ E) : Prop :=
  ∀ a, M.map (U a : E →ₗ[ℂ] E) ≤ M ∧
    M.map ((U a).adjoint : E →ₗ[ℂ] E) ≤ M

theorem source_le_forwardCarrier (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    V ≤ (forwardCarrier U V : Submodule ℂ E) :=
  (source_le_generatedCarrier (fun a => (U a : E →ₗ[ℂ] E)) V).trans
    (Submodule.le_topologicalClosure _)

theorem forwardCarrier_invariant
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) (a : ι) :
    (forwardCarrier U V : Submodule ℂ E).map (U a : E →ₗ[ℂ] E) ≤
      (forwardCarrier U V : Submodule ℂ E) := by
  exact (Submodule.topologicalClosure_map (U a)
      (generatedCarrier (fun b => (U b : E →ₗ[ℂ] E)) V)).trans
    (Submodule.topologicalClosure_mono
      (generatedCarrier_invariant (fun b => (U b : E →ₗ[ℂ] E)) V a))

/-- The closed forward carrier is the unique minimum closed invariant carrier
containing the source. -/
theorem forwardCarrier_minimal
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E)
    (M : ClosedSubmodule ℂ E) (hV : V ≤ (M : Submodule ℂ E))
    (hinv : ∀ a, (M : Submodule ℂ E).map (U a : E →ₗ[ℂ] E) ≤ M) :
    (forwardCarrier U V : Submodule ℂ E) ≤ M := by
  apply Submodule.topologicalClosure_minimal
  · exact generatedCarrier_le_of_invariant
      (fun a => (U a : E →ₗ[ℂ] E)) V M hV hinv
  · exact M.isClosed

theorem source_le_twoSidedCarrier
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    V ≤ (twoSidedCarrier U V : Submodule ℂ E) :=
  (source_le_generatedCarrier
      (fun a => (starLetters U a : E →ₗ[ℂ] E)) V).trans
    (Submodule.le_topologicalClosure _)

theorem twoSidedCarrier_reduces
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    Reduces U (twoSidedCarrier U V : Submodule ℂ E) := by
  intro a
  constructor
  · exact (Submodule.topologicalClosure_map (U a)
        (generatedCarrier (fun s => (starLetters U s : E →ₗ[ℂ] E)) V)).trans
      (Submodule.topologicalClosure_mono
        (generatedCarrier_invariant
          (fun s => (starLetters U s : E →ₗ[ℂ] E)) V (Sum.inl a)))
  · exact (Submodule.topologicalClosure_map ((U a).adjoint)
        (generatedCarrier (fun s => (starLetters U s : E →ₗ[ℂ] E)) V)).trans
      (Submodule.topologicalClosure_mono
        (generatedCarrier_invariant
          (fun s => (starLetters U s : E →ₗ[ℂ] E)) V (Sum.inr a)))

/-- The closed two-sided carrier is the unique minimum closed reducing carrier
containing the source. -/
theorem twoSidedCarrier_minimal
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E)
    (M : ClosedSubmodule ℂ E) (hV : V ≤ (M : Submodule ℂ E))
    (hred : Reduces U (M : Submodule ℂ E)) :
    (twoSidedCarrier U V : Submodule ℂ E) ≤ M := by
  apply Submodule.topologicalClosure_minimal
  · apply generatedCarrier_le_of_invariant
      (fun s => (starLetters U s : E →ₗ[ℂ] E)) V M hV
    intro s
    cases s with
    | inl a => exact (hred a).1
    | inr a => exact (hred a).2
  · exact M.isClosed

theorem forwardCarrier_le_twoSided
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    (forwardCarrier U V : Submodule ℂ E) ≤ twoSidedCarrier U V :=
  forwardCarrier_minimal U V (twoSidedCarrier U V)
    (source_le_twoSidedCarrier U V)
    (fun a => (twoSidedCarrier_reduces U V a).1)

/-- The predictive carrier equals the minimum reducing carrier exactly when
it is invariant under every adjoint branch. -/
theorem carriers_eq_iff_adjoint_invariant
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    forwardCarrier U V = twoSidedCarrier U V ↔
      ∀ a, (forwardCarrier U V : Submodule ℂ E).map
        ((U a).adjoint : E →ₗ[ℂ] E) ≤ forwardCarrier U V := by
  constructor
  · intro h a
    rw [h]
    exact (twoSidedCarrier_reduces U V a).2
  · intro hadj
    apply ClosedSubmodule.toSubmodule_injective
    apply le_antisymm (forwardCarrier_le_twoSided U V)
    exact twoSidedCarrier_minimal U V (forwardCarrier U V)
      (source_le_forwardCarrier U V)
      (fun a => ⟨forwardCarrier_invariant U V a, hadj a⟩)

/-- Invariance of a closed subspace under a bounded operator is the literal
projection identity `(I-P) A P = 0`. -/
theorem invariant_iff_projection_identity
    (M : ClosedSubmodule ℂ E) (A : E →L[ℂ] E) :
    (M : Submodule ℂ E).map (A : E →ₗ[ℂ] E) ≤ M ↔
      ((1 : E →L[ℂ] E) - (M : Submodule ℂ E).starProjection) ∘L A ∘L
        (M : Submodule ℂ E).starProjection = 0 := by
  constructor
  · intro hinv
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply]
    have hmem : A ((M : Submodule ℂ E).starProjection x) ∈ M :=
      hinv ⟨_, (M : Submodule ℂ E).starProjection_apply_mem x, rfl⟩
    rw [(M : Submodule ℂ E).starProjection_eq_self_iff.mpr hmem, sub_self]
  · intro h
    rintro _ ⟨y, hy, rfl⟩
    have hp : (M : Submodule ℂ E).starProjection y = y :=
      (M : Submodule ℂ E).starProjection_eq_self_iff.mpr hy
    have hx := DFunLike.congr_fun h y
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply, hp] at hx
    rw [sub_eq_zero] at hx
    exact hx ▸ (M : Submodule ℂ E).starProjection_apply_mem (A y)

/-- **PA.3 on Hilbert space.**  Equality of the closed predictive and reducing
carriers is equivalent to `(I-P₊)Uₐ†P₊=0` for every primitive branch. -/
theorem carriers_eq_iff_projection_identity
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    forwardCarrier U V = twoSidedCarrier U V ↔
      ∀ a, ((1 : E →L[ℂ] E) -
          (forwardCarrier U V : Submodule ℂ E).starProjection) ∘L
        (U a).adjoint ∘L
          (forwardCarrier U V : Submodule ℂ E).starProjection = 0 := by
  rw [carriers_eq_iff_adjoint_invariant]
  apply forall_congr'
  intro a
  exact invariant_iff_projection_identity (forwardCarrier U V) (U a).adjoint

/-- The table-native adjoint innovation is the Gram `X†X`, hence positive,
and it vanishes exactly when the adjoint leakage `X=(I-P)A†P` vanishes. -/
theorem innovation_positive_and_eq_zero_iff
    (M : ClosedSubmodule ℂ E) (A : E →L[ℂ] E) :
    let X := ((1 : E →L[ℂ] E) - (M : Submodule ℂ E).starProjection) ∘L
      A.adjoint ∘L (M : Submodule ℂ E).starProjection
    let Iminus := X.adjoint ∘L X
    (∀ x, 0 ≤ (inner ℂ x (Iminus x)).re) ∧ (Iminus = 0 ↔ X = 0) := by
  dsimp only
  let X := ((1 : E →L[ℂ] E) - (M : Submodule ℂ E).starProjection) ∘L
    A.adjoint ∘L (M : Submodule ℂ E).starProjection
  change (∀ x, 0 ≤ (inner ℂ x ((X.adjoint ∘L X) x)).re) ∧
    (X.adjoint ∘L X = 0 ↔ X = 0)
  constructor
  · intro x
    rw [ContinuousLinearMap.comp_apply, X.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact sq_nonneg ‖X x‖
  · constructor
    · intro h
      ext x
      have hx := X.apply_norm_sq_eq_inner_adjoint_right x
      rw [h] at hx
      simp at hx
      exact hx
    · intro h
      rw [h]
      simp

/-- **PA.4 action autonomy on Hilbert space.**  All adjoint innovations vanish
exactly when the predictive carrier is already reducing. -/
theorem action_autonomy_iff
    (U : ι → E →L[ℂ] E) (V : Submodule ℂ E) :
    (∀ a,
      let X := ((1 : E →L[ℂ] E) -
          (forwardCarrier U V : Submodule ℂ E).starProjection) ∘L
        (U a).adjoint ∘L
          (forwardCarrier U V : Submodule ℂ E).starProjection
      X.adjoint ∘L X = 0) ↔
      forwardCarrier U V = twoSidedCarrier U V := by
  rw [carriers_eq_iff_projection_identity]
  apply forall_congr'
  intro a
  exact (innovation_positive_and_eq_zero_iff
    (forwardCarrier U V) (U a)).2

end PredictiveActionCarriersHilbert
end NCG
