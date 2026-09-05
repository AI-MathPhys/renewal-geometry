/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalCompletion

/-!
# The canonical relational-completion process morphism

This file supplies the RC.7 packaging missing from `thm:relational-completion`.
The forgetful map and the old/refined branches are bundled into an honest finite-word
process morphism.  Its naturality is proved for every word, and an explicit one-sector
lift proves that every old initial state and every finite old process history is in the
image of the relational completion.
-/

open Matrix

namespace NCG
namespace RelationalCompletionProcessMorphism

/-- A morphism of deterministic labelled process presentations. -/
structure FiniteWordProcessMorphism (O New Old : Type*) where
  newStep : O → New → New
  oldStep : O → Old → Old
  forget : New → Old
  commutes : ∀ o x, forget (newStep o x) = oldStep o (forget x)

namespace FiniteWordProcessMorphism

/-- Run a finite process word, in chronological `foldl` order. -/
def run {O State : Type*} (step : O → State → State)
    (word : List O) (x : State) : State :=
  word.foldl (fun state o => step o state) x

/-- A process morphism commutes with every finite process word. -/
theorem run_naturality {O New Old : Type*}
    (M : FiniteWordProcessMorphism O New Old) (word : List O) (x : New) :
    M.forget (run M.newStep word x) = run M.oldStep word (M.forget x) := by
  exact RelationalCompletion.forget_intertwines_every_word
    M.oldStep M.newStep M.forget M.commutes word x

end FiniteWordProcessMorphism

/-- **RC.7.** The normalized relational kernel defines a canonical morphism from
the relationally completed process to the old process. -/
noncomputable def canonicalProcessMorphism
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : RelationalCompletion.Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    FiniteWordProcessMorphism O (Z → Matrix d d ℂ) (Matrix d d ℂ) where
  newStep o ρ := RelationalCompletion.totalBranch K Φ o ρ
  oldStep o A := Φ o A
  forget := RelationalCompletion.forgetRelation
  commutes := RelationalCompletion.forget_totalBranch K Φ

/-- The RC.7 morphism recovers the old process after every finite branch word. -/
theorem canonical_process_morphism_every_word
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : RelationalCompletion.Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (word : List O) (ρ : Z → Matrix d d ℂ) :
    RelationalCompletion.forgetRelation
        (FiniteWordProcessMorphism.run
          (canonicalProcessMorphism K Φ).newStep word ρ) =
      FiniteWordProcessMorphism.run
        (canonicalProcessMorphism K Φ).oldStep word
        (RelationalCompletion.forgetRelation ρ) :=
  (canonicalProcessMorphism K Φ).run_naturality word ρ

/-- Embed an old state in one selected persistent relation sector. -/
def oneSectorLift {Z d : Type*} [DecidableEq Z]
    (z₀ : Z) (A : Matrix d d ℂ) : Z → Matrix d d ℂ :=
  fun z => if z = z₀ then A else 0

/-- Forgetting the explicit one-sector lift is exactly the old state. -/
theorem forget_oneSectorLift
    {Z d : Type*} [Fintype Z] [DecidableEq Z]
    (z₀ : Z) (A : Matrix d d ℂ) :
    RelationalCompletion.forgetRelation (oneSectorLift z₀ A) = A := by
  classical
  simp [RelationalCompletion.forgetRelation, oneSectorLift]

/-- Every old initial state has an explicit relational lift, and the entire old finite
history starting there is the forgetful image of the corresponding refined history. -/
theorem every_old_finite_history_has_relational_lift
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    [DecidableEq Z] [Nonempty Z]
    (K : RelationalCompletion.Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (A : Matrix d d ℂ) :
    ∃ ρ : Z → Matrix d d ℂ,
      RelationalCompletion.forgetRelation ρ = A ∧
      ∀ word : List O,
        RelationalCompletion.forgetRelation
            (FiniteWordProcessMorphism.run
              (canonicalProcessMorphism K Φ).newStep word ρ) =
          FiniteWordProcessMorphism.run
            (canonicalProcessMorphism K Φ).oldStep word A := by
  classical
  let z₀ : Z := Classical.choice inferInstance
  refine ⟨oneSectorLift z₀ A, forget_oneSectorLift z₀ A, fun word => ?_⟩
  rw [canonical_process_morphism_every_word K Φ word]
  simp only [forget_oneSectorLift]

/-- Exact RC.7 quotient statement: the canonical process morphism is surjective on
states, and its naturality identifies every refined finite history with the old history
of its forgotten initial state. -/
theorem relational_completion_is_process_quotient
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    [DecidableEq Z] [Nonempty Z]
    (K : RelationalCompletion.Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    Function.Surjective (canonicalProcessMorphism K Φ).forget ∧
      ∀ word : List O, ∀ ρ : Z → Matrix d d ℂ,
        (canonicalProcessMorphism K Φ).forget
            (FiniteWordProcessMorphism.run
              (canonicalProcessMorphism K Φ).newStep word ρ) =
          FiniteWordProcessMorphism.run
            (canonicalProcessMorphism K Φ).oldStep word
            ((canonicalProcessMorphism K Φ).forget ρ) := by
  constructor
  · intro A
    obtain ⟨ρ, hρ, _⟩ := every_old_finite_history_has_relational_lift K Φ A
    exact ⟨ρ, hρ⟩
  · exact fun word ρ => (canonicalProcessMorphism K Φ).run_naturality word ρ

end RelationalCompletionProcessMorphism
end NCG
