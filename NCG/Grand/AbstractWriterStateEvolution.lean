/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Abstract positive writer-state evolution

This file removes the ambient `B(H)` rendering from
`thm:GT-writer-state-derived-current`.  The writer carrier is an arbitrary
finite-dimensional complex normed space equipped with a declared positive
cone predicate and a distinguished unit.  Only positivity preservation,
unitality, and the right-generator identity are used.
-/

namespace NCG
namespace AbstractWriterStateEvolution

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [FiniteDimensional ℂ S]

/-- A positive normalized state on an abstract writer system. -/
structure IsWriterState (positive : S → Prop) (unit : S)
    (ω : S →L[ℂ] ℂ) : Prop where
  pos : ∀ a, positive a → ∃ r : ℝ, 0 ≤ r ∧ ω a = r
  unital : ω unit = 1

/-- A positive unital writer evolution. -/
structure IsPositiveUnital (positive : S → Prop) (unit : S)
    (T : S →L[ℂ] S) : Prop where
  pos : ∀ a, positive a → positive (T a)
  unital : T unit = unit

/-- The evolved state `ω_t = ω₀ ∘ T(t,0)`. -/
noncomputable def evolved (ω₀ : S →L[ℂ] ℂ) (T : S →L[ℂ] S) : S →L[ℂ] ℂ :=
  ω₀.comp T

@[simp] theorem evolved_apply (ω₀ : S →L[ℂ] ℂ)
    (T : S →L[ℂ] S) (f : S) : evolved ω₀ T f = ω₀ (T f) := rfl

/-- TR.10 in an arbitrary writer system: composition with a positive unital
map preserves positivity and normalization. -/
theorem evolved_isWriterState (positive : S → Prop) (unit : S)
    {ω₀ : S →L[ℂ] ℂ} (hω : IsWriterState positive unit ω₀)
    {T : S →L[ℂ] S} (hT : IsPositiveUnital positive unit T) :
    IsWriterState positive unit (evolved ω₀ T) where
  pos a ha := hω.pos (T a) (hT.pos a ha)
  unital := by rw [evolved_apply, hT.unital, hω.unital]

/-- Right-generator identity on a declared writer core. -/
def HasRightGenerator (T : ℝ → S →L[ℂ] S) (L : ℝ → S →L[ℂ] S)
    (core : Set S) : Prop :=
  ∀ f ∈ core, ∀ t : ℝ, HasDerivAt (fun s => T s f) (T t (L t f)) t

/-- The current defined from the evolved state and declared source writer. -/
noncomputable def current (ω₀ : S →L[ℂ] ℂ)
    (T : ℝ → S →L[ℂ] S) (source : ℝ → S →L[ℂ] ℂ)
    (t : ℝ) (f : S) : ℂ :=
  deriv (fun s => evolved ω₀ (T s) f) t + source t f

/-- Differentiating TR.10 on the generator core. -/
theorem hasDerivAt_evolved (ω₀ : S →L[ℂ] ℂ)
    (T : ℝ → S →L[ℂ] S) (L : ℝ → S →L[ℂ] S)
    {core : Set S} (hgen : HasRightGenerator T L core)
    {f : S} (hf : f ∈ core) (t : ℝ) :
    HasDerivAt (fun s => evolved ω₀ (T s) f)
      (evolved ω₀ (T t) (L t f)) t := by
  have h := (ω₀.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hgen f hf t)
  simpa [Function.comp_def, evolved_apply] using h

/-- TR.11: the target current is derived, rather than independently added. -/
theorem current_eq (ω₀ : S →L[ℂ] ℂ)
    (T : ℝ → S →L[ℂ] S) (L : ℝ → S →L[ℂ] S)
    (source : ℝ → S →L[ℂ] ℂ)
    {core : Set S} (hgen : HasRightGenerator T L core)
    {f : S} (hf : f ∈ core) (t : ℝ) :
    current ω₀ T source t f =
      evolved ω₀ (T t) (L t f) + source t f := by
  rw [current, (hasDerivAt_evolved ω₀ T L hgen hf t).deriv]

/-- A writer set separates the positive normalized states relevant to it. -/
def Separates (positive : S → Prop) (unit : S) (writers : Set S) : Prop :=
  ∀ ω ω' : S →L[ℂ] ℂ,
    IsWriterState positive unit ω → IsWriterState positive unit ω' →
      (∀ f ∈ writers, ω f = ω' f) → ω = ω'

/-- Separation is exactly the uniqueness condition for state extensions. -/
theorem extension_unique_of_separating
    (positive : S → Prop) (unit : S) {writers : Set S}
    (hsep : Separates positive unit writers)
    {ω ω' : S →L[ℂ] ℂ}
    (hω : IsWriterState positive unit ω)
    (hω' : IsWriterState positive unit ω')
    (hagree : ∀ f ∈ writers, ω f = ω' f) : ω = ω' :=
  hsep ω ω' hω hω' hagree

/-- Failure of separation supplies two distinct positive normalized extensions
with the same writer restriction. -/
theorem exists_two_extensions_of_not_separating
    (positive : S → Prop) (unit : S) {writers : Set S}
    (hsep : ¬Separates positive unit writers) :
    ∃ ω ω' : S →L[ℂ] ℂ,
      IsWriterState positive unit ω ∧ IsWriterState positive unit ω' ∧
      (∀ f ∈ writers, ω f = ω' f) ∧ ω ≠ ω' := by
  unfold Separates at hsep
  push Not at hsep
  exact hsep

/-- Exact abstract assembly of `thm:GT-writer-state-derived-current`:
TR.10, TR.11, and the extension uniqueness/nonuniqueness alternative. -/
theorem abstract_writer_state_derived_current
    (positive : S → Prop) (unit : S)
    {ω₀ : S →L[ℂ] ℂ} (hω : IsWriterState positive unit ω₀)
    (T : ℝ → S →L[ℂ] S) (L : ℝ → S →L[ℂ] S)
    (source : ℝ → S →L[ℂ] ℂ)
    (hT : ∀ t, IsPositiveUnital positive unit (T t))
    {core : Set S} (hgen : HasRightGenerator T L core) :
    (∀ t, IsWriterState positive unit (evolved ω₀ (T t))) ∧
      (∀ f ∈ core, ∀ t,
        HasDerivAt (fun s => evolved ω₀ (T s) f)
          (evolved ω₀ (T t) (L t f)) t) ∧
      (∀ f ∈ core, ∀ t,
        current ω₀ T source t f =
          evolved ω₀ (T t) (L t f) + source t f) ∧
      (∀ writers : Set S, Separates positive unit writers →
        ∀ ω ω' : S →L[ℂ] ℂ,
          IsWriterState positive unit ω → IsWriterState positive unit ω' →
          (∀ f ∈ writers, ω f = ω' f) → ω = ω') ∧
      ∀ writers : Set S, ¬Separates positive unit writers →
        ∃ ω ω' : S →L[ℂ] ℂ,
          IsWriterState positive unit ω ∧ IsWriterState positive unit ω' ∧
          (∀ f ∈ writers, ω f = ω' f) ∧ ω ≠ ω' := by
  refine ⟨fun t => evolved_isWriterState positive unit hω (hT t),
    fun _ hf t => hasDerivAt_evolved ω₀ T L hgen hf t,
    fun _ hf t => current_eq ω₀ T L source hgen hf t, ?_, ?_⟩
  · intro writers hsep ω ω' hω hω' hagree
    exact extension_unique_of_separating positive unit hsep hω hω' hagree
  · intro writers hsep
    exact exists_two_extensions_of_not_separating positive unit hsep

end AbstractWriterStateEvolution
end NCG
