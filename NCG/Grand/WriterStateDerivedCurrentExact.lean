/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive writer evolution and derived current

Machinery for `thm:GT-writer-state-derived-current`.  The writer system lives inside the
finite-dimensional operator algebra `A = H →L[ℂ] H`; a positive unital evolution
`T t s : A →ₗ[ℂ] A` maps positive operators to positive operators and fixes `1`; a state `ω₀`
is a positive normalized linear functional.

* (TR.10) `ω_t := ω₀ ∘ T t 0` is positive and normalized (`evolved_isState`);
* (TR.11) if the right generator `𝓛_t` exists on a core, `∂_t T t 0 f = T t 0 (𝓛_t f)`, then
  `∂_t ω_t(f) = ω_t(𝓛_t f)` and the target current `ȷ_t(f) = ∂_t ω_t(f) + 𝔰_t(f)` is derived as
  `ω_t(𝓛_t f) + 𝔰_t(f)` (`hasDerivAt_evolved`, `current_eq`);
* extensions: two states on `A` agreeing on a writer system that separates states coincide
  (`extension_unique_of_separating`), while without separation the restriction does not
  determine the extension (`exists_two_extensions_of_not_separating`).
-/

open ContinuousLinearMap

namespace NCG
namespace WriterState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

/-- The operator algebra `A = H →L[ℂ] H`. -/
abbrev A (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  H →L[ℂ] H

/-- A state: a positive, normalized linear functional on `A`. -/
structure IsState (ω : A H →ₗ[ℂ] ℂ) : Prop where
  pos : ∀ a : A H, a.IsPositive → ∃ r : ℝ, 0 ≤ r ∧ ω a = r
  unital : ω 1 = 1

/-- A positive unital map on `A`. -/
structure IsPositiveUnital (T : A H →ₗ[ℂ] A H) : Prop where
  pos : ∀ a : A H, a.IsPositive → (T a).IsPositive
  unital : T 1 = 1

/-- (TR.10) the evolved state `ω_t = ω₀ ∘ T(t,0)`. -/
def evolved (ω₀ : A H →ₗ[ℂ] ℂ) (T : A H →ₗ[ℂ] A H) : A H →ₗ[ℂ] ℂ := ω₀.comp T

omit [FiniteDimensional ℂ H] in
theorem evolved_apply (ω₀ : A H →ₗ[ℂ] ℂ) (T : A H →ₗ[ℂ] A H) (f : A H) :
    evolved ω₀ T f = ω₀ (T f) := rfl

omit [FiniteDimensional ℂ H] in
/-- **(TR.10)**: a positive unital evolution transports states to states. -/
theorem evolved_isState {ω₀ : A H →ₗ[ℂ] ℂ} (hω : IsState ω₀) {T : A H →ₗ[ℂ] A H}
    (hT : IsPositiveUnital T) : IsState (evolved ω₀ T) where
  pos a ha := hω.pos (T a) (hT.pos a ha)
  unital := by rw [evolved_apply, hT.unital, hω.unital]

/-! ### (TR.11): the derived current -/

variable (ω₀ : A H →ₗ[ℂ] ℂ) (T : ℝ → A H →ₗ[ℂ] A H) (L : ℝ → A H →ₗ[ℂ] A H)
  (src : ℝ → A H →ₗ[ℂ] ℂ)

/-- The right generator on a core `C`: `∂_t T(t,0) f = T(t,0)(𝓛_t f)` for `f ∈ C`. -/
def HasRightGenerator (C : Set (A H)) : Prop :=
  ∀ f ∈ C, ∀ t : ℝ, HasDerivAt (fun s => T s f) (T t (L t f)) t

/-- The target current `ȷ_t(f) = ∂_t ω_t(f) + 𝔰_t(f)`. -/
noncomputable def current (t : ℝ) (f : A H) : ℂ :=
  deriv (fun s => evolved ω₀ (T s) f) t + src t f

/-- `∂_t ω_t(f) = ω_t(𝓛_t f)` on the generator core. -/
theorem hasDerivAt_evolved {C : Set (A H)} (hgen : HasRightGenerator T L C) {f : A H}
    (hf : f ∈ C) (t : ℝ) :
    HasDerivAt (fun s => evolved ω₀ (T s) f) (evolved ω₀ (T t) (L t f)) t := by
  have h := ((LinearMap.toContinuousLinearMap ω₀).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t (hgen f hf t)
  simpa [Function.comp_def, evolved_apply] using h

/-- **(TR.11)**: the target current is derived by `ȷ_t(f) = ω_t(𝓛_t f) + 𝔰_t(f)` on the
generator core. -/
theorem current_eq {C : Set (A H)} (hgen : HasRightGenerator T L C) {f : A H} (hf : f ∈ C)
    (t : ℝ) : current ω₀ T src t f = evolved ω₀ (T t) (L t f) + src t f := by
  rw [current, (hasDerivAt_evolved ω₀ T L hgen hf t).deriv]

/-! ### Extensions -/

/-- A writer system `S` separates states when two states agreeing on `S` coincide. -/
def Separates (S : Set (A H)) : Prop :=
  ∀ ω ω' : A H →ₗ[ℂ] ℂ, IsState ω → IsState ω' → (∀ f ∈ S, ω f = ω' f) → ω = ω'

omit [FiniteDimensional ℂ H] in
/-- Uniqueness of the positive extension under separation. -/
theorem extension_unique_of_separating {S : Set (A H)} (hS : Separates S)
    {ω ω' : A H →ₗ[ℂ] ℂ} (hω : IsState ω) (hω' : IsState ω') (h : ∀ f ∈ S, ω f = ω' f) :
    ω = ω' :=
  hS ω ω' hω hω' h

omit [FiniteDimensional ℂ H] in
/-- Without separation, a restriction to `S` has two distinct state extensions. -/
theorem exists_two_extensions_of_not_separating {S : Set (A H)} (hS : ¬ Separates S) :
    ∃ ω ω' : A H →ₗ[ℂ] ℂ, IsState ω ∧ IsState ω' ∧ (∀ f ∈ S, ω f = ω' f) ∧ ω ≠ ω' := by
  unfold Separates at hS
  push Not at hS
  obtain ⟨ω, ω', hω, hω', h, hne⟩ := hS
  exact ⟨ω, ω', hω, hω', h, hne⟩

/-- **`thm:GT-writer-state-derived-current`**: (TR.10) positive unital evolutions transport
states to states; (TR.11) on the right-generator core the target current is
`ȷ_t(f) = ω_t(𝓛_t f) + 𝔰_t(f)`; extensions of a state from a writer system are unique exactly
under separation. -/
theorem writer_state_derived_current {ω₀ : A H →ₗ[ℂ] ℂ} (hω : IsState ω₀)
    (hT : ∀ t, IsPositiveUnital (T t)) {C : Set (A H)} (hgen : HasRightGenerator T L C) :
    (∀ t, IsState (evolved ω₀ (T t))) ∧
      (∀ f ∈ C, ∀ t, HasDerivAt (fun s => evolved ω₀ (T s) f) (evolved ω₀ (T t) (L t f)) t) ∧
      (∀ f ∈ C, ∀ t, current ω₀ T src t f = evolved ω₀ (T t) (L t f) + src t f) ∧
      (∀ S : Set (A H), Separates S → ∀ ω ω' : A H →ₗ[ℂ] ℂ, IsState ω → IsState ω' →
        (∀ f ∈ S, ω f = ω' f) → ω = ω') ∧
      ∀ S : Set (A H), ¬ Separates S →
        ∃ ω ω' : A H →ₗ[ℂ] ℂ, IsState ω ∧ IsState ω' ∧ (∀ f ∈ S, ω f = ω' f) ∧ ω ≠ ω' :=
  ⟨fun t => evolved_isState hω (hT t), fun _ hf t => hasDerivAt_evolved ω₀ T L hgen hf t,
    fun _ hf t => current_eq ω₀ T L src hgen hf t,
    fun _ hS _ _ hω hω' h => extension_unique_of_separating hS hω hω' h,
    fun _ hS => exists_two_extensions_of_not_separating hS⟩

end WriterState
end NCG
