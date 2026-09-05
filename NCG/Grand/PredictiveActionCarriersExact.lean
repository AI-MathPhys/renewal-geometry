/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AdaptiveWordLocalizerStopExact
import NCG.Grand.FiniteRecurrenceAndPredictiveCarriers

/-!
# Predictive and two-sided source carriers

Exact finite-dimensional encoding of `def:GT-forward-star-carriers` and
`thm:GT-predictive-action-carriers`.

On a finite-dimensional complex inner product space `E`, with primitive
branches `U a : E →ₗ[ℂ] E` and source range `V`:

* `forwardCarrier U V = H₊` is the span of all `U_w V`; it is the least
  `U`-invariant subspace containing `V` (`forwardCarrier_minimal`);
* `twoSidedCarrier U V = H_*` is the span of all star words (letters `U a`
  and `U a†`); it is the least reducing subspace containing `V`
  (`twoSidedCarrier_minimal`); `H₊ ≤ H_*` (`forwardCarrier_le_twoSided`);
* **(PA.3)** `H₊ = H_*` ⇔ `H₊` is invariant under every adjoint ⇔
  `(I - P₊) U_a† P₊ = 0` for every `a` (`carriers_eq_iff_adjoint_invariant`,
  `adjoint_invariant_iff_projection_identity`);
* **(PA.4)** the adjoint innovation `I_a⁻ = P₊ U_a (I - P₊) U_a† P₊` is the
  Gram of `X_a = (I - P₊) U_a† P₊` — matrix form
  `FiniteRecurrenceAndPredictiveCarriers.predictive_action_innovation`; in
  operator form `⟪x, I_a⁻ x⟫ = ‖X_a x‖²` (`innovation_quadratic_form`), so
  `I_a⁻ = 0 ⇔ X_a = 0` and simultaneous vanishing is action autonomy of the
  predictive carrier (`action_autonomy_iff`).
-/

open Submodule NCG.AdaptiveWordLocalizerStop

namespace NCG
namespace PredictiveActionCarriers

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The forward carrier `H₊ = span{U_w V x}`. -/
def forwardCarrier (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) : Submodule ℂ E :=
  generatedCarrier U V

/-- Star letters: a branch or its adjoint. -/
noncomputable def starLetters (U : ι → E →ₗ[ℂ] E) : ι ⊕ ι → E →ₗ[ℂ] E
  | Sum.inl a => U a
  | Sum.inr a => LinearMap.adjoint (U a)

/-- The two-sided carrier `H_* = span{U_ω V x}` over star words. -/
noncomputable def twoSidedCarrier (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) : Submodule ℂ E :=
  generatedCarrier (starLetters U) V

/-- A subspace reduces every branch when it is invariant under each `U a` and
each `U a†`. -/
def Reduces (U : ι → E →ₗ[ℂ] E) (M : Submodule ℂ E) : Prop :=
  ∀ a, M.map (U a) ≤ M ∧ M.map (LinearMap.adjoint (U a)) ≤ M

omit [FiniteDimensional ℂ E] in
theorem source_le_forwardCarrier (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    V ≤ forwardCarrier U V :=
  source_le_generatedCarrier U V

omit [FiniteDimensional ℂ E] in
theorem forwardCarrier_invariant (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) (a : ι) :
    (forwardCarrier U V).map (U a) ≤ forwardCarrier U V :=
  generatedCarrier_invariant U V a

omit [FiniteDimensional ℂ E] in
/-- **Minimum predictive carrier**: `H₊` is the least forward-invariant subspace
containing the source. -/
theorem forwardCarrier_minimal (U : ι → E →ₗ[ℂ] E) (V M : Submodule ℂ E)
    (hV : V ≤ M) (hinv : ∀ a, M.map (U a) ≤ M) : forwardCarrier U V ≤ M :=
  generatedCarrier_le_of_invariant U V M hV hinv

theorem source_le_twoSidedCarrier (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    V ≤ twoSidedCarrier U V :=
  source_le_generatedCarrier _ V

theorem twoSidedCarrier_reduces (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    Reduces U (twoSidedCarrier U V) := fun a =>
  ⟨generatedCarrier_invariant (starLetters U) V (Sum.inl a),
    generatedCarrier_invariant (starLetters U) V (Sum.inr a)⟩

/-- **Minimum reducing carrier**: `H_*` is the least reducing subspace containing
the source. -/
theorem twoSidedCarrier_minimal (U : ι → E →ₗ[ℂ] E) (V M : Submodule ℂ E)
    (hV : V ≤ M) (hred : Reduces U M) : twoSidedCarrier U V ≤ M :=
  generatedCarrier_le_of_invariant (starLetters U) V M hV fun s => by
    cases s with
    | inl a => exact (hred a).1
    | inr a => exact (hred a).2

theorem forwardCarrier_le_twoSided (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    forwardCarrier U V ≤ twoSidedCarrier U V :=
  forwardCarrier_minimal U V _ (source_le_twoSidedCarrier U V)
    fun a => (twoSidedCarrier_reduces U V a).1

/-- **(PA.3, subspace form)**: `H₊ = H_*` iff `H₊` is invariant under every
adjoint branch. -/
theorem carriers_eq_iff_adjoint_invariant (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    forwardCarrier U V = twoSidedCarrier U V ↔
      ∀ a, (forwardCarrier U V).map (LinearMap.adjoint (U a)) ≤ forwardCarrier U V := by
  constructor
  · intro heq a
    rw [heq]
    exact (twoSidedCarrier_reduces U V a).2
  · intro hadj
    refine le_antisymm (forwardCarrier_le_twoSided U V) ?_
    exact twoSidedCarrier_minimal U V _ (source_le_forwardCarrier U V)
      fun a => ⟨forwardCarrier_invariant U V a, hadj a⟩

/-! ### Projection form of (PA.3) and the adjoint innovation (PA.4) -/

/-- Invariance of a subspace under `A` is the operator identity
`(I - P) A P = 0` for its orthogonal projection `P`. -/
theorem invariant_iff_projection_identity (M : Submodule ℂ E) (A : E →ₗ[ℂ] E) :
    M.map A ≤ M ↔
      ∀ x, (x - M.starProjection x) = 0 ∨ True → A (M.starProjection x)
        - M.starProjection (A (M.starProjection x)) = 0 := by
  constructor
  · intro hinv x _
    have hmem : A (M.starProjection x) ∈ M :=
      hinv ⟨M.starProjection x, M.starProjection_apply_mem x, rfl⟩
    rw [M.starProjection_eq_self_iff.mpr hmem, sub_self]
  · intro h
    rintro _ ⟨y, hy, rfl⟩
    have hx := h y (Or.inr trivial)
    rw [M.starProjection_eq_self_iff.mpr hy] at hx
    rw [sub_eq_zero] at hx
    rw [hx]
    exact M.starProjection_apply_mem _

/-- **(PA.3, projection form)**: with `P₊` the orthogonal projection onto `H₊`,
`H₊` is adjoint-invariant iff `(I - P₊) U_a† P₊ = 0` on every vector. -/
theorem adjoint_invariant_iff_projection_identity (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E)
    (a : ι) :
    (forwardCarrier U V).map (LinearMap.adjoint (U a)) ≤ forwardCarrier U V ↔
      ∀ x, LinearMap.adjoint (U a) ((forwardCarrier U V).starProjection x)
        - (forwardCarrier U V).starProjection
            (LinearMap.adjoint (U a) ((forwardCarrier U V).starProjection x)) = 0 := by
  rw [invariant_iff_projection_identity]
  constructor
  · intro h x; exact h x (Or.inr trivial)
  · intro h x _; exact h x

/-- The adjoint innovation quadratic form: `⟪x, P U (I - P) U† P x⟫ = ‖(I - P) U† P x‖²`. -/
theorem innovation_quadratic_form (M : Submodule ℂ E) (A : E →ₗ[ℂ] E) (x : E) :
    let X := fun y => LinearMap.adjoint A (M.starProjection y)
      - M.starProjection (LinearMap.adjoint A (M.starProjection y))
    inner ℂ x (M.starProjection (A (X x))) = (‖X x‖ ^ 2 : ℝ) := by
  intro X
  have hX : X x = LinearMap.adjoint A (M.starProjection x)
      - M.starProjection (LinearMap.adjoint A (M.starProjection x)) := rfl
  -- `X x` is orthogonal to `M`, and `P` is self-adjoint
  have hXorth : X x ∈ Mᗮ := by
    rw [hX]
    exact M.sub_starProjection_mem_orthogonal _
  calc inner ℂ x (M.starProjection (A (X x)))
      = inner ℂ (M.starProjection x) (A (X x)) := by
        rw [Submodule.inner_starProjection_left_eq_right]
    _ = inner ℂ (LinearMap.adjoint A (M.starProjection x)) (X x) := by
        rw [LinearMap.adjoint_inner_left]
    _ = inner ℂ (X x) (X x) := by
        have : LinearMap.adjoint A (M.starProjection x) = X x
            + M.starProjection (LinearMap.adjoint A (M.starProjection x)) := by
          rw [hX]; abel
        rw [this, inner_add_left]
        have h0 : inner ℂ (M.starProjection (LinearMap.adjoint A (M.starProjection x)))
            (X x) = 0 :=
          Submodule.inner_right_of_mem_orthogonal (M.starProjection_apply_mem _) hXorth
        rw [h0, add_zero]
    _ = (‖X x‖ ^ 2 : ℝ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- **Action autonomy**: the adjoint innovations vanish simultaneously iff `H₊`
is adjoint-invariant, i.e. iff `H₊ = H_*`. -/
theorem action_autonomy_iff (U : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    (∀ a x, LinearMap.adjoint (U a) ((forwardCarrier U V).starProjection x)
        - (forwardCarrier U V).starProjection
            (LinearMap.adjoint (U a) ((forwardCarrier U V).starProjection x)) = 0)
      ↔ forwardCarrier U V = twoSidedCarrier U V := by
  rw [carriers_eq_iff_adjoint_invariant]
  constructor
  · intro h a
    exact (adjoint_invariant_iff_projection_identity U V a).mpr (h a)
  · intro h a
    exact (adjoint_invariant_iff_projection_identity U V a).mp (h a)

end PredictiveActionCarriers
end NCG
