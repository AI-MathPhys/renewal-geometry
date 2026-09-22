/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive and completely positive maps

This file defines positive and completely positive (CP) linear maps on a
`*`-ordered algebra `A`, and the monoid `NCG.UCPMap A` of *unital completely
positive* maps under **diagrammatic** composition (`f * g` = "first `f`,
then `g`").

This is the operator-algebraic input of the manuscript's
Definition `def:renewal-memory`: a finite completely positive renewal memory
is a finite alphabet together with a family of unital completely positive
maps `Φ_σ : A → A`; histories act through the monoid `UCPMap A`.

## Implementation notes

* Positivity of a square matrix over `A` is stated in *quadratic-form* form
  (`NCG.MatrixQF`): `M` is positive when `0 ≤ ∑ i j, (x i)⋆ * M i j * x j`
  for all vectors `x : n → A`.  Over a C⋆-algebra this is equivalent to
  positivity in the matrix C⋆-algebra `Mₙ(A)`; the quadratic-form version has
  the advantage of making sense over any `*`-ordered ring, and of making
  closure of complete positivity under composition and identity trivial.
* Complete positivity quantifies `MatrixQF` over all finite matrix
  amplifications.

## Main definitions

* `NCG.IsPositiveMap` — order-preserving linear maps;
* `NCG.MatrixQF` — quadratic-form positivity of a square matrix over `A`;
* `NCG.IsCompletelyPositive` — CP maps via matrix amplification;
* `NCG.UCPMap` — bundled unital CP maps, with a `Monoid` instance in
  diagrammatic order.

## Main results

* `NCG.IsCompletelyPositive.isPositiveMap` — CP maps are positive
  (the `n = 1` amplification);
* `NCG.IsCompletelyPositive.comp`, `NCG.IsCompletelyPositive.id` — the CP
  maps form a monoid; this is what feeds the renewal-memory layer
  (`NCG.RenewalMemory`).
-/

namespace NCG

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Algebra ℂ A]

/-- A linear map is a **positive map** when it preserves the positive cone. -/
def IsPositiveMap (φ : A →ₗ[ℂ] A) : Prop :=
  ∀ a : A, 0 ≤ a → 0 ≤ φ a

/-- Quadratic-form positivity of a square matrix over a `*`-ordered ring:
`M` is positive when all "sandwiches" `∑ i j, (x i)⋆ * M i j * x j` are
positive.  Over a C⋆-algebra this agrees with positivity in `Mₙ(A)`. -/
def MatrixQF {n : Type*} [Fintype n] (M : Matrix n n A) : Prop :=
  ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j

/-- A linear map `φ : A → A` is **completely positive** when every matrix
amplification `Mₙ(A) → Mₙ(A)`, `M ↦ M.map φ`, preserves quadratic-form
positivity (manuscript, Definition `def:renewal-memory`). -/
def IsCompletelyPositive (φ : A →ₗ[ℂ] A) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) A), MatrixQF M → MatrixQF (M.map φ)

namespace IsCompletelyPositive

omit [StarOrderedRing A] in
/-- The identity map is completely positive. -/
protected theorem id : IsCompletelyPositive (LinearMap.id : A →ₗ[ℂ] A) := by
  intro k M hM
  have h : M.map ⇑(LinearMap.id : A →ₗ[ℂ] A) = M := by
    ext i j
    simp [Matrix.map_apply]
  rw [h]
  exact hM

omit [StarOrderedRing A] in
/-- Completely positive maps are closed under (diagrammatic) composition. -/
protected theorem comp {φ ψ : A →ₗ[ℂ] A} (hφ : IsCompletelyPositive φ)
    (hψ : IsCompletelyPositive ψ) : IsCompletelyPositive (ψ ∘ₗ φ) := by
  intro k M hM
  have h : (M.map φ).map ψ = M.map (ψ ∘ₗ φ) := by
    rw [Matrix.map_map]
    rfl
  simpa [h] using hψ k (M.map φ) (hφ k M hM)

/-- A completely positive map is positive: this is the `1 × 1` matrix
amplification. -/
theorem isPositiveMap {φ : A →ₗ[ℂ] A} (hφ : IsCompletelyPositive φ) :
    IsPositiveMap φ := by
  intro a ha
  -- the 1×1 matrix with entry `a` is quadratic-form positive
  have hM : MatrixQF (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) A) := by
    intro x
    simpa [Fin.sum_univ_one, Matrix.of_apply] using
      star_left_conjugate_nonneg ha (x 0)
  -- amplify and evaluate at the vector `x = 1`
  have h := hφ 1 (Matrix.of fun _ _ => a) hM fun _ => (1 : A)
  simp only [Fin.sum_univ_one, star_one, one_mul, mul_one, Matrix.map_apply,
    Matrix.of_apply] at h
  exact h

end IsCompletelyPositive

/-- A **unital completely positive map** on `A`: the bundled channel type of
the renewal-memory formalism (Definition `def:renewal-memory`). -/
structure UCPMap (A : Type*) [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra ℂ A] where
  /-- The underlying `ℂ`-linear map. -/
  toLinearMap : A →ₗ[ℂ] A
  /-- The map is unital. -/
  map_one' : toLinearMap 1 = 1
  /-- The map is completely positive. -/
  completelyPositive' : IsCompletelyPositive toLinearMap

namespace UCPMap

instance : FunLike (UCPMap A) A A where
  coe φ := φ.toLinearMap
  coe_injective := by
    rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
    congr 1
    exact DFunLike.coe_injective h

@[ext]
theorem ext {φ ψ : UCPMap A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toLinearMap (φ : UCPMap A) : ⇑φ.toLinearMap = ⇑φ := rfl

@[simp]
theorem map_one (φ : UCPMap A) : φ 1 = 1 := φ.map_one'

theorem completelyPositive (φ : UCPMap A) :
    IsCompletelyPositive φ.toLinearMap := φ.completelyPositive'

theorem isPositiveMap (φ : UCPMap A) : IsPositiveMap φ.toLinearMap :=
  φ.completelyPositive.isPositiveMap

/-- Unital CP maps form a monoid under **diagrammatic** composition:
`(φ * ψ) a = ψ (φ a)` — first `φ`, then `ψ`.  This matches the manuscript's
convention `Φ_{σw} = Φ_w ∘ Φ_σ` for accumulated channels of histories. -/
instance : Monoid (UCPMap A) where
  one := ⟨LinearMap.id, rfl, IsCompletelyPositive.id⟩
  mul φ ψ :=
    ⟨ψ.toLinearMap ∘ₗ φ.toLinearMap,
      by simp,
      φ.completelyPositive.comp ψ.completelyPositive⟩
  one_mul φ := by ext a; rfl
  mul_one φ := by ext a; rfl
  mul_assoc φ ψ ρ := by ext a; rfl

@[simp]
theorem one_apply (a : A) : (1 : UCPMap A) a = a := rfl

@[simp]
theorem mul_apply (φ ψ : UCPMap A) (a : A) : (φ * ψ) a = ψ (φ a) := rfl

end UCPMap

end NCG
