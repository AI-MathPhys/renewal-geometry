/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContextualFutureNullIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Universal property of the contextual history envelope

This file proves `thm:contextual-envelope-universal` for the concrete
finite-dimensional C-star history algebra constructed from the surviving
matrix blocks.  Every context-preserving surjective star-algebra quotient has
kernel contained in contextual future nullity and therefore admits a unique
surjective star-algebra map onto the history envelope.  If the intermediate
quotient is contextually future separated, that canonical map is a
star-algebra equivalence.
-/

namespace NCG

open scoped ComplexOrder

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (d : ι → Type*) [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
variable {κ B : Type*} [CStarAlgebra B]

/-- Contextual future separation for a family of Reads on an intermediate
history quotient.  Both the element and adjoint test families are included. -/
def ContextuallyFutureSeparated
    (R' : κ → B →ₗ[ℂ] ℂ) : Prop :=
  ∀ b : B,
    ((∀ (k : κ) (u v : B), R' k (u * b * v) = 0) ∧
      ∀ (k : κ) (u v : B), R' k (u * star b * v) = 0) → b = 0

/-- The full C-star universal property of the contextual history envelope. -/
theorem contextualHistoryEnvelope_universal
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ)
    (π : FiniteMatrixBlockAlgebra d →⋆ₐ[ℂ] B)
    (hπ : Function.Surjective π)
    (R' : κ → B →ₗ[ℂ] ℂ)
    (hfact : ∀ k x, R k x = R' k (π x)) :
    let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
    let H := ContextualHistoryBlockAlgebra d R
    let quotientMap := contextualHistoryBlockRepresentation d R
    (∀ x, π x = 0 → x ∈ N)
      ∧ ∃! ψ : B →⋆ₐ[ℂ] H,
        (∀ x, ψ (π x) = quotientMap x)
          ∧ Function.Surjective ψ
          ∧ (ContextuallyFutureSeparated R' →
            ∃ e : B ≃⋆ₐ[ℂ] H, ∀ x, e (π x) = quotientMap x) := by
  classical
  dsimp only
  let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
  let quotientMap := contextualHistoryBlockRepresentation d R
  have hker : ∀ x, π x = 0 → x ∈ N := by
    intro x hx
    change contextualFutureNull (fun k => (R k).toAddMonoidHom) x
    constructor
    · intro k u v
      change R k (u * x * v) = 0
      rw [hfact, map_mul π, map_mul π, hx, mul_zero, zero_mul, map_zero]
    · intro k u v
      change R k (u * star x * v) = 0
      rw [hfact, map_mul π, map_mul π, map_star π, hx, star_zero,
        mul_zero, zero_mul, map_zero]
  have hle : RingHom.ker π.toAlgHom.toRingHom ≤
      RingHom.ker quotientMap.toAlgHom.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    exact (contextualHistoryBlockRepresentation_ker d R x).2 (hker x hx)
  let ψRing : B →+* ContextualHistoryBlockAlgebra d R :=
    π.toAlgHom.toRingHom.liftOfSurjective hπ
      ⟨quotientMap.toAlgHom.toRingHom, hle⟩
  have hψRing : ∀ x, ψRing (π x) = quotientMap x := by
    intro x
    exact π.toAlgHom.toRingHom.liftOfSurjective_comp_apply hπ
      ⟨quotientMap.toAlgHom.toRingHom, hle⟩ x
  let ψAlg : B →ₐ[ℂ] ContextualHistoryBlockAlgebra d R :=
    { ψRing with
      commutes' := fun c => by
        change ψRing (algebraMap ℂ B c) =
          algebraMap ℂ (ContextualHistoryBlockAlgebra d R) c
        calc
          ψRing (algebraMap ℂ B c) =
              ψRing (π (algebraMap ℂ (FiniteMatrixBlockAlgebra d) c)) :=
            congrArg ψRing (π.commutes c).symm
          _ = quotientMap (algebraMap ℂ (FiniteMatrixBlockAlgebra d) c) :=
            hψRing _
          _ = algebraMap ℂ (ContextualHistoryBlockAlgebra d R) c :=
            quotientMap.commutes c }
  have hψAlg : ∀ x, ψAlg (π x) = quotientMap x := hψRing
  let ψ : B →⋆ₐ[ℂ] ContextualHistoryBlockAlgebra d R :=
    { ψAlg with
      map_star' := fun b => by
        obtain ⟨x, rfl⟩ := hπ b
        change ψAlg (star (π x)) = star (ψAlg (π x))
        calc
          ψAlg (star (π x)) = ψAlg (π (star x)) :=
            congrArg ψAlg (map_star π x).symm
          _ = quotientMap (star x) := hψAlg (star x)
          _ = star (quotientMap x) := map_star quotientMap x
          _ = star (ψAlg (π x)) := congrArg star (hψAlg x).symm }
  have hψ : ∀ x, ψ (π x) = quotientMap x := hψAlg
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := contextualHistoryBlockRepresentation_surjective d R y
    exact ⟨π x, hψ x |>.trans hx⟩
  have hψunique : ∀ φ : B →⋆ₐ[ℂ] ContextualHistoryBlockAlgebra d R,
      (∀ x, φ (π x) = quotientMap x) → φ = ψ := by
    intro φ hφ
    ext b
    obtain ⟨x, rfl⟩ := hπ b
    rw [hφ, hψ]
  refine ⟨hker, ψ, ⟨hψ, hψsurj, ?_⟩, ?_⟩
  · intro hsep
    have hψinj : Function.Injective ψ := by
      have hzero : ∀ b : B, ψ b = 0 → b = 0 := by
        intro b hb
        obtain ⟨x, rfl⟩ := hπ b
        have hxquot : quotientMap x = 0 := (hψ x).symm.trans hb
        have hxN := (contextualHistoryBlockRepresentation_ker d R x).1 hxquot
        apply hsep (π x)
        change contextualFutureNull (fun k => (R k).toAddMonoidHom) x at hxN
        constructor
        · intro k u v
          obtain ⟨a, rfl⟩ := hπ u
          obtain ⟨c, rfl⟩ := hπ v
          rw [← map_mul π, ← map_mul π, ← hfact]
          exact hxN.1 k a c
        · intro k u v
          obtain ⟨a, rfl⟩ := hπ u
          obtain ⟨c, rfl⟩ := hπ v
          rw [← map_star π, ← map_mul π, ← map_mul π, ← hfact]
          exact hxN.2 k a c
      intro b₁ b₂ heq
      apply sub_eq_zero.mp
      apply hzero (b₁ - b₂)
      calc
        ψ (b₁ - b₂) = ψ b₁ - ψ b₂ := map_sub ψ b₁ b₂
        _ = 0 := sub_eq_zero.mpr heq
    let e := StarAlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
    exact ⟨e, fun x => by exact hψ x⟩
  · intro φ hφ
    exact hψunique φ hφ.1

end

end NCG
