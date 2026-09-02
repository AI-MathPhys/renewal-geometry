/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Explicit independent whitened internal interventions

This file constructs, rather than assumes, the positive branch in CA.4 of
`thm:SMST-universal-coupled-action`.  The common history space is enlarged by
an orthogonal internal intervention summand.  Gravitational sources embed in
the first summand, internal interventions in the second; restriction to the
old summand is a literal conservative discard.
-/

open scoped BigOperators ComplexConjugate

namespace NCG
namespace IndependentWhitenedInternalInterventions

variable {Eg Ei : Type*}

/-- The explicit common history carrier. -/
abbrev CommonCarrier (Eg Ei : Type*) := Sum Eg Ei → ℂ

/-- Gravitational source embedding into the common history carrier. -/
def gravitationalEmbedding :
    (Eg → ℂ) →ₗ[ℂ] CommonCarrier Eg Ei where
  toFun x := Sum.elim x 0
  map_add' x y := by
    funext s
    cases s <;> simp
  map_smul' c x := by
    funext s
    cases s <;> simp

/-- Independent internal source embedding into the orthogonal summand. -/
def internalEmbedding :
    (Ei → ℂ) →ₗ[ℂ] CommonCarrier Eg Ei where
  toFun y := Sum.elim 0 y
  map_add' x y := by
    funext s
    cases s <;> simp
  map_smul' c x := by
    funext s
    cases s <;> simp

/-- Physical discard of the newly adjoined internal intervention register. -/
def discardInternal : CommonCarrier Eg Ei →ₗ[ℂ] (Eg → ℂ) where
  toFun z := fun e => z (.inl e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Readout of the independent internal intervention register. -/
def readInternal : CommonCarrier Eg Ei →ₗ[ℂ] (Ei → ℂ) where
  toFun z := fun i => z (.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem discardInternal_gravitationalEmbedding (x : Eg → ℂ) :
    discardInternal (gravitationalEmbedding (Ei := Ei) x) = x := by
  rfl

@[simp] theorem discardInternal_internalEmbedding (y : Ei → ℂ) :
    discardInternal (internalEmbedding (Eg := Eg) y) = 0 := by
  rfl

@[simp] theorem readInternal_gravitationalEmbedding (x : Eg → ℂ) :
    readInternal (gravitationalEmbedding (Ei := Ei) x) = 0 := by
  rfl

@[simp] theorem readInternal_internalEmbedding (y : Ei → ℂ) :
    readInternal (internalEmbedding (Eg := Eg) y) = y := by
  rfl

section Finite

variable [Fintype Eg] [Fintype Ei]

/-- Standard Hermitian form on one finite coefficient bank. -/
def bankInner {I : Type*} [Fintype I] (x y : I → ℂ) : ℂ :=
  ∑ i, starRingEnd ℂ (x i) * y i

/-- Orthogonal direct-sum Hermitian form on the common carrier. -/
def commonInner (x y : CommonCarrier Eg Ei) : ℂ :=
  bankInner (fun e => x (.inl e)) (fun e => y (.inl e)) +
    bankInner (fun i => x (.inr i)) (fun i => y (.inr i))

/-- The mixed covariance vanishes identically by construction. -/
theorem mixed_inner_zero (x : Eg → ℂ) (y : Ei → ℂ) :
    commonInner (gravitationalEmbedding x) (internalEmbedding y) = 0 := by
  simp [commonInner, bankInner, gravitationalEmbedding, internalEmbedding]

/-- The internal intervention covariance is already whitened. -/
theorem internal_inner_eq (x y : Ei → ℂ) :
    commonInner (internalEmbedding (Eg := Eg) x)
      (internalEmbedding (Eg := Eg) y) = bankInner x y := by
  simp [commonInner, bankInner, internalEmbedding]

/-- The gravitational source Gram is unchanged by the extension. -/
theorem gravitational_inner_eq (x y : Eg → ℂ) :
    commonInner (gravitationalEmbedding (Ei := Ei) x)
      (gravitationalEmbedding (Ei := Ei) y) = bankInner x y := by
  simp [commonInner, bankInner, gravitationalEmbedding]

/-- The two embedded source banks are faithful. -/
theorem gravitationalEmbedding_injective :
    Function.Injective (gravitationalEmbedding (Eg := Eg) (Ei := Ei)) := by
  intro x y h
  have := congrArg discardInternal h
  simpa using this

theorem internalEmbedding_injective :
    Function.Injective (internalEmbedding (Eg := Eg) (Ei := Ei)) := by
  intro x y h
  have := congrArg readInternal h
  simpa using this

/-- Their ranges meet only at the zero history. -/
theorem embedding_ranges_intersection :
    Set.range (gravitationalEmbedding (Eg := Eg) (Ei := Ei)) ∩
        Set.range (internalEmbedding (Eg := Eg) (Ei := Ei)) = {0} := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx0 : x = 0 := by
      have := congrArg discardInternal (hx.trans hy.symm)
      simpa using this
    have hy0 : y = 0 := by
      have := congrArg readInternal (hx.trans hy.symm)
      simpa using this.symm
    subst x
    subst y
    simpa using hx.symm
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    exact ⟨⟨0, by ext s; cases s <;> rfl⟩,
      ⟨0, by ext s; cases s <;> rfl⟩⟩

/-- Complete constructive CA.4 packet: zero cross covariance, identity
internal covariance, unchanged gravitational Gram, and conservative discard. -/
theorem explicit_independent_whitened_branch :
    (∀ x : Eg → ℂ, ∀ y : Ei → ℂ,
      commonInner (gravitationalEmbedding x) (internalEmbedding y) = 0) ∧
    (∀ x y : Ei → ℂ,
      commonInner (internalEmbedding (Eg := Eg) x)
        (internalEmbedding (Eg := Eg) y) = bankInner x y) ∧
    (∀ x y : Eg → ℂ,
      commonInner (gravitationalEmbedding (Ei := Ei) x)
        (gravitationalEmbedding (Ei := Ei) y) = bankInner x y) ∧
    Function.LeftInverse discardInternal
      (gravitationalEmbedding (Eg := Eg) (Ei := Ei)) := by
  exact ⟨mixed_inner_zero, internal_inner_eq, gravitational_inner_eq,
    discardInternal_gravitationalEmbedding⟩

end Finite

end IndependentWhitenedInternalInterventions
end NCG
