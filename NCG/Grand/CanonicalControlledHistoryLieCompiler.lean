/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ControlledCompiler
import NCG.Grand.TwoClockFullMatrixLieGeneration
import NCG.Grand.FiniteCommonCPCompletion

/-!
# Canonical controlled-history Lie compiler

This file proves the Lie-ideal step omitted by the original finite controlled
matrix bookkeeping.  A nonzero score-seen target axis propagates across a
resolved simple target, giving both `i Z ⊗ su(d)` and
`i p₁ ⊗ su(d)`, where `p₁ = (I - Z) / 2`.
-/

open Matrix Kronecker

namespace NCG

variable {ε d : Type*} [Fintype ε] [DecidableEq ε]
  [Fintype d] [DecidableEq d]

/-- The one-sided score-path projector associated to a sign observable. -/
noncomputable def scorePathProjection (Z : Matrix ε ε ℂ) : Matrix ε ε ℂ :=
  (2 : ℂ)⁻¹ • (1 - Z)

theorem scorePathProjection_idempotent (Z : Matrix ε ε ℂ)
    (hZ : Z * Z = 1) :
    scorePathProjection Z * scorePathProjection Z = scorePathProjection Z := by
  exact path_projection_idempotent Z hZ

private theorem kron_sub_right_general
    (C : Matrix ε ε ℂ) (A B : Matrix d d ℂ) :
    C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B := by
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

private theorem joint_local_control_bracket
    (Z : Matrix ε ε ℂ) (A B : Matrix d d ℂ) :
    matrixCommutator ((1 : Matrix ε ε ℂ) ⊗ₖ A) (Z ⊗ₖ B) =
      Z ⊗ₖ matrixCommutator A B := by
  unfold matrixCommutator
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, kron_sub_right_general]

/-- Target axes whose score-controlled copies already lie in the joint
control space. -/
def controlledAxisIdeal (Z : Matrix ε ε ℂ)
    (S : Submodule ℂ (Matrix d d ℂ))
    (L : Submodule ℂ (Matrix (ε × d) (ε × d) ℂ)) :
    Submodule ℂ (Matrix d d ℂ) where
  carrier := {A | A ∈ S ∧ Z ⊗ₖ A ∈ L}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    refine ⟨S.add_mem hA.1 hB.1, ?_⟩
    have hEq : Z ⊗ₖ (A + B) = Z ⊗ₖ A + Z ⊗ₖ B := by
      ext i j
      simp only [Matrix.kroneckerMap_apply, Matrix.add_apply]
      ring
    rw [hEq]
    exact L.add_mem hA.2 hB.2
  smul_mem' c A hA := by
    refine ⟨S.smul_mem c hA.1, ?_⟩
    have hEq : Z ⊗ₖ (c • A) = c • (Z ⊗ₖ A) := by
      ext i j
      simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hEq]
    exact L.smul_mem c hA.2

theorem controlledAxisIdeal_le (Z : Matrix ε ε ℂ)
    (S : Submodule ℂ (Matrix d d ℂ))
    (L : Submodule ℂ (Matrix (ε × d) (ε × d) ℂ)) :
    controlledAxisIdeal Z S L ≤ S := fun _ hA => hA.1

/-- Closure of the joint control space makes the controlled-axis preimage a
Lie ideal of the resolved target. -/
theorem controlledAxisIdeal_commutator_closed
    (Z : Matrix ε ε ℂ)
    (S : Submodule ℂ (Matrix d d ℂ))
    (L : Submodule ℂ (Matrix (ε × d) (ε × d) ℂ))
    (htarget : ∀ A ∈ S, ∀ B ∈ S, matrixCommutator A B ∈ S)
    (hcomm : ∀ A ∈ L, ∀ B ∈ L, matrixCommutator A B ∈ L)
    (hlocal : ∀ A ∈ S, (1 : Matrix ε ε ℂ) ⊗ₖ A ∈ L) :
    ∀ A ∈ S, ∀ B ∈ controlledAxisIdeal Z S L,
      matrixCommutator A B ∈ controlledAxisIdeal Z S L := by
  intro A hA B hB
  refine ⟨?_, ?_⟩
  · exact htarget A hA B hB.1
  · have hc := hcomm _ (hlocal A hA) _ hB.2
    rwa [joint_local_control_bracket] at hc

/-- Exact Lie-generation package for the canonical history compiler.  The
`htarget` hypothesis records closure of the resolved target under its own
matrix commutator. -/
theorem canonicalControlledHistory_lie_generation
    (Z : Matrix ε ε ℂ)
    (S : Submodule ℂ (Matrix d d ℂ))
    (L : Submodule ℂ (Matrix (ε × d) (ε × d) ℂ))
    (hsimple : IsSimpleCommutatorTarget S)
    (htarget : ∀ A ∈ S, ∀ B ∈ S, matrixCommutator A B ∈ S)
    (hcomm : ∀ A ∈ L, ∀ B ∈ L, matrixCommutator A B ∈ L)
    (hlocal : ∀ A ∈ S, (1 : Matrix ε ε ℂ) ⊗ₖ A ∈ L)
    (X : Matrix d d ℂ) (hXS : X ∈ S) (hX0 : X ≠ 0)
    (hseed : Z ⊗ₖ X ∈ L) :
    (∀ A ∈ S, Complex.I • (Z ⊗ₖ A) ∈ L) ∧
      (∀ A ∈ S, Complex.I • (scorePathProjection Z ⊗ₖ A) ∈ L) := by
  let J := controlledAxisIdeal Z S L
  have hJle : J ≤ S := controlledAxisIdeal_le Z S L
  have hJideal : ∀ A ∈ S, ∀ B ∈ J, matrixCommutator A B ∈ J := by
    intro A hA B hB
    refine ⟨htarget A hA B (hJle hB), ?_⟩
    have hc := hcomm _ (hlocal A hA) _ hB.2
    rwa [joint_local_control_bracket] at hc
  have hXinJ : X ∈ J := ⟨hXS, hseed⟩
  have hJ : J = S :=
    simpleCommutatorTarget_control S J hsimple hJle hJideal hXinJ hX0
  have hZA : ∀ A ∈ S, Z ⊗ₖ A ∈ L := by
    intro A hA
    have : A ∈ J := by rw [hJ]; exact hA
    exact this.2
  constructor
  · intro A hA
    exact L.smul_mem Complex.I (hZA A hA)
  · intro A hA
    have hdiff : (1 : Matrix ε ε ℂ) ⊗ₖ A - Z ⊗ₖ A ∈ L :=
      L.sub_mem (hlocal A hA) (hZA A hA)
    have hp : scorePathProjection Z ⊗ₖ A =
        (2 : ℂ)⁻¹ • ((1 : Matrix ε ε ℂ) ⊗ₖ A - Z ⊗ₖ A) := by
      ext i j
      simp only [scorePathProjection, Matrix.kroneckerMap_apply,
        Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rw [hp]
    exact L.smul_mem Complex.I (L.smul_mem (2 : ℂ)⁻¹ hdiff)

/-- The reversible and irreversible conclusions used by the compiler are
the exact one-sided lift/word laws and the finite path-labelled common
completion proved by the companion modules. -/
theorem canonicalControlledHistory_compiler_package :
    (∀ (U : Matrix d d ℂ), Uᴴ * U = 1 →
      (Matrix.fromBlocks (1 : Matrix ε ε ℂ) 0 0 U)ᴴ *
        Matrix.fromBlocks (1 : Matrix ε ε ℂ) 0 0 U = 1) ∧
    (∀ (P : Matrix ε ε ℂ), P * P = P → ∀ U V : Matrix d d ℂ,
      (P ⊗ₖ U + (1 - P) ⊗ₖ (1 : Matrix d d ℂ)) *
          (P ⊗ₖ V + (1 - P) ⊗ₖ (1 : Matrix d d ℂ)) =
        P ⊗ₖ (U * V) + (1 - P) ⊗ₖ (1 : Matrix d d ℂ)) := by
  exact ⟨fun U hU => controlled_lift_unitary U hU,
    fun P hP U V => controlled_letters_multiply P hP U V⟩

end NCG
