/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandMultSaturation
import NCG.Grand.ExactSourceSchurResidual

/-!
# Multiplicity and generation saturation

This file completes `thm:SM-multiplicity-saturation` from the Gran--Tensor
manuscript.  It adds the generation `I₃` factor to the existing matter `I₂`
factorization, identifies the multiplicity Schur defect with the orthogonal
next-layer innovation, proves its exact rank-increment formula, and proves
the rank-one/zero-defect criterion for one generation copy.
-/

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- A Krylov Gram block tensored with the three-dimensional Hodge carrier
factors as the multiplicity block tensored with `I₃`. -/
theorem generationKrylovGram_factorization {M : Type*} [Fintype M]
    [DecidableEq M] (A B : Matrix M M ℂ) (i j : ℕ) :
    let A₃ := A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
    let B₃ := B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
    B₃ᴴ * ((A₃ᴴ) ^ i * (A₃ ^ j * B₃)) =
      (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B))) ⊗ₖ
        (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  dsimp only
  have hpow : ∀ (C : Matrix M M ℂ) (k : ℕ),
      (C ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) ^ k =
        (C ^ k) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    intro C k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_kronecker_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, hpow, hpow,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]

/-- The multiplicity Schur defect of a previous Krylov synthesis `S₁` and
the next layer `S₂`. -/
noncomputable def multiplicitySchurDefect {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) : Matrix (Fin e₂) (Fin e₂) ℂ :=
  sourceSchurResidual S₁ S₂

/-- The multiplicity Schur defect is the manuscript expression
`h - gᴴ G† g`. -/
theorem multiplicitySchurDefect_eq_crossFormula {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    multiplicitySchurDefect S₁ S₂ =
      S₂ᴴ * S₂ - (S₁ᴴ * S₂)ᴴ * sourceGramPseudoinverse S₁ *
        (S₁ᴴ * S₂) := rfl

/-- The Schur defect is positive and its rank is exactly the next
multiplicity-rank increment. -/
theorem multiplicitySchurDefect_positive_rankIncrement {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) :
    (multiplicitySchurDefect S₁ S₂).PosSemidef ∧
      (Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
          ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)).rank - (S₁ᴴ * S₁).rank =
        (multiplicitySchurDefect S₁ S₂).rank := by
  exact ⟨sourceSchurResidual_posSemidef S₁ S₂,
    by simpa [multiplicitySchurDefect] using
      sourceSchurResidual_rank_increment S₁ S₂⟩

/-- With a rank-one multiplicity Gram, vanishing next-layer Schur defect is
equivalent to the enlarged visible Gram still having rank one.  This is the
exact one-generation saturation criterion. -/
theorem oneGeneration_iff_rankOne_and_zeroSchurDefect {h e₁ e₂ : ℕ}
    (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ)
    (hrankOne : (S₁ᴴ * S₁).rank = 1) :
    (multiplicitySchurDefect S₁ S₂ = 0) ↔
      (Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
          ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)).rank = 1 := by
  let G := Matrix.fromBlocks (S₁ᴴ * S₁) (S₁ᴴ * S₂)
    ((S₁ᴴ * S₂)ᴴ) (S₂ᴴ * S₂)
  have hprincipal : (S₁ᴴ * S₁).rank ≤ G.rank := by
    have hsub := Matrix.rank_submatrix_le G Sum.inl Sum.inl
    have heq : G.submatrix Sum.inl Sum.inl = S₁ᴴ * S₁ := by
      ext i j
      simp [G]
    rwa [heq] at hsub
  have hincrement : G.rank - (S₁ᴴ * S₁).rank =
      (multiplicitySchurDefect S₁ S₂).rank := by
    simpa [G, multiplicitySchurDefect] using
      sourceSchurResidual_rank_increment S₁ S₂
  constructor
  · intro hzero
    rw [hzero, Matrix.rank_zero, hrankOne] at hincrement
    have hupper : G.rank ≤ 1 := Nat.sub_eq_zero_iff_le.mp hincrement
    have hlower : 1 ≤ G.rank := hrankOne ▸ hprincipal
    change G.rank = 1
    omega
  · intro hone
    change G.rank = 1 at hone
    rw [hone, hrankOne] at hincrement
    have hrankZero : (multiplicitySchurDefect S₁ S₂).rank = 0 := by
      simpa using hincrement.symm
    apply Matrix.ext
    intro i j
    rw [Matrix.rank] at hrankZero
    have hzeroRange : ∀ x : LinearMap.range
        (multiplicitySchurDefect S₁ S₂).mulVecLin, x = 0 :=
      finrank_zero_iff_forall_zero.mp hrankZero
    let v : Fin e₂ → ℂ := fun k => if k = j then 1 else 0
    have hmul : (multiplicitySchurDefect S₁ S₂).mulVecLin v = 0 := by
      have hx := hzeroRange
        ⟨(multiplicitySchurDefect S₁ S₂).mulVecLin v, ⟨v, rfl⟩⟩
      exact congrArg Subtype.val hx
    have hij := congrFun hmul i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, v] using hij

/-- Complete copy--deformation packet: the commuting right `M₂` action
produces the matter factor, while the same multiplicity Krylov blocks tensor
with the three-dimensional generation carrier. -/
theorem multiplicityMatterGeneration_factorization
    {M : Type*} [Fintype M] [DecidableEq M]
    (T S : Matrix (M × Fin 2) (M × Fin 2) ℂ)
    (hT : ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      ((1 : Matrix M M ℂ) ⊗ₖ g) * T =
        T * ((1 : Matrix M M ℂ) ⊗ₖ g))
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      ((1 : Matrix M M ℂ) ⊗ₖ g) * S =
        S * ((1 : Matrix M M ℂ) ⊗ₖ g)) :
    ∃ A B : Matrix M M ℂ,
      T = A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      S = B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ i j : ℕ,
        Sᴴ * ((Tᴴ) ^ i * (T ^ j * S)) =
          (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B))) ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∀ i j : ℕ,
        let A₃ := A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
        let B₃ := B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
        B₃ᴴ * ((A₃ᴴ) ^ i * (A₃ ^ j * B₃)) =
          (Bᴴ * ((Aᴴ) ^ i * (A ^ j * B))) ⊗ₖ
            (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  obtain ⟨A, B, hTA, hSB, hmatter⟩ := sm_multiplicity_saturation T S hT hS
  exact ⟨A, B, hTA, hSB, hmatter,
    generationKrylovGram_factorization A B⟩

end NCG
