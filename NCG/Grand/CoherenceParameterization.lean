/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete parameterization of physical two-history coherence
  (`thm:coherence-parameterization`, Gran-Tensor manuscript)

* `coherence_parameterization`: with declared Gram
  factorizations `J₀ = PᴴP`, `J₁ = QᴴQ` of the two diagonal
  Choi blocks, every contraction `C` (i.e. `I - CᴴC ⪰ 0`)
  yields a positive controlled completion with off-diagonal
  block `X = PᴴCQ` — via the explicit sum-of-squares
  decomposition
  `[[PᴴP, PᴴCQ],[QᴴCᴴP, QᴴQ]] = NᴴN + Eᴴ(I - CᴴC)E` with
  `N = [P | CQ]`, `E = [0 | Q]`; and conversely the diagonal
  blocks of any positive completion are positive (the diagonal
  histories bound but do not select `C`).

Rendering disclosed: the square roots `J₀^{1/2}, J₁^{1/2}` are
rendered by the declared Gram factors `P, Q` (the invisible
polar gauge); the forward extraction of `C` from a given
positive completion (Schur pseudo-inverse on supports) is the
manuscript's remaining functional-calculus step, disclosed and
not formalized here.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:coherence-parameterization`. -/
theorem coherence_parameterization {h n m : Type*} [Fintype h]
    [Finite n] [Finite m] [DecidableEq h]
    (P : Matrix h n ℂ) (Q : Matrix h m ℂ) (C : Matrix h h ℂ)
    (hC : ((1 : Matrix h h ℂ) - Cᴴ * C).PosSemidef) :
    -- sufficiency: every contraction completes positively
    (Matrix.fromBlocks (Pᴴ * P) (Pᴴ * (C * Q))
        ((Pᴴ * (C * Q))ᴴ) (Qᴴ * Q)).PosSemidef
    -- necessity: diagonal blocks of a positive completion
    ∧ (∀ (A : Matrix n n ℂ) (X : Matrix n m ℂ)
        (B : Matrix m m ℂ),
        (Matrix.fromBlocks A X Xᴴ B).PosSemidef →
        A.PosSemidef ∧ B.PosSemidef) := by
  constructor
  · have h1 : (Matrix.fromCols P (C * Q))ᴴ
        * Matrix.fromCols P (C * Q)
        = Matrix.fromBlocks (Pᴴ * P) (Pᴴ * (C * Q))
            ((C * Q)ᴴ * P) ((C * Q)ᴴ * (C * Q)) := by
      rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromRows_mul_fromCols]
    have h2 : (Matrix.fromCols (0 : Matrix h n ℂ) Q)ᴴ
        * ((1 : Matrix h h ℂ) - Cᴴ * C)
        * Matrix.fromCols (0 : Matrix h n ℂ) Q
        = Matrix.fromBlocks 0 0 0
            (Qᴴ * ((1 : Matrix h h ℂ) - Cᴴ * C) * Q) := by
      rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.conjTranspose_zero, Matrix.fromRows_mul,
        Matrix.zero_mul, Matrix.fromRows_mul_fromCols,
        Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_zero]
    have hsum : Matrix.fromBlocks (Pᴴ * P) (Pᴴ * (C * Q))
        ((Pᴴ * (C * Q))ᴴ) (Qᴴ * Q)
        = (Matrix.fromCols P (C * Q))ᴴ
            * Matrix.fromCols P (C * Q)
          + (Matrix.fromCols (0 : Matrix h n ℂ) Q)ᴴ
              * ((1 : Matrix h h ℂ) - Cᴴ * C)
              * Matrix.fromCols (0 : Matrix h n ℂ) Q := by
      rw [h1, h2, Matrix.fromBlocks_add]
      congr 1
      · rw [add_zero]
      · rw [add_zero]
      · rw [add_zero, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      · rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.mul_assoc]
        abel
    rw [hsum]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).add
      (hC.conjTranspose_mul_mul_same _)
  · intro A X B hM
    constructor
    · have hsub := hM.submatrix (Sum.inl : n → n ⊕ m)
      have he : (Matrix.fromBlocks A X Xᴴ B).submatrix
          Sum.inl Sum.inl = A := by
        ext i j
        simp [Matrix.submatrix_apply]
      rwa [he] at hsub
    · have hsub := hM.submatrix (Sum.inr : m → n ⊕ m)
      have he : (Matrix.fromBlocks A X Xᴴ B).submatrix
          Sum.inr Sum.inr = B := by
        ext i j
        simp [Matrix.submatrix_apply]
      rwa [he] at hsub

end NCG
