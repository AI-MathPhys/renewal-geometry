/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block

/-!
# Positivity and range of finite dependent block-diagonal matrices

This file supplies the finite direct-sum linear algebra used by isotypic
decompositions.  It is intentionally representation-independent.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace FiniteBlockDiagonal

variable {L : Type} [Fintype L] [DecidableEq L]
variable (E : L → Type) [∀ l, Fintype (E l)] [∀ l, DecidableEq (E l)]

/-- Restriction of a dependent direct-sum vector to one block. -/
def slice (x : (Σ l, E l) → ℂ) (l : L) : E l → ℂ :=
  fun i => x ⟨l, i⟩

/-- Multiplication by a dependent block-diagonal matrix is blockwise. -/
theorem blockDiagonal'_mulVec_apply
    (B : ∀ l, Matrix (E l) (E l) ℂ) (x : (Σ l, E l) → ℂ)
    (l : L) (i : E l) :
    (Matrix.blockDiagonal' B *ᵥ x) ⟨l, i⟩ = (B l *ᵥ slice E x l) i := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single l]
  · simp [Matrix.blockDiagonal'_apply_eq, slice]
  · intro k hk
    exact Finset.sum_eq_zero fun j _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hk)]
      simp

/-- The quadratic form of a finite dependent block diagonal is the sum of
the quadratic forms of its blocks. -/
theorem blockDiagonal'_quadraticForm
    (B : ∀ l, Matrix (E l) (E l) ℂ) (x : (Σ l, E l) → ℂ) :
    star x ⬝ᵥ (Matrix.blockDiagonal' B *ᵥ x) =
      ∑ l, star (slice E x l) ⬝ᵥ (B l *ᵥ slice E x l) := by
  simp [dotProduct, blockDiagonal'_mulVec_apply, slice,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]

/-- A finite dependent block diagonal is positive semidefinite exactly when
each of its blocks is positive semidefinite. -/
theorem posSemidef_blockDiagonal'_iff
    (B : ∀ l, Matrix (E l) (E l) ℂ) :
    (Matrix.blockDiagonal' B).PosSemidef ↔ ∀ l, (B l).PosSemidef := by
  constructor
  · intro h l
    have hs := h.submatrix (fun i : E l => Sigma.mk l i)
    have heq : (Matrix.blockDiagonal' B).submatrix
        (fun i : E l => Sigma.mk l i) (fun i : E l => Sigma.mk l i) = B l := by
      ext i j
      exact Matrix.blockDiagonal'_apply_eq B l i j
    rwa [heq] at hs
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_blockDiagonal'_iff.mpr fun l => (h l).isHermitian) ?_
    intro x
    rw [blockDiagonal'_quadraticForm E]
    exact Finset.sum_nonneg fun l _ => (h l).dotProduct_mulVec_nonneg _

/-- A finite dependent block diagonal is positive definite exactly when
each of its blocks is positive definite. -/
theorem posDef_blockDiagonal'_iff
    (B : ∀ l, Matrix (E l) (E l) ℂ) :
    (Matrix.blockDiagonal' B).PosDef ↔ ∀ l, (B l).PosDef := by
  constructor
  · intro h l
    have hinj : Function.Injective (fun i : E l => Sigma.mk l i) := by
      intro i j hij
      cases hij
      rfl
    have hs := h.submatrix hinj
    have heq : (Matrix.blockDiagonal' B).submatrix
        (fun i : E l => Sigma.mk l i) (fun i : E l => Sigma.mk l i) = B l := by
      ext i j
      exact Matrix.blockDiagonal'_apply_eq B l i j
    rwa [heq] at hs
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_blockDiagonal'_iff.mpr fun l => (h l).isHermitian) ?_
    intro x hx
    rw [blockDiagonal'_quadraticForm E]
    obtain ⟨⟨l, i⟩, hxi⟩ : ∃ p, x p ≠ 0 := by
      simpa [funext_iff] using hx
    have hslice : slice E x l ≠ 0 := by
      intro hs
      exact hxi (congrFun hs i)
    exact Finset.sum_pos'
      (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _)
      ⟨l, Finset.mem_univ l, (h l).dotProduct_mulVec_pos hslice⟩

/-- Exact range of a finite dependent block-diagonal operator. -/
theorem range_blockDiagonal'_mulVec
    (B : ∀ l, Matrix (E l) (E l) ℂ) :
    Set.range (fun x : (Σ l, E l) → ℂ => Matrix.blockDiagonal' B *ᵥ x) =
      {x | ∀ l, slice E x l ∈ LinearMap.range (B l).mulVecLin} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩ l
    refine ⟨slice E z l, ?_⟩
    funext i
    exact (blockDiagonal'_mulVec_apply E B z l i).symm
  · intro hx
    choose z hz using hx
    let y : (Σ l, E l) → ℂ := fun p => z p.1 p.2
    refine ⟨y, ?_⟩
    funext p
    rcases p with ⟨l, i⟩
    change (Matrix.blockDiagonal' B *ᵥ y) ⟨l, i⟩ = x ⟨l, i⟩
    rw [blockDiagonal'_mulVec_apply E B y l i]
    have hi := congrFun (hz l) i
    exact hi

end FiniteBlockDiagonal
end NCG
