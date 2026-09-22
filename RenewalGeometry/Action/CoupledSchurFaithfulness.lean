/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.UniversalCoupledActionCarrier
/-!
# Faithfulness clause of the universal coupled source quotient

Clause (i) of `thm:coupled-schur` (spacetime--gauge duality manuscript): on a
faithful gravitational source (`G_g ≻ 0`) the joint variation carrier is
faithful — the joint source Gram `[[G_g, C*], [C, G_i]]` is positive definite,
equivalently the joint synthesis `(S_g | S_i)` is injective — exactly when the
Schur residual `G_{i|g} = G_i - C G_g⁻¹ C*` is positive definite.  The
factorization clauses (ii)–(iii) are already in
`Action/UniversalCoupledActionCarrier.lean`
(`coupledSourceSchur_factorization`, `sourceMinimalInternalVariation`).
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry

/-- A block-diagonal matrix is positive definite exactly when both diagonal
blocks are. -/
theorem posDef_fromBlocks_diag_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    (Matrix.fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hsub := h.submatrix (e := Sum.inl) Sum.inl_injective
      have hA : (Matrix.fromBlocks A 0 0 D).submatrix Sum.inl Sum.inl = A := by
        ext i j
        simp [Matrix.submatrix_apply]
      rw [hA] at hsub
      exact hsub
    · have hsub := h.submatrix (e := Sum.inr) Sum.inr_injective
      have hD : (Matrix.fromBlocks A 0 0 D).submatrix Sum.inr Sum.inr = D := by
        ext i j
        simp [Matrix.submatrix_apply]
      rw [hD] at hsub
      exact hsub
  · rintro ⟨hA, hD⟩
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1.eq, hD.1.eq]
      simp
    · intro x hx
      have hstar : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
        funext i
        cases i <;> rfl
      rw [Matrix.fromBlocks_mulVec, hstar]
      simp only [Matrix.zero_mulVec, add_zero, zero_add,
        sumElim_dotProduct_sumElim]
      have hne : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hx
        funext i
        cases i with
        | inl i => exact congrFun hcon.1 i
        | inr i => exact congrFun hcon.2 i
      rcases hne with hu | hv
      · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hu)
          (hD.posSemidef.dotProduct_mulVec_nonneg _)
      · exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
          (hD.dotProduct_mulVec_pos hv)

/-- A Gram matrix `Aᴴ A` is positive definite exactly when `A` acts injectively. -/
theorem posDef_conjTranspose_mul_self_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    (Aᴴ * A).PosDef ↔ Function.Injective A.mulVec := by
  constructor
  · intro h x y hxy
    by_contra hne
    have hsub : A *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hpos := h.dotProduct_mulVec_pos (sub_ne_zero.2 hne)
    rw [← Matrix.mulVec_mulVec, hsub, Matrix.mulVec_zero, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos
  · intro h
    exact Matrix.PosDef.conjTranspose_mul_self A h

/-- The joint source Gram is the Gram of the joint synthesis `(S_g | S_i)`. -/
theorem coupledSourceGram_eq_conjTranspose_mul_self {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ) (Si : Matrix (Fin h) (Fin ei) ℂ) :
    Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si) ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)
      = (Matrix.fromCols Sg Si)ᴴ * Matrix.fromCols Sg Si := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  simp

/-- **`thm:coupled-schur`, clause (i)** (spacetime--gauge duality manuscript).
On a faithful gravitational source `G_g = S_gᴴ S_g ≻ 0`, the joint source Gram
`[[G_g, C*], [C, G_i]]` is positive definite — equivalently the joint variation
carrier is faithful, i.e. the joint synthesis `(S_g | S_i)` is injective — exactly
when the Schur residual `G_{i|g} = G_i - C G_g⁻¹ C*` is positive definite. -/
theorem coupledSourceSchur_faithful_iff {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ) (Si : Matrix (Fin h) (Fin ei) ℂ)
    (hGg : (Sgᴴ * Sg).PosDef) :
    ((Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si) ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)).PosDef
        ↔ (sourceSchurResidual Sg Si).PosDef)
    ∧ (Function.Injective (Matrix.fromCols Sg Si).mulVec
        ↔ (sourceSchurResidual Sg Si).PosDef) := by
  have hfull := coupledSourceSchur_factorization Sg Si hGg
  dsimp only at hfull
  obtain ⟨hR, -, hfac, -, -⟩ := hfull
  have hUstar :
      star (Matrix.fromBlocks (1 : Matrix (Fin eg) (Fin eg) ℂ)
          ((Sgᴴ * Sg)⁻¹ * (Sgᴴ * Si))
          (0 : Matrix (Fin ei) (Fin eg) ℂ) (1 : Matrix (Fin ei) (Fin ei) ℂ))
        = Matrix.fromBlocks 1 0 (((Sgᴴ * Sg)⁻¹ * (Sgᴴ * Si))ᴴ) 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
    simp
  have hU : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin eg) (Fin eg) ℂ)
      ((Sgᴴ * Sg)⁻¹ * (Sgᴴ * Si))
      (0 : Matrix (Fin ei) (Fin eg) ℂ) (1 : Matrix (Fin ei) (Fin ei) ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.2 ⟨isUnit_one, isUnit_one⟩
  have hmain :
      (Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si) ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)).PosDef
        ↔ (sourceSchurResidual Sg Si).PosDef := by
    rw [← hR, hfac, ← hUstar, hU.posDef_star_left_conjugate_iff,
      posDef_fromBlocks_diag_iff]
    exact ⟨fun h => h.2, fun h => ⟨hGg, h⟩⟩
  refine ⟨hmain, ?_⟩
  rw [← hmain, coupledSourceGram_eq_conjTranspose_mul_self,
    posDef_conjTranspose_mul_self_iff]

end RenewalGeometry
