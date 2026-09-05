/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalCoupledActionCarrier
import NCG.Grand.JointSourceRangeUnitary

/-!
# Faithfulness and naturality of the coupled source Schur quotient

This file supplies the two structural clauses of CA.2--CA.3 which are not
merely the block factorization: faithfulness of the full joint Gram is
equivalent to positive definiteness of the internal Schur residual, and the
residual quotient depends only on the three same-history Gram blocks.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace CoupledSourceSchurNaturality

/-- With a faithful gravitational source, the complete joint source Gram is
faithful exactly when the orthogonal internal residual is positive definite. -/
theorem jointGram_posDef_iff_sourceSchurResidual_posDef
    {h eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (hGg : (Sgᴴ * Sg).PosDef) :
    (Matrix.fromBlocks (Sgᴴ * Sg) (Sgᴴ * Si)
      ((Sgᴴ * Si)ᴴ) (Siᴴ * Si)).PosDef ↔
      (sourceSchurResidual Sg Si).PosDef := by
  let Gg : Matrix (Fin eg) (Fin eg) ℂ := Sgᴴ * Sg
  let B : Matrix (Fin eg) (Fin ei) ℂ := Sgᴴ * Si
  let Gi : Matrix (Fin ei) (Fin ei) ℂ := Siᴴ * Si
  let R : Matrix (Fin ei) (Fin ei) ℂ := sourceSchurResidual Sg Si
  haveI := hGg.isUnit.invertible
  have hfull :
      (Matrix.fromBlocks Gg B Bᴴ Gi).PosSemidef := by
    let S : Matrix (Fin h) (Fin eg ⊕ Fin ei) ℂ :=
      Matrix.fromCols Sg Si
    have hs : Sᴴ * S = Matrix.fromBlocks Gg B Bᴴ Gi := by
      dsimp only [S, Gg, B, Gi]
      rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromRows_mul_fromCols]
      simp
    rw [← hs]
    exact Matrix.posSemidef_conjTranspose_mul_self S
  have hR : R.PosSemidef := by
    exact sourceSchurResidual_posSemidef Sg Si
  have hschur : Gi - Bᴴ * Gg⁻¹ * B = R := by
    dsimp only [Gg, B, Gi, R]
    rw [sourceSchurResidual,
      sourceGramPseudoinverse_eq_inv_of_posDef Sg hGg]
  have hdet :
      (Matrix.fromBlocks Gg B Bᴴ Gi).det = Gg.det * R.det := by
    rw [Matrix.det_fromBlocks₁₁]
    simpa only [Matrix.invOf_eq_nonsing_inv, hschur]
  have hGgdet : Gg.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det Gg).mp hGg.isUnit).ne_zero
  change (Matrix.fromBlocks Gg B Bᴴ Gi).PosDef ↔ R.PosDef
  rw [hfull.posDef_iff_det_ne_zero, hR.posDef_iff_det_ne_zero, hdet,
    mul_ne_zero_iff]
  simp [hGgdet]

/-- On the faithful gravitational branch, the internal Schur residual depends
only on the gravitational, mixed, and internal Gram blocks. -/
theorem sourceSchurResidual_eq_of_gramBlocks
    {h h' eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (Tg : Matrix (Fin h') (Fin eg) ℂ)
    (Ti : Matrix (Fin h') (Fin ei) ℂ)
    (hSg : (Sgᴴ * Sg).PosDef)
    (hTg : (Tgᴴ * Tg).PosDef)
    (hgg : Sgᴴ * Sg = Tgᴴ * Tg)
    (hgi : Sgᴴ * Si = Tgᴴ * Ti)
    (hii : Siᴴ * Si = Tiᴴ * Ti) :
    sourceSchurResidual Sg Si = sourceSchurResidual Tg Ti := by
  rw [sourceSchurResidual, sourceSchurResidual,
    sourceGramPseudoinverse_eq_inv_of_posDef Sg hSg,
    sourceGramPseudoinverse_eq_inv_of_posDef Tg hTg,
    hgg, hgi, hii]

/-- Consequently the source-minimal internal quotient is unchanged by every
source-fixing change of realization which preserves the three Gram blocks. -/
theorem sourceMinimalInternalVariation_eq_of_gramBlocks
    {h h' eg ei : ℕ}
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (Tg : Matrix (Fin h') (Fin eg) ℂ)
    (Ti : Matrix (Fin h') (Fin ei) ℂ)
    (hSg : (Sgᴴ * Sg).PosDef)
    (hTg : (Tgᴴ * Tg).PosDef)
    (hgg : Sgᴴ * Sg = Tgᴴ * Tg)
    (hgi : Sgᴴ * Si = Tgᴴ * Ti)
    (hii : Siᴴ * Si = Tiᴴ * Ti) :
    sourceMinimalInternalVariation Sg Si =
      sourceMinimalInternalVariation Tg Ti := by
  unfold sourceMinimalInternalVariation
  rw [sourceSchurResidual_eq_of_gramBlocks
    Sg Si Tg Ti hSg hTg hgg hgi hii]

/-- An ambient isometric refinement preserves the Schur residual and its
source-minimal quotient.  This is the finite unread-record refinement law. -/
theorem ambientIsometry_preserves_sourceSchur
    {h h' eg ei : ℕ}
    (U : Matrix (Fin h') (Fin h) ℂ)
    (Sg : Matrix (Fin h) (Fin eg) ℂ)
    (Si : Matrix (Fin h) (Fin ei) ℂ)
    (hU : Uᴴ * U = 1)
    (hGg : (Sgᴴ * Sg).PosDef) :
    sourceSchurResidual (U * Sg) (U * Si) =
        sourceSchurResidual Sg Si
      ∧ sourceMinimalInternalVariation (U * Sg) (U * Si) =
        sourceMinimalInternalVariation Sg Si := by
  have hgg : (U * Sg)ᴴ * (U * Sg) = Sgᴴ * Sg := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hU]
  have hgi : (U * Sg)ᴴ * (U * Si) = Sgᴴ * Si := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hU]
  have hii : (U * Si)ᴴ * (U * Si) = Siᴴ * Si := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hU]
  have hUGg : ((U * Sg)ᴴ * (U * Sg)).PosDef := by
    rw [hgg]
    exact hGg
  have hres := sourceSchurResidual_eq_of_gramBlocks
    (U * Sg) (U * Si) Sg Si hUGg hGg hgg hgi hii
  exact ⟨hres, by
    unfold sourceMinimalInternalVariation
    rw [hres]⟩

end CoupledSourceSchurNaturality
end NCG
