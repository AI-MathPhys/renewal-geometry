/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.IsotypicPartialTraceFormula
import Mathlib.Data.Matrix.Block

/-!
# Finite pairwise-inequivalent isotypic packet decomposition

This file assembles the single-isotypic partial-trace formula across a finite
dependent family of pairwise nonisomorphic irreducible representations.
Diagonal coefficient blocks are scalar by Schur's lemma; off-diagonal blocks
vanish by the nonisomorphic form of Schur's lemma.
-/

open Matrix CategoryTheory
open scoped ComplexOrder Kronecker

namespace NCG
namespace FiniteIsotypicPacketDecomposition

variable {G L : Type} [Group G] [Fintype L] [DecidableEq L]
variable (I M : L → Type)
variable [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]
variable [∀ l, Nonempty (I l)]
variable [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)]

/-- The diagonal matrix block belonging to one isotypic label. -/
def diagonalIsotypicBlock
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ) (l : L) :
    Matrix (I l × M l) (I l × M l) ℂ :=
  fun p q => F ⟨l, p⟩ ⟨l, q⟩

/-- The irreducible-coordinate coefficient block between two multiplicity
coordinates and two isotypic labels. -/
def interIsotypicCoefficientBlock
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ)
    (l k : L) (a : M l) (b : M k) : Matrix (I l) (I k) ℂ :=
  fun i j => F ⟨l, (i, a)⟩ ⟨k, (j, b)⟩

/-- Multiplicity partial trace of one diagonal isotypic block. -/
noncomputable def familyMultiplicityPartialTrace
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ) (l : L) :
    Matrix (M l) (M l) ℂ :=
  NCG.IsotypicPartialTrace.multiplicityPartialTrace
    (diagonalIsotypicBlock I M F l)

/-- Global covariance under the dependent direct-sum representation implies
the coefficient-level intertwining equations used by Schur's lemma. -/
theorem coefficient_intertwines_of_global_covariance
    (ρ : ∀ l, G →* Matrix (I l) (I l) ℂ)
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ)
    (hglobal : ∀ g,
      F * Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) =
      Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) * F) :
    ∀ g l k a b,
      interIsotypicCoefficientBlock I M F l k a b * ρ k g =
        ρ l g * interIsotypicCoefficientBlock I M F l k a b := by
  intro g l k a b
  ext i j
  have hentry := congrFun (congrFun (hglobal g) ⟨l, (i, a)⟩) ⟨k, (j, b)⟩
  simpa [Matrix.mul_apply, Matrix.blockDiagonal'_apply,
    Matrix.kronecker_apply, Matrix.one_apply,
    interIsotypicCoefficientBlock, ← Finset.univ_sigma_univ,
    Finset.sum_sigma, ← Finset.univ_product_univ,
    Finset.sum_product] using hentry

/-- Full pairwise-inequivalent Schur decomposition.  The hypothesis is the
coefficient form of covariance of the averaged operator under the direct-sum
representation. -/
theorem finite_isotypic_partialTrace_decomposition
    (ρ : ∀ l, G →* Matrix (I l) (I l) ℂ)
    [∀ l, Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l)))]
    (hpair : ∀ {l k : L}, l ≠ k → IsEmpty
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ k)) ≅
        FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l))))
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ)
    (hcomm : ∀ g l k a b,
      interIsotypicCoefficientBlock I M F l k a b * ρ k g =
        ρ l g * interIsotypicCoefficientBlock I M F l k a b) :
    F = Matrix.blockDiagonal' (fun l =>
      ((Fintype.card (I l) : ℂ)⁻¹ • (1 : Matrix (I l) (I l) ℂ)) ⊗ₖ
        familyMultiplicityPartialTrace I M F l) := by
  ext ⟨l, ⟨i, a⟩⟩ ⟨k, ⟨j, b⟩⟩
  by_cases hlk : l = k
  · subst k
    have hformula :=
      NCG.IsotypicPartialTrace.eq_invDimension_smul_one_kronecker_partialTrace_of_irreducible
        (ρ l) (diagonalIsotypicBlock I M F l)
        (fun g a b => by
          change interIsotypicCoefficientBlock I M F l l a b * ρ l g =
            ρ l g * interIsotypicCoefficientBlock I M F l l a b
          exact hcomm g l l a b)
    rw [Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun hformula (i, a)) (j, b)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hlk]
    have hzero :=
      NCG.CompactIsotypicSchur.matrix_eq_zero_of_intertwines_nonisomorphic
        (ρ k) (ρ l) (hpair hlk)
        (interIsotypicCoefficientBlock I M F l k a b)
        (fun g => hcomm g l k a b)
    exact congrFun (congrFun hzero i) j

/-- Full finite isotypic decomposition derived directly from global
direct-sum covariance. -/
theorem finite_isotypic_decomposition_of_global_covariance
    (ρ : ∀ l, G →* Matrix (I l) (I l) ℂ)
    [∀ l, Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l)))]
    (hpair : ∀ {l k : L}, l ≠ k → IsEmpty
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ k)) ≅
        FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation (ρ l))))
    (F : Matrix (Σ l, I l × M l) (Σ l, I l × M l) ℂ)
    (hglobal : ∀ g,
      F * Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) =
      Matrix.blockDiagonal' (fun l =>
        ρ l g ⊗ₖ (1 : Matrix (M l) (M l) ℂ)) * F) :
    F = Matrix.blockDiagonal' (fun l =>
      ((Fintype.card (I l) : ℂ)⁻¹ • (1 : Matrix (I l) (I l) ℂ)) ⊗ₖ
        familyMultiplicityPartialTrace I M F l) :=
  finite_isotypic_partialTrace_decomposition I M ρ hpair F
    (coefficient_intertwines_of_global_covariance I M ρ F hglobal)

end FiniteIsotypicPacketDecomposition
end NCG
