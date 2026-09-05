/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCompoundMatrixExteriorPower

/-!
# Finite Grassmann Wick--exterior theorem

This file proves `thm:SMQG-Grassmann-Wick` in the finite orthonormal wedge
basis.  A Fock vector is a family of coefficients on the subset basis of each
exterior grade.  The reflected Gaussian pairing is defined from the Wick
determinants of the one-particle covariance.  The theorem identifies it with
the Euclidean pairing against the direct sum of compound matrices, including
the vacuum coefficient and the vanishing of cross-grade blocks by construction.
-/

open Matrix Finset

namespace NCG
namespace FiniteGrassmannWickExterior

open FiniteCompoundMatrixExteriorPower

/-- Coefficients of a finite fermionic Fock vector in the orthonormal subset
basis.  Grades above `d` have empty basis and hence carry no coefficients. -/
abbrev FockVector (d : ℕ) := (r : ℕ) → GradeIdx r d → ℂ

/-- The Wick coefficient between two grade-`r` basis words: the corresponding
minor of the one-particle covariance. -/
noncomputable def wickCoefficient {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (r : ℕ) (S T : GradeIdx r d) : ℂ :=
  (P.submatrix (sel S) (sel T)).det

/-- The normalized gauge-invariant reflected Gaussian pairing, written
directly as the finite Wick determinant sum. -/
noncomputable def reflectedGaussianPairing {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (F G : FockVector d) : ℂ :=
  ∑ r ∈ Finset.range (d + 1),
    ∑ S, star (F r S) * ∑ T, wickCoefficient P r S T * G r T

/-- Pairing of Fock vectors against fermionic second quantization
`Γ_∧(P)=⊕ᵣ ⋀^r P`. -/
noncomputable def secondQuantizationPairing {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (F G : FockVector d) : ℂ :=
  ∑ r ∈ Finset.range (d + 1),
    dotProduct (star (F r)) ((cmpd r P).mulVec (G r))

/-- Each reflected mixed-word coefficient is literally the corresponding
compound-matrix entry, hence the corresponding minor of `P`. -/
theorem wickCoefficient_eq_compound {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (S T : GradeIdx r d) :
    wickCoefficient P r S T = cmpd r P S T := rfl

/-- The vacuum coefficient is one. -/
theorem wickCoefficient_vacuum {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ)
    (S T : GradeIdx 0 d) : wickCoefficient P 0 S T = 1 := by
  rw [wickCoefficient_eq_compound]
  have hS : S = T := by
    apply Subtype.ext
    rw [Finset.card_eq_zero.mp S.2, Finset.card_eq_zero.mp T.2]
  subst T
  rw [cmpd_apply]
  exact Matrix.det_isEmpty

/-- **`thm:SMQG-Grassmann-Wick`.**  The Wick determinant functional is the
Fock-space inner product against exterior second quantization. -/
theorem reflectedGaussianPairing_eq_secondQuantization {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (F G : FockVector d) :
    reflectedGaussianPairing P F G = secondQuantizationPairing P F G := by
  simp only [reflectedGaussianPairing, secondQuantizationPairing,
    dotProduct, Matrix.mulVec, wickCoefficient, cmpd_apply, Pi.star_apply]

/-- Consolidated finite Wick--exterior certificate: arbitrary Fock-vector
pairing, the grade matrix identity, the minor formula, and vacuum normalization. -/
theorem finite_Grassmann_Wick_exterior {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) :
    (∀ F G : FockVector d,
      reflectedGaussianPairing P F G = secondQuantizationPairing P F G) ∧
    (∀ (r : ℕ) (S T : GradeIdx r d),
      wickCoefficient P r S T = cmpd r P S T) ∧
    (∀ S T : GradeIdx 0 d, wickCoefficient P 0 S T = 1) :=
  ⟨reflectedGaussianPairing_eq_secondQuantization P,
    wickCoefficient_eq_compound P, wickCoefficient_vacuum P⟩

end FiniteGrassmannWickExterior
end NCG
