/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PotentialPalatini
import NCG.Grand.ExactSourceSchurResidual

/-!
# Pseudoinverse counterterm least squares

This file completes the Moore--Penrose least-squares clause of
`thm:potential-counterterm-exactness`.  No full-column-rank hypothesis is
imposed on the allowed counterterm synthesis.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The canonical minimum-norm allowed coefficient used to cancel a raw
source through `C`. -/
noncomputable def optimalCountertermCoefficient {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin f) (Fin e) ℂ :=
  sourceGramPseudoinverse C * Cᴴ * R

/-- The optimally uncancelled part of a raw source. -/
noncomputable def irreducibleCountertermResidual {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin h) (Fin e) ℂ :=
  R - C * optimalCountertermCoefficient C R

/-- The canonical residual is exactly the orthogonal complement of the
allowed counterterm range. -/
theorem irreducibleCountertermResidual_eq_orthogonalProjection {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ) :
    irreducibleCountertermResidual C R =
      (1 - sourceRangeProjection C) * R := by
  simp only [irreducibleCountertermResidual, optimalCountertermCoefficient,
    sourceRangeProjection, Matrix.sub_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

/-- Every allowed cancellation splits orthogonally into the irreducible
residual and an allowed range term. -/
theorem countertermCancellation_orthogonalDecomposition {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ)
    (K : Matrix (Fin f) (Fin e) ℂ) :
    let K₀ := optimalCountertermCoefficient C R
    let E := irreducibleCountertermResidual C R
    R - C * K = E + C * (K₀ - K) ∧
      Cᴴ * E = 0 ∧ Eᴴ * C = 0 := by
  let P := sourceRangeProjection C
  let K₀ := optimalCountertermCoefficient C R
  let E := irreducibleCountertermResidual C R
  obtain ⟨hPH, -, hPC⟩ :=
    (sourceGramPseudoinverse_projection C).2.2.2
  change Pᴴ = P at hPH
  change P * C = C at hPC
  have hCP : Cᴴ * P = Cᴴ := by
    calc
      Cᴴ * P = (P * C)ᴴ := by rw [Matrix.conjTranspose_mul, hPH]
      _ = Cᴴ := by rw [hPC]
  have hE : E = (1 - P) * R := by
    simpa only [E, P] using
      irreducibleCountertermResidual_eq_orthogonalProjection C R
  have hCE : Cᴴ * E = 0 := by
    rw [hE, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hCP,
      sub_self, Matrix.zero_mul]
  have hEC : Eᴴ * C = 0 := by
    have h := congrArg Matrix.conjTranspose hCE
    simpa [Matrix.conjTranspose_mul] using h
  refine ⟨?_, hCE, hEC⟩
  simp only [irreducibleCountertermResidual]
  rw [Matrix.mul_sub]
  abel

/-- Exact Moore--Penrose Pythagoras formula for arbitrary allowed
counterterm coefficients. -/
theorem countertermLeastSquares_gramDecomposition {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ)
    (K : Matrix (Fin f) (Fin e) ℂ) :
    let K₀ := optimalCountertermCoefficient C R
    let E := irreducibleCountertermResidual C R
    (R - C * K)ᴴ * (R - C * K) =
      Eᴴ * E + (K₀ - K)ᴴ * (Cᴴ * C) * (K₀ - K) := by
  let K₀ := optimalCountertermCoefficient C R
  let E := irreducibleCountertermResidual C R
  let L := K₀ - K
  obtain ⟨hdec, hCE, hEC⟩ :=
    countertermCancellation_orthogonalDecomposition C R K
  change Cᴴ * E = 0 at hCE
  change Eᴴ * C = 0 at hEC
  have hdec' : R - C * K = E + C * L := by
    simpa only [E, K₀, L] using hdec
  change (R - C * K)ᴴ * (R - C * K) =
    Eᴴ * E + Lᴴ * (Cᴴ * C) * L
  rw [hdec', Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
  calc
    (Eᴴ + Lᴴ * Cᴴ) * (E + C * L) =
        Eᴴ * E + Eᴴ * C * L +
          Lᴴ * Cᴴ * E + Lᴴ * (Cᴴ * C) * L := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      simp only [Matrix.mul_assoc]
      abel
    _ = Eᴴ * E + Lᴴ * (Cᴴ * C) * L := by
      rw [hEC, Matrix.zero_mul,
        Matrix.mul_assoc Lᴴ Cᴴ E, hCE, Matrix.mul_zero]
      simp

/-- The irreducible Gram is the exact pseudoinverse Schur residual, and every
other allowed cancellation has a positive-semidefinite Gram excess. -/
theorem countertermLeastSquares_optimality {h f e : ℕ}
    (C : Matrix (Fin h) (Fin f) ℂ)
    (R : Matrix (Fin h) (Fin e) ℂ) :
    let E := irreducibleCountertermResidual C R
    Eᴴ * E = sourceSchurResidual C R ∧
      ∀ K : Matrix (Fin f) (Fin e) ℂ,
        ((R - C * K)ᴴ * (R - C * K) - Eᴴ * E).PosSemidef := by
  let P := sourceRangeProjection C
  let E := irreducibleCountertermResidual C R
  obtain ⟨hPH, hP2, -⟩ :=
    (sourceGramPseudoinverse_projection C).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hE : E = (1 - P) * R := by
    simpa only [E, P] using
      irreducibleCountertermResidual_eq_orthogonalProjection C R
  have hgram : Eᴴ * E = Rᴴ * (1 - P) * R := by
    rw [hE, Matrix.conjTranspose_mul, hQH]
    calc
      Rᴴ * (1 - P) * ((1 - P) * R) =
          Rᴴ * ((1 - P) * (1 - P)) * R := by
            simp only [Matrix.mul_assoc]
      _ = Rᴴ * (1 - P) * R := by rw [hQ2]
  constructor
  · rw [hgram, sourceSchurResidual_eq_orthogonalResidual]
  · intro K
    rw [countertermLeastSquares_gramDecomposition C R K]
    simp only [add_sub_cancel_left]
    have hpsd := Matrix.posSemidef_conjTranspose_mul_self
      (C * (optimalCountertermCoefficient C R - K))
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hpsd

end NCG
