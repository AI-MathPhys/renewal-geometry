/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpectralResolventGap
import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Analysis.Matrix.PosDef
/-!
# Exact finite Hermitian resolvent gap

This file connects the finite spectral-frame calculation to a literal Hermitian matrix.  The
canonical unitary eigenbasis identifies the transported diagonal resolvent with `(λ I + A)⁻¹`.
Consequently, compression away from the zero eigenspace recovers the least positive eigenvalue
by the shifted inverse-norm formula.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.SpectralGap

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- In the canonical eigenbasis of a Hermitian matrix, the transported spectral resolvent is the
literal inverse of the shifted matrix. -/
theorem finiteUnitarySpectralResolvent_eigenvector_eq_inv_shiftedHermitian
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (lam : ℝ)
    (hlam : 0 < lam) (hν : ∀ i, 0 ≤ hA.eigenvalues i) :
    finiteUnitarySpectralResolvent hA.eigenvectorUnitary hA.eigenvalues lam =
      ((lam : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ := by
  have hspectral :
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (fun i ↦ ((hA.eigenvalues i : ℝ) : ℂ))) = A := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
        apply congrArg (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary)
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [Matrix.diagonal_apply, if_pos, Function.comp_apply]
          apply Complex.ext <;> simp [RCLike.ofReal]
        · simp [hij]
      _ = A := hA.spectral_theorem.symm
  unfold finiteUnitarySpectralResolvent
  rw [finiteUnitarySpectralResolvent_eq_inv_shiftedConjugate
    hA.eigenvectorUnitary hA.eigenvalues lam hlam hν, hspectral]

/-- Exact norm of the literal shifted Hermitian resolvent after deleting its zero eigenspace. -/
theorem norm_shiftedHermitianResolvent_zeroCompression_eq_inv_add
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ hA.eigenvalues i)
    (hmin : ∀ i, hA.eigenvalues i ≠ 0 → μ ≤ hA.eigenvalues i)
    (hattain : ∃ i, hA.eigenvalues i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection hA.eigenvectorUnitary hA.eigenvalues) *
        (((lam : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) *
        (1 - finiteUnitaryZeroSpectralProjection hA.eigenvectorUnitary hA.eigenvalues)‖ =
      (lam + μ)⁻¹ := by
  rw [← finiteUnitarySpectralResolvent_eigenvector_eq_inv_shiftedHermitian
    hA lam hlam hν]
  exact norm_finiteUnitarySpectralResolvent_compression_eq_inv_add
    hA.eigenvectorUnitary hA.eigenvalues lam μ hlam hμ hν hmin hattain

/-- The literal finite Hermitian resolvent recovers the least positive eigenvalue by the shifted
inverse-norm formula. -/
theorem inverseNormGap_shiftedHermitianResolvent_eq_leastPositive
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ hA.eigenvalues i)
    (hmin : ∀ i, hA.eigenvalues i ≠ 0 → μ ≤ hA.eigenvalues i)
    (hattain : ∃ i, hA.eigenvalues i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection hA.eigenvectorUnitary hA.eigenvalues) *
        (((lam : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) *
        (1 - finiteUnitaryZeroSpectralProjection hA.eigenvectorUnitary hA.eigenvalues)‖⁻¹ -
      lam = μ := by
  rw [norm_shiftedHermitianResolvent_zeroCompression_eq_inv_add
    hA lam μ hlam hμ hν hmin hattain, inv_inv]
  ring

/-- Positive semidefiniteness discharges the spectral nonnegativity premise in the literal
compressed-resolvent norm formula. -/
theorem norm_shiftedPosSemidefiniteResolvent_zeroCompression_eq_inv_add
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hmin : ∀ i, hA.1.eigenvalues i ≠ 0 → μ ≤ hA.1.eigenvalues i)
    (hattain : ∃ i, hA.1.eigenvalues i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection hA.1.eigenvectorUnitary hA.1.eigenvalues) *
        (((lam : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) *
        (1 - finiteUnitaryZeroSpectralProjection hA.1.eigenvectorUnitary hA.1.eigenvalues)‖ =
      (lam + μ)⁻¹ := by
  exact norm_shiftedHermitianResolvent_zeroCompression_eq_inv_add
    hA.1 lam μ hlam hμ hA.eigenvalues_nonneg hmin hattain

/-- Positive semidefiniteness also discharges nonnegativity in the literal inverse-norm gap
formula. -/
theorem inverseNormGap_shiftedPosSemidefiniteResolvent_eq_leastPositive
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hmin : ∀ i, hA.1.eigenvalues i ≠ 0 → μ ≤ hA.1.eigenvalues i)
    (hattain : ∃ i, hA.1.eigenvalues i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection hA.1.eigenvectorUnitary hA.1.eigenvalues) *
        (((lam : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) *
        (1 - finiteUnitaryZeroSpectralProjection hA.1.eigenvectorUnitary hA.1.eigenvalues)‖⁻¹ -
      lam = μ := by
  exact inverseNormGap_shiftedHermitianResolvent_eq_leastPositive
    hA.1 lam μ hlam hμ hA.eigenvalues_nonneg hmin hattain
end NCG.SpectralGap
