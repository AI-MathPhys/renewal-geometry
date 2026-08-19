/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ComplementCompressedResolventGap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Exact finite spectral resolvent gap

In a finite spectral frame, let `ν i ≥ 0` be the eigenvalues of a nonnegative operator.  The
projection onto the zero eigenspace deletes precisely the zero coordinates.  If `μ` is an attained
least positive eigenvalue, the complement-compressed shifted resolvent has operator norm
`(λ + μ)⁻¹`; consequently its shifted inverse norm is exactly `μ`.

This is the reusable finite-dimensional spectral calculation needed by the continuum Howe
compiler.  Concrete Hermitian matrices reach this frame through their unitary eigenbasis.
-/

open Matrix
open scoped Norms.L2Operator

noncomputable section

namespace NCG.SpectralGap

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Diagonal shifted resolvent associated with a finite nonnegative spectrum. -/
def finiteSpectralResolvent (ν : ι → ℝ) (lam : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i ↦ (((lam + ν i)⁻¹ : ℝ) : ℂ)

/-- Diagonal orthogonal projection onto the zero spectral coordinates. -/
def finiteZeroSpectralProjection (ν : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i ↦ if ν i = 0 then 1 else 0

/-- Resolvent weight after deleting the zero spectral coordinates. -/
def finiteTransientResolventWeight (ν : ι → ℝ) (lam : ℝ) (i : ι) : ℂ :=
  if ν i = 0 then 0 else (((lam + ν i)⁻¹ : ℝ) : ℂ)

/-- Complement compression by the zero projection is exactly the transient diagonal resolvent. -/
theorem finiteSpectralResolvent_compression_diagonal (ν : ι → ℝ) (lam : ℝ) :
    (1 - finiteZeroSpectralProjection ν) * finiteSpectralResolvent ν lam *
        (1 - finiteZeroSpectralProjection ν) =
      Matrix.diagonal (finiteTransientResolventWeight ν lam) := by
  unfold finiteZeroSpectralProjection finiteSpectralResolvent
  rw [← Matrix.diagonal_one]
  have hdiag :
      Matrix.diagonal (fun _ : ι ↦ (1 : ℂ)) -
          Matrix.diagonal (fun i ↦ if ν i = 0 then 1 else 0) =
        Matrix.diagonal (fun i ↦ 1 - if ν i = 0 then 1 else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : ν i = 0 <;> simp [finiteTransientResolventWeight, hi]

/-- The norm of the zero-complement compressed shifted resolvent is the reciprocal of the shifted
least positive eigenvalue.  The hypotheses state nonnegativity, minimality, and attainment of `μ`.
-/
theorem norm_finiteSpectralResolvent_compression_eq_inv_add
    (ν : ι → ℝ) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ ν i)
    (hmin : ∀ i, ν i ≠ 0 → μ ≤ ν i)
    (hattain : ∃ i, ν i = μ) :
    ‖(1 - finiteZeroSpectralProjection ν) * finiteSpectralResolvent ν lam *
        (1 - finiteZeroSpectralProjection ν)‖ = (lam + μ)⁻¹ := by
  rw [finiteSpectralResolvent_compression_diagonal, Matrix.l2_opNorm_diagonal]
  have hshift : 0 < lam + μ := by positivity
  have htarget : 0 ≤ (lam + μ)⁻¹ := (inv_nonneg.mpr hshift.le)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg htarget).2
    intro i
    by_cases hi : ν i = 0
    · simp [finiteTransientResolventWeight, hi, htarget]
    · have hνi : 0 < ν i := lt_of_le_of_ne (hν i) (Ne.symm hi)
      have hdenom : 0 < lam + ν i := by positivity
      have hinv : (lam + ν i)⁻¹ ≤ (lam + μ)⁻¹ := by
        exact inv_anti₀ hshift (by linarith [hmin i hi])
      simpa only [finiteTransientResolventWeight, if_neg hi, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hdenom)] using hinv
  · obtain ⟨i, hi⟩ := hattain
    have hi0 : ν i ≠ 0 := by rw [hi]; exact ne_of_gt hμ
    calc
      (lam + μ)⁻¹ = ‖finiteTransientResolventWeight ν lam i‖ := by
        rw [finiteTransientResolventWeight, if_neg hi0, hi, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hshift)]
      _ ≤ ‖finiteTransientResolventWeight ν lam‖ := norm_le_pi_norm _ i

/-- The diagonal spectral resolvent is a left inverse of the shifted diagonal operator. -/
theorem finiteSpectralResolvent_mul_shiftedDiagonal
    (ν : ι → ℝ) (lam : ℝ) (hlam : 0 < lam) (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralResolvent ν lam *
      ((lam : ℂ) • (1 : Matrix ι ι ℂ) +
        Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))) = 1 := by
  have hshift :
      (lam : ℂ) • (1 : Matrix ι ι ℂ) +
          Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)) =
        Matrix.diagonal (fun i ↦ (((lam + ν i) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hshift]
  unfold finiteSpectralResolvent
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hdenom : lam + ν i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hlam (hν i))
    simp only [Matrix.diagonal_apply, Matrix.one_apply, if_pos]
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hdenom)
  · simp [hij]

/-- The diagonal spectral resolvent is the literal inverse of the shifted diagonal operator. -/
theorem finiteSpectralResolvent_eq_inv_shiftedDiagonal
    (ν : ι → ℝ) (lam : ℝ) (hlam : 0 < lam) (hν : ∀ i, 0 ≤ ν i) :
    finiteSpectralResolvent ν lam =
      ((lam : ℂ) • (1 : Matrix ι ι ℂ) +
        Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))⁻¹ := by
  exact (Matrix.inv_eq_left_inv
    (finiteSpectralResolvent_mul_shiftedDiagonal ν lam hlam hν)).symm


/-- Unitary spectral transport is the literal inverse of the corresponding shifted operator. -/
theorem finiteUnitarySpectralResolvent_eq_inv_shiftedConjugate
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hν : ∀ i, 0 ≤ ν i) :
    Unitary.conjStarAlgAut ℂ _ U (finiteSpectralResolvent ν lam) =
      ((lam : ℂ) • (1 : Matrix ι ι ℂ) +
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ))))⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change e (finiteSpectralResolvent ν lam) *
      ((lam : ℂ) • 1 + e (Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))) = 1
  calc
    _ = e (finiteSpectralResolvent ν lam *
        ((lam : ℂ) • 1 + Matrix.diagonal (fun i ↦ ((ν i : ℝ) : ℂ)))) := by
      simp only [map_mul, map_add, map_smul, map_one]
    _ = e 1 := by
      rw [finiteSpectralResolvent_mul_shiftedDiagonal ν lam hlam hν]
    _ = 1 := map_one e


/-- The finite shifted resolvent transported from its spectral frame by a unitary matrix. -/
def finiteUnitarySpectralResolvent (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) (lam : ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (finiteSpectralResolvent ν lam)

/-- The zero spectral projection transported by the same unitary matrix. -/
def finiteUnitaryZeroSpectralProjection (U : Matrix.unitaryGroup ι ℂ)
    (ν : ι → ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (finiteZeroSpectralProjection ν)

/-- Unitary conjugation preserves the exact compressed-resolvent norm calculation. -/
theorem norm_finiteUnitarySpectralResolvent_compression_eq_inv_add
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ ν i)
    (hmin : ∀ i, ν i ≠ 0 → μ ≤ ν i)
    (hattain : ∃ i, ν i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection U ν) *
        finiteUnitarySpectralResolvent U ν lam *
        (1 - finiteUnitaryZeroSpectralProjection U ν)‖ = (lam + μ)⁻¹ := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hcompress :
      (1 - finiteUnitaryZeroSpectralProjection U ν) *
          finiteUnitarySpectralResolvent U ν lam *
          (1 - finiteUnitaryZeroSpectralProjection U ν) =
        e ((1 - finiteZeroSpectralProjection ν) * finiteSpectralResolvent ν lam *
          (1 - finiteZeroSpectralProjection ν)) := by
    change (1 - e (finiteZeroSpectralProjection ν)) *
        e (finiteSpectralResolvent ν lam) * (1 - e (finiteZeroSpectralProjection ν)) = _
    simp only [map_one, map_sub, map_mul]
  rw [hcompress]
  change ‖(U : Matrix ι ι ℂ) *
      ((1 - finiteZeroSpectralProjection ν) * finiteSpectralResolvent ν lam *
        (1 - finiteZeroSpectralProjection ν)) *
      (star U : Matrix ι ι ℂ)‖ = _
  rw [← Unitary.coe_star]
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  exact norm_finiteSpectralResolvent_compression_eq_inv_add
    ν lam μ hlam hμ hν hmin hattain

/-- The inverse-norm gap formula is invariant under a unitary change of spectral frame. -/
theorem inverseNormGap_finiteUnitarySpectralResolvent_eq_leastPositive
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ ν i)
    (hmin : ∀ i, ν i ≠ 0 → μ ≤ ν i)
    (hattain : ∃ i, ν i = μ) :
    ‖(1 - finiteUnitaryZeroSpectralProjection U ν) *
        finiteUnitarySpectralResolvent U ν lam *
        (1 - finiteUnitaryZeroSpectralProjection U ν)‖⁻¹ - lam = μ := by
  rw [norm_finiteUnitarySpectralResolvent_compression_eq_inv_add
    U ν lam μ hlam hμ hν hmin hattain, inv_inv]
  ring

/-- Exact numerical identification of the inverse-norm gap in the finite spectral frame. -/
theorem inverseNormGap_finiteSpectralResolvent_eq_leastPositive
    (ν : ι → ℝ) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hν : ∀ i, 0 ≤ ν i)
    (hmin : ∀ i, ν i ≠ 0 → μ ≤ ν i)
    (hattain : ∃ i, ν i = μ) :
    ‖(1 - finiteZeroSpectralProjection ν) * finiteSpectralResolvent ν lam *
        (1 - finiteZeroSpectralProjection ν)‖⁻¹ - lam = μ := by
  rw [norm_finiteSpectralResolvent_compression_eq_inv_add
    ν lam μ hlam hμ hν hmin hattain, inv_inv]
  ring

end NCG.SpectralGap
