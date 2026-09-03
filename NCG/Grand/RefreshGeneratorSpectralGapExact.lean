/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral gap from a global refresh generator

This is the operator core of (RP.8)--(RP.9).  Adding a rate-`rho` refresh to a
symmetric nonpositive local generator preserves symmetry/nonpositivity and
gives a sharp gap on the kernel of the refresh projection.  A centered Green
inverse then obeys the corresponding `rho⁻¹` norm and quadratic-form bounds.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NCG.RefreshGeneratorSpectralGap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `rho (R-I) + Lloc`, the reflected slab generator with global refresh. -/
def refreshGenerator (rho : ℝ) (refresh localGenerator : H →L[ℝ] H) : H →L[ℝ] H :=
  rho • (refresh - ContinuousLinearMap.id ℝ H) + localGenerator

/-- Symmetry of the refresh and local rows implies symmetry of the assembled
generator. -/
theorem refreshGenerator_symmetric
    (rho : ℝ) (refresh localGenerator : H →L[ℝ] H)
    (hrefresh : ∀ x y, ⟪refresh x, y⟫ = ⟪x, refresh y⟫)
    (hlocal : ∀ x y, ⟪localGenerator x, y⟫ = ⟪x, localGenerator y⟫) :
    ∀ x y, ⟪refreshGenerator rho refresh localGenerator x, y⟫ =
      ⟪x, refreshGenerator rho refresh localGenerator y⟫ := by
  intro x y
  simp only [refreshGenerator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [hrefresh, hlocal]

/-- If `R` is contractive in quadratic form and the local generator is
nonpositive, then the assembled generator is nonpositive. -/
theorem refreshGenerator_nonpositive
    (rho : ℝ) (hrho : 0 ≤ rho) (refresh localGenerator : H →L[ℝ] H)
    (hrefresh : ∀ x, ⟪refresh x, x⟫ ≤ ‖x‖ ^ 2)
    (hlocal : ∀ x, ⟪localGenerator x, x⟫ ≤ 0) :
    ∀ x, ⟪refreshGenerator rho refresh localGenerator x, x⟫ ≤ 0 := by
  intro x
  simp only [refreshGenerator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_smul_left,
    inner_sub_left, real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]
  have hmul := mul_le_mul_of_nonneg_left (hrefresh x) hrho
  linarith [hlocal x]

/-- **(RP.9)**: on centered writers (`R f=0`) the refresh contributes the
sharp coercive floor `rho`. -/
theorem centered_refresh_gap
    (rho : ℝ) (refresh localGenerator : H →L[ℝ] H) (f : H)
    (hcentered : refresh f = 0)
    (hlocal : ⟪localGenerator f, f⟫ ≤ 0) :
    rho * ‖f‖ ^ 2 ≤ ⟪-(refreshGenerator rho refresh localGenerator f), f⟫ := by
  simp only [refreshGenerator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, hcentered, zero_sub, smul_neg,
    neg_add_rev, neg_neg, inner_add_left, inner_smul_left,
    inner_neg_left, real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]
  linarith

/-- A centered inverse of `-L` inherits `‖Gf‖ ≤ rho⁻¹‖f‖`. -/
theorem centered_green_norm_bound
    (rho : ℝ) (hrho : 0 < rho) (refresh localGenerator green : H →L[ℝ] H)
    (hgreenCentered : ∀ f, refresh (green f) = 0)
    (hlocal : ∀ f, ⟪localGenerator f, f⟫ ≤ 0)
    (hinverse : ∀ f, -(refreshGenerator rho refresh localGenerator (green f)) = f) :
    ∀ f, ‖green f‖ ≤ rho⁻¹ * ‖f‖ := by
  intro f
  have hgap := centered_refresh_gap rho refresh localGenerator (green f)
    (hgreenCentered f) (hlocal (green f))
  rw [hinverse] at hgap
  have hcs : ⟪f, green f⟫ ≤ ‖f‖ * ‖green f‖ :=
    real_inner_le_norm f (green f)
  by_cases hz : ‖green f‖ = 0
  · rw [hz]
    positivity
  · have hgpos : 0 < ‖green f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hdiv : rho * ‖green f‖ ≤ ‖f‖ := by
      nlinarith
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hrho).2 (by simpa [mul_comm] using hdiv)

/-- The Green quadratic form is positive and bounded above by
`rho⁻¹ ‖f‖²`. -/
theorem centered_green_quadratic_bound
    (rho : ℝ) (hrho : 0 < rho) (refresh localGenerator green : H →L[ℝ] H)
    (hgreenCentered : ∀ f, refresh (green f) = 0)
    (hlocal : ∀ f, ⟪localGenerator f, f⟫ ≤ 0)
    (hinverse : ∀ f, -(refreshGenerator rho refresh localGenerator (green f)) = f) :
    ∀ f, 0 ≤ ⟪f, green f⟫ ∧
      ⟪f, green f⟫ ≤ rho⁻¹ * ‖f‖ ^ 2 := by
  intro f
  have hgap := centered_refresh_gap rho refresh localGenerator (green f)
    (hgreenCentered f) (hlocal (green f))
  rw [hinverse] at hgap
  have hnonneg : 0 ≤ ⟪f, green f⟫ :=
    le_trans (mul_nonneg hrho.le (sq_nonneg _)) hgap
  have hcs : ⟪f, green f⟫ ≤ ‖f‖ * ‖green f‖ :=
    real_inner_le_norm f (green f)
  have hnorm := centered_green_norm_bound rho hrho refresh localGenerator green
    hgreenCentered hlocal hinverse f
  constructor
  · exact hnonneg
  · calc
      ⟪f, green f⟫ ≤ ‖f‖ * ‖green f‖ := hcs
      _ ≤ ‖f‖ * (rho⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = rho⁻¹ * ‖f‖ ^ 2 := by ring

end NCG.RefreshGeneratorSpectralGap
