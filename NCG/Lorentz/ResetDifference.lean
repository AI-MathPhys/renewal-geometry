/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Symmetric reset differences and their Fourier multipliers

**Definition `def:reset-differences`**: the symmetric reset difference
`δ_θ,h` has real Fourier multiplier `s_θ,h(ξ) = h⁻¹ sin(h·θ·ξ)`, and

* `s_θ,h(ξ) → θ·ξ` as the mesh `h → 0`
  (`NCG.resetSymbol_tendsto` — the calibration limit that makes the
  lattice momenta converge to the continuum momenta, the pointwise core
  of the band estimates in `thm:rg-eigenvalue` and
  `thm:band-norm-resolvent`);
* the uniform bound `|s_θ,h(ξ)| ≤ |θ·ξ|` (`NCG.abs_resetSymbol_le`),
  from `|sin x| ≤ |x|`. -/

namespace NCG

open Real Filter

/-- `|sin x| ≤ |x|`. -/
theorem abs_sin_le_abs (x : ℝ) : |Real.sin x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → |Real.sin y| ≤ y := by
    intro y hy
    rcases le_or_gt y (π / 2) with hsmall | hbig
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy
        (by linarith [Real.pi_pos]))]
      exact Real.sin_le hy
    · calc |Real.sin y| ≤ 1 := Real.abs_sin_le_one y
        _ ≤ y := by nlinarith [Real.pi_gt_three]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact key x hx
  · rw [abs_of_neg hx]
    have h := key (-x) (by linarith)
    rwa [Real.sin_neg, abs_neg] at h

/-- **The reset-difference multiplier**
`s_θ,h(ξ) = h⁻¹ sin(h·(θ·ξ))` (Definition `def:reset-differences`),
written in the scalar variable `u = θ·ξ`. -/
noncomputable def resetSymbol (u h : ℝ) : ℝ := h⁻¹ * Real.sin (h * u)

/-- **Mesh calibration** (Definition `def:reset-differences`): the reset
multiplier converges to the continuum momentum, `s_θ,h(ξ) → θ·ξ` as
`h → 0`. -/
theorem resetSymbol_tendsto (u : ℝ) :
    Tendsto (fun h => resetSymbol u h) (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds u) := by
  have hd : HasDerivAt (fun h : ℝ => Real.sin (h * u)) u 0 := by
    have h1 : HasDerivAt (fun h : ℝ => h * u) u 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const u
    have h2 := h1.sin
    simpa using h2
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  refine hslope.congr fun h => ?_
  simp [slope_def_field, resetSymbol, div_eq_inv_mul]

/-- **The uniform momentum bound** (Definition `def:reset-differences`):
`|s_θ,h(ξ)| ≤ |θ·ξ|` for every mesh `h ≠ 0`. -/
theorem abs_resetSymbol_le (u : ℝ) {h : ℝ} (hh : h ≠ 0) :
    |resetSymbol u h| ≤ |u| := by
  unfold resetSymbol
  rw [abs_mul, abs_inv]
  have hs := abs_sin_le_abs (h * u)
  rw [abs_mul] at hs
  have hpos : 0 < |h| := abs_pos.mpr hh
  calc |h|⁻¹ * |Real.sin (h * u)| ≤ |h|⁻¹ * (|h| * |u|) := by
        exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = |u| := by field_simp

end NCG
