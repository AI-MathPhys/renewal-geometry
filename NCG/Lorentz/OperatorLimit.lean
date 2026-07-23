/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operator-level continuum limit (symbol cores)

**Theorem `thm:operator-limit`**: the discrete central-difference
symbol converges to the continuum Dirac symbol as the mesh vanishes:
`sin(hξ)/h → ξ` (`NCG.discrete_symbol_limit` — the slope of sine at
the origin).

**Theorem `thm:band-norm-resolvent`**: on a momentum band `|ξ| ≤ Λ`
the convergence is *uniform* with explicit cubic error:
`|sin(hξ)/h − ξ| ≤ h²Λ³/6` (`NCG.band_symbol_bound`), from the global
sine inequality `|sin x − x| ≤ |x|³/6` (`NCG.abs_sin_sub_le`).
Combined with the resolvent identity this gives norm-resolvent
closeness on bands; the Fourier band-projection packaging is the
noted step.
-/

namespace NCG

/-- Global sine comparison: `|sin x − x| ≤ |x|³/6`. -/
theorem abs_sin_sub_le (x : ℝ) : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  have key : ∀ y : ℝ, 0 < y → |Real.sin y - y| ≤ |y| ^ 3 / 6 := by
    intro y hy
    have h1 : Real.sin y < y := Real.sin_lt hy
    have h2 : y - y ^ 3 / 6 < Real.sin y := Real.sin_gt_sub_cube hy
    rw [abs_of_neg (by linarith), abs_of_pos hy]
    linarith
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := key (-x) (by linarith)
    rw [Real.sin_neg, abs_neg] at h
    calc |Real.sin x - x| = |-(Real.sin x - x)| := (abs_neg _).symm
      _ = |-Real.sin x - -x| := by ring_nf
      _ ≤ |x| ^ 3 / 6 := h
  · simp [hx]
  · exact key x hx

/-- **Theorem `thm:operator-limit` (symbol core)**: the discrete
difference symbol converges to the continuum symbol as the mesh
vanishes — `sin(hξ)/h → ξ` for `h → 0`, the slope of sine at the
origin. -/
theorem discrete_symbol_limit (ξ : ℝ) :
    Filter.Tendsto (fun h : ℝ => Real.sin (h * ξ) / h)
      (nhdsWithin 0 {0}ᶜ) (nhds ξ) := by
  have h1 : HasDerivAt (fun h : ℝ => Real.sin (h * ξ)) ξ 0 := by
    have h2 : HasDerivAt (fun h : ℝ => h * ξ) ξ 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const ξ
    simpa using h2.sin
  rw [hasDerivAt_iff_tendsto_slope] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [slope_def_field]
  simp

/-- **Theorem `thm:band-norm-resolvent` (uniform band bound)**: on the
momentum band `|ξ| ≤ Λ` the discrete symbol is uniformly within
`h²Λ³/6` of the continuum symbol. -/
theorem band_symbol_bound (Λ h ξ : ℝ) (hh : 0 < h) (_hΛ : 0 ≤ Λ)
    (hξ : |ξ| ≤ Λ) :
    |Real.sin (h * ξ) / h - ξ| ≤ h ^ 2 * Λ ^ 3 / 6 := by
  have heq : Real.sin (h * ξ) / h - ξ = (Real.sin (h * ξ) - h * ξ) / h := by
    field_simp
  rw [heq, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have hb := abs_sin_sub_le (h * ξ)
  have hcube : |h * ξ| ^ 3 = h ^ 3 * |ξ| ^ 3 := by
    rw [abs_mul, abs_of_pos hh]
    ring
  have hpow : |ξ| ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hξ 3
  calc |Real.sin (h * ξ) - h * ξ| ≤ |h * ξ| ^ 3 / 6 := hb
    _ = h ^ 3 * |ξ| ^ 3 / 6 := by rw [hcube]
    _ ≤ h ^ 2 * Λ ^ 3 / 6 * h := by nlinarith [hh.le, pow_nonneg hh.le 3]

end NCG
