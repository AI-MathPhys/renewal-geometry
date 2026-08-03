/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Flat Dirac scaling
  (`thm:dirac-scaling`, arithmetic manuscript)

The provable core of the lattice-to-continuum Dirac limit:

* `centered_difference_plane_wave`: the exact symbol identity —
  the centered difference of a plane wave is multiplication by
  `i·sin(hp)/h`:
  `(e^{ip(x+h)} - e^{ip(x-h)})/(2h) = (sin(hp)/h)·i·e^{ipx}`;
* `abs_sin_sub_le`: the cubic sine remainder
  `|sin u - u| ≤ |u|³/6`;
* `dirac_symbol_bound`: the uniform-on-compacts symbol
  convergence — for `|p| ≤ K` and `h > 0`,
  `|sin(hp)/h - p| ≤ h² K³ / 6`,
  so the lattice symbols `sin(hp)/h` converge to `p` uniformly on
  every compact momentum set as `h ↓ 0`.

Rendering disclosed: the passage from uniform symbol convergence
on compacts to `L²` convergence on Schwartz spinors and to strong
resolvent convergence of the self-adjoint Fourier-multiplier
Hamiltonians is the standard core-convergence argument
(the manuscript's citation of the common-core theorem); Mathlib
has no unbounded self-adjoint spectral theory, so that layer
stays disclosed per house policy, as in the reduced-cell record.
-/

open Complex

namespace NCG

/-- The centered difference of a plane wave is multiplication by
the lattice symbol `i·sin(hp)/h`. -/
theorem centered_difference_plane_wave (p x h : ℝ) (hh : h ≠ 0) :
    (Complex.exp ((p * (x + h) : ℝ) * I)
      - Complex.exp ((p * (x - h) : ℝ) * I)) / (2 * h)
    = (Real.sin (h * p) : ℂ) / h * I
        * Complex.exp ((p * x : ℝ) * I) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have h1 : ((p * (x + h) : ℝ) : ℂ) * I
      = ((p * x : ℝ) : ℂ) * I + ((p * h : ℝ) : ℂ) * I := by
    push_cast
    ring
  have h2 : ((p * (x - h) : ℝ) : ℂ) * I
      = ((p * x : ℝ) : ℂ) * I + ((-(p * h) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add]
  simp only [Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  rw [show Real.sin (h * p) = Real.sin (p * h) from by
    rw [mul_comm]]
  push_cast
  field_simp
  ring

/-- Cubic sine remainder: `|sin u - u| ≤ |u|³/6`. -/
theorem abs_sin_sub_le (u : ℝ) :
    |Real.sin u - u| ≤ |u| ^ 3 / 6 := by
  rcases lt_trichotomy u 0 with hneg | hzero | hpos
  · have hu' : 0 < -u := by linarith
    have hlow : -u - (-u) ^ 3 / 6 < Real.sin (-u) :=
      Real.sin_gt_sub_cube hu'
    have hup : Real.sin (-u) < -u := Real.sin_lt hu'
    rw [Real.sin_neg] at hlow hup
    have habs : |u| = -u := abs_of_neg hneg
    rw [habs, abs_le]
    constructor <;> nlinarith
  · simp [hzero]
  · have hlow : u - u ^ 3 / 6 < Real.sin u :=
      Real.sin_gt_sub_cube hpos
    have hup : Real.sin u < u := Real.sin_lt hpos
    have habs : |u| = u := abs_of_pos hpos
    rw [habs, abs_le]
    constructor <;> nlinarith

/-- `thm:dirac-scaling`, symbol convergence: uniformly on the
compact momentum set `|p| ≤ K`, the lattice symbol satisfies
`|sin(hp)/h - p| ≤ h²K³/6 → 0` as `h ↓ 0`. -/
theorem dirac_symbol_bound (K p h : ℝ) (hp : |p| ≤ K)
    (hh : 0 < h) :
    |Real.sin (h * p) / h - p| ≤ h ^ 2 * K ^ 3 / 6 := by
  have hbound := abs_sin_sub_le (h * p)
  have hkey : Real.sin (h * p) / h - p
      = (Real.sin (h * p) - h * p) / h := by
    field_simp
  rw [hkey, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |Real.sin (h * p) - h * p| ≤ |h * p| ^ 3 / 6 := hbound
    _ = h ^ 3 * |p| ^ 3 / 6 := by
        rw [abs_mul, abs_of_pos hh, mul_pow]
    _ ≤ h ^ 3 * K ^ 3 / 6 := by
        have h3 : |p| ^ 3 ≤ K ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) hp 3
        nlinarith [pow_pos hh 3]
    _ = h ^ 2 * K ^ 3 / 6 * h := by ring

end NCG
