/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Band symbol and Legendre dual
  (`lem:band-legendre`, GR_emergence)

For the band symbol `h(θ) = √(λ² + c²θ²) - λ` (radial reduction of
the isotropic metric case):

* `band_legendre_upper` — the two-term Cauchy–Schwarz bound
  `θv - h(θ) ≤ λ(1 - √(1 - v²/c²))` for every `θ`, inside the
  spectral velocity cone `|v| < c`;
* `band_legendre_attained` — the bound is attained at the
  stationary covector `θ* = λv/(c√(c² - v²))`, so the Legendre
  transform is exactly `L(v) = λ(1 - √(1 - v²/c²))`;
* `band_legendre_infinite_outside` — strictly outside the cone
  (`v > c`) the dual supremum is `+∞`: the tilted symbol is
  unbounded above.

The reduction of the anisotropic metric symbol to this radial form
along `g`-geodesic polar coordinates is the declared geometric
step.
-/

namespace NCG

/-- The Cauchy–Schwarz upper bound: inside the cone, every covector
satisfies `θv - (√(λ² + c²θ²) - λ) ≤ λ(1 - √(1 - v²/c²))`. -/
theorem band_legendre_upper (lam c v th : ℝ) (hlam : 0 < lam)
    (hc : 0 < c) (hv : |v| < c) :
    th * v - (Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) - lam)
      ≤ lam * (1 - Real.sqrt (1 - v ^ 2 / c ^ 2)) := by
  have hv2 : v ^ 2 < c ^ 2 := by
    have := abs_lt.mp hv
    nlinarith [abs_nonneg v, sq_abs v]
  have hcv : (0 : ℝ) ≤ c ^ 2 - v ^ 2 := by linarith
  -- √(1 - v²/c²) = √(c² - v²)/c
  have hratio : Real.sqrt (1 - v ^ 2 / c ^ 2)
      = Real.sqrt (c ^ 2 - v ^ 2) / c := by
    rw [show (1 : ℝ) - v ^ 2 / c ^ 2 = (c ^ 2 - v ^ 2) / c ^ 2 from
        by field_simp]
    rw [Real.sqrt_div hcv, Real.sqrt_sq hc.le]
  -- Cauchy–Schwarz: θv + (λ/c)√(c²-v²) ≤ √(λ² + c²θ²)
  have hs := Real.sq_sqrt hcv
  have hsnn := Real.sqrt_nonneg (c ^ 2 - v ^ 2)
  have hkey : th * v + (lam / c) * Real.sqrt (c ^ 2 - v ^ 2)
      ≤ Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) := by
    have hrhsnn : (0 : ℝ) ≤ Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) :=
      Real.sqrt_nonneg _
    have hsq : (th * v + (lam / c) * Real.sqrt (c ^ 2 - v ^ 2)) ^ 2
        ≤ lam ^ 2 + c ^ 2 * th ^ 2 := by
      have hcs := sq_nonneg
        (th * Real.sqrt (c ^ 2 - v ^ 2) - (lam / c) * v)
      have hc0 : c ≠ 0 := hc.ne'
      have hexp : lam ^ 2 + c ^ 2 * th ^ 2
          - (th * v + (lam / c) * Real.sqrt (c ^ 2 - v ^ 2)) ^ 2
          = (th * Real.sqrt (c ^ 2 - v ^ 2) - (lam / c) * v) ^ 2 := by
        set q : ℝ := lam / c with hqdef
        have hlam' : lam = q * c := by
          rw [hqdef]
          field_simp
        rw [hlam']
        linear_combination (-(q ^ 2) - th ^ 2) * hs
      linarith [hcs, hexp]
    calc th * v + (lam / c) * Real.sqrt (c ^ 2 - v ^ 2)
        ≤ |th * v + (lam / c) * Real.sqrt (c ^ 2 - v ^ 2)| :=
          le_abs_self _
    _ ≤ Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt hsq
  rw [hratio]
  have hgoal : th * v - Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2)
      ≤ -(lam / c) * Real.sqrt (c ^ 2 - v ^ 2) := by linarith
  have : lam * (1 - Real.sqrt (c ^ 2 - v ^ 2) / c)
      = lam - (lam / c) * Real.sqrt (c ^ 2 - v ^ 2) := by
    field_simp
  linarith [hgoal, this.ge]

/-- The bound is attained at the stationary covector
`θ* = λv/(c√(c² - v²))`: the Legendre transform of the band symbol
is exactly `L(v) = λ(1 - √(1 - v²/c²))` inside the cone. -/
theorem band_legendre_attained (lam c v : ℝ) (hlam : 0 < lam)
    (hc : 0 < c) (hv : |v| < c) :
    (lam * v / (c * Real.sqrt (c ^ 2 - v ^ 2))) * v
        - (Real.sqrt (lam ^ 2 + c ^ 2
            * (lam * v / (c * Real.sqrt (c ^ 2 - v ^ 2))) ^ 2)
          - lam)
      = lam * (1 - Real.sqrt (1 - v ^ 2 / c ^ 2)) := by
  have hv2 : v ^ 2 < c ^ 2 := by
    have := abs_lt.mp hv
    nlinarith [abs_nonneg v, sq_abs v]
  have hcvpos : (0 : ℝ) < c ^ 2 - v ^ 2 := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (c ^ 2 - v ^ 2) :=
    Real.sqrt_pos.mpr hcvpos
  have hs := Real.sq_sqrt hcvpos.le
  have hratio : Real.sqrt (1 - v ^ 2 / c ^ 2)
      = Real.sqrt (c ^ 2 - v ^ 2) / c := by
    rw [show (1 : ℝ) - v ^ 2 / c ^ 2 = (c ^ 2 - v ^ 2) / c ^ 2 from
        by field_simp]
    rw [Real.sqrt_div hcvpos.le, Real.sqrt_sq hc.le]
  -- the square root at the stationary point evaluates in closed form
  have hinner : lam ^ 2 + c ^ 2
      * (lam * v / (c * Real.sqrt (c ^ 2 - v ^ 2))) ^ 2
      = (lam * c / Real.sqrt (c ^ 2 - v ^ 2)) ^ 2 := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hcvpos.le]
    ring
  have hsqrt : Real.sqrt (lam ^ 2 + c ^ 2
      * (lam * v / (c * Real.sqrt (c ^ 2 - v ^ 2))) ^ 2)
      = lam * c / Real.sqrt (c ^ 2 - v ^ 2) := by
    rw [hinner, Real.sqrt_sq (by positivity)]
  rw [hsqrt, hratio]
  field_simp
  ring_nf
  have hs2 : Real.sqrt (-v ^ 2 + c ^ 2) ^ 2 = -v ^ 2 + c ^ 2 :=
    Real.sq_sqrt (by linarith)
  linear_combination hs2

/-- Strictly outside the spectral velocity cone (`v > c`) the tilt
`θv - h(θ)` is unbounded above: no finite dual point exists. -/
theorem band_legendre_infinite_outside (lam c v M : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hv : c < v) :
    ∃ th : ℝ, M < th * v
      - (Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) - lam) := by
  -- for θ ≥ 0, √(λ² + c²θ²) ≤ λ + cθ, so the tilt grows like θ(v-c)
  have hgrow : ∀ th : ℝ, 0 ≤ th →
      th * v - (Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2) - lam)
        ≥ th * (v - c) := by
    intro th hth
    have hb : Real.sqrt (lam ^ 2 + c ^ 2 * th ^ 2)
        ≤ lam + c * th := by
      rw [show lam + c * th = Real.sqrt ((lam + c * th) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg hlam.le (mul_nonneg hc.le hth)]
    nlinarith
  refine ⟨max 0 ((M + 1) / (v - c)), ?_⟩
  have hvc : (0 : ℝ) < v - c := by linarith
  have hth0 : (0 : ℝ) ≤ max 0 ((M + 1) / (v - c)) := le_max_left _ _
  have hthM : (M + 1) / (v - c) ≤ max 0 ((M + 1) / (v - c)) :=
    le_max_right _ _
  have h1 := hgrow _ hth0
  have h2 : (M + 1) ≤ max 0 ((M + 1) / (v - c)) * (v - c) := by
    rw [← div_le_iff₀ hvc]
    exact hthM
  linarith

end NCG
