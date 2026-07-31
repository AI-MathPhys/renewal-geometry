/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The local cubic orbit on an `S₃`-standard plane
  (`thm:local-pressure-cubic`, `cor:fixed-radius-cubic-flow`,
   SM_emergence)

For the cubic truncation
`𝒫₃ = a₀ + a₂r² + A·r³·cos(3(θ-θ₀))`:

* `cubic_maxima` / `cubic_maximizer_characterization` — for
  `A, r > 0` the angular maxima are exactly `θ₀ + 2kπ/3`: a
  three-point orbit per period;
* `cubic_pressure_deriv` — `∂_θ𝒫₃ = -3Ar³ sin(3(θ-θ₀))`, so the
  fixed-radius ascent flow is `θ̇ = -3gAr³ sin(3(θ-θ₀))`;
* `cubic_flow_critical_characterization` — the critical points are
  `θ₀ + kπ/3`, six per period, spaced by `π/3`;
* `flow_linearization` / `cubic_maxima_stable` /
  `cubic_saddle_unstable` — the linearization is
  `-9gAr³cos(3(θ-θ₀))`: strictly negative (stable) exactly at the
  three maxima, strictly positive (unstable) at the three
  interlaced minima;
* `orbit_stabilizer_two` — a three-point orbit of a six-element
  group has stabilizers of order two: the local selection pattern
  is `S₃ → ℤ₂`.

The invariant-theoretic expansion of a general analytic
`S₃`-invariant pressure (generation of the local invariant ring by
`r²` and one cubic harmonic) is the declared input; the theorems
above cover the cubic term it produces.
-/

namespace NCG

open Real

/-- The cubic pressure truncation
`𝒫₃ = a₀ + a₂r² + A·r³·cos(3(θ-θ₀))`. -/
noncomputable def cubicPressure (a0 a2 A r th0 th : ℝ) : ℝ :=
  a0 + a2 * r ^ 2 + A * r ^ 3 * Real.cos (3 * (th - th0))

/-- The points `θ₀ + 2kπ/3` are global angular maxima of the cubic
pressure at fixed radius. -/
theorem cubic_maxima (a0 a2 A r th0 : ℝ) (hA : 0 < A) (hr : 0 < r)
    (k : ℤ) (th : ℝ) :
    cubicPressure a0 a2 A r th0 th
      ≤ cubicPressure a0 a2 A r th0 (th0 + 2 * k * π / 3) := by
  unfold cubicPressure
  have h1 : Real.cos (3 * (th - th0)) ≤ 1 := Real.cos_le_one _
  have h2 : Real.cos (3 * (th0 + 2 * k * π / 3 - th0)) = 1 := by
    rw [show 3 * (th0 + 2 * k * π / 3 - th0) = (k : ℝ) * (2 * π)
      from by ring]
    exact Real.cos_int_mul_two_pi k
  rw [h2]
  have hpos : (0 : ℝ) < A * r ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

/-- The angular maximizers are exactly the three-point orbit
`θ = θ₀ + 2kπ/3`. -/
theorem cubic_maximizer_characterization (th0 th : ℝ) :
    Real.cos (3 * (th - th0)) = 1
      ↔ ∃ k : ℤ, th = th0 + 2 * k * π / 3 := by
  rw [Real.cos_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- The angular derivative of the cubic pressure:
`∂_θ𝒫₃ = -3Ar³·sin(3(θ-θ₀))`. -/
theorem cubic_pressure_deriv (a0 a2 A r th0 th : ℝ) :
    HasDerivAt (fun th => cubicPressure a0 a2 A r th0 th)
      (-3 * (A * r ^ 3) * Real.sin (3 * (th - th0))) th := by
  have hu : HasDerivAt (fun th : ℝ => 3 * (th - th0)) 3 th := by
    exact (((hasDerivAt_id th).sub_const th0).const_mul 3).congr_deriv
      (by ring)
  have hcos := (Real.hasDerivAt_cos (3 * (th - th0))).comp th hu
  exact (((hasDerivAt_const th (a0 + a2 * r ^ 2)).add
    (hcos.const_mul (A * r ^ 3)))).congr_deriv (by ring)

/-- The fixed-radius flow `θ̇ = -3gAr³ sin(3(θ-θ₀))` has critical
points exactly at `θ = θ₀ + kπ/3`: six per period, spaced `π/3`. -/
theorem cubic_flow_critical_characterization (g A r th0 th : ℝ)
    (hg : g ≠ 0) (hA : A ≠ 0) (hr : r ≠ 0) :
    -3 * g * (A * r ^ 3) * Real.sin (3 * (th - th0)) = 0
      ↔ ∃ k : ℤ, th = th0 + k * π / 3 := by
  have hc : (-3 : ℝ) * g * (A * r ^ 3) ≠ 0 := by
    simp [hg, hA, hr]
  rw [mul_eq_zero]
  constructor
  · rintro (hzero | hsin)
    · exact absurd hzero hc
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
      exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩
    right
    apply Real.sin_eq_zero_iff.mpr
    exact ⟨k, by rw [hk]; ring⟩

/-- Linearization of the fixed-radius flow:
`F'(θ) = -9gAr³·cos(3(θ-θ₀))`. -/
theorem flow_linearization (g A r th0 th : ℝ) :
    HasDerivAt
      (fun th => -3 * g * (A * r ^ 3) * Real.sin (3 * (th - th0)))
      (-9 * g * (A * r ^ 3) * Real.cos (3 * (th - th0))) th := by
  have hu : HasDerivAt (fun th : ℝ => 3 * (th - th0)) 3 th := by
    exact (((hasDerivAt_id th).sub_const th0).const_mul 3).congr_deriv
      (by ring)
  have hsin := (Real.hasDerivAt_sin (3 * (th - th0))).comp th hu
  exact (hsin.const_mul (-3 * g * (A * r ^ 3))).congr_deriv (by ring)

/-- The three cubic maxima are linearly stable: the linearization
is strictly negative there. -/
theorem cubic_maxima_stable (g A r th0 : ℝ) (hg : 0 < g)
    (hA : 0 < A) (hr : 0 < r) (k : ℤ) :
    -9 * g * (A * r ^ 3)
        * Real.cos (3 * (th0 + 2 * k * π / 3 - th0)) < 0 := by
  rw [show 3 * (th0 + 2 * k * π / 3 - th0) = (k : ℝ) * (2 * π)
    from by ring, Real.cos_int_mul_two_pi]
  have : (0 : ℝ) < 9 * g * (A * r ^ 3) := by positivity
  linarith

/-- The three interlaced critical points (the cubic minima on the
circle) are linearly unstable: the linearization is strictly
positive there. -/
theorem cubic_saddle_unstable (g A r th0 : ℝ) (hg : 0 < g)
    (hA : 0 < A) (hr : 0 < r) (k : ℤ) :
    0 < -9 * g * (A * r ^ 3)
        * Real.cos (3 * (th0 + (2 * k + 1) * π / 3 - th0)) := by
  rw [show 3 * (th0 + (2 * k + 1) * π / 3 - th0)
      = (k : ℝ) * (2 * π) + π from by ring,
    Real.cos_int_mul_two_pi_add_pi]
  have : (0 : ℝ) < 9 * g * (A * r ^ 3) := by positivity
  linarith

/-- Orbit–stabilizer for the cubic selection pattern: a three-point
orbit of a six-element group has stabilizers of order two —
`S₃ → ℤ₂`. -/
theorem orbit_stabilizer_two {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] (v : X) [Fintype (MulAction.orbit G v)]
    [Fintype (MulAction.stabilizer G v)]
    (hG : Fintype.card G = 6)
    (horb : Fintype.card (MulAction.orbit G v) = 3) :
    Fintype.card (MulAction.stabilizer G v) = 2 := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G v
  rw [hG, horb] at h
  omega

end NCG
