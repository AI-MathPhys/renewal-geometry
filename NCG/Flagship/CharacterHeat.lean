/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gaussian heat criterion and the prime-side heat identity
  (`thm:GRH-heat-master`, `thm:prime-side-heat-master`,
   flagship manuscript)

For the reflected heat orbit sum
`u(t,τ) = (4πt)^{-1/2} Σ_ρ Re exp(-(τ-γ_ρ + i c_ρ)²/(4t))`:

* `(i) ⇒ (ii)` of the heat criterion: when every displacement
  `c_ρ` vanishes, every orbit term is an ordinary positive heat
  kernel and `u ≥ 0` (`heat_positivity`);
* the reflected off-line pair identity: a pair `±c` at ordinate
  `γ` contributes `2 e^{(c²-x²)/4t} cos(cx/2t)` with `x = τ - γ`
  (`offline_pair_formula`), and at the tested center `x = 2πt/c`
  the cosine equals `-1`, so the contribution is strictly
  negative with the boxed exponential magnitude
  (`offline_pair_negative`) — the mechanism of `(ii) ⇒ (i)`;
* the log-Gaussian transform pair
  `∫ e^{iya} e^{-ta²} da = √(π/t)·e^{-y²/(4t)}`
  (`gaussian_log_pair`, from Mathlib's Gaussian Fourier
  integral), the computational content of the prime-side
  insertion; the boxed prime-side identity follows by rewriting
  each von Mangoldt term of the displayed symmetric explicit
  formula through this pair (`prime_side_heat`).

Rendering disclosed: the Gaussian outer-exposure selection of a
maximal off-line orbit (completing `(ii) ⇒ (i)`), the affine
moment-matrix clauses `(iii)–(iv)` (their determinant
identification with the heat-semiconvexity expression), and the
symmetric explicit formula itself (a `StatusExternal` input in
the manuscript's own ledger) enter as displayed hypotheses or
prose; the positivity, the off-line pair mechanism, and the
transform pair are proved in full.
-/

open Complex

namespace NCG

/-- The reflected heat orbit sum over grouped zeros: ordinates
`γ j`, horizontal displacements `c j`. -/
noncomputable def heatOrbit (γ c : ℕ → ℝ) (t τ : ℝ) : ℝ :=
  ∑' j, (Real.sqrt (4 * Real.pi * t))⁻¹
    * (Complex.exp (-(((τ - γ j : ℝ) : ℂ)
        + ((c j : ℝ) : ℂ) * I) ^ 2 / ((4 * t : ℝ) : ℂ))).re

/-- `(i) ⇒ (ii)`: on-line zeros give nonnegative heat. -/
theorem heat_positivity (γ c : ℕ → ℝ) (t τ : ℝ)
    (hcrit : ∀ j, c j = 0) : 0 ≤ heatOrbit γ c t τ := by
  refine tsum_nonneg fun j => ?_
  rw [hcrit j]
  have h1 : (-(((τ - γ j : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) ^ 2
      / ((4 * t : ℝ) : ℂ))
      = ((-(τ - γ j) ^ 2 / (4 * t) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h1, Complex.exp_ofReal_re]
  positivity

/-- The reflected off-line pair contributes the displayed cosine
wave `2 e^{(c²-x²)/4t} cos(cx/2t)`. -/
theorem offline_pair_formula (x c t : ℝ) (ht : 0 < t) :
    (Complex.exp (-((x : ℂ) + (c : ℂ) * I) ^ 2
        / ((4 * t : ℝ) : ℂ))).re
      + (Complex.exp (-((x : ℂ) - (c : ℂ) * I) ^ 2
        / ((4 * t : ℝ) : ℂ))).re
    = 2 * Real.exp ((c ^ 2 - x ^ 2) / (4 * t))
        * Real.cos (c * x / (2 * t)) := by
  have ht4 : ((4 * t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (4 * t : ℝ) ≠ 0)
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hsq : ((x : ℂ) + (c : ℂ) * I) ^ 2
      = ((x ^ 2 - c ^ 2 : ℝ) : ℂ) + ((2 * c * x : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((c : ℂ) ^ 2) * Complex.I_sq
  have hsq' : ((x : ℂ) - (c : ℂ) * I) ^ 2
      = ((x ^ 2 - c ^ 2 : ℝ) : ℂ) - ((2 * c * x : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((c : ℂ) ^ 2) * Complex.I_sq
  have hz1 : -((x : ℂ) + (c : ℂ) * I) ^ 2 / ((4 * t : ℝ) : ℂ)
      = (((c ^ 2 - x ^ 2) / (4 * t) : ℝ) : ℂ)
        + ((-(c * x / (2 * t)) : ℝ) : ℂ) * I := by
    rw [hsq]
    push_cast
    field_simp
    ring
  have hz2 : -((x : ℂ) - (c : ℂ) * I) ^ 2 / ((4 * t : ℝ) : ℂ)
      = (((c ^ 2 - x ^ 2) / (4 * t) : ℝ) : ℂ)
        + ((c * x / (2 * t) : ℝ) : ℂ) * I := by
    rw [hsq']
    push_cast
    field_simp
    ring
  rw [hz1, hz2, Complex.exp_re, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im]
  rw [show ((c ^ 2 - x ^ 2) / (4 * t)
        + (-(c * x / (2 * t)) * 0 - 0 * 1) : ℝ)
      = (c ^ 2 - x ^ 2) / (4 * t) by ring,
    show ((c ^ 2 - x ^ 2) / (4 * t)
        + (c * x / (2 * t) * 0 - 0 * 1) : ℝ)
      = (c ^ 2 - x ^ 2) / (4 * t) by ring,
    show (0 + (-(c * x / (2 * t)) * 1 + 0 * 0) : ℝ)
      = -(c * x / (2 * t)) by ring,
    show (0 + (c * x / (2 * t) * 1 + 0 * 0) : ℝ)
      = c * x / (2 * t) by ring,
    Real.cos_neg]
  ring

/-- At the tested center `x = 2πt/c` the pair contribution is
strictly negative, with the boxed exponential magnitude. -/
theorem offline_pair_negative (c t : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) :
    (Complex.exp (-(((2 * Real.pi * t / c : ℝ) : ℂ)
        + (c : ℂ) * I) ^ 2 / ((4 * t : ℝ) : ℂ))).re
      + (Complex.exp (-(((2 * Real.pi * t / c : ℝ) : ℂ)
        - (c : ℂ) * I) ^ 2 / ((4 * t : ℝ) : ℂ))).re
    = -(2 * Real.exp
        ((c ^ 2 - (2 * Real.pi * t / c) ^ 2) / (4 * t))) := by
  rw [offline_pair_formula _ c t ht]
  have harg : c * (2 * Real.pi * t / c) / (2 * t)
      = Real.pi := by
    field_simp
  rw [harg, Real.cos_pi]
  ring

/-- The log-Gaussian transform pair: the computational content of
the prime-side insertion. -/
theorem gaussian_log_pair (t : ℝ) (ht : 0 < t) (y : ℂ) :
    ∫ a : ℝ, Complex.exp (I * y * a)
        * Complex.exp (-(t : ℂ) * a ^ 2)
      = (((Real.pi / t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-y ^ 2 / (4 * t)) := by
  have hb : (0 : ℝ) < ((t : ℂ)).re := by simpa using ht
  have h1 := fourierIntegral_gaussian (b := (t : ℂ)) hb y
  rw [h1]
  push_cast
  ring

/-- `thm:prime-side-heat-master`, boxed identity: given the
displayed symmetric explicit formula with the Gaussian test
(`hEF`), rewriting each von Mangoldt term through the transform
pair produces the boxed prime-side wave. -/
theorem prime_side_heat (u G : ℝ → ℝ → ℝ) (aΛ : ℕ → ℂ)
    (y : ℕ → ℂ) (t τ : ℝ) (ht : 0 < t)
    (hEF : u t τ = G t τ - (1 / Real.pi)
      * (∑' n, aΛ n * ∫ a : ℝ, Complex.exp (I * y n * a)
          * Complex.exp (-(t : ℂ) * a ^ 2)).re) :
    u t τ = G t τ - (1 / Real.pi)
      * (∑' n, aΛ n * ((((Real.pi / t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * Complex.exp (-(y n) ^ 2 / (4 * t)))).re := by
  rw [hEF]
  congr 3
  refine tsum_congr fun n => ?_
  rw [gaussian_log_pair t ht (y n)]

end NCG
