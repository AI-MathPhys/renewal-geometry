/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Relative source-sector theorem
  (`thm:relative-source-sector-master`, flagship manuscript)

Primitive covariance reduces the clock–geometry discrepancy to
two sector amplitudes and two phases.  The Schur-lemma block
forms `A = a₀P₀ + a₅P₅` etc. are the multiplicity-free interface
(disclosed); on each loaded sector the data are the vectors
`u = S_clk|_α`, `v = S_geo|_α` with `a = ‖u‖²`, `b = ⟨u,v⟩`,
`d = ‖v‖²`, and we prove per sector:

* the boxed Cauchy–Schwarz bound `|b|² ≤ a·d`
  (`sector_cauchy_schwarz`);
* the boxed residual formula: the geometry-outside-clock
  residual `d - |b|²/a` is exactly the squared distance of `v`
  from the clock line (`sector_residual`), hence nonnegative
  (`sector_residual_nonneg`);
* the boxed equality case: a vanishing residual forces
  `v = (b/a)·u` (`sector_collinear`), i.e.
  `S_geo P_α = λ_α e^{iφ_α} S_clk P_α` with amplitude
  `λ_α = √(d/a)` and phase `e^{iφ_α} = b/|b|`
  (`sector_amplitude_phase`).

The two-sector assembly `𝔾 = Σ_α (d_α - |b_α|²/a_α)P_α` is the
formula just proved applied to `α ∈ {0, 5}` (disclosed).
-/

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Boxed sector Cauchy–Schwarz: `|b_α|² ≤ a_α d_α`. -/
theorem sector_cauchy_schwarz (u v : E) :
    ‖(inner ℂ u v : ℂ)‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u v
  have h2 : (0 : ℝ) ≤ ‖(inner ℂ u v : ℂ)‖ := norm_nonneg _
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Boxed residual formula: `d - |b|²/a` is the squared distance
of the geometry source from the clock line. -/
theorem sector_residual (u v : E) (hu : u ≠ 0) :
    ‖v - ((inner ℂ u v : ℂ) / ((‖u‖ : ℂ) ^ 2)) • u‖ ^ 2
      = ‖v‖ ^ 2 - ‖(inner ℂ u v : ℂ)‖ ^ 2 / ‖u‖ ^ 2 := by
  have ha : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have hac : ((‖u‖ : ℂ)) ^ 2 ≠ 0 := by
    exact_mod_cast pow_ne_zero 2
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))
  set b : ℂ := inner ℂ u v with hb
  have hvu : (inner ℂ v u : ℂ) = star b := by
    rw [hb, ← inner_conj_symm]
    rfl
  have hsub := norm_sub_sq (𝕜 := ℂ) v
    ((b / ((‖u‖ : ℂ) ^ 2)) • u)
  rw [inner_smul_right, hvu] at hsub
  have hre : RCLike.re (K := ℂ) (b / ((‖u‖ : ℂ) ^ 2) * star b)
      = ‖b‖ ^ 2 / ‖u‖ ^ 2 := by
    rw [show b / ((‖u‖ : ℂ) ^ 2) * star b
        = ((b * star b) : ℂ) / ((‖u‖ : ℂ) ^ 2) by ring,
      Complex.star_def, Complex.mul_conj,
      show ((Complex.normSq b : ℝ) : ℂ) / ((‖u‖ : ℂ) ^ 2)
        = ((Complex.normSq b / ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖(b / ((‖u‖ : ℂ) ^ 2)) • u‖ ^ 2
      = ‖b‖ ^ 2 / ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow, norm_div, div_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_norm]
    field_simp
  rw [hre, hnorm] at hsub
  rw [hsub]
  ring

/-- The residual is nonnegative. -/
theorem sector_residual_nonneg (u v : E) (hu : u ≠ 0) :
    0 ≤ ‖v‖ ^ 2 - ‖(inner ℂ u v : ℂ)‖ ^ 2 / ‖u‖ ^ 2 := by
  rw [← sector_residual u v hu]
  positivity

/-- Boxed equality case: a vanishing sector residual forces
collinearity `v = (b/a)·u`. -/
theorem sector_collinear (u v : E) (hu : u ≠ 0)
    (hflat : ‖v‖ ^ 2 = ‖(inner ℂ u v : ℂ)‖ ^ 2 / ‖u‖ ^ 2) :
    v = ((inner ℂ u v : ℂ) / ((‖u‖ : ℂ) ^ 2)) • u := by
  have h := sector_residual u v hu
  rw [← hflat, sub_self] at h
  have h0 : ‖v - ((inner ℂ u v : ℂ) / ((‖u‖ : ℂ) ^ 2)) • u‖
      = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [norm_eq_zero, sub_eq_zero] at h0
  exact h0

/-- Boxed amplitude/phase form of the equality case:
`S_geo P_α = λ_α e^{iφ_α} S_clk P_α` with `λ_α = √(d_α/a_α)` and
`e^{iφ_α} = b_α/|b_α|`. -/
theorem sector_amplitude_phase (u v : E) (hu : u ≠ 0)
    (hb : (inner ℂ u v : ℂ) ≠ 0)
    (hflat : ‖v‖ ^ 2 = ‖(inner ℂ u v : ℂ)‖ ^ 2 / ‖u‖ ^ 2) :
    v = (((Real.sqrt (‖v‖ ^ 2 / ‖u‖ ^ 2) : ℝ) : ℂ)
        * ((inner ℂ u v : ℂ) / ((‖(inner ℂ u v : ℂ)‖ : ℝ) : ℂ)))
        • u := by
  have hbn : (0 : ℝ) < ‖(inner ℂ u v : ℂ)‖ := by
    positivity
  have hsqrt : Real.sqrt (‖v‖ ^ 2 / ‖u‖ ^ 2)
      = ‖(inner ℂ u v : ℂ)‖ / ‖u‖ ^ 2 := by
    rw [hflat, show ‖(inner ℂ u v : ℂ)‖ ^ 2 / ‖u‖ ^ 2 / ‖u‖ ^ 2
        = (‖(inner ℂ u v : ℂ)‖ / ‖u‖ ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hbC : ((‖(inner ℂ u v : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbn.ne'
  have huC : ((‖u‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have hcoef : (((Real.sqrt (‖v‖ ^ 2 / ‖u‖ ^ 2) : ℝ) : ℂ)
      * ((inner ℂ u v : ℂ) / ((‖(inner ℂ u v : ℂ)‖ : ℝ) : ℂ)))
      = (inner ℂ u v : ℂ) / ((‖u‖ : ℂ) ^ 2) := by
    rw [hsqrt]
    push_cast
    field_simp
  rw [hcoef]
  exact sector_collinear u v hu hflat

end NCG
