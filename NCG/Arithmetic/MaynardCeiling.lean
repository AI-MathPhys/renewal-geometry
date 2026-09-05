/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Maynard coordinate ceiling
  (`prop:v003-maynard-ceiling`, arithmetic monograph)

* `sq_integral_le` — Cauchy–Schwarz on a probability coordinate:
  `(∫ f dν)² ≤ ∫ f² dν`;
* `maynard_coordinate_CS` — the coordinate inequality
  `J_k^{(i)}(F) ≤ I_k(F)`: Cauchy–Schwarz in the `i`-th coordinate
  followed by integration over the remaining variables, stated for
  the product splitting `(remaining coordinates) × (i-th coordinate)`
  with the `i`-th coordinate carrying a probability measure;
* `maynard_ceiling` — the ceiling: substituting `J ≤ I` into the
  standard first-moment asymptotic
  `π_i = (log R / log N)·J/I + o(1)`, `R = N^{θ/2−δ}`, forces the
  marginals to converge to a limit `≤ θ/2 − δ < 1/2`, hence they are
  compatible with the twin-free model of `thm:v003-twinfree-marginals`
  (`NCG.twinfree_marginals`).
-/

open MeasureTheory Filter

namespace NCG

/-- Cauchy–Schwarz for a probability measure:
`(∫ f dν)² ≤ ∫ f² dν`. -/
theorem sq_integral_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (f : X → ℝ)
    (hf : Integrable f ν) (hf2 : Integrable (fun x => f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  set m : ℝ := ∫ x, f x ∂ν with hm
  have h1 : ∀ x, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 :=
    fun x => by ring
  have h0 : 0 ≤ ∫ x, (f x - m) ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have hint2 : Integrable (fun x => 2 * m * f x) ν :=
    hf.const_mul (2 * m)
  have hint1 : Integrable (fun x => f x ^ 2 - 2 * m * f x) ν :=
    hf2.sub hint2
  have hexpand : ∫ x, (f x - m) ^ 2 ∂ν
      = (∫ x, f x ^ 2 ∂ν) - m ^ 2 := by
    have e1 : (fun x => (f x - m) ^ 2)
        = fun x => (f x ^ 2 - 2 * m * f x) + m ^ 2 :=
      funext fun x => by ring
    rw [e1, integral_add hint1 (integrable_const _),
      integral_sub hf2 hint2, MeasureTheory.integral_const_mul,
      integral_const, ← hm]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul]
    ring
  linarith

/-- `prop:v003-maynard-ceiling` (coordinate Cauchy–Schwarz):
`J_k^{(i)}(F) ≤ I_k(F)`.  The `i`-th coordinate (probability
measure `ν`) is split off from the remaining coordinates
(σ-finite measure `ρ`). -/
theorem maynard_coordinate_CS {Y X : Type*} [MeasurableSpace Y]
    [MeasurableSpace X] (ρ : Measure Y) [SFinite ρ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (F : Y × X → ℝ)
    (hF1 : Integrable F (ρ.prod ν))
    (hF2 : Integrable (fun p => F p ^ 2) (ρ.prod ν)) :
    (∫ y, (∫ x, F (y, x) ∂ν) ^ 2 ∂ρ)
      ≤ ∫ p, F p ^ 2 ∂(ρ.prod ν) := by
  rw [MeasureTheory.integral_prod _ hF2]
  have hae : ∀ᵐ y ∂ρ, Integrable (fun x => F (y, x)) ν :=
    hF1.prod_right_ae
  have hae2 : ∀ᵐ y ∂ρ, Integrable (fun x => F (y, x) ^ 2) ν :=
    hF2.prod_right_ae
  have hbound : ∀ᵐ y ∂ρ,
      (∫ x, F (y, x) ∂ν) ^ 2 ≤ ∫ x, F (y, x) ^ 2 ∂ν := by
    filter_upwards [hae, hae2] with y h1 h2
    exact sq_integral_le ν _ h1 h2
  have hG : Integrable (fun y => ∫ x, F (y, x) ^ 2 ∂ν) ρ :=
    hF2.integral_prod_left
  have hH : Integrable (fun y => (∫ x, F (y, x) ∂ν) ^ 2) ρ := by
    refine Integrable.mono' hG ?_ ?_
    · have hm := hF1.integral_prod_left.aestronglyMeasurable
      simp_rw [sq]
      exact hm.mul hm
    · filter_upwards [hbound] with y hy
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hy
  exact integral_mono_ae hH hG hbound

/-- `prop:v003-maynard-ceiling` (the ceiling): substituting
`J ≤ I` into the first-moment asymptotic
`π_i(n) = r(n)·(J/I) + e(n)` with `r(n) → θ/2 − δ` and `e(n) → 0`
forces the marginals to converge to a limit at most `θ/2 − δ`,
which is `< 1/2` for `δ > 0` and `θ ≤ 1` — within the twin-free
regime of `NCG.twinfree_marginals`. -/
theorem maynard_ceiling {J I θ δ : ℝ} (hJI : J ≤ I) (hI : 0 < I)
    (_hJ0 : 0 ≤ J) (hθδ : 0 ≤ θ / 2 - δ) (hδ : 0 < δ) (hθ : θ ≤ 1)
    (π r e : ℕ → ℝ)
    (hπ : ∀ n, π n = r n * (J / I) + e n)
    (hr : Tendsto r atTop (nhds (θ / 2 - δ)))
    (he : Tendsto e atTop (nhds 0)) :
    ∃ L : ℝ, L ≤ θ / 2 - δ ∧ (θ / 2 - δ) < 1 / 2 ∧
      Tendsto π atTop (nhds L) := by
  refine ⟨(θ / 2 - δ) * (J / I), ?_, by linarith, ?_⟩
  · have hdiv : J / I ≤ 1 := (div_le_one hI).mpr hJI
    exact mul_le_of_le_one_right hθδ hdiv
  · have h1 : Tendsto (fun n => r n * (J / I) + e n) atTop
        (nhds ((θ / 2 - δ) * (J / I) + 0)) :=
      (hr.mul_const _).add he
    rw [add_zero] at h1
    exact h1.congr fun n => (hπ n).symm

end NCG
