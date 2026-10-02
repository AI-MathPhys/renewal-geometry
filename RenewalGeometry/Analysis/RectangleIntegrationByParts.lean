/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Integration by parts on a time × periodic-space rectangle and cell Riemann sums
  (infrastructure for `eq:supp-gowdy-action-test`, `thm:main-gowdy-regulator` (G4);
  emergent-spacetime supplement)

General facts about iterated integrals `∫ t in α..β, ∫ θ in 0..L, F (t, θ)` over a rectangle in
`ℝ × ℝ`, used for the first-variation (action) tests of the Gowdy regulator.

* `RectangleIntegrationByParts.integral2_divergence_eq_zero`: **integration by parts** — for `C¹`
  fluxes `f, g : ℝ × ℝ → ℝ` such that `f` vanishes on the two time edges `t = α, β` and `g` takes
  equal values on the two space edges `θ = 0, L` (periodic boundary convention),
  `∫ t in α..β, ∫ θ in 0..L, (∂_t f + ∂_θ g) = 0` (from Mathlib's divergence theorem on a
  rectangle).
* `RectangleIntegrationByParts.abs_intervalIntegral_sub_const_le`: one-dimensional one-point
  quadrature, `|∫_a^b f - (b - a) c| ≤ η (b - a)` if `|f - c| ≤ η` on `[a, b]`.
* `RectangleIntegrationByParts.abs_sum_cells_sub_integral2_le`: **cell Riemann sums** — on the
  uniform cell grid `[a + n h, a + (n+1) h] × [jℓ, (j+1)ℓ]`, `n < n₀`, `j < N`, if the continuous
  integrand stays within `η` of the cell values `q n j`, then
  `|∑ₙ ∑ⱼ h ℓ q n j - ∫ t in a..a + n₀h, ∫ θ in 0..Nℓ, F| ≤ η (n₀ h) (N ℓ)`.
-/

open Set Finset MeasureTheory
open scoped BigOperators

namespace RenewalGeometry.RectangleIntegrationByParts

/-- **Integration by parts on a rectangle with periodic space edges.**  Let `f, g : ℝ × ℝ → ℝ`
be `C¹`, with `f (α, θ) = f (β, θ) = 0` for all `θ` (vanishing on the time
edges) and `g (t, L) = g (t, 0)` for all `t` (periodic space edges).  Then
`∫ t in α..β, ∫ θ in 0..L, (∂_t f + ∂_θ g)(t, θ) = 0`. -/
theorem integral2_divergence_eq_zero {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {α β L : ℝ}
    (hfα : ∀ θ, f (α, θ) = 0) (hfβ : ∀ θ, f (β, θ) = 0) (hgL : ∀ t, g (t, L) = g (t, 0)) :
    ∫ t in α..β, ∫ θ in (0 : ℝ)..L, (fderiv ℝ f (t, θ) (1, 0) + fderiv ℝ g (t, θ) (0, 1)) = 0 := by
  have hcf : Continuous fun x : ℝ × ℝ => fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hdiv := integral2_divergence_prod_of_hasFDerivAt f g (fderiv ℝ f) (fderiv ℝ g) α 0 β L
    hf.continuous.continuousOn hg.continuous.continuousOn
    (fun x _ => (hf.differentiable one_ne_zero x).hasFDerivAt)
    (fun x _ => (hg.differentiable one_ne_zero x).hasFDerivAt)
    (hcf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc))
  rw [hdiv]
  simp only [hgL, hfα, hfβ, sub_self, intervalIntegral.integral_zero, add_zero]

/-- One-point quadrature on an interval: if `f` is interval integrable on `[a, b]`, `a ≤ b`,
and `|f x - c| ≤ η` on `[a, b]`, then `|∫_a^b f - (b - a) c| ≤ η (b - a)`. -/
theorem abs_intervalIntegral_sub_const_le {f : ℝ → ℝ} {a b c η : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hη : ∀ x ∈ Icc a b, |f x - c| ≤ η) :
    |(∫ x in a..b, f x) - (b - a) * c| ≤ η * (b - a) := by
  have hc : (∫ _x in a..b, c) = (b - a) * c := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hc, ← intervalIntegral.integral_sub hf intervalIntegrable_const]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := η)
    (f := fun x => f x - c) (fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hη x ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
  exact this

/-- Splitting `∫_0^{Nℓ}` into the `N` cells `[jℓ, (j+1)ℓ]`. -/
theorem integral_eq_sum_cells {f : ℝ → ℝ} (hf : Continuous f) (ℓ : ℝ) (N : ℕ) :
    ∫ θ in (0 : ℝ)..N * ℓ, f θ = ∑ j ∈ range N, ∫ θ in (j * ℓ : ℝ)..(j * ℓ + ℓ), f θ := by
  have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun j : ℕ => (j : ℝ) * ℓ) (n := N) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, Nat.cast_succ, add_mul, one_mul] at this
  rw [← this]

/-- **Cell Riemann sums on a rectangle.**  Let `F : ℝ × ℝ → ℝ` be continuous, `h, ℓ > 0`, and
suppose that on every cell `[a + n h, a + n h + h] × [jℓ, jℓ + ℓ]` (`n < n₀`, `j < N`) the
integrand stays within `η` of the cell value `q n j`.  Then
`|∑_{n<n₀} ∑_{j<N} h ℓ q n j - ∫ t in a..a + n₀ h, ∫ θ in 0..Nℓ, F (t, θ)| ≤ η (n₀ h) (N ℓ)`. -/
theorem abs_sum_cells_sub_integral2_le {F : ℝ × ℝ → ℝ} (hF : Continuous F) {a h ℓ η : ℝ}
    (hh : 0 < h) (hℓ : 0 < ℓ) (n₀ N : ℕ) (q : ℕ → ℕ → ℝ)
    (hq : ∀ n < n₀, ∀ j < N, ∀ t ∈ Icc (a + n * h) (a + n * h + h),
      ∀ θ ∈ Icc (j * ℓ : ℝ) (j * ℓ + ℓ), |F (t, θ) - q n j| ≤ η) :
    |∑ n ∈ range n₀, ∑ j ∈ range N, h * ℓ * q n j -
        ∫ t in a..a + n₀ * h, ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ)| ≤ η * (n₀ * h) * (N * ℓ) := by
  -- continuity of the partial integrals
  have hcell : ∀ c d : ℝ, Continuous fun t => ∫ θ in c..d, F (t, θ) := fun c d =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t θ => F (t, θ)) (by exact hF) c d
  -- split the time integral
  have hsplit : ∫ t in a..a + n₀ * h, ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ) =
      ∑ n ∈ range n₀, ∫ t in (a + n * h)..(a + n * h + h), ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ) := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t => ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ)) (a := fun n : ℕ => a + n * h) (n := n₀)
      (fun k _ => (hcell _ _).intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ, add_mul, one_mul,
      ← add_assoc] at this
    rw [← this]
  rw [hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hcellbd : ∀ n ∈ range n₀, |∑ j ∈ range N, h * ℓ * q n j -
      ∫ t in (a + n * h)..(a + n * h + h), ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ)| ≤
        η * (N * ℓ) * h := by
    intro n hn
    have hn' := mem_range.1 hn
    have hin : ∀ t ∈ Icc (a + n * h) (a + n * h + h),
        |(∫ θ in (0 : ℝ)..N * ℓ, F (t, θ)) - ℓ * ∑ j ∈ range N, q n j| ≤ η * (N * ℓ) := by
      intro t ht
      rw [integral_eq_sum_cells (f := fun θ => F (t, θ)) (hF.comp (Continuous.prodMk_right t)) ℓ N,
        Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ range N, |(∫ θ in (j * ℓ : ℝ)..(j * ℓ + ℓ), F (t, θ)) - ℓ * q n j|
          ≤ ∑ _j ∈ range N, η * ℓ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have := abs_intervalIntegral_sub_const_le (f := fun θ => F (t, θ)) (c := q n j)
              (η := η) (a := j * ℓ) (b := j * ℓ + ℓ) (by linarith)
              ((hF.comp (Continuous.prodMk_right t)).intervalIntegrable _ _)
              (fun θ hθ => hq n hn' j (mem_range.1 hj) t ht θ hθ)
            simpa only [add_sub_cancel_left] using this
        _ = η * (N * ℓ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have := abs_intervalIntegral_sub_const_le (f := fun t => ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ))
      (c := ℓ * ∑ j ∈ range N, q n j) (by linarith) ((hcell _ _).intervalIntegrable _ _) hin
    rw [abs_sub_comm]
    have e : ∑ j ∈ range N, h * ℓ * q n j = (a + n * h + h - (a + n * h)) *
        (ℓ * ∑ j ∈ range N, q n j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simpa only [add_sub_cancel_left] using this
  calc ∑ n ∈ range n₀, |∑ j ∈ range N, h * ℓ * q n j -
        ∫ t in (a + n * h)..(a + n * h + h), ∫ θ in (0 : ℝ)..N * ℓ, F (t, θ)|
      ≤ ∑ _n ∈ range n₀, η * (N * ℓ) * h := Finset.sum_le_sum hcellbd
    _ = η * (n₀ * h) * (N * ℓ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end RenewalGeometry.RectangleIntegrationByParts
