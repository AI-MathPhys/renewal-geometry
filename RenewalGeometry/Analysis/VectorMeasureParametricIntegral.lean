/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Differentiation under the vector-measure integral sign

Mathlib's parametric-integral theorems (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) are
stated for Bochner integrals against positive measures.  This file provides the analogous
statement for Mathlib's vector-measure integrals `∫ᵛ a, Φ x a ∂[B; μ]` (`VectorMeasure.integral`),
for a real parameter `x` ranging over a convex set `s` and one-sided derivatives within `s`:

* `hasDerivWithinAt_integral_of_dominated`: if `x ↦ Φ x a` has derivative `Φ' x a` within `s`
  for `μ`-a.e. `a`, with `‖Φ' x a‖ ≤ bound a` uniformly on `s` and `bound` integrable against the
  variation of `μ`, then `x ↦ ∫ᵛ Φ x dμ` has derivative `∫ᵛ Φ' x₀ dμ` within `s` at `x₀ ∈ s`.

The proof writes the difference quotient of the integral as the integral of the difference
quotient, bounds the latter by `bound` through the mean value inequality on the convex set `s`,
and applies dominated convergence along `𝓝[s \ {x₀}] x₀`.

Used for the inverse-moment boundary jets of `thm:supp-dynamic-jets` in
`papers/predictive_spectral_geometry`.
-/

open MeasureTheory Filter Topology Set

namespace RenewalGeometry
namespace VectorMeasureCalculus

variable {X : Type*} [MeasurableSpace X] {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}

/-- **Differentiation under the vector-measure integral sign** on a convex set `s ⊆ ℝ`. -/
theorem hasDerivWithinAt_integral_of_dominated {s : Set ℝ} (hs : Convex ℝ s)
    {Φ Φ' : ℝ → X → E} {x₀ : ℝ} (hx₀ : x₀ ∈ s)
    (hΦ_meas : ∀ x ∈ s, AEStronglyMeasurable (Φ x) μ.variation)
    (hΦ_int : Integrable (Φ x₀) μ.variation)
    {bound : X → ℝ} (h_bound : ∀ᵐ a ∂μ.variation, ∀ x ∈ s, ‖Φ' x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_diff : ∀ᵐ a ∂μ.variation, ∀ x ∈ s, HasDerivWithinAt (fun x => Φ x a) (Φ' x a) s x) :
    HasDerivWithinAt (fun x => VectorMeasure.integral μ (Φ x) B)
      (VectorMeasure.integral μ (Φ' x₀) B) s x₀ := by
  -- mean value inequality on `s`
  have hmvt : ∀ᵐ a ∂μ.variation, ∀ x ∈ s, ‖Φ x a - Φ x₀ a‖ ≤ bound a * ‖x - x₀‖ := by
    filter_upwards [h_bound, h_diff] with a ha hd
    intro x hx
    exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun y hy => hd y hy)
      (fun y hy => ha y hy) hx₀ hx
  -- every `Φ x` is integrable
  have hint : ∀ x ∈ s, Integrable (Φ x) μ.variation := by
    intro x hx
    refine Integrable.mono' (hΦ_int.norm.add (bound_integrable.const_mul ‖x - x₀‖))
      (hΦ_meas x hx) ?_
    filter_upwards [hmvt] with a ha
    calc ‖Φ x a‖ ≤ ‖Φ x₀ a‖ + ‖Φ x a - Φ x₀ a‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖Φ x₀ a‖ + bound a * ‖x - x₀‖ := by gcongr; exact ha x hx
      _ = ‖Φ x₀ a‖ + ‖x - x₀‖ * bound a := by ring
  -- the slope of the integral is the integral of the slope
  have hslope : ∀ x ∈ s \ {x₀},
      slope (fun x => VectorMeasure.integral μ (Φ x) B) x₀ x =
        VectorMeasure.integral μ (fun a => slope (fun x => Φ x a) x₀ x) B := by
    intro x hx
    simp only [slope_def_module]
    rw [← VectorMeasure.integral_fun_sub (hint x hx.1) hΦ_int, ← VectorMeasure.integral_fun_smul]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdct : Tendsto (fun x => VectorMeasure.integral μ (fun a => slope (fun x => Φ x a) x₀ x) B)
      (𝓝[s \ {x₀}] x₀) (𝓝 (VectorMeasure.integral μ (Φ' x₀) B)) := by
    refine VectorMeasure.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_
      bound_integrable ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [slope_def_module]
      exact ((hΦ_meas x hx.1).sub (hΦ_meas x₀ hx₀)).const_smul _
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [hmvt] with a ha
      have hne : x - x₀ ≠ 0 := sub_ne_zero.mpr hx.2
      rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
      calc |x - x₀|⁻¹ * ‖Φ x a - Φ x₀ a‖ ≤ |x - x₀|⁻¹ * (bound a * ‖x - x₀‖) := by
            gcongr
            exact ha x hx.1
        _ = bound a := by
            rw [Real.norm_eq_abs]
            field_simp
    · filter_upwards [h_diff] with a hd
      have := hd x₀ hx₀
      rwa [hasDerivWithinAt_iff_tendsto_slope] at this
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hslope x hx).symm

end VectorMeasureCalculus
end RenewalGeometry
