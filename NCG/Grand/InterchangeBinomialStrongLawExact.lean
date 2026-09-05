/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.StrongLaw
import NCG.Grand.InterchangeActualAudit

/-!
# Almost-sure cubic-volume density for the renewal phase count

The stationary phase variables are i.i.d. Bernoulli variables of mean `6/11`.
Mathlib's Banach-valued strong law, restricted to the cofinal cubic sample
sizes `N³`, gives the almost-sure density limit used in item (A6) of the
actual cubic-regulator audit.
-/

open Filter MeasureTheory ProbabilityTheory

namespace NCG
namespace InterchangeAudit

/-- The strong law remains valid on cubic volumes.  In the renewal model,
`X i` is the indicator that the `i`th site is in the private phase, so the
left side is exactly `K_N/N³`. -/
theorem cubic_volume_phase_density_strong_law
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise (fun i j => X i ⟂ᵢ[μ] X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 6 / 11) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun N : ℕ =>
        ((N ^ 3 : ℕ) : ℝ)⁻¹ •
          ∑ i ∈ Finset.range (N ^ 3), X i ω)
        atTop (nhds (6 / 11 : ℝ)) := by
  have hstrong := strong_law_ae X hint hindep hident
  filter_upwards [hstrong] with ω hω
  have hcubic : Tendsto (fun N : ℕ => N ^ 3) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
  have heq :
      (fun N : ℕ => ((N ^ 3 : ℕ) : ℝ)⁻¹ •
          ∑ i ∈ Finset.range (N ^ 3), X i ω) =
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, X i ω) ∘ (fun N : ℕ => N ^ 3) := by
    funext N
    rfl
  rw [heq]
  simpa [hmean] using hω.comp hcubic

/-- Equivalent division notation for the stationary count density. -/
theorem cubic_volume_phase_density_div_strong_law
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise (fun i j => X i ⟂ᵢ[μ] X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 6 / 11) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range (N ^ 3), X i ω) / (N ^ 3 : ℝ))
        atTop (nhds (6 / 11 : ℝ)) := by
  simpa [div_eq_inv_mul, smul_eq_mul] using
    cubic_volume_phase_density_strong_law μ X hint hindep hident hmean

end InterchangeAudit
end NCG
