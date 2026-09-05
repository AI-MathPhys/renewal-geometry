/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalNoiseWardRemainder

/-!
# Little-o completion of the renewal noise-shorted Ward identity

The exact finite decomposition and norm estimate were already available.  This
file converts them into the literal filter limits used in
`thm:renewal-noise-shorted-Ward`: a predictable residual `o(τ)` has Gram
`o(τ²)`, while adding a noise remainder `o(τ)` gives a raw Ward remainder
`o(τ)`.
-/

open Filter Matrix
open scoped Topology Norms.L2Operator

namespace NCG
namespace RenewalNoiseWardLittleO

/-- Norm-ratio formulation of `f = o(scale)` along a filter. -/
def NormLittleO {α E : Type*} [NormedAddCommGroup E]
    (l : Filter α) (f : α → E) (scale : α → ℝ) : Prop :=
  Tendsto (fun i => ‖f i‖ / |scale i|) l (nhds 0)

/-- Exact filter-limit completion of both little-o conclusions in the
noise-shorted Ward theorem. -/
theorem renewal_noise_shorted_ward_littleO
    {α e : Type*} [Fintype e] [DecidableEq e]
    (l : Filter α)
    (raw Gn E X : α → Matrix e e ℂ) (τ : α → ℝ)
    (hτ : Tendsto τ l (nhds 0))
    (hτne : ∀ᶠ i in l, τ i ≠ 0)
    (hX : NormLittleO l X τ)
    (hE : NormLittleO l E τ)
    (hsplit : ∀ i,
      raw i = (τ i : ℂ) • Gn i + ((X i)ᴴ * X i + E i)) :
    NormLittleO l (fun i => raw i - (τ i : ℂ) • Gn i) τ ∧
      Tendsto (fun i => ‖(X i)ᴴ * X i‖ / |τ i| ^ 2) l (nhds 0) := by
  have hτabs : Tendsto (fun i => |τ i|) l (nhds 0) := by
    simpa only [abs_zero] using hτ.abs
  have hXsq : Tendsto (fun i => (‖X i‖ / |τ i|) ^ 2) l (nhds 0) := by
    simpa using hX.pow 2
  have hupper : Tendsto
      (fun i => (‖X i‖ / |τ i|) ^ 2 * |τ i| + ‖E i‖ / |τ i|)
      l (nhds 0) := by
    simpa using (hXsq.mul hτabs).add hE
  constructor
  · unfold NormLittleO
    apply squeeze_zero'
    · exact Eventually.of_forall fun i => div_nonneg (norm_nonneg _) (abs_nonneg _)
    · filter_upwards [hτne] with i hi
      have habs : 0 < |τ i| := abs_pos.mpr hi
      have hb := (renewal_noise_shorted_ward_remainder
        (raw i) (Gn i) (E i) (X i) (τ i) (hsplit i)).1
      calc
        ‖raw i - (τ i : ℂ) • Gn i‖ / |τ i|
            ≤ (‖X i‖ ^ 2 + ‖E i‖) / |τ i| :=
              div_le_div_of_nonneg_right hb habs.le
        _ = (‖X i‖ / |τ i|) ^ 2 * |τ i| + ‖E i‖ / |τ i| := by
              field_simp [hi]
    · exact hupper
  · apply hXsq.congr'
    filter_upwards [hτne] with i hi
    have hgram := (renewal_noise_shorted_ward_remainder
      ((X i)ᴴ * X i) 0 0 (X i) (τ i) (by simp)).2
    rw [hgram]
    field_simp [hi]

end RenewalNoiseWardLittleO
end NCG
