/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DifferentiableLegendreDualExact

/-!
# Strict shifted-SCGF gaps from differentiability

At a differentiability point `k` with slope `a`, every positive deviation
window admits small right and left exponential tilts with strictly negative
shifted cumulant exponent.  These are the analytic estimates that make the
tilted law concentrate at `a` in the Gartner--Ellis lower-bound argument.
-/

open Filter Set
open scoped Topology

namespace NCG.DifferentiableSCGFTiltGap

/-- Small positive tilts penalize the upper deviation `a + delta`. -/
theorem eventually_right_tilt_gap
    {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      psi (k + q) - psi k - q * (a + delta) < 0 := by
  have hs := hderiv.tendsto_slope_zero_right
  have hnear : Iio (a + delta) ∈ 𝓝 a :=
    Iio_mem_nhds (lt_add_of_pos_right a hdelta)
  have hev := hs.eventually hnear
  filter_upwards [hev, self_mem_nhdsWithin] with q hquot hq
  have hqpos : 0 < q := hq
  change q⁻¹ * (psi (k + q) - psi k) < a + delta at hquot
  rw [inv_mul_eq_div] at hquot
  have hmul := (div_lt_iff₀ hqpos).mp hquot
  nlinarith

/-- Small negative tilts penalize the lower deviation `a - delta`. -/
theorem eventually_left_tilt_gap
    {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta) :
    ∀ᶠ q in 𝓝[<] (0 : ℝ),
      psi (k + q) - psi k - q * (a - delta) < 0 := by
  have hs := hderiv.tendsto_slope_zero_left
  have hnear : Ioi (a - delta) ∈ 𝓝 a :=
    Ioi_mem_nhds (sub_lt_self a hdelta)
  have hev := hs.eventually hnear
  filter_upwards [hev, self_mem_nhdsWithin] with q hquot hq
  have hqneg : q < 0 := hq
  change a - delta < q⁻¹ * (psi (k + q) - psi k) at hquot
  rw [inv_mul_eq_div] at hquot
  have hmul := (lt_div_iff_of_neg hqneg).mp hquot
  nlinarith

/-- Existence of an explicit positive upper-tail tilt. -/
theorem exists_positive_right_tilt_gap
    {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta) :
    ∃ q : ℝ, 0 < q ∧
      psi (k + q) - psi k - q * (a + delta) < 0 := by
  have hev := eventually_right_tilt_gap hderiv hdelta
  have hall : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q ∧
      psi (k + q) - psi k - q * (a + delta) < 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with q hgap hq
    exact ⟨hq, hgap⟩
  exact hall.exists

/-- Existence of an explicit negative lower-tail tilt. -/
theorem exists_negative_left_tilt_gap
    {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta) :
    ∃ q : ℝ, q < 0 ∧
      psi (k + q) - psi k - q * (a - delta) < 0 := by
  have hev := eventually_left_tilt_gap hderiv hdelta
  have hall : ∀ᶠ q in 𝓝[<] (0 : ℝ), q < 0 ∧
      psi (k + q) - psi k - q * (a - delta) < 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with q hgap hq
    exact ⟨hq, hgap⟩
  exact hall.exists

end NCG.DifferentiableSCGFTiltGap
