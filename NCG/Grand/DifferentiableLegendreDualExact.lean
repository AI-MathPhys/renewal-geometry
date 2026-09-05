/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.RateFunction

/-!
# Exact Legendre duality at differentiable exposed points

For a convex differentiable pressure `psi`, the tangent slope
`a = psi'(k)` is an exposed current and the Legendre--Fenchel transform is
attained exactly at `k`:

`I(a) = k*a - psi(k)`.

This is the convex-duality identification required in the lower-bound half
of the finite-state Gartner--Ellis argument.
-/

noncomputable section

namespace NCG.DifferentiableLegendreDual

/-- A convex real function lies above every differentiable tangent line. -/
theorem convex_tangent_lower_bound
    {psi : ℝ → ℝ} {k a : ℝ}
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) :
    ∀ q : ℝ, psi k + a * (q - k) ≤ psi q := by
  intro q
  rcases lt_trichotomy q k with hq | hq | hq
  · have hs := hconv.slope_le_of_hasDerivAt
      (Set.mem_univ q) (Set.mem_univ k) hq hderiv
    rw [slope_def_field] at hs
    have hpos : 0 < k - q := sub_pos.mpr hq
    have hmul := (div_le_iff₀ hpos).mp hs
    nlinarith
  · subst q
    simp
  · have hs := hconv.le_slope_of_hasDerivAt
      (Set.mem_univ k) (Set.mem_univ q) hq hderiv
    rw [slope_def_field] at hs
    have hpos : 0 < q - k := sub_pos.mpr hq
    have hmul := (le_div_iff₀ hpos).mp hs
    nlinarith

/-- At a differentiable exposed slope, the Legendre--Fenchel supremum is
attained by the exposing parameter. -/
theorem rateFunction_at_derivative
    {psi : ℝ → ℝ} {k a : ℝ}
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) :
    NCG.rateFunction psi a = k * a - psi k := by
  have hgreat : IsGreatest
      (Set.range fun q : ℝ => q * a - psi q) (k * a - psi k) := by
    constructor
    · exact ⟨k, rfl⟩
    · rintro y ⟨q, rfl⟩
      have htangent := convex_tangent_lower_bound hconv hderiv q
      linarith
  rw [NCG.rateFunction, iSup]
  exact hgreat.csSup_eq

/-- The exposed-point rate is finite, with an explicit maximizer and value. -/
theorem rateFunction_exposed_certificate
    {psi : ℝ → ℝ} {k a : ℝ}
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) :
    (∀ q, q * a - psi q ≤ k * a - psi k) ∧
      NCG.rateFunction psi a = k * a - psi k := by
  refine ⟨?_, rateFunction_at_derivative hconv hderiv⟩
  intro q
  have htangent := convex_tangent_lower_bound hconv hderiv q
  linarith

end NCG.DifferentiableLegendreDual
