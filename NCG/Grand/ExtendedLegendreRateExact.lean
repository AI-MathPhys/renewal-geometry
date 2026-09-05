/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DifferentiableLegendreDualExact

/-!
# Extended-valued Legendre rates and compact sublevels

The large-deviation rate must retain infinite values. The supremum below is
taken in `EReal`, not the conditionally complete real line. Every everywhere
finite pressure has a lower semicontinuous convex Legendre rate with compact
finite sublevels. No convexity assumption on the pressure is needed for
these structural conclusions. At differentiable points of a convex pressure,
the rate agrees with the existing real-valued exposed-point calculation.
-/

namespace NCG.ExtendedLegendreRate

open Set

noncomputable section

/-- The full Legendre--Fenchel rate, retaining infinite costs. -/
def rate (psi : ℝ → ℝ) (a : ℝ) : EReal :=
  ⨆ q : ℝ, ((q * a - psi q : ℝ) : EReal)

/-- Every affine tilt is below the extended-valued rate. -/
theorem affine_le_rate (psi : ℝ → ℝ) (a q : ℝ) :
    ((q * a - psi q : ℝ) : EReal) ≤ rate psi a :=
  le_iSup (fun q : ℝ => ((q * a - psi q : ℝ) : EReal)) q

/-- A finite upper bound on the rate is precisely a uniform affine bound. -/
theorem rate_le_coe_iff (psi : ℝ → ℝ) (a r : ℝ) :
    rate psi a ≤ (r : EReal) ↔ ∀ q : ℝ, q * a - psi q ≤ r := by
  simp only [rate, iSup_le_iff, EReal.coe_le_coe_iff]

/-- Strict lower bounds produce a concrete exponential tilt, including
when the rate is infinite. -/
theorem coe_lt_rate_iff (psi : ℝ → ℝ) (a r : ℝ) :
    (r : EReal) < rate psi a ↔ ∃ q : ℝ, r < q * a - psi q := by
  simp only [rate, lt_iSup_iff, EReal.coe_lt_coe_iff]

/-- Infinite rate is exactly unboundedness of the affine tilt costs. -/
theorem rate_eq_top_iff (psi : ℝ → ℝ) (a : ℝ) :
    rate psi a = ⊤ ↔ ∀ r : ℝ, ∃ q : ℝ, r < q * a - psi q := by
  rw [EReal.eq_top_iff_forall_lt]
  simp only [coe_lt_rate_iff]

/-- The rate never takes the negative-infinity value. -/
theorem rate_ne_bot (psi : ℝ → ℝ) (a : ℝ) : rate psi a ≠ ⊥ := by
  have h := affine_le_rate psi a 0
  intro heq
  rw [heq] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

/-- A normalized pressure gives a nonnegative rate, including infinite costs. -/
theorem rate_nonneg (psi : ℝ → ℝ) (hzero : psi 0 = 0) (a : ℝ) :
    0 ≤ rate psi a := by
  simpa [hzero] using affine_le_rate psi a 0

/-- Supremizing continuous affine functions gives lower semicontinuity. -/
theorem lowerSemicontinuous_rate (psi : ℝ → ℝ) : LowerSemicontinuous (rate psi) := by
  apply lowerSemicontinuous_iSup
  intro q
  exact (continuous_coe_real_ereal.comp
    ((continuous_const.mul continuous_id).sub continuous_const)).lowerSemicontinuous

/-- Every finite sublevel is closed. -/
theorem isClosed_sublevel (psi : ℝ → ℝ) (r : ℝ) :
    IsClosed {a : ℝ | rate psi a ≤ (r : EReal)} :=
  (lowerSemicontinuous_rate psi).isClosed_preimage (r : EReal)

/-- The tilts at plus and minus one bound every finite sublevel. -/
theorem sublevel_subset_interval (psi : ℝ → ℝ) (r : ℝ) :
    {a : ℝ | rate psi a ≤ (r : EReal)} ⊆ Icc (-r - psi (-1)) (r + psi 1) := by
  intro a ha
  have hb := (rate_le_coe_iff psi a r).mp ha
  have hneg := hb (-1)
  have hpos := hb 1
  constructor <;> linarith

/-- The extended rate is good: every finite sublevel is compact. -/
theorem isCompact_sublevel (psi : ℝ → ℝ) (r : ℝ) :
    IsCompact {a : ℝ | rate psi a ≤ (r : EReal)} :=
  isCompact_Icc.of_isClosed_subset (isClosed_sublevel psi r)
    (sublevel_subset_interval psi r)

/-- Convexity in the epigraph formulation for an extended-valued rate. -/
theorem convex_epigraph (psi : ℝ → ℝ) :
    Convex ℝ {p : ℝ × ℝ | rate psi p.1 ≤ (p.2 : EReal)} := by
  intro x hx y hy a b ha hb hab
  apply (rate_le_coe_iff psi _ _).mpr
  intro q
  have hxq := (rate_le_coe_iff psi x.1 x.2).mp hx q
  have hyq := (rate_le_coe_iff psi y.1 y.2).mp hy q
  have hax := mul_le_mul_of_nonneg_left hxq ha
  have hby := mul_le_mul_of_nonneg_left hyq hb
  change q * (a * x.1 + b * y.1) - psi q ≤ a * x.2 + b * y.2
  nlinarith [congrArg (fun t : ℝ => t * psi q) hab]

/-- A differentiable tangent of a convex pressure attains the full extended supremum. -/
theorem rate_at_derivative {psi : ℝ → ℝ} {k a : ℝ}
    (hconv : ConvexOn ℝ univ psi) (hderiv : HasDerivAt psi a k) :
    rate psi a = ((k * a - psi k : ℝ) : EReal) := by
  apply le_antisymm
  · apply (rate_le_coe_iff psi a _).mpr
    intro q
    have ht := DifferentiableLegendreDual.convex_tangent_lower_bound hconv hderiv q
    linarith
  · exact affine_le_rate psi a k

/-- Compatibility with the real-valued API exactly where its supremum is
proved finite and attained. -/
theorem rate_eq_coe_realRate_at_derivative {psi : ℝ → ℝ} {k a : ℝ}
    (hconv : ConvexOn ℝ univ psi) (hderiv : HasDerivAt psi a k) :
    rate psi a = (NCG.rateFunction psi a : EReal) := by
  rw [rate_at_derivative hconv hderiv,
    DifferentiableLegendreDual.rateFunction_at_derivative hconv hderiv]

/-- A deterministic current has zero rate at its sole possible value. -/
theorem rate_linear_at_mean (c : ℝ) : rate (fun q => q * c) c = 0 := by
  simp [rate]

/-- A deterministic current has infinite rate at every impossible value.
This checks that unbounded affine suprema are not collapsed to a real default. -/
theorem rate_linear_eq_top_of_ne (c a : ℝ) (h : a ≠ c) :
    rate (fun q => q * c) a = ⊤ := by
  apply (rate_eq_top_iff _ a).mpr
  intro r
  refine ⟨(r + 1) / (a - c), ?_⟩
  have hid : (r + 1) / (a - c) * a - (r + 1) / (a - c) * c = r + 1 := by
    field_simp [sub_ne_zero.mpr h]
  rw [hid]
  linarith

end

end NCG.ExtendedLegendreRate
