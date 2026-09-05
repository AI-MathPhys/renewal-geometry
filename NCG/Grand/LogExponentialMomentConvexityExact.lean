/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Convexity of log exponential moments and their pointwise limits

Normalize the exponential integrands to have integral one, apply convexity
of the exponential pointwise, and integrate. This proves log-moment
convexity without assuming it or assuming a Holder inequality as an input.
The second theorem passes convexity to a pointwise filter limit.
-/

open MeasureTheory Filter Set Topology

namespace NCG.LogExponentialMomentConvexity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- All finite exponential moments of a nonzero measure have a convex logarithm. -/
theorem convexOn_log_integral_exp
    (mu : Measure Ω) [NeZero mu] (X : Ω → ℝ)
    (hint : ∀ q : ℝ, Integrable (fun w => Real.exp (q * X w)) mu) :
    ConvexOn ℝ univ (fun q => Real.log (∫ w, Real.exp (q * X w) ∂mu)) := by
  let Z : ℝ → ℝ := fun q => ∫ w, Real.exp (q * X w) ∂mu
  have hpos : ∀ q, 0 < Z q := fun q => integral_exp_pos (hint q)
  have hnorm : ∀ q, Integrable (fun w => Real.exp (q * X w - Real.log (Z q))) mu := by
    intro q
    simpa only [Real.exp_sub, Real.exp_log (hpos q)] using (hint q).div_const (Z q)
  have hnormIntegral : ∀ q,
      (∫ w, Real.exp (q * X w - Real.log (Z q)) ∂mu) = 1 := by
    intro q
    simp only [Real.exp_sub, Real.exp_log (hpos q), integral_div]
    exact div_self (hpos q).ne'
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let M : ℝ := a * Real.log (Z x) + b * Real.log (Z y)
  have hpoint : ∀ w,
      Real.exp ((a * x + b * y) * X w - M) ≤
        a * Real.exp (x * X w - Real.log (Z x)) +
          b * Real.exp (y * X w - Real.log (Z y)) := by
    intro w
    have hc := convexOn_exp.2
      (mem_univ (x * X w - Real.log (Z x)))
      (mem_univ (y * X w - Real.log (Z y))) ha hb hab
    simp only [smul_eq_mul] at hc
    have hid : (a * x + b * y) * X w - M =
        a * (x * X w - Real.log (Z x)) + b * (y * X w - Real.log (Z y)) := by
      dsimp only [M]
      ring
    rw [hid]
    exact hc
  have hleft : Integrable (fun w => Real.exp ((a * x + b * y) * X w - M)) mu := by
    simpa only [Real.exp_sub] using (hint (a * x + b * y)).div_const (Real.exp M)
  have hright := ((hnorm x).const_mul a).add ((hnorm y).const_mul b)
  have hbound := integral_mono hleft hright hpoint
  have hratio : Z (a * x + b * y) / Real.exp M ≤ 1 := by
    simp only [Pi.add_apply,
      integral_add ((hnorm x).const_mul a) ((hnorm y).const_mul b),
      integral_const_mul, hnormIntegral, mul_one, hab] at hbound
    simpa only [Real.exp_sub, integral_div] using hbound
  have hZle : Z (a * x + b * y) ≤ Real.exp M := by
    simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos M)).mp hratio
  have hlog := Real.log_le_log (hpos (a * x + b * y)) hZle
  rw [Real.log_exp] at hlog
  exact hlog

/-- Pointwise limits of eventually convex real functions are convex, for
any nontrivial filter; no uniform convergence is required. -/
theorem convexOn_of_pointwise_tendsto {ι : Type*} (l : Filter ι) [l.NeBot]
    (F : ι → ℝ → ℝ) (psi : ℝ → ℝ)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ univ (F i))
    (hlim : ∀ q, Tendsto (fun i => F i q) l (𝓝 (psi q))) :
    ConvexOn ℝ univ psi := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change psi (a * x + b * y) ≤ a * psi x + b * psi y
  apply le_of_tendsto_of_tendsto (hlim (a * x + b * y))
    (((hlim x).const_mul a).add ((hlim y).const_mul b))
  filter_upwards [hconv] with i hi
  exact hi.2 (mem_univ x) (mem_univ y) ha hb hab

end NCG.LogExponentialMomentConvexity
