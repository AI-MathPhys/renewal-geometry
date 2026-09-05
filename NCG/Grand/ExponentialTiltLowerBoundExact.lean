/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SCGFExponentialTiltConcentrationExact

/-!
# Local large-deviation lower bounds by exponential tilting

This file isolates the final asymptotic change-of-measure step in the
Gartner--Ellis lower bound.  Once a tilted window mass tends to one and the
original mass dominates it by the exponential Radon--Nikodym factor, the
normalized log-moment limit supplies the sharp local exponential lower rate.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace NCG.ExponentialTiltLowerBound

open NCG.SCGFExponentialTiltConcentration

/-- Exponential tilting transfers concentration of the tilted window into a
local lower bound for the original window mass. -/
theorem eventually_originalMass_lower_bound
    (Z : ℕ → ℝ → ℝ) (P Q : ℕ → ℝ)
    (psi : ℝ → ℝ) (k cost epsilon : ℝ)
    (hZpos : ∀ n q, 0 < Z n q)
    (hZlim : Tendsto (fun n => normalizedLogMoment Z n k)
      atTop (𝓝 (psi k)))
    (hQlim : Tendsto Q atTop (𝓝 1))
    (hchange : ∀ n : ℕ,
      Real.exp (-(n : ℝ) * cost) * Z n k * Q n ≤ P n)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * (cost - psi k + epsilon)) ≤ P n := by
  have hepsHalf : 0 < epsilon / 2 := half_pos hepsilon
  have hlogNear : Ioi (psi k - epsilon / 2) ∈ 𝓝 (psi k) :=
    Ioi_mem_nhds (sub_lt_self _ hepsHalf)
  have hlog := hZlim.eventually hlogNear
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have hZlower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) * (psi k - epsilon / 2)) ≤ Z n k := by
    filter_upwards [hlog, hnpos] with n hnlog hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmul : (n : ℝ) * (psi k - epsilon / 2) <
        Real.log (Z n k) := by
      have := (lt_div_iff₀ hnreal).mp hnlog
      nlinarith
    have hexp := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log (hZpos n k)] at hexp
    exact le_of_lt hexp
  have hdecay : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * (-(epsilon / 2))))
      atTop (𝓝 0) := by
    have hlinear : Tendsto
        (fun n : ℕ => (n : ℝ) * (-(epsilon / 2))) atTop atBot :=
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (neg_neg_of_pos hepsHalf)
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hlinear
  have hQnear : Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) := by
    exact Ioi_mem_nhds (by norm_num)
  have hdecayNear : Iio (1 / 2 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact Iio_mem_nhds (by norm_num)
  have hQhalf := hQlim.eventually hQnear
  have hdecayHalf := hdecay.eventually hdecayNear
  have hQlower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) * (-(epsilon / 2))) ≤ Q n := by
    filter_upwards [hQhalf, hdecayHalf] with n hQn hdn
    exact le_of_lt (lt_trans hdn hQn)
  filter_upwards [hZlower, hQlower] with n hZn hQn
  have hec : 0 ≤ Real.exp (-(n : ℝ) * cost) := Real.exp_nonneg _
  have heq : 0 ≤ Real.exp ((n : ℝ) * (-(epsilon / 2))) := Real.exp_nonneg _
  calc
    Real.exp (-(n : ℝ) * (cost - psi k + epsilon)) =
        Real.exp (-(n : ℝ) * cost) *
          Real.exp ((n : ℝ) * (psi k - epsilon / 2)) *
          Real.exp ((n : ℝ) * (-(epsilon / 2))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(n : ℝ) * cost) * Z n k *
          Real.exp ((n : ℝ) * (-(epsilon / 2))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hZn hec) heq
    _ ≤ Real.exp (-(n : ℝ) * cost) * Z n k * Q n := by
      exact mul_le_mul_of_nonneg_left hQn
        (mul_nonneg hec (hZpos n k).le)
    _ ≤ P n := hchange n

end NCG.ExponentialTiltLowerBound
