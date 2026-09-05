/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventEulerScalarTransform
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform convergence and continuity of one-resolvent Euler multipliers

The transformed Euler powers are continuous on the full positive reference-resolvent interval.
Their dimension-free error bound gives uniform convergence to the heat multiplier, including at
the singular spectral endpoint zero.  The heat multiplier is consequently continuous on the
whole interval and is ready for bounded continuous functional calculus.
-/

open Filter Topology

noncomputable section

namespace NCG.ImplicitEuler

/-- Every transformed Euler root is continuous on the full positive reference-resolvent
interval.  Positivity of the shift keeps its rational denominator away from zero. -/
theorem continuousOn_resolventEulerRoot
    (b t : ℝ) (k : ℕ) (hb : 0 < b) (ht : 0 < t) (hk : 0 < k) :
    ContinuousOn (resolventEulerRoot b t k) (Set.Icc 0 b⁻¹) := by
  intro r hr
  have hden : 1 + (((k : ℝ) / t) - b) * r ≠ 0 := by
    by_cases hr0 : r = 0
    · subst r
      norm_num
    · have hrPos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
      have hbr : b * r ≤ 1 := by
        calc
          b * r ≤ b * b⁻¹ := mul_le_mul_of_nonneg_left hr.2 hb.le
          _ = 1 := mul_inv_cancel₀ hb.ne'
      have hrewrite :
          1 + (((k : ℝ) / t) - b) * r =
            (1 - b * r) + ((k : ℝ) / t) * r := by ring
      rw [hrewrite]
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (sub_nonneg.mpr hbr) (mul_pos (div_pos (by exact_mod_cast hk) ht) hrPos))
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact hden

/-- Every fixed transformed Euler power is continuous on the positive reference-resolvent
interval. -/
theorem continuousOn_resolventEulerRoot_pow
    (b t : ℝ) (k : ℕ) (hb : 0 < b) (ht : 0 < t) (hk : 0 < k) :
    ContinuousOn (fun r ↦ resolventEulerRoot b t k r ^ k)
      (Set.Icc 0 b⁻¹) := by
  exact (continuousOn_resolventEulerRoot b t k hb ht hk).pow k

/-- The transformed Euler powers converge uniformly on the full reference-resolvent interval to
the heat multiplier. -/
theorem tendstoUniformlyOn_resolventEulerRoot_pow
    (b t : ℝ) (ht : 0 < t) :
    TendstoUniformlyOn
      (fun m r ↦ resolventEulerRoot b t (m + 1) r ^ (m + 1))
      (resolventHeatMultiplier b t) atTop (Set.Icc 0 b⁻¹) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have herr : ∀ᶠ m : ℕ in atTop, errorRate m < epsilon :=
    errorRate_tendsto_zero.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [herr] with m hm
  intro r hr
  rw [Real.dist_eq]
  have hbound := abs_resolventEulerRoot_pow_sub_heat_le_inv_sqrt
    b t r (m + 1) ht (Nat.succ_pos m) hr.1 hr.2
  have hrates :
      (Real.sqrt (((m + 1 : ℕ) : ℝ)))⁻¹ = errorRate m := by
    simp [errorRate, Nat.cast_add, Nat.cast_one]
  rw [hrates] at hbound
  simpa [abs_sub_comm] using hbound.trans_lt hm

/-- The one-resolvent heat multiplier is continuous on the full spectral interval, including the
endpoint zero. -/
theorem continuousOn_resolventHeatMultiplier
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    ContinuousOn (resolventHeatMultiplier b t) (Set.Icc 0 b⁻¹) := by
  apply (tendstoUniformlyOn_resolventEulerRoot_pow b t ht).continuousOn
  exact (Filter.Eventually.of_forall fun m ↦
    continuousOn_resolventEulerRoot_pow b t (m + 1) hb ht (Nat.succ_pos m)).frequently

end NCG.ImplicitEuler
