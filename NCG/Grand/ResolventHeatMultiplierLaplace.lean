/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventEulerMultiplierContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace transform of the one-resolvent heat multiplier

The heat multiplier represented by one positive reference resolvent is
jointly continuous in positive time and the full reference spectral
interval.  Its Laplace transform is exactly the rational multiplier which
transports the reference resolvent to any other positive shift.
-/

open Filter Set Topology

noncomputable section

namespace NCG.ImplicitEuler

/-- Fixed-order resolvent Euler powers are jointly continuous in positive
time and the reference spectral parameter. -/
theorem continuousOn_uncurry_resolventEulerRoot_pow
    (b : ℝ) (k : ℕ) (hb : 0 < b) (hk : 0 < k) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ resolventEulerRoot b p.1 k p.2 ^ k)
      (Ioi 0 ×ˢ Icc 0 b⁻¹) := by
  intro p hp
  have ht : 0 < p.1 := hp.1
  have hr0 : 0 ≤ p.2 := hp.2.1
  have hrb : p.2 ≤ b⁻¹ := hp.2.2
  have hden : 1 + (((k : ℝ) / p.1) - b) * p.2 ≠ 0 := by
    by_cases hrZero : p.2 = 0
    · simp [hrZero]
    · have hrPos : 0 < p.2 := lt_of_le_of_ne hr0 (Ne.symm hrZero)
      have hbr : b * p.2 ≤ 1 := by
        calc
          b * p.2 ≤ b * b⁻¹ := mul_le_mul_of_nonneg_left hrb hb.le
          _ = 1 := mul_inv_cancel₀ hb.ne'
      have hrewrite :
          1 + (((k : ℝ) / p.1) - b) * p.2 =
            (1 - b * p.2) + ((k : ℝ) / p.1) * p.2 := by ring
      rw [hrewrite]
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (sub_nonneg.mpr hbr)
        (mul_pos (div_pos (by exact_mod_cast hk) ht) hrPos))
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.pow
  apply ContinuousAt.div
  · exact
      ((continuousAt_const.div continuousAt_fst (ne_of_gt ht)).mul
        continuousAt_snd)
  · exact continuousAt_const.add
      (((continuousAt_const.div continuousAt_fst (ne_of_gt ht)).sub
        continuousAt_const).mul continuousAt_snd)
  · exact hden

/-- The one-resolvent heat multiplier is jointly continuous in positive time
and the full closed reference spectral interval. -/
theorem continuousOn_uncurry_resolventHeatMultiplier
    (b : ℝ) (hb : 0 < b) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ resolventHeatMultiplier b p.1 p.2)
      (Ioi 0 ×ˢ Icc 0 b⁻¹) := by
  apply (show TendstoUniformlyOn
      (fun (m : ℕ) (p : ℝ × ℝ) ↦
        resolventEulerRoot b p.1 (m + 1) p.2 ^ (m + 1))
      (fun p ↦ resolventHeatMultiplier b p.1 p.2)
      atTop (Ioi 0 ×ˢ Icc 0 b⁻¹) by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    have herr : ∀ᶠ m : ℕ in atTop, errorRate m < epsilon :=
      errorRate_tendsto_zero.eventually (eventually_lt_nhds hepsilon)
    filter_upwards [herr] with m hm
    intro p hp
    rw [Real.dist_eq]
    have hbound :=
      abs_resolventEulerRoot_pow_sub_heat_le_inv_sqrt
        b p.1 p.2 (m + 1) hp.1 (Nat.succ_pos m)
        hp.2.1 hp.2.2
    have hrates :
        (Real.sqrt (((m + 1 : ℕ) : ℝ)))⁻¹ = errorRate m := by
      simp [errorRate, Nat.cast_add, Nat.cast_one]
    rw [hrates] at hbound
    simpa [abs_sub_comm] using hbound.trans_lt hm).continuousOn
  exact (Filter.Eventually.of_forall fun m ↦
    continuousOn_uncurry_resolventEulerRoot_pow
      b (m + 1) hb (Nat.succ_pos m)).frequently

/-- Scalar Laplace transform of the canonical heat multiplier. -/
theorem integral_exp_mul_resolventHeatMultiplier
    (b lam r : ℝ) (hlam : 0 < lam)
    (hr0 : 0 ≤ r) (hrb : r ≤ b⁻¹) :
    (∫ t : ℝ in Ioi 0,
        Real.exp (-lam * t) * resolventHeatMultiplier b t r) =
      r / (1 + (lam - b) * r) := by
  by_cases hrZero : r = 0
  · subst r
    simp [resolventHeatMultiplier]
  · have hrPos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrZero)
    have henergy : 0 ≤ r⁻¹ - b :=
      resolventEnergy_nonneg hrPos hrb
    let a : ℝ := -(lam + (r⁻¹ - b))
    have ha : a < 0 := by
      dsimp [a]
      linarith
    have hfun :
        (fun t : ℝ ↦
          Real.exp (-lam * t) * resolventHeatMultiplier b t r) =
        (fun t : ℝ ↦ Real.exp (a * t)) := by
      funext t
      simp only [resolventHeatMultiplier, hrZero, if_false]
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    rw [hfun, integral_exp_mul_Ioi ha 0]
    simp only [mul_zero, Real.exp_zero]
    dsimp [a]
    field_simp [hrZero]
    ring

end NCG.ImplicitEuler
