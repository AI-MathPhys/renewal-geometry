/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BkmResolventCurvatureLimitExact

/-!
# Scalar logarithm from the resolvent kernel

The matrix-log Hessian argument uses the standard normalized resolvent
primitive.  This file proves its finite-cutoff identity and convergence to
the ordinary logarithm from the already established BKM kernel integral.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace NCG
namespace QRE

/-- The normalized finite-cutoff resolvent approximation to `log a`. -/
noncomputable def truncatedLogKernel (a R : ℝ) : ℝ :=
  (a - 1) * ∫ s in (0 : ℝ)..R, ((1 + s) * (a + s))⁻¹

/-- Integrability of the normalized resolvent difference on a finite positive
cutoff interval. -/
theorem log_resolvent_diff_integrable {a R : ℝ} (ha : 0 < a)
    (hR : 0 ≤ R) :
    IntervalIntegrable (fun s : ℝ => (1 + s)⁻¹ - (a + s)⁻¹)
      volume 0 R := by
  have hint := (resolvent_prod_integrable one_pos ha hR).const_mul (a - 1)
  refine hint.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hR] at hs
  have h1 : 1 + s ≠ 0 := ne_of_gt (by linarith [hs.1])
  have h2 : a + s ≠ 0 := ne_of_gt (by linarith [hs.1])
  field_simp
  ring

/-- The normalized kernel is the integral of the difference between the
reference resolvent at `1` and the resolvent at `a`. -/
theorem truncatedLogKernel_eq_integral_sub {a R : ℝ} (ha : 0 < a)
    (hR : 0 ≤ R) :
    truncatedLogKernel a R =
      ∫ s in (0 : ℝ)..R, (1 + s)⁻¹ - (a + s)⁻¹ := by
  unfold truncatedLogKernel
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hR] at hs
  have h1 : 1 + s ≠ 0 := ne_of_gt (by linarith [hs.1])
  have h2 : a + s ≠ 0 := ne_of_gt (by linarith [hs.1])
  field_simp
  ring

/-- **Resolvent representation of the logarithm.**  The normalized
finite-cutoff kernel converges to `log a` for every `a > 0`. -/
theorem tendsto_truncatedLogKernel {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => truncatedLogKernel a R) atTop
      (𝓝 (Real.log a)) := by
  have hlim := (tendsto_integral_resolvent (a := 1) (b := a) one_pos ha).const_mul
    (a - 1)
  have hvalue : (a - 1) * bkmKernel 1 a = Real.log a := by
    by_cases h : (1 : ℝ) = a
    · subst a
      simp
    · rw [bkmKernel]
      simp only [if_neg h, Real.log_one, zero_sub]
      field_simp
      ring
  simpa only [truncatedLogKernel, hvalue] using hlim

end QRE
end NCG
