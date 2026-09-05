/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Laplace-pole obstruction (`lem:laplace-pole`, arithmetic manuscript)

For `f(r) = R(r) + Σⱼ cⱼ e^{λⱼ r}` on `(0,∞)` with `Σ|cⱼ| < ∞`
and finite weighted energy `∫ e^{-2σr}|f|² < ∞`, the exponent under
test satisfies `Re λₖ ≤ σ`.

The proof is the manuscript's pole contradiction made quantitative
and elementary: test the Laplace transform at `z = λₖ + ε`.  The
energy hypothesis bounds `|L f(z)|` uniformly in `ε` (via the AM–GM
splitting `‖f‖e^{-(σ+a+ε)r} ≤ ½(e^{-2σr}‖f‖² + e^{-2(a+ε)r})`,
which replaces Cauchy–Schwarz), termwise integration is justified by
`Σⱼ ∫‖·‖ < ∞` (each exponent is dominated because `λₖ` has maximal
real part), each term integrates to `cⱼ/(z-λⱼ)`, the isolated
`k`-term contributes `|cₖ|/ε`, and the separated tail is bounded by
`(2/δ)Σ|cⱼ|`.  Taking `ε` small makes `|cₖ|/ε` exceed every bound —
contradiction.

Rendering disclosed: the tested exponent is taken isolated (`hsep`,
the manuscript's "equal exponents grouped" for a discrete zero set)
and of maximal real part (`hmax`, the manuscript's rightmost
displacement; the pole tested is the rightmost one), and the entire
Laplace transform of `R` enters through its local integrability and
boundedness near `λₖ` (`hR`).
-/

open MeasureTheory Set Filter Topology

namespace NCG

theorem laplace_pole_obstruction
    (f R : ℝ → ℂ) (c lam : ℕ → ℂ) (σ δ CR : ℝ) (k : ℕ)
    (hδ : 0 < δ) (hck : c k ≠ 0)
    (hcs : Summable fun j => ‖c j‖)
    (hmax : ∀ j, (lam j).re ≤ (lam k).re)
    (hsep : ∀ j, j ≠ k → δ ≤ ‖lam k - lam j‖)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hE : IntegrableOn
      (fun r => Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2) (Ioi 0))
    (hf : ∀ r : ℝ, 0 < r →
      f r = R r + ∑' j, c j * Complex.exp (lam j * r))
    (hR : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IntegrableOn (fun r => R r
        * Complex.exp (-(lam k + (ε : ℂ)) * r)) (Ioi 0)
      ∧ ‖∫ r in Ioi (0 : ℝ), R r
          * Complex.exp (-(lam k + (ε : ℂ)) * r)‖ ≤ CR) :
    (lam k).re ≤ σ := by
  by_contra hcon
  rw [not_le] at hcon
  set a : ℝ := (lam k).re - σ with ha_def
  have ha : 0 < a := sub_pos.mpr hcon
  set E : ℝ := ∫ r in Ioi (0 : ℝ),
    Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2 with hE_def
  have hE0 : 0 ≤ E := by
    rw [hE_def]
    exact setIntegral_nonneg measurableSet_Ioi
      fun r _ => by positivity
  set B1 : ℝ := E / 2 + 1 / (4 * a) with hB1_def
  have hB10 : 0 ≤ B1 := by rw [hB1_def]; positivity
  set B2 : ℝ := 2 / δ * ∑' j, ‖c j‖ with hB2_def
  set denom : ℝ := max 1 (B1 + CR + B2 + 1) with hdenom_def
  have hdenom : 0 < denom :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hck' : 0 < ‖c k‖ := norm_pos_iff.mpr hck
  set ε : ℝ := min (min 1 (δ / 2)) (‖c k‖ / (2 * denom))
    with hε_def
  have hε : 0 < ε := by
    rw [hε_def]
    exact lt_min (lt_min one_pos (by linarith)) (by positivity)
  have hε1 : ε ≤ 1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ : ε ≤ δ / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hεc : ε ≤ ‖c k‖ / (2 * denom) := min_le_right _ _
  -- the tested point and its real part
  have hzre : (lam k + (ε : ℂ)).re = σ + a + ε := by
    simp only [Complex.add_re, Complex.ofReal_re, ha_def]
    ring
  have hnormexp : ∀ (w : ℂ) (r : ℝ),
      ‖Complex.exp (w * r)‖ = Real.exp (w.re * r) := by
    intro w r
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  -- integrability and bound for the f-side Laplace integral
  have hexpint2 : IntegrableOn
      (fun r => Real.exp (-(2 * (a + ε)) * r)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hmaj : IntegrableOn (fun r : ℝ =>
      (Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2
        + Real.exp (-(2 * (a + ε)) * r)) / 2) (Ioi 0) :=
    (hE.add hexpint2).div_const 2
  have hptbound : ∀ r ∈ Ioi (0 : ℝ),
      ‖f r * Complex.exp (-(lam k + (ε : ℂ)) * r)‖
      ≤ (Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2
          + Real.exp (-(2 * (a + ε)) * r)) / 2 := by
    intro r _
    rw [norm_mul, hnormexp, Complex.neg_re, hzre]
    rw [show -(σ + a + ε) * r = -σ * r + -(a + ε) * r by ring,
      Real.exp_add]
    rw [show -(2 * σ) * r = -σ * r + -σ * r by ring,
      Real.exp_add]
    rw [show -(2 * (a + ε)) * r
        = -(a + ε) * r + -(a + ε) * r by ring, Real.exp_add]
    nlinarith [sq_nonneg (‖f r‖ * Real.exp (-σ * r)
        - Real.exp (-(a + ε) * r)),
      Real.exp_pos (-σ * r), Real.exp_pos (-(a + ε) * r),
      norm_nonneg (f r)]
  have hfint : IntegrableOn
      (fun r => f r * Complex.exp (-(lam k + (ε : ℂ)) * r))
      (Ioi 0) := by
    refine Integrable.mono' hmaj
      (hfm.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ hptbound)
  have hexpval : ∫ r in Ioi (0 : ℝ),
      Real.exp (-(2 * (a + ε)) * r) = 1 / (2 * (a + ε)) := by
    have h := integral_exp_mul_Ioi
      (a := -(2 * (a + ε))) (by linarith) 0
    rw [mul_zero, Real.exp_zero] at h
    rw [h, neg_div_neg_eq]
  have hLfbound : ‖∫ r in Ioi (0 : ℝ),
      f r * Complex.exp (-(lam k + (ε : ℂ)) * r)‖ ≤ B1 := by
    calc ‖∫ r in Ioi (0 : ℝ),
        f r * Complex.exp (-(lam k + (ε : ℂ)) * r)‖
        ≤ ∫ r in Ioi (0 : ℝ),
            ‖f r * Complex.exp (-(lam k + (ε : ℂ)) * r)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ r in Ioi (0 : ℝ),
            (Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2
              + Real.exp (-(2 * (a + ε)) * r)) / 2 :=
          setIntegral_mono_on hfint.norm hmaj
            measurableSet_Ioi hptbound
      _ = (E + 1 / (2 * (a + ε))) / 2 := by
          rw [integral_div, integral_add hE hexpint2,
            ← hE_def, hexpval]
      _ ≤ B1 := by
          rw [hB1_def]
          have h1 : 1 / (2 * (a + ε)) ≤ 1 / (2 * a) :=
            one_div_le_one_div_of_le (by linarith) (by linarith)
          have h2 : (1 : ℝ) / (2 * a) / 2 = 1 / (4 * a) := by
            rw [div_div]
            congr 1
            ring
          calc (E + 1 / (2 * (a + ε))) / 2
              ≤ (E + 1 / (2 * a)) / 2 := by linarith
            _ = E / 2 + 1 / (2 * a) / 2 := by ring
            _ = E / 2 + 1 / (4 * a) := by rw [h2]
  -- the R-side data at the chosen ε
  obtain ⟨hRint, hRbdd⟩ := hR ε hε hε1
  -- the series side: pointwise identity under the exponential
  have hgm : ∀ r ∈ Ioi (0 : ℝ),
      (∑' j, c j * Complex.exp (lam j * r))
        * Complex.exp (-(lam k + (ε : ℂ)) * r)
      = ∑' j, c j * Complex.exp
          ((lam j - (lam k + (ε : ℂ))) * r) := by
    intro r _
    rw [← tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  -- negativity of every shifted exponent
  have hre : ∀ j, (lam j - (lam k + (ε : ℂ))).re ≤ -ε := by
    intro j
    simp only [Complex.sub_re, Complex.add_re,
      Complex.ofReal_re]
    linarith [hmax j]
  have hreneg : ∀ j, (lam j - (lam k + (ε : ℂ))).re < 0 :=
    fun j => lt_of_le_of_lt (hre j) (by linarith)
  -- per-term integrability
  have hFint : ∀ j, Integrable (fun r : ℝ =>
      c j * Complex.exp ((lam j - (lam k + (ε : ℂ))) * r))
      (volume.restrict (Ioi 0)) := fun j =>
    (integrableOn_exp_mul_complex_Ioi (hreneg j) 0).const_mul
      (c j)
  -- per-term norm-integral bound
  have hFnorm : ∀ j, (∫ r in Ioi (0 : ℝ), ‖c j * Complex.exp
      ((lam j - (lam k + (ε : ℂ))) * r)‖) ≤ ‖c j‖ * ε⁻¹ := by
    intro j
    have hval : ∫ r in Ioi (0 : ℝ), Real.exp
        ((lam j - (lam k + (ε : ℂ))).re * r)
        = 1 / -(lam j - (lam k + (ε : ℂ))).re := by
      have h := integral_exp_mul_Ioi (hreneg j) 0
      rw [mul_zero, Real.exp_zero] at h
      rw [h, div_neg, neg_div]
    calc (∫ r in Ioi (0 : ℝ), ‖c j * Complex.exp
        ((lam j - (lam k + (ε : ℂ))) * r)‖)
        = ∫ r in Ioi (0 : ℝ), ‖c j‖ * Real.exp
            ((lam j - (lam k + (ε : ℂ))).re * r) := by
          refine setIntegral_congr_fun measurableSet_Ioi
            fun r _ => ?_
          rw [norm_mul, hnormexp]
      _ = ‖c j‖ * ∫ r in Ioi (0 : ℝ), Real.exp
            ((lam j - (lam k + (ε : ℂ))).re * r) :=
          integral_const_mul _ _
      _ ≤ ‖c j‖ * ε⁻¹ := by
          rw [hval]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : ε ≤ -(lam j - (lam k + (ε : ℂ))).re := by
            have := hre j
            linarith
          have h2 := one_div_le_one_div_of_le hε h1
          rw [one_div ε] at h2
          exact h2
  have hnn : ∀ j, 0 ≤ ∫ r in Ioi (0 : ℝ), ‖c j * Complex.exp
      ((lam j - (lam k + (ε : ℂ))) * r)‖ := fun j =>
    setIntegral_nonneg measurableSet_Ioi fun r _ =>
      norm_nonneg _
  have hsumnorm : Summable (fun j => ∫ r in Ioi (0 : ℝ),
      ‖c j * Complex.exp
        ((lam j - (lam k + (ε : ℂ))) * r)‖) :=
    Summable.of_nonneg_of_le hnn hFnorm (hcs.mul_right ε⁻¹)
  have hswap : (∫ r in Ioi (0 : ℝ), ∑' j, c j * Complex.exp
      ((lam j - (lam k + (ε : ℂ))) * r))
      = ∑' j, c j * ∫ r in Ioi (0 : ℝ), Complex.exp
          ((lam j - (lam k + (ε : ℂ))) * r) := by
    rw [← integral_tsum_of_summable_integral_norm hFint hsumnorm]
    exact tsum_congr fun j => integral_const_mul _ _
  have hterm : ∀ j, (∫ r in Ioi (0 : ℝ), Complex.exp
      ((lam j - (lam k + (ε : ℂ))) * r))
      = ((lam k + (ε : ℂ)) - lam j)⁻¹ := by
    intro j
    have h := integral_exp_mul_complex_Ioi (hreneg j) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
    have h2 : (lam k + (ε : ℂ)) - lam j
        = -(lam j - (lam k + (ε : ℂ))) := by ring
    rw [h, neg_div, one_div, h2, inv_neg]
  have hseries_int_eq : (∫ r in Ioi (0 : ℝ), ∑' j,
      c j * Complex.exp ((lam j - (lam k + (ε : ℂ))) * r))
      = (∫ r in Ioi (0 : ℝ),
          f r * Complex.exp (-(lam k + (ε : ℂ)) * r))
        - ∫ r in Ioi (0 : ℝ),
            R r * Complex.exp (-(lam k + (ε : ℂ)) * r) := by
    rw [← integral_sub hfint hRint]
    refine setIntegral_congr_fun measurableSet_Ioi
      fun r hr => ?_
    rw [← hgm r hr, hf r hr]
    ring
  have hsum_formula : (∑' j,
      c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)
      = (∫ r in Ioi (0 : ℝ),
          f r * Complex.exp (-(lam k + (ε : ℂ)) * r))
        - ∫ r in Ioi (0 : ℝ),
            R r * Complex.exp (-(lam k + (ε : ℂ)) * r) := by
    rw [← hseries_int_eq, hswap]
    exact tsum_congr fun j => by rw [hterm j]
  have hSbound : ‖∑' j,
      c j * ((lam k + (ε : ℂ)) - lam j)⁻¹‖ ≤ B1 + CR := by
    rw [hsum_formula]
    exact le_trans (norm_sub_le _ _)
      (add_le_add hLfbound hRbdd)
  -- summability and splitting of the pole sum
  have hwge : ∀ j, ε ≤ ‖(lam k + (ε : ℂ)) - lam j‖ := by
    intro j
    have h1 : ε ≤ ((lam k + (ε : ℂ)) - lam j).re := by
      simp only [Complex.sub_re, Complex.add_re,
        Complex.ofReal_re]
      linarith [hmax j]
    exact le_trans h1 (le_trans (le_abs_self _)
      (Complex.abs_re_le_norm _))
  have hSsummable : Summable (fun j =>
      c j * ((lam k + (ε : ℂ)) - lam j)⁻¹) := by
    refine Summable.of_norm_bounded (hcs.mul_right ε⁻¹)
      fun j => ?_
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h2 := one_div_le_one_div_of_le hε (hwge j)
    rw [one_div ε] at h2
    exact le_trans (by rw [one_div]) h2
  have hsplit := hSsummable.tsum_eq_add_tsum_ite k
  have hkval : (lam k + (ε : ℂ)) - lam k = (ε : ℂ) := by ring
  have hεnorm : ‖(ε : ℂ)‖ = ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hknorm : ‖c k * ((lam k + (ε : ℂ)) - lam k)⁻¹‖
      = ‖c k‖ / ε := by
    rw [hkval, norm_mul, norm_inv, hεnorm, div_eq_mul_inv]
  -- tail termwise bound
  have htail_term : ∀ j, ‖(if j = k then 0 else
      c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖
      ≤ 2 / δ * ‖c j‖ := by
    intro j
    by_cases hj : j = k
    · simp only [if_pos hj, norm_zero]
      positivity
    · simp only [if_neg hj]
      rw [norm_mul, norm_inv]
      have h1 : δ / 2 ≤ ‖(lam k + (ε : ℂ)) - lam j‖ := by
        have h2 : (lam k + (ε : ℂ)) - lam j
            = (lam k - lam j) + (ε : ℂ) := by ring
        rw [h2]
        have h3 := norm_sub_norm_le (lam k - lam j) (-(ε : ℂ))
        rw [sub_neg_eq_add, norm_neg, hεnorm] at h3
        have h5 := hsep j hj
        linarith
      have h6 : ‖(lam k + (ε : ℂ)) - lam j‖⁻¹ ≤ 2 / δ := by
        have h7 := one_div_le_one_div_of_le
          (by linarith : (0 : ℝ) < δ / 2) h1
        rw [one_div_div] at h7
        exact le_trans (by rw [one_div]) h7
      rw [mul_comm (2 / δ)]
      exact mul_le_mul_of_nonneg_left h6 (norm_nonneg _)
  have htail_summable : Summable (fun j =>
      ‖(if j = k then 0 else
        c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      htail_term (hcs.mul_left (2 / δ))
  have htail : ‖∑' j, (if j = k then 0 else
      c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖ ≤ B2 := by
    refine le_trans (norm_tsum_le_tsum_norm htail_summable) ?_
    calc (∑' j, ‖(if j = k then 0 else
        c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖)
        ≤ ∑' j, 2 / δ * ‖c j‖ :=
          htail_summable.tsum_le_tsum htail_term
            (hcs.mul_left (2 / δ))
      _ = B2 := by rw [tsum_mul_left, hB2_def]
  -- final contradiction
  have hfinal : ‖c k‖ / ε ≤ B1 + CR + B2 := by
    have h1 : ‖c k * ((lam k + (ε : ℂ)) - lam k)⁻¹‖
        ≤ ‖∑' j, c j * ((lam k + (ε : ℂ)) - lam j)⁻¹‖
          + ‖∑' j, (if j = k then 0 else
              c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖ := by
      calc ‖c k * ((lam k + (ε : ℂ)) - lam k)⁻¹‖
          = ‖(c k * ((lam k + (ε : ℂ)) - lam k)⁻¹
              + ∑' j, (if j = k then 0 else
                c j * ((lam k + (ε : ℂ)) - lam j)⁻¹))
              - ∑' j, (if j = k then 0 else
                c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖ := by
            rw [add_sub_cancel_right]
        _ ≤ ‖c k * ((lam k + (ε : ℂ)) - lam k)⁻¹
              + ∑' j, (if j = k then 0 else
                c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖
            + ‖∑' j, (if j = k then 0 else
                c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖ :=
            norm_sub_le _ _
        _ = ‖∑' j, c j * ((lam k + (ε : ℂ)) - lam j)⁻¹‖
            + ‖∑' j, (if j = k then 0 else
                c j * ((lam k + (ε : ℂ)) - lam j)⁻¹)‖ := by
            rw [← hsplit]
    rw [hknorm] at h1
    linarith [hSbound, htail]
  have h2 : 2 * denom ≤ ‖c k‖ / ε := by
    rw [le_div_iff₀ hε]
    have h3 := (le_div_iff₀
      (by positivity : (0 : ℝ) < 2 * denom)).mp hεc
    linarith
  have h4 : B1 + CR + B2 + 1 ≤ denom := le_max_right _ _
  linarith [hfinal, h2, hdenom]

end NCG
