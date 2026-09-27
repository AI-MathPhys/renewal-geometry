/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.StieltjesLaplaceScalar
/-!
# All integer moments can miss the dynamic self-energy

This file proves `cth:supp-moment-indeterminate` of `papers/predictive_spectral_geometry`.

For `|ε| ≤ 1` the perturbed lognormal family (`eq:supp-lognormal-family`)
`dμ_ε(x) = [1 + ε sin(2π log x)] e^{-(log x)²/2} / (x √(2π)) dx` on `(0, ∞)` is encoded as
`lognormalMeasure ε`.  We prove

* `integral_zpow_lognormalMeasure` (`eq:supp-lognormal-moments`): `∫ xⁿ dμ_ε = e^{n²/2}` for
  every integer `n ∈ ℤ`, independently of `ε` (substitution `x = e^y`, completing the square in
  the Gaussian integral, and the vanishing of `∫ e^{-(y-n)²/2} sin(2πy) dy` by the shift
  `y ↦ y + n` and oddness);
* `stieltjesTransform_ne_of_ne`: for `ε ≠ ε'` the Stieltjes transforms
  `Σ_ε(z) = ∫ (x - z)⁻¹ dμ_ε(x)` differ at some `z ∈ ℂ ∖ [0, ∞)`, by injectivity of the
  Stieltjes transform (`StieltjesLaplace.measure_eq_of_forall_integral_inv_add_eq`, proved through
  the Laplace relation and two applications of Laplace uniqueness as in the paper);
* `exists_isOpen_stieltjesTransform_ne`: hence on a nonempty open set of such `z`;
* `moment_indeterminate`: the packaged statement.  Since every positive moment, every inverse
  integer moment and every finite Hankel panel is a function of the integer moment sequence,
  they all agree along the family while the self-energies are distinct.
-/

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace RenewalGeometry
namespace LognormalIndeterminacy

/-- The scalar Stieltjes transform `Σ_ν(z) = ∫ (x - z)⁻¹ dν(x)` of a measure on `ℝ`. -/
noncomputable def stieltjesTransform (ν : Measure ℝ) (z : ℂ) : ℂ := ∫ x, ((x : ℂ) - z)⁻¹ ∂ν

/-- The perturbed lognormal density `[1 + ε sin(2π log x)] e^{-(log x)²/2} / (x √(2π))`
(`eq:supp-lognormal-family`). -/
noncomputable def lognormalDensity (ε x : ℝ) : ℝ :=
  (1 + ε * Real.sin (2 * π * Real.log x)) *
    (Real.exp (-(Real.log x ^ 2) / 2) / (x * Real.sqrt (2 * π)))

/-- The perturbed lognormal measure `μ_ε` on `(0, ∞)` (`eq:supp-lognormal-family`). -/
noncomputable def lognormalMeasure (ε : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun x =>
    ENNReal.ofReal (lognormalDensity ε x)

/-! ## Gaussian integrals -/

theorem integral_gaussian_half : ∫ y : ℝ, Real.exp (-(1 / 2 : ℝ) * y ^ 2) = Real.sqrt (2 * π) := by
  rw [integral_gaussian]
  congr 1
  field_simp

theorem integrable_gaussian_half : Integrable fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2) :=
  integrable_exp_neg_mul_sq (by norm_num)

theorem integrable_gaussian_shift (c : ℝ) :
    Integrable fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * (y - c) ^ 2) :=
  integrable_gaussian_half.comp_sub_right c

/-- `∫ e^{-(y-c)²/2} dy = √(2π)`. -/
theorem integral_gaussian_shift (c : ℝ) :
    ∫ y : ℝ, Real.exp (-(1 / 2 : ℝ) * (y - c) ^ 2) = Real.sqrt (2 * π) := by
  rw [← integral_gaussian_half]
  exact integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2)) c

/-- The odd integrand `sin(2πy) e^{-y²/2}` integrates to zero. -/
theorem integral_sin_mul_gaussian :
    ∫ y : ℝ, Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) = 0 := by
  have h := integral_neg_eq_self
    (fun y : ℝ => Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) volume
  have h2 : ∀ y : ℝ, Real.sin (2 * π * -y) * Real.exp (-(1 / 2 : ℝ) * (-y) ^ 2) =
      -(Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) := by
    intro y
    rw [neg_sq, mul_neg, Real.sin_neg]
    ring
  simp only [h2, integral_neg] at h
  linarith

/-- `∫ sin(2πy) e^{-(y-n)²/2} dy = 0` for every integer `n` (shift `y ↦ y + n` and oddness). -/
theorem integral_sin_mul_gaussian_shift (n : ℤ) :
    ∫ y : ℝ, Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2) = 0 := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2)) (n : ℝ)
  rw [← h]
  have hsin : ∀ y : ℝ, Real.sin (2 * π * (y + n)) = Real.sin (2 * π * y) := fun y => by
    rw [show 2 * π * (y + n) = 2 * π * y + n * (2 * π) by ring]
    exact Real.sin_add_int_mul_two_pi _ n
  simp only [add_sub_cancel_right, hsin]
  exact integral_sin_mul_gaussian

/-- Completing the square: `e^{yn} e^{-y²/2} = e^{n²/2} e^{-(y-n)²/2}`. -/
theorem exp_mul_gaussian (n y : ℝ) :
    Real.exp (-(1 / 2 : ℝ) * y ^ 2) * Real.exp (y * n) =
      Real.exp (n ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The transformed moment integral: `∫ [1 + ε sin(2πy)] e^{-y²/2} e^{ny} dy = √(2π) e^{n²/2}`. -/
theorem integral_lognormal_transformed (ε : ℝ) (n : ℤ) :
    ∫ y : ℝ, (1 + ε * Real.sin (2 * π * y)) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) * Real.exp (y * n) =
      Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 / 2) := by
  have hG := integrable_gaussian_shift (n : ℝ)
  have hGs : Integrable fun y : ℝ =>
      Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2) :=
    hG.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact Real.abs_sin_le_one _)
  have key : ∀ y : ℝ,
      (1 + ε * Real.sin (2 * π * y)) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) * Real.exp (y * n) =
        Real.exp ((n : ℝ) ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2) +
          (ε * Real.exp ((n : ℝ) ^ 2 / 2)) *
            (Real.sin (2 * π * y) * Real.exp (-(1 / 2 : ℝ) * (y - n) ^ 2)) := by
    intro y
    rw [mul_assoc, exp_mul_gaussian]
    ring
  simp_rw [key]
  rw [integral_add (hG.const_mul _) (hGs.const_mul _), integral_const_mul, integral_const_mul,
    integral_gaussian_shift, integral_sin_mul_gaussian_shift]
  ring

/-! ## The lognormal family -/

theorem lognormalDensity_nonneg {ε : ℝ} (hε : |ε| ≤ 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ lognormalDensity ε x := by
  unfold lognormalDensity
  apply mul_nonneg
  · have h1 : |ε * Real.sin (2 * π * Real.log x)| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ hε (abs_nonneg _) (Real.abs_sin_le_one _)
    linarith [(abs_le.mp h1).1]
  · positivity

theorem measurable_lognormalDensity (ε : ℝ) : Measurable (lognormalDensity ε) := by
  unfold lognormalDensity
  fun_prop

theorem continuousOn_lognormalDensity (ε : ℝ) : ContinuousOn (lognormalDensity ε) (Ioi 0) := by
  unfold lognormalDensity
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt hx
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_const.add (continuousOn_const.mul
      (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul hlog)))
  · refine ContinuousOn.div (Real.continuous_exp.comp_continuousOn
      (((hlog.pow 2).neg).div_const 2)) (continuousOn_id.mul continuousOn_const) fun x hx => ?_
    exact mul_ne_zero (ne_of_gt hx) (Real.sqrt_pos.mpr (by positivity)).ne'

/-- Substitution `x = e^y` on `(0, ∞)`. -/
theorem integral_Ioi_eq_integral_exp (g : ℝ → ℝ) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ y : ℝ, Real.exp y * g (Real.exp y) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  beta_reduce
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul]

/-- The density transforms under `x = e^y` to `[1 + ε sin(2πy)] e^{-y²/2} / √(2π)`. -/
theorem exp_mul_lognormalDensity_exp (ε y : ℝ) :
    Real.exp y * lognormalDensity ε (Real.exp y) =
      (Real.sqrt (2 * π))⁻¹ * ((1 + ε * Real.sin (2 * π * y)) * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) := by
  unfold lognormalDensity
  rw [Real.log_exp, show -(y ^ 2) / 2 = -(1 / 2 : ℝ) * y ^ 2 by ring]
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have he : 0 < Real.exp y := Real.exp_pos y
  field_simp
  try ring

/-- **`eq:supp-lognormal-moments`.**  Every integer moment of `μ_ε` equals `e^{n²/2}`,
independently of `ε` (`|ε| ≤ 1`). -/
theorem integral_zpow_lognormalMeasure {ε : ℝ} (hε : |ε| ≤ 1) (n : ℤ) :
    ∫ x, x ^ n ∂(lognormalMeasure ε) = Real.exp ((n : ℝ) ^ 2 / 2) := by
  unfold lognormalMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_lognormalDensity ε).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∫ x in Ioi (0 : ℝ), (ENNReal.ofReal (lognormalDensity ε x)).toReal • x ^ n =
      ∫ x in Ioi (0 : ℝ), lognormalDensity ε x * x ^ n := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (lognormalDensity_nonneg hε hx)]
  rw [h1, integral_Ioi_eq_integral_exp]
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h2 : ∀ y : ℝ, Real.exp y * (lognormalDensity ε (Real.exp y) * Real.exp y ^ n) =
      (Real.sqrt (2 * π))⁻¹ *
        ((1 + ε * Real.sin (2 * π * y)) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) * Real.exp (y * n)) := by
    intro y
    rw [← mul_assoc, exp_mul_lognormalDensity_exp, ← Real.rpow_intCast, ← Real.exp_mul]
    ring
  simp_rw [h2]
  rw [integral_const_mul, integral_lognormal_transformed, ← mul_assoc, inv_mul_cancel₀ hs.ne',
    one_mul]

/-- `μ_ε` is a finite measure (its mass is the zeroth moment `e^0 = 1`). -/
theorem isFiniteMeasure_lognormalMeasure {ε : ℝ} (hε : |ε| ≤ 1) :
    IsFiniteMeasure (lognormalMeasure ε) := by
  refine ⟨lt_top_iff_ne_top.2 fun htop => ?_⟩
  have h := integral_zpow_lognormalMeasure hε 0
  simp only [zpow_zero, integral_const, smul_eq_mul, mul_one, measureReal_def, htop,
    ENNReal.toReal_top, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, Real.exp_zero] at h
  exact zero_ne_one h

theorem lognormalMeasure_Iio (ε : ℝ) : lognormalMeasure ε (Iio 0) = 0 :=
  withDensity_absolutelyContinuous _ _ StieltjesLaplace.restrict_Ioi_apply_Iio

/-- Distinct parameters give distinct measures. -/
theorem lognormalMeasure_injective {ε ε' : ℝ} (hε : |ε| ≤ 1) (hε' : |ε'| ≤ 1)
    (h : lognormalMeasure ε = lognormalMeasure ε') : ε = ε' := by
  unfold lognormalMeasure at h
  rw [withDensity_eq_iff_of_sigmaFinite (measurable_lognormalDensity ε).ennreal_ofReal.aemeasurable
    (measurable_lognormalDensity ε').ennreal_ofReal.aemeasurable] at h
  have heq : EqOn (lognormalDensity ε) (lognormalDensity ε') (Ioi 0) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi
      (continuousOn_lognormalDensity ε) (continuousOn_lognormalDensity ε')
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    rwa [ENNReal.ofReal_eq_ofReal_iff (lognormalDensity_nonneg hε hx0)
      (lognormalDensity_nonneg hε' hx0)] at hx
  have hx0 : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  have hval := heq (mem_Ioi.mpr hx0)
  unfold lognormalDensity at hval
  rw [Real.log_exp] at hval
  have hsin : Real.sin (2 * π * (1 / 4)) = 1 := by
    rw [show 2 * π * (1 / 4) = π / 2 by ring]
    exact Real.sin_pi_div_two
  rw [hsin] at hval
  have hpos : 0 < Real.exp (-((1 / 4 : ℝ) ^ 2) / 2) / (Real.exp (1 / 4) * Real.sqrt (2 * π)) := by
    positivity
  have := mul_right_cancel₀ hpos.ne' hval
  linarith

/-! ## Continuity of the Stieltjes transform off `[0, ∞)` -/

/-- Distance from a point `z ∉ [0, ∞)` to the half-line `[0,∞)`. -/
theorem exists_pos_le_norm_sub {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → δ ≤ ‖(x : ℂ) - z‖ := by
  refine ⟨if z.im = 0 then -z.re else |z.im|, ?_, ?_⟩
  · split_ifs with h
    · have : ¬ 0 ≤ z.re := fun h' => hz ⟨h, h'⟩
      linarith [not_le.mp this]
    · exact abs_pos.mpr h
  · intro x hx
    split_ifs with h
    · have hre : z.re < 0 := not_le.mp fun h' => hz ⟨h, h'⟩
      have e1 : |((x : ℂ) - z).re| = x - z.re := by
        rw [Complex.sub_re, Complex.ofReal_re, abs_of_nonneg (by linarith)]
      have e2 := Complex.abs_re_le_norm ((x : ℂ) - z)
      rw [e1] at e2
      linarith
    · have e1 : |((x : ℂ) - z).im| = |z.im| := by
        rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
      have e2 := Complex.abs_im_le_norm ((x : ℂ) - z)
      rw [e1] at e2
      exact e2

/-- The Stieltjes transform of a finite measure on `[0,∞)` is continuous at every
`z₀ ∉ [0, ∞)`. -/
theorem continuousAt_stieltjesTransform {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0)
    {z₀ : ℂ} (hz : ¬ (z₀.im = 0 ∧ 0 ≤ z₀.re)) : ContinuousAt (stieltjesTransform ν) z₀ := by
  obtain ⟨δ, hδ, hlow⟩ := exists_pos_le_norm_sub hz
  unfold stieltjesTransform
  refine continuousAt_of_dominated (bound := fun _ => 2 / δ) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun z =>
      ((Complex.measurable_ofReal.sub measurable_const).inv).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z₀ (half_pos hδ)] with z hz'
    filter_upwards [StieltjesLaplace.ae_nonneg_of_measure_Iio hν] with x hx
    rw [norm_inv]
    have h1 : δ / 2 ≤ ‖(x : ℂ) - z‖ := by
      have h2 := hlow x hx
      have h3 : ‖(x : ℂ) - z₀‖ - ‖(x : ℂ) - z‖ ≤ ‖z - z₀‖ := by
        have := norm_sub_norm_le ((x : ℂ) - z₀) ((x : ℂ) - z)
        rwa [show (x : ℂ) - z₀ - ((x : ℂ) - z) = z - z₀ by ring] at this
      rw [Metric.mem_ball, dist_eq_norm] at hz'
      linarith
    calc ‖(x : ℂ) - z‖⁻¹ ≤ (δ / 2)⁻¹ := inv_anti₀ (by positivity) h1
      _ = 2 / δ := by rw [inv_div]
  · filter_upwards [StieltjesLaplace.ae_nonneg_of_measure_Iio hν] with x hx
    have hne : (x : ℂ) - z₀ ≠ 0 := by
      intro h0
      have := hlow x hx
      rw [h0, norm_zero] at this
      linarith
    exact ((continuous_const.sub continuous_id).continuousAt).inv₀ hne

/-- On the negative real axis the Stieltjes transform is the real integral `∫ (x + s)⁻¹ dν`. -/
theorem stieltjesTransform_neg_real (ν : Measure ℝ) (s : ℝ) :
    stieltjesTransform ν (-(s : ℂ)) = ((∫ x, (x + s)⁻¹ ∂ν : ℝ) : ℂ) := by
  unfold stieltjesTransform
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  push_cast
  rw [sub_neg_eq_add]

/-- **Distinct parameters give distinct self-energies.**  For `|ε|, |ε'| ≤ 1` and `ε ≠ ε'`, the
Stieltjes transforms of `μ_ε` and `μ_ε'` differ at some `z ∈ ℂ ∖ [0, ∞)`. -/
theorem stieltjesTransform_ne_of_ne {ε ε' : ℝ} (hε : |ε| ≤ 1) (hε' : |ε'| ≤ 1) (hne : ε ≠ ε') :
    ∃ z : ℂ, ¬ (z.im = 0 ∧ 0 ≤ z.re) ∧
      stieltjesTransform (lognormalMeasure ε) z ≠ stieltjesTransform (lognormalMeasure ε') z := by
  by_contra hcon
  apply hne
  refine lognormalMeasure_injective hε hε' ?_
  have := isFiniteMeasure_lognormalMeasure hε
  have := isFiniteMeasure_lognormalMeasure hε'
  refine StieltjesLaplace.measure_eq_of_forall_integral_inv_add_eq (lognormalMeasure_Iio ε)
    (lognormalMeasure_Iio ε') fun s hs => ?_
  have hz : ¬ ((-(s : ℂ)).im = 0 ∧ 0 ≤ (-(s : ℂ)).re) := fun h => by
    have := h.2
    simp only [Complex.neg_re, Complex.ofReal_re, Left.nonneg_neg_iff] at this
    linarith
  have h : stieltjesTransform (lognormalMeasure ε) (-(s : ℂ)) =
      stieltjesTransform (lognormalMeasure ε') (-(s : ℂ)) := by
    by_contra hne''
    exact hcon ⟨_, hz, hne''⟩
  rw [stieltjesTransform_neg_real, stieltjesTransform_neg_real] at h
  exact_mod_cast h

/-- The self-energies differ on a nonempty open subset of `ℂ ∖ [0, ∞)`. -/
theorem exists_isOpen_stieltjesTransform_ne {ε ε' : ℝ} (hε : |ε| ≤ 1) (hε' : |ε'| ≤ 1)
    (hne : ε ≠ ε') :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ (∀ z ∈ U, ¬ (z.im = 0 ∧ 0 ≤ z.re)) ∧
      ∀ z ∈ U, stieltjesTransform (lognormalMeasure ε) z ≠
        stieltjesTransform (lognormalMeasure ε') z := by
  obtain ⟨z₀, hz₀, hne'⟩ := stieltjesTransform_ne_of_ne hε hε' hne
  have := isFiniteMeasure_lognormalMeasure hε
  have := isFiniteMeasure_lognormalMeasure hε'
  set S : Set ℂ := {z | ¬ (z.im = 0 ∧ 0 ≤ z.re)} with hSdef
  have hS : IsOpen S := by
    have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)
    exact hc.isOpen_compl
  set D : ℂ → ℂ := fun z =>
    stieltjesTransform (lognormalMeasure ε) z - stieltjesTransform (lognormalMeasure ε') z
  have hD : ContinuousOn D S := fun z hz =>
    ((continuousAt_stieltjesTransform (lognormalMeasure_Iio ε) hz).sub
      (continuousAt_stieltjesTransform (lognormalMeasure_Iio ε') hz)).continuousWithinAt
  refine ⟨S ∩ D ⁻¹' {0}ᶜ, hD.isOpen_inter_preimage hS isOpen_compl_singleton,
    ⟨z₀, hz₀, ?_⟩, fun z hz => hz.1, fun z hz => ?_⟩
  · exact sub_ne_zero.mpr hne'
  · exact sub_ne_zero.mp hz.2

/-- **`cth:supp-moment-indeterminate` (All integer moments can miss the dynamic self-energy).**
For `|ε| ≤ 1` the family `μ_ε` (`eq:supp-lognormal-family`) has all integer moments
`∫ xⁿ dμ_ε = e^{n²/2}`, `n ∈ ℤ`, independent of `ε` (so all positive moments, all inverse
integer moments and every finite Hankel panel agree along the family), while for `ε ≠ ε'` the
Stieltjes self-energies differ on a nonempty open subset of `ℂ ∖ [0, ∞)`. -/
theorem moment_indeterminate :
    (∀ ε : ℝ, |ε| ≤ 1 → ∀ n : ℤ,
      ∫ x, x ^ n ∂(lognormalMeasure ε) = Real.exp ((n : ℝ) ^ 2 / 2)) ∧
    (∀ ε ε' : ℝ, |ε| ≤ 1 → |ε'| ≤ 1 → ε ≠ ε' →
      ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ (∀ z ∈ U, ¬ (z.im = 0 ∧ 0 ≤ z.re)) ∧
        ∀ z ∈ U, stieltjesTransform (lognormalMeasure ε) z ≠
          stieltjesTransform (lognormalMeasure ε') z) :=
  ⟨fun _ hε n => integral_zpow_lognormalMeasure hε n,
    fun _ _ hε hε' hne => exists_isOpen_stieltjesTransform_ne hε hε' hne⟩

end LognormalIndeterminacy
end RenewalGeometry
