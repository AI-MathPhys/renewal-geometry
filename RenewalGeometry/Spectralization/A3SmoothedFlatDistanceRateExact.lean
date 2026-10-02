/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.A3SmoothedFlatDistanceExact
import RenewalGeometry.Continuum.LipschitzConvolutionDerivativeModulusExact

/-!
# Uniform smoothing of the flat `A₃` torus distance with the `ε⁻¹` rate

Paper `predictive_spectral_geometry`, label `lem:A3-uniform-distance-smoothing`.

The mollifier is the rescaled bump `η_ε = (scaledBump ε).normed`, with inner radius `ε/2` and
outer radius `ε`.  Mathlib's bumps with fixed radius ratio are exact rescalings of each other
(`scaledBump_apply`), so `η_ε(x) = ε⁻³ η_1(ε⁻¹ x)` (`scaledBump_normed_apply`) and
`∫ ‖Dη_ε‖ = ε⁻¹ ∫ ‖Dη_1‖` (`integral_norm_fderiv_scaledBump_normed`).

`F_{y,ε} = η_ε ⋆ d_g(y, ·)` (`A3SmoothedFlatDistance.smoothDistance`) is `C^∞`, lattice
periodic (so it descends to the torus `M`), `ε`-close to the distance, `1`-Lipschitz, and by the
first-derivative modulus for convolutions with Lipschitz data
(`LipschitzConvolutionDerivativeModulus.norm_fderiv_convolution_sub_le_of_lipschitz`) its
derivative is `ε⁻¹ ∫ ‖Dη_1‖`-Lipschitz, so its second derivative is bounded by the same constant.
The `C²` norm is rendered as the supremum of `|F| + ‖DF‖ + ‖D²F‖`.
-/

open MeasureTheory Filter Set Module
open scoped Convolution Topology

namespace RenewalGeometry.A3SmoothedFlatDistanceRate

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3FlatTorusMetric
open A3SmoothedFlatDistance LipschitzConvolutionDerivativeModulus

noncomputable section

/-- The bump of inner radius `ε/2` and outer radius `ε`, centred at the origin. -/
def scaledBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Space) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Bumps with the same radius ratio are rescalings of each other. -/
theorem scaledBump_apply (ε : ℝ) (hε : 0 < ε) (x : Space) :
    scaledBump ε hε x = scaledBump 1 one_pos (ε⁻¹ • x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  simp only [scaledBump, sub_zero, smul_smul]
  have h1 : ε / (ε / 2) = 1 / (1 / 2) := by field_simp
  have h2 : (ε / 2)⁻¹ = (1 / 2)⁻¹ * ε⁻¹ := by field_simp
  rw [h1, h2]

theorem integral_scaledBump (ε : ℝ) (hε : 0 < ε) :
    ∫ x, scaledBump ε hε x = ε ^ 3 * ∫ x, scaledBump 1 one_pos x := by
  simp_rw [scaledBump_apply ε hε]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume _ hε.le, finrank_euclideanSpace_fin,
    smul_eq_mul]

/-- The normalized rescaled bump: `η_ε(x) = ε⁻³ η_1(ε⁻¹ x)`. -/
theorem scaledBump_normed_apply (ε : ℝ) (hε : 0 < ε) (x : Space) :
    (scaledBump ε hε).normed volume x =
      (ε ^ 3)⁻¹ * (scaledBump 1 one_pos).normed volume (ε⁻¹ • x) := by
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, integral_scaledBump, scaledBump_apply]
  have h3 : ε ^ 3 ≠ 0 := by positivity
  have hI : (∫ x, scaledBump 1 one_pos x) ≠ 0 := (ContDiffBump.integral_pos _).ne'
  field_simp

/-- The reference mollifier `η_1`. -/
def referenceKernel : Space → ℝ := (scaledBump 1 one_pos).normed volume

/-- The gradient mass `∫ ‖Dη_1‖` of the reference mollifier. -/
def referenceGradientMass : ℝ := ∫ x, ‖fderiv ℝ referenceKernel x‖

theorem referenceGradientMass_nonneg : 0 ≤ referenceGradientMass :=
  integral_nonneg fun _ => norm_nonneg _

theorem norm_fderiv_scaledBump_normed (ε : ℝ) (hε : 0 < ε) (x : Space) :
    ‖fderiv ℝ ((scaledBump ε hε).normed volume) x‖ =
      (ε ^ 3)⁻¹ * ε⁻¹ * ‖fderiv ℝ referenceKernel (ε⁻¹ • x)‖ := by
  have hfun : (scaledBump ε hε).normed volume =
      fun x => (ε ^ 3)⁻¹ * referenceKernel (ε⁻¹ • x) := by
    funext x
    exact scaledBump_normed_apply ε hε x
  have hg : Differentiable ℝ referenceKernel :=
    ((scaledBump 1 one_pos).contDiff_normed (n := 1)).differentiable one_ne_zero
  have hd : HasFDerivAt (fun x : Space => (ε ^ 3)⁻¹ * referenceKernel (ε⁻¹ • x))
      ((ε ^ 3)⁻¹ • ((fderiv ℝ referenceKernel (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ Space))) x := by
    have hin : HasFDerivAt (fun x : Space => ε⁻¹ • x) (ε⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
      (hasFDerivAt_id x).const_smul ε⁻¹
    exact ((hg (ε⁻¹ • x)).hasFDerivAt.comp x hin).const_mul _
  rw [hfun, hd.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
    norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_pos (by positivity), mul_assoc]

/-- **Scaling of the gradient mass:** `∫ ‖Dη_ε‖ = ε⁻¹ ∫ ‖Dη_1‖`. -/
theorem integral_norm_fderiv_scaledBump_normed (ε : ℝ) (hε : 0 < ε) :
    ∫ x, ‖fderiv ℝ ((scaledBump ε hε).normed volume) x‖ = ε⁻¹ * referenceGradientMass := by
  simp_rw [norm_fderiv_scaledBump_normed ε hε]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun y => ‖fderiv ℝ referenceKernel y‖) hε.le,
    finrank_euclideanSpace_fin, smul_eq_mul, referenceGradientMass]
  have h3 : ε ^ 3 ≠ 0 := by positivity
  field_simp

/-- The smoothed distance `F_{y,ε} = η_ε ⋆ d_g(y, ·)`. -/
def smoothedDistance (ε : ℝ) (hε : 0 < ε) (y : Space) : Space → ℝ :=
  smoothDistance (scaledBump ε hε) y

/-- **Derivative modulus with the `ε⁻¹` rate**, uniformly in the centre `y`. -/
theorem norm_fderiv_smoothedDistance_sub_le (ε : ℝ) (hε : 0 < ε) (y p q : Space) :
    ‖fderiv ℝ (smoothedDistance ε hε y) q - fderiv ℝ (smoothedDistance ε hε y) p‖ ≤
      ε⁻¹ * referenceGradientMass * ‖q - p‖ := by
  have h := norm_fderiv_convolution_sub_le_of_lipschitz volume
    ((scaledBump ε hε).normed volume) (scaledBump ε hε).hasCompactSupport_normed
    (scaledBump ε hε).contDiff_normed (flatDistance y) 1 (flatDistance_lipschitz y) p q
  rw [integral_norm_fderiv_scaledBump_normed, NNReal.coe_one, one_mul] at h
  exact h

/-- **Second-derivative bound with the `ε⁻¹` rate**, uniformly in the centre `y`. -/
theorem norm_fderiv_fderiv_smoothedDistance_le (ε : ℝ) (hε : 0 < ε) (y p : Space) :
    ‖fderiv ℝ (fderiv ℝ (smoothedDistance ε hε y)) p‖ ≤ ε⁻¹ * referenceGradientMass := by
  have hF : ContDiff ℝ 2 (smoothedDistance ε hε y) :=
    (contDiff_smoothDistance (scaledBump ε hε) y).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hDF : Differentiable ℝ (fderiv ℝ (smoothedDistance ε hε y)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  refine (hDF p).hasFDerivAt.le_of_lip' (by
    exact mul_nonneg (inv_nonneg.mpr hε.le) referenceGradientMass_nonneg) ?_
  exact Eventually.of_forall fun q => norm_fderiv_smoothedDistance_sub_le ε hε y p q

/-- **`lem:A3-uniform-distance-smoothing`.**  With `ε₀ = 1` and `C_M = 8 + ∫ ‖Dη_1‖`: for every
centre `y` and `0 < ε < ε₀`, `F_{y,ε}` is `C^∞`, lattice periodic (it descends to the flat torus
`M`), satisfies `‖F_{y,ε} - d_g(y, ·)‖_∞ ≤ ε` and `‖∇F_{y,ε}‖_∞ ≤ 1`, and
`sup (|F| + ‖DF‖ + ‖D²F‖) ≤ C_M ε⁻¹`.  All constants are independent of `y`. -/
theorem a3_uniform_distance_smoothing :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, ∀ ε (hε : 0 < ε), ε < ε₀ → ∀ y : Space,
      ContDiff ℝ (⊤ : ℕ∞) (smoothedDistance ε hε y) ∧
      (∀ (q : lattice) (p : Space),
        smoothedDistance ε hε y (p + q) = smoothedDistance ε hε y p) ∧
      (∀ p, |smoothedDistance ε hε y p - flatDistance y p| ≤ ε) ∧
      (∀ p, ‖fderiv ℝ (smoothedDistance ε hε y) p‖ ≤ 1) ∧
      (∀ p, |smoothedDistance ε hε y p| + ‖fderiv ℝ (smoothedDistance ε hε y) p‖ +
          ‖fderiv ℝ (fderiv ℝ (smoothedDistance ε hε y)) p‖ ≤ C * ε⁻¹) := by
  refine ⟨1, one_pos, 8 + referenceGradientMass, fun ε hε hε1 y => ?_⟩
  have happrox : ∀ p, |smoothedDistance ε hε y p - flatDistance y p| ≤ ε := fun p =>
    abs_smoothDistance_sub_le (scaledBump ε hε) y p
  refine ⟨contDiff_smoothDistance _ y, fun q p => smoothDistance_periodic _ y q p, happrox,
    fun p => norm_fderiv_smoothDistance_le_one _ y p, fun p => ?_⟩
  have h0 : |smoothedDistance ε hε y p| ≤ 7 := by
    have hd0 : 0 ≤ flatDistance y p := PeriodicQuotientDistance.distance_nonneg lattice y p
    have hd6 := flatDistance_le_six y p
    have ha := happrox p
    rw [abs_le] at ha ⊢
    constructor <;> linarith
  have h1 : ‖fderiv ℝ (smoothedDistance ε hε y) p‖ ≤ 1 :=
    norm_fderiv_smoothDistance_le_one (scaledBump ε hε) y p
  have h2 := norm_fderiv_fderiv_smoothedDistance_le ε hε y p
  have hinv : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1.le⟩
  have h8 : (8 : ℝ) ≤ 8 * ε⁻¹ := by linarith
  calc _ ≤ 7 + 1 + ε⁻¹ * referenceGradientMass := by linarith
    _ ≤ (8 + referenceGradientMass) * ε⁻¹ := by rw [add_mul, mul_comm ε⁻¹]; linarith

end

end RenewalGeometry.A3SmoothedFlatDistanceRate
