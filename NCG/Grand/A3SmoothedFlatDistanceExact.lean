/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3FlatTorusMetricExact
import NCG.Grand.A3SmoothPeriodicUnitEnergyExact
import NCG.Grand.CompactKernelConvolutionDerivativeBoundExact

/-!
# Smooth distance tests for the genuine flat A3 torus

All centers share the same derivative modulus. Smoothing preserves the sharp
Lipschitz constant one and approximates the quotient distance within the
kernel radius, uniformly over both arguments.
-/

open MeasureTheory Filter Set
open scoped Convolution ENNReal

namespace NCG.A3SmoothedFlatDistance

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicSmoothEnergy
open A3FlatTorusMetric A3SmoothPeriodicUnitEnergy CompactKernelConvolutionDerivativeBound

noncomputable section

theorem flatDistance_le_six (x y : Space) : flatDistance x y ≤ 6 := by
  obtain ⟨q, hq⟩ := LatticePeriodicDifferentiation.periodLattice_bounded_cover basis (x - y)
  have hb : (∑ i : Fin 3, ‖basis i‖) ≤ 6 := by
    calc
      _ ≤ ∑ _i : Fin 3, (2 : ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [basis_eq_selected_root]; exact root_norm_le_two _)
      _ = 6 := by norm_num
  rw [flatDistance_eq_infDist]
  exact (Metric.infDist_le_dist_of_mem q.property).trans (by
    simpa only [dist_eq_norm] using hq.trans hb)

theorem flatDistance_lipschitz (x : Space) : LipschitzWith 1 (flatDistance x) :=
  PeriodicQuotientDistance.distance_to_base_lipschitz lattice x

theorem norm_flatDistance_le_six (x y : Space) : ‖flatDistance x y‖ ≤ 6 := by
  have hnonneg : 0 ≤ flatDistance x y :=
    PeriodicQuotientDistance.distance_nonneg lattice x y
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact flatDistance_le_six x y

def smoothDistance (φ : ContDiffBump (0 : Space)) (x : Space) : Space → ℝ :=
  φ.normed volume ⋆ flatDistance x

theorem smoothDistance_eq_integral (φ : ContDiffBump (0 : Space)) (x p : Space) :
    smoothDistance φ x p = ∫ z, flatDistance x (p - z) ∂probabilityKernel φ := by
  rw [probabilityKernel, integral_withDensity_eq_integral_toReal_smul
    φ.continuous_normed.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _), smoothDistance, convolution_lsmul]

theorem integrable_flatDistance_translate (φ : ContDiffBump (0 : Space)) (x p : Space) :
    Integrable (fun z => flatDistance x (p - z)) (probabilityKernel φ) := by
  apply Integrable.of_bound
    (((flatDistance_lipschitz x).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) 6
  exact Eventually.of_forall (fun z => norm_flatDistance_le_six x (p - z))

theorem smoothDistance_lipschitz (φ : ContDiffBump (0 : Space)) (x : Space) :
    LipschitzWith 1 (smoothDistance φ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, smoothDistance_eq_integral]
  rw [← integral_sub (integrable_flatDistance_translate φ x p)
    (integrable_flatDistance_translate φ x q)]
  have hbound : ∀ᵐ z ∂probabilityKernel φ,
      ‖flatDistance x (p - z) - flatDistance x (q - z)‖ ≤ dist p q := by
    apply Eventually.of_forall
    intro z
    have h := (flatDistance_lipschitz x).dist_le_mul (p - z) (q - z)
    simpa only [NNReal.coe_one, one_mul, dist_sub_right, Real.dist_eq,
      Real.norm_eq_abs] using h
  simpa [Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const hbound

theorem contDiff_smoothDistance (φ : ContDiffBump (0 : Space)) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDistance φ x) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (flatDistance_lipschitz x).continuous.locallyIntegrable

theorem smoothDistance_periodic (φ : ContDiffBump (0 : Space)) (x : Space)
    (q : lattice) (p : Space) : smoothDistance φ x (p + q) = smoothDistance φ x p := by
  rw [smoothDistance_eq_integral, smoothDistance_eq_integral]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change flatDistance x (p + q.val - z) = flatDistance x (p - z)
  rw [show p + q.val - z = (p - z) + q.val by abel]
  exact PeriodicQuotientDistance.distance_periodic_right lattice x (p - z) q

theorem abs_smoothDistance_sub_le (φ : ContDiffBump (0 : Space)) (x p : Space) :
    |smoothDistance φ x p - flatDistance x p| ≤ φ.rOut := by
  have h := φ.dist_normed_convolution_le (μ := (volume : Measure Space))
    (x₀ := p) (ε := φ.rOut) (flatDistance_lipschitz x).continuous.aestronglyMeasurable
    (fun y hy => by
      have h := (flatDistance_lipschitz x).dist_le_mul y p
      simp only [NNReal.coe_one, one_mul] at h
      exact h.trans (Metric.mem_ball.mp hy).le)
  simpa only [smoothDistance, Real.dist_eq, Real.norm_eq_abs] using h

theorem norm_fderiv_smoothDistance_le_one (φ : ContDiffBump (0 : Space)) (x p : Space) :
    ‖fderiv ℝ (smoothDistance φ x) p‖ ≤ 1 :=
  norm_fderiv_le_of_lipschitz ℝ (smoothDistance_lipschitz φ x)

def distanceDerivativeBound (φ : ContDiffBump (0 : Space)) : ℝ :=
  derivativeBound volume (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume) 6

theorem distanceDerivativeBound_nonneg (φ : ContDiffBump (0 : Space)) :
    0 ≤ distanceDerivativeBound φ := derivativeBound_nonneg _ _ _ _ (by norm_num)

theorem norm_fderiv_smoothDistance_sub_le (φ : ContDiffBump (0 : Space)) (x p q : Space) :
    ‖fderiv ℝ (smoothDistance φ x) q - fderiv ℝ (smoothDistance φ x) p‖ ≤
      distanceDerivativeBound φ * ‖q - p‖ :=
  norm_fderiv_convolution_sub_le volume (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.normed volume) φ.hasCompactSupport_normed φ.contDiff_normed (flatDistance x)
    (flatDistance_lipschitz x).continuous.locallyIntegrable 6 (norm_flatDistance_le_six x) p q

end

end NCG.A3SmoothedFlatDistance
