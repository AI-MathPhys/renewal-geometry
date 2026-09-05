/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The normal-ordered Gaussian stress cumulant is purely Wick

For the actual standard Gaussian measure, this file derives the fourth moment from Mathlib's
moment-generating-function theorem, proves that `T(x) = x² - 1` has mean zero and variance two,
and checks that this is exactly its Wick contraction.  Thus the direct-minus-Wick excess vanishes
despite a nonzero raw stress correlation.
-/

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace NCG.SMOSStandardGaussianStressWick

open ProbabilityTheory

private noncomputable def standardMGF (t : ℝ) : ℝ := Real.exp (t ^ 2 / 2)

private lemma hasDerivAt_exp_half_sq (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
  convert ((((hasDerivAt_id t).pow 2).div_const 2).exp) using 1
  · funext x
    simp
  · simp only [Pi.pow_apply, id_eq]
    ring

private lemma deriv_standardMGF :
    deriv standardMGF = fun t : ℝ => t * Real.exp (t ^ 2 / 2) := by
  funext t
  unfold standardMGF
  exact (hasDerivAt_exp_half_sq t).deriv

private lemma deriv_standardMGF_one :
    deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h := (hasDerivAt_id t).mul (hasDerivAt_exp_half_sq t)
  have h' : HasDerivAt (fun x : ℝ => x * Real.exp (x ^ 2 / 2))
      (1 * Real.exp (t ^ 2 / 2) + t * (t * Real.exp (t ^ 2 / 2))) t :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall (by intro x; simp))
  exact (h'.congr_deriv (by ring)).deriv

private lemma deriv_standardMGF_two :
    deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  funext t
  have hpolyRaw := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)
  have hpoly : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t :=
    (hpolyRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp))).congr_deriv (by simp)
  have hraw := hpoly.mul (hasDerivAt_exp_half_sq t)
  have h : HasDerivAt
      (fun x : ℝ => (1 + x ^ 2) * Real.exp (x ^ 2 / 2))
      (2 * t * Real.exp (t ^ 2 / 2) +
        (1 + t ^ 2) * (t * Real.exp (t ^ 2 / 2))) t :=
    hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (by intro x; rfl))
  exact (h.congr_deriv (by ring)).deriv

private lemma deriv_standardMGF_three :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  funext t
  have hpolyRaw := ((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)
  have hpoly : HasDerivAt (fun x : ℝ => 3 * x + x ^ 3) (3 + 3 * t ^ 2) t :=
    (hpolyRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp [mul_comm]))).congr_deriv
        (by simp)
  have hraw := hpoly.mul (hasDerivAt_exp_half_sq t)
  have h : HasDerivAt
      (fun x : ℝ => (3 * x + x ^ 3) * Real.exp (x ^ 2 / 2))
      ((3 + 3 * t ^ 2) * Real.exp (t ^ 2 / 2) +
        (3 * t + t ^ 3) * (t * Real.exp (t ^ 2 / 2))) t :=
    hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (by intro x; rfl))
  exact (h.congr_deriv (by ring)).deriv

/-- The fourth moment of the actual standard Gaussian measure is three. -/
theorem standardGaussian_fourth_moment :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) 4
  simp only [Pi.pow_apply] at hm
  rw [← hm]
  rw [mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
  change iteratedDeriv 4 standardMGF 0 = 3
  change iteratedDeriv (3 + 1) standardMGF 0 = 3
  rw [iteratedDeriv_succ', deriv_standardMGF]
  change iteratedDeriv (2 + 1)
    (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) 0 = 3
  rw [iteratedDeriv_succ', deriv_standardMGF_one]
  change iteratedDeriv (1 + 1)
    (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) 0 = 3
  rw [iteratedDeriv_succ', deriv_standardMGF_two]
  rw [iteratedDeriv_one, deriv_standardMGF_three]
  norm_num

/-- The normal-ordered quadratic candidate stress. -/
def wickStress (x : ℝ) : ℝ := x ^ 2 - 1

/-- The standard Gaussian second moment is one. -/
theorem standardGaussian_second_moment :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

private lemma integrable_standardGaussian_pow_two :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2).integrable_norm_pow'
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma integrable_standardGaussian_pow_four :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 4).integrable_norm_pow'
  convert h using 1
  ext x
  rw [Real.norm_eq_abs]
  rw [← abs_pow]
  exact (abs_of_nonneg (by positivity : 0 ≤ x ^ 4)).symm

/-- The normal-ordered stress has zero Gaussian mean. -/
theorem wickStress_mean_zero :
    ∫ x : ℝ, wickStress x ∂gaussianReal 0 1 = 0 := by
  rw [show (fun x : ℝ => wickStress x) = fun x => x ^ 2 - 1 by rfl,
    integral_sub integrable_standardGaussian_pow_two (integrable_const (c := (1 : ℝ)))]
  simp [standardGaussian_second_moment]

/-- Its raw quadratic correlation is two. -/
theorem wickStress_second_moment :
    ∫ x : ℝ, wickStress x ^ 2 ∂gaussianReal 0 1 = 2 := by
  have hpoint : (fun x : ℝ => wickStress x ^ 2) =
      fun x => x ^ 4 - 2 * x ^ 2 + 1 := by
    funext x
    simp [wickStress]
    ring
  rw [hpoint]
  let f : ℝ → ℝ := fun x => x ^ 4 - 2 * x ^ 2
  let g : ℝ → ℝ := fun _ => 1
  have hf : Integrable f (gaussianReal 0 1) :=
    integrable_standardGaussian_pow_four.sub
      (integrable_standardGaussian_pow_two.const_mul 2)
  have hg : Integrable g (gaussianReal 0 1) := integrable_const (c := (1 : ℝ))
  calc
    (∫ x : ℝ, x ^ 4 - 2 * x ^ 2 + 1 ∂gaussianReal 0 1) =
        (∫ x, f x ∂gaussianReal 0 1) + ∫ x, g x ∂gaussianReal 0 1 := by
      simpa [f, g] using integral_add hf hg
    _ = ((∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) -
          ∫ x : ℝ, 2 * x ^ 2 ∂gaussianReal 0 1) +
          ∫ _x : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
      rw [integral_sub integrable_standardGaussian_pow_four
        (integrable_standardGaussian_pow_two.const_mul 2)]
    _ = 2 := by
      rw [integral_const_mul]
      simp only [standardGaussian_fourth_moment, standardGaussian_second_moment]
      norm_num

/-- `Var(:X²:) = 2` for `X ∼ N(0,1)`. -/
theorem wickStress_variance :
    Var[wickStress; gaussianReal 0 1] = 2 := by
  have hcontinuous : Continuous wickStress := by
    unfold wickStress
    fun_prop
  rw [variance_eq_integral hcontinuous.aemeasurable]
  rw [wickStress_mean_zero]
  simpa using wickStress_second_moment

/-- Exact form of `cth:SMOS-raw-stress-cumulant`: the raw variance is nonzero but agrees with the
Wick prediction `2`, so the direct-minus-Wick excess is zero. -/
theorem raw_stress_cumulant_can_be_purely_Wick :
    Var[wickStress; gaussianReal 0 1] = 2 ∧
      (2 : ℝ) ≠ 0 ∧
      Var[wickStress; gaussianReal 0 1] - 2 = 0 := by
  rw [wickStress_variance]
  norm_num

end NCG.SMOSStandardGaussianStressWick
