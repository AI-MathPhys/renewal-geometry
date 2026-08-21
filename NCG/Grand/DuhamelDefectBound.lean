/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Quantitative Duhamel defect bounds

This module isolates the Banach-space estimate behind generator and semigroup
intertwining.  It applies equally to ordinary carriers and to graph-norm
domains: once a Duhamel identity is available, exponential semigroup bounds
give exactly the convolution factor used in the Gran-Tensor manuscript.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace NCG

/-- The exponential convolution factor appearing in a Duhamel estimate. -/
def exponentialConvolution (t omegaLeft omegaRight : ℝ) : ℝ :=
  ∫ s in 0..t, Real.exp (omegaLeft * (t - s) + omegaRight * s)

theorem exponentialConvolution_nonneg
    {t omegaLeft omegaRight : ℝ} (ht : 0 ≤ t) :
    0 ≤ exponentialConvolution t omegaLeft omegaRight := by
  apply intervalIntegral.integral_nonneg ht
  intro s _
  exact (Real.exp_pos _).le

universe u v w

variable {K : Type u} [RCLike K]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace K X]
variable {H : Type w} [NormedAddCommGroup H] [NormedSpace K H]
  [NormedSpace ℝ H] [CompleteSpace H]

/-- Banach-valued fundamental theorem in the sign convention used by
Duhamel's formula: a path with derivative `-integrand` has initial-minus-final
increment equal to the integral of `integrand`. -/
theorem sub_eq_intervalIntegral_of_hasDerivAt_neg
    (path integrand : ℝ → H) (t : ℝ) (ht : 0 ≤ t)
    (hderiv : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt path (-integrand s) s)
    (hcont : ContinuousOn integrand (Icc (0 : ℝ) t)) :
    path 0 - path t = ∫ s in 0..t, integrand s := by
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t)
    (fun s hs ↦ hderiv s (by simpa [uIcc_of_le ht] using hs))
    (hcont.neg.intervalIntegrable_of_Icc ht)
  rw [intervalIntegral.integral_neg] at hfund
  calc
    path 0 - path t = -(path t - path 0) := by abel
    _ = - (-(∫ s in 0..t, integrand s)) := by rw [← hfund]
    _ = ∫ s in 0..t, integrand s := neg_neg _

/-- Banach-valued fundamental theorem in Duhamel sign convention using only
right derivatives in the interior.  This is the natural form for C₀
semigroup generators. -/
theorem sub_eq_intervalIntegral_of_hasDerivWithinAt_right_neg
    (path integrand : ℝ → H) (t : ℝ) (ht : 0 ≤ t)
    (hpath : ContinuousOn path (Icc (0 : ℝ) t))
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt path (-integrand s) (Ioi s) s)
    (hint : IntervalIntegrable integrand volume 0 t) :
    path 0 - path t = ∫ s in 0..t, integrand s := by
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := path) (f' := fun s ↦ -integrand s) ht hpath hderiv hint.neg
  rw [intervalIntegral.integral_neg] at hfund
  calc
    path 0 - path t = -(path t - path 0) := by abel
    _ = - (-(∫ s in 0..t, integrand s)) := by rw [← hfund]
    _ = ∫ s in 0..t, integrand s := neg_neg _

/-- Exact Duhamel identity from the right product-path derivative.  Unlike
the full-derivative wrapper below, this version matches the native
one-sided derivative of a strongly continuous semigroup generator. -/
theorem semigroupDefect_eq_duhamel_of_rightPathDerivative
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X)
    (V : X →L[K] H) (R : X →L[K] H) (t : ℝ) (x : X)
    (ht : 0 ≤ t) (hTzero : T 0 = 1) (hSzero : S 0 = 1)
    (hpath : ContinuousOn (fun r ↦ T (t - r) (V (S r x)))
      (Icc (0 : ℝ) t))
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun r ↦ T (t - r) (V (S r x)))
        (-(T (t - s) (R (S s x)))) (Ioi s) s)
    (hint : IntervalIntegrable
      (fun s ↦ T (t - s) (R (S s x))) volume 0 t) :
    T t (V x) - V (S t x) =
      ∫ s in 0..t, T (t - s) (R (S s x)) := by
  simpa [hTzero, hSzero] using
    sub_eq_intervalIntegral_of_hasDerivWithinAt_right_neg
      (fun r ↦ T (t - r) (V (S r x)))
      (fun s ↦ T (t - s) (R (S s x))) t ht hpath hderiv hint

/-- Exact Duhamel identity once the standard product path derivative is
available.  This formulation is valid when `X` is the graph-norm domain of an
unbounded generator. -/
theorem semigroupDefect_eq_duhamel_of_pathDerivative
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X)
    (V : X →L[K] H) (R : X →L[K] H) (t : ℝ) (x : X)
    (ht : 0 ≤ t) (hTzero : T 0 = 1) (hSzero : S 0 = 1)
    (hderiv : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun r ↦ T (t - r) (V (S r x)))
        (-(T (t - s) (R (S s x)))) s)
    (hcont : ContinuousOn (fun s ↦ T (t - s) (R (S s x)))
      (Icc (0 : ℝ) t)) :
    T t (V x) - V (S t x) =
      ∫ s in 0..t, T (t - s) (R (S s x)) := by
  simpa [hTzero, hSzero] using
    sub_eq_intervalIntegral_of_hasDerivAt_neg
      (fun r ↦ T (t - r) (V (S r x)))
      (fun s ↦ T (t - s) (R (S s x))) t ht hderiv hcont

omit [CompleteSpace H] in
/-- Norm bound for a Duhamel integral under exponential operator bounds.
The source space `X` may itself be a graph-norm carrier. -/
theorem norm_duhamelIntegral_le_exponentialConvolution
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X) (R : X →L[K] H)
    (t MLeft MRight omegaLeft omegaRight : ℝ) (x : X)
    (ht : 0 ≤ t) (hMLeft : 0 ≤ MLeft)
    (hT : ∀ s ∈ Icc (0 : ℝ) t,
      ‖T (t - s)‖ ≤ MLeft * Real.exp (omegaLeft * (t - s)))
    (hS : ∀ s ∈ Icc (0 : ℝ) t,
      ‖S s‖ ≤ MRight * Real.exp (omegaRight * s)) :
    ‖∫ s in 0..t, T (t - s) (R (S s x))‖ ≤
      (MLeft * MRight * ‖R‖ * ‖x‖) *
        exponentialConvolution t omegaLeft omegaRight := by
  let C : ℝ := MLeft * MRight * ‖R‖ * ‖x‖
  let weight : ℝ → ℝ := fun s ↦
    Real.exp (omegaLeft * (t - s) + omegaRight * s)
  have hpoint : ∀ s ∈ Icc (0 : ℝ) t,
      ‖T (t - s) (R (S s x))‖ ≤ C * weight s := by
    intro s hs
    calc
      ‖T (t - s) (R (S s x))‖
          ≤ ‖T (t - s)‖ * ‖R (S s x)‖ :=
            (T (t - s)).le_opNorm _
      _ ≤ (MLeft * Real.exp (omegaLeft * (t - s))) *
          (‖R‖ * ‖S s x‖) := by
            gcongr
            · exact hT s hs
            · exact R.le_opNorm _
      _ ≤ (MLeft * Real.exp (omegaLeft * (t - s))) *
          (‖R‖ * (‖S s‖ * ‖x‖)) := by
            gcongr
            exact (S s).le_opNorm _
      _ ≤ (MLeft * Real.exp (omegaLeft * (t - s))) *
          (‖R‖ * ((MRight * Real.exp (omegaRight * s)) * ‖x‖)) := by
            gcongr
            exact hS s hs
      _ = C * weight s := by
            simp only [C, weight]
            rw [Real.exp_add]
            ring
  have hweight : Continuous weight := by
    fun_prop
  have hbound : IntervalIntegrable (fun s ↦ C * weight s) volume 0 t :=
    (continuous_const.mul hweight).intervalIntegrable 0 t
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall fun s hs ↦ hpoint s ⟨hs.1.le, hs.2⟩) hbound
  rw [intervalIntegral.integral_const_mul] at hnorm
  simpa only [C, weight, exponentialConvolution] using hnorm

omit [CompleteSpace H] in
/-- A vector-valued Duhamel identity immediately yields the same quantitative
defect estimate. -/
theorem norm_semigroupDefect_le_of_duhamel
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X) (R : X →L[K] H)
    (defect : ℝ → X → H)
    (t MLeft MRight omegaLeft omegaRight : ℝ) (x : X)
    (ht : 0 ≤ t) (hMLeft : 0 ≤ MLeft)
    (hT : ∀ s ∈ Icc (0 : ℝ) t,
      ‖T (t - s)‖ ≤ MLeft * Real.exp (omegaLeft * (t - s)))
    (hS : ∀ s ∈ Icc (0 : ℝ) t,
      ‖S s‖ ≤ MRight * Real.exp (omegaRight * s))
    (hduhamel : defect t x = ∫ s in 0..t, T (t - s) (R (S s x))) :
    ‖defect t x‖ ≤
      (MLeft * MRight * ‖R‖ * ‖x‖) *
        exponentialConvolution t omegaLeft omegaRight := by
  rw [hduhamel]
  exact norm_duhamelIntegral_le_exponentialConvolution
    T S R t MLeft MRight omegaLeft omegaRight x ht hMLeft hT hS

omit [CompleteSpace H] in
/-- Operator-norm Duhamel estimate.  This is the uniform version of
`norm_semigroupDefect_le_of_duhamel` used for graph-norm source carriers. -/
theorem opNorm_semigroupDefect_le_of_duhamel
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X) (R : X →L[K] H)
    (defect : X →L[K] H)
    (t MLeft MRight omegaLeft omegaRight : ℝ)
    (ht : 0 ≤ t) (hMLeft : 0 ≤ MLeft) (hMRight : 0 ≤ MRight)
    (hT : ∀ s ∈ Icc (0 : ℝ) t,
      ‖T (t - s)‖ ≤ MLeft * Real.exp (omegaLeft * (t - s)))
    (hS : ∀ s ∈ Icc (0 : ℝ) t,
      ‖S s‖ ≤ MRight * Real.exp (omegaRight * s))
    (hduhamel : ∀ x : X,
      defect x = ∫ s in 0..t, T (t - s) (R (S s x))) :
    ‖defect‖ ≤
      (MLeft * MRight * ‖R‖) *
        exponentialConvolution t omegaLeft omegaRight := by
  have hPhi : 0 ≤ exponentialConvolution t omegaLeft omegaRight :=
    exponentialConvolution_nonneg ht
  apply defect.opNorm_le_bound
  · positivity
  intro x
  have hx := norm_semigroupDefect_le_of_duhamel
    T S R (fun _ y ↦ defect y) t MLeft MRight omegaLeft omegaRight x
    ht hMLeft hT hS (hduhamel x)
  calc
    ‖defect x‖
        ≤ (MLeft * MRight * ‖R‖ * ‖x‖) *
            exponentialConvolution t omegaLeft omegaRight := hx
    _ = ((MLeft * MRight * ‖R‖) *
          exponentialConvolution t omegaLeft omegaRight) * ‖x‖ := by ring

omit [CompleteSpace H] in
/-- The exact quantitative source-core bound from the manuscript: combine
Duhamel's formula with the sharp operator-norm consequence of the orthogonal
leakage/compression decomposition. -/
theorem opNorm_semigroupDefect_le_sqrt_residual
    (T : ℝ → H →L[K] H) (S : ℝ → X →L[K] X) (R : X →L[K] H)
    (defect : X →L[K] H)
    (t MLeft MRight omegaLeft omegaRight deltaLeak deltaComp : ℝ)
    (ht : 0 ≤ t) (hMLeft : 0 ≤ MLeft) (hMRight : 0 ≤ MRight)
    (hR : ‖R‖ ≤ Real.sqrt (deltaLeak + deltaComp))
    (hT : ∀ s ∈ Icc (0 : ℝ) t,
      ‖T (t - s)‖ ≤ MLeft * Real.exp (omegaLeft * (t - s)))
    (hS : ∀ s ∈ Icc (0 : ℝ) t,
      ‖S s‖ ≤ MRight * Real.exp (omegaRight * s))
    (hduhamel : ∀ x : X,
      defect x = ∫ s in 0..t, T (t - s) (R (S s x))) :
    ‖defect‖ ≤ MLeft * MRight *
      exponentialConvolution t omegaLeft omegaRight *
        Real.sqrt (deltaLeak + deltaComp) := by
  have hPhi : 0 ≤ exponentialConvolution t omegaLeft omegaRight :=
    exponentialConvolution_nonneg ht
  calc
    ‖defect‖ ≤ (MLeft * MRight * ‖R‖) *
        exponentialConvolution t omegaLeft omegaRight :=
      opNorm_semigroupDefect_le_of_duhamel
        T S R defect t MLeft MRight omegaLeft omegaRight
        ht hMLeft hMRight hT hS hduhamel
    _ ≤ (MLeft * MRight * Real.sqrt (deltaLeak + deltaComp)) *
        exponentialConvolution t omegaLeft omegaRight := by
      gcongr
    _ = MLeft * MRight * exponentialConvolution t omegaLeft omegaRight *
        Real.sqrt (deltaLeak + deltaComp) := by ring

end NCG
