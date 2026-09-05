/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weighted Duhamel convolution bounds

Abstract Banach-algebra estimates for the first and symmetric second
Duhamel integrals. They are independent of the concrete weighted Schur
model and can therefore be reused by every locality response built in that
algebra.
-/

open Set MeasureTheory
open scoped Interval

namespace NCG

namespace WeightedDuhamelConvolutionBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The first ordered Duhamel insertion. -/
noncomputable def firstDuhamel
    (P : ℝ → A) (V : A) (t : ℝ) : A :=
  ∫ s in (0 : ℝ)..t, P (t - s) * V * P s

/-- The exact first Duhamel convolution estimate. -/
theorem norm_firstDuhamel_le_convolution
    (P : ℝ → A) (V : A) (t : ℝ) (ht : 0 ≤ t)
    (hm : IntervalIntegrable
      (fun s => ‖P (t - s)‖ * ‖P s‖) volume 0 t) :
    ‖firstDuhamel P V t‖
      ≤ ‖V‖ * ∫ s in (0 : ℝ)..t, ‖P (t - s)‖ * ‖P s‖ := by
  unfold firstDuhamel
  have hbound : IntervalIntegrable
      (fun s => ‖V‖ * (‖P (t - s)‖ * ‖P s‖)) volume 0 t :=
    hm.const_mul ‖V‖
  have h := intervalIntegral.norm_integral_le_of_norm_le ht
    (f := fun s => P (t - s) * V * P s)
    (g := fun s => ‖V‖ * (‖P (t - s)‖ * ‖P s‖))
    (by
      filter_upwards [] with s
      intro hs
      calc
        ‖P (t - s) * V * P s‖
            ≤ ‖P (t - s)‖ * ‖V‖ * ‖P s‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _))
        _ = ‖V‖ * (‖P (t - s)‖ * ‖P s‖) := by ring)
    hbound
  simpa only [intervalIntegral.integral_const_mul] using h

/-- Exponential semigroup growth gives the exact first-response constant. -/
theorem norm_firstDuhamel_le
    (P : ℝ → A) (V : A) (t M ω : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hP : ∀ r, 0 ≤ r → ‖P r‖ ≤ M * Real.exp (ω * r)) :
    ‖firstDuhamel P V t‖
      ≤ M ^ 2 * t * Real.exp (ω * t) * ‖V‖ := by
  unfold firstDuhamel
  have hpoint : ∀ s ∈ Ι (0 : ℝ) t,
      ‖P (t - s) * V * P s‖
        ≤ M ^ 2 * Real.exp (ω * t) * ‖V‖ := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s ≤ t := hs.2
    calc
      ‖P (t - s) * V * P s‖
          ≤ ‖P (t - s)‖ * ‖V‖ * ‖P s‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
      _ ≤ (M * Real.exp (ω * (t - s))) * ‖V‖
            * (M * Real.exp (ω * s)) := by
        gcongr
        · exact hP (t - s) (sub_nonneg.mpr hst)
        · exact hP s hs0
      _ = M ^ 2 * ‖V‖ *
            (Real.exp (ω * (t - s)) * Real.exp (ω * s)) := by ring
      _ = M ^ 2 * ‖V‖ *
            Real.exp (ω * (t - s) + ω * s) := by rw [Real.exp_add]
      _ = M ^ 2 * Real.exp (ω * t) * ‖V‖ := by
        rw [show ω * (t - s) + ω * s = ω * t by ring]
        ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc
    ‖∫ s in (0 : ℝ)..t, P (t - s) * V * P s‖
        ≤ (M ^ 2 * Real.exp (ω * t) * ‖V‖) * |t - 0| := h
    _ = (M ^ 2 * Real.exp (ω * t) * ‖V‖) * t := by
      rw [sub_zero, abs_of_nonneg ht]
    _ = M ^ 2 * t * Real.exp (ω * t) * ‖V‖ := by ring

/-- An iterated integral over the time simplex has the sharp area factor
t squared over two under a uniform norm bound. -/
theorem norm_triangleIntegral_le
    (F : ℝ → ℝ → A) (t C : ℝ)
    (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hF : ∀ s ∈ Ι (0 : ℝ) t, ∀ r ∈ Ι (0 : ℝ) s,
      ‖F s r‖ ≤ C) :
    ‖∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, F s r‖
      ≤ C * t ^ 2 / 2 := by
  have hinner : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ r in (0 : ℝ)..s, F s r‖ ≤ C * s := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hF s (by simpa [uIoc_of_le ht] using hs))
    calc
      ‖∫ r in (0 : ℝ)..s, F s r‖ ≤ C * |s - 0| := h
      _ = C * s := by rw [sub_zero, abs_of_nonneg hs0]
  have hg : IntervalIntegrable (fun s : ℝ => C * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  have houter := intervalIntegral.norm_integral_le_of_norm_le ht
    (f := fun s => ∫ r in (0 : ℝ)..s, F s r)
    (g := fun s : ℝ => C * s)
    (by
      filter_upwards [] with s
      intro hs
      exact hinner s (by simpa [uIoc_of_le ht] using hs))
    hg
  calc
    ‖∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, F s r‖
        ≤ ∫ s in (0 : ℝ)..t, C * s := houter
    _ = C * ((t ^ 2 - 0 ^ 2) / 2) := by
      rw [intervalIntegral.integral_const_mul,
        integral_id]
    _ = C * t ^ 2 / 2 := by ring

/-- One time-ordered second Duhamel insertion. -/
noncomputable def orderedSecondDuhamel
    (P : ℝ → A) (V W : A) (t : ℝ) : A :=
  ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s,
    P (t - s) * V * P (s - r) * W * P r

/-- Scalar norm convolution over the two-dimensional time simplex. -/
noncomputable def simplexConvolution (P : ℝ → A) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖P (t - s)‖ *
    ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖

/-- Exact convolution-form estimate for one insertion order. -/
theorem norm_orderedSecondDuhamel_le_convolution
    (P : ℝ → A) (V W : A) (t : ℝ) (ht : 0 ≤ t)
    (hinner : ∀ s ∈ Ι (0 : ℝ) t,
      IntervalIntegrable
        (fun r => ‖P (s - r)‖ * ‖P r‖) volume 0 s)
    (houter : IntervalIntegrable
      (fun s => ‖P (t - s)‖ *
        ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖)
      volume 0 t) :
    ‖orderedSecondDuhamel P V W t‖
      ≤ ‖V‖ * ‖W‖ * simplexConvolution P t := by
  unfold orderedSecondDuhamel simplexConvolution
  have hinnerNorm : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ r in (0 : ℝ)..s,
          P (t - s) * V * P (s - r) * W * P r‖
        ≤ ‖V‖ * ‖W‖ * ‖P (t - s)‖ *
          ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖ := by
    intro s hs
    have hs0 : 0 ≤ s := by
      rw [uIoc_of_le ht] at hs
      exact hs.1.le
    let D := ‖V‖ * ‖W‖ * ‖P (t - s)‖
    have hbound : IntervalIntegrable
        (fun r => D * (‖P (s - r)‖ * ‖P r‖)) volume 0 s :=
      (hinner s hs).const_mul D
    have h := intervalIntegral.norm_integral_le_of_norm_le hs0
      (f := fun r => P (t - s) * V * P (s - r) * W * P r)
      (g := fun r => D * (‖P (s - r)‖ * ‖P r‖))
      (by
        filter_upwards [] with r
        intro hr
        calc
          ‖P (t - s) * V * P (s - r) * W * P r‖
              ≤ ‖P (t - s)‖ * ‖V‖ * ‖P (s - r)‖ *
                  ‖W‖ * ‖P r‖ := by
            calc
              ‖P (t - s) * V * P (s - r) * W * P r‖
                  ≤ ‖P (t - s) * V * P (s - r) * W‖ * ‖P r‖ :=
                    norm_mul_le _ _
              _ ≤ (‖P (t - s) * V * P (s - r)‖ * ‖W‖) * ‖P r‖ := by
                    gcongr
                    exact norm_mul_le _ _
              _ ≤ ((‖P (t - s) * V‖ * ‖P (s - r)‖) * ‖W‖) * ‖P r‖ := by
                    gcongr
                    exact norm_mul_le _ _
              _ ≤ (((‖P (t - s)‖ * ‖V‖) * ‖P (s - r)‖) * ‖W‖) * ‖P r‖ := by
                    gcongr
                    exact norm_mul_le _ _
          _ = D * (‖P (s - r)‖ * ‖P r‖) := by
            dsimp [D]
            ring)
      hbound
    simpa only [intervalIntegral.integral_const_mul] using h
  have hboundOuter : IntervalIntegrable
      (fun s => (‖V‖ * ‖W‖) *
        (‖P (t - s)‖ *
          ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖))
      volume 0 t :=
    houter.const_mul (‖V‖ * ‖W‖)
  have h := intervalIntegral.norm_integral_le_of_norm_le ht
    (f := fun s => ∫ r in (0 : ℝ)..s,
      P (t - s) * V * P (s - r) * W * P r)
    (g := fun s => (‖V‖ * ‖W‖) *
      (‖P (t - s)‖ *
        ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖))
    (by
      filter_upwards [] with s
      intro hs
      have hsU : s ∈ Ι (0 : ℝ) t := by
        simpa [uIoc_of_le ht] using hs
      exact (hinnerNorm s hsU).trans_eq (by ring))
    hboundOuter
  simpa only [intervalIntegral.integral_const_mul] using h

/-- Exact symmetric pair-response convolution estimate. -/
theorem norm_symmetricSecondDuhamel_le_convolution
    (P : ℝ → A) (V W : A) (t : ℝ) (ht : 0 ≤ t)
    (hinner : ∀ s ∈ Ι (0 : ℝ) t,
      IntervalIntegrable
        (fun r => ‖P (s - r)‖ * ‖P r‖) volume 0 s)
    (houter : IntervalIntegrable
      (fun s => ‖P (t - s)‖ *
        ∫ r in (0 : ℝ)..s, ‖P (s - r)‖ * ‖P r‖)
      volume 0 t) :
    ‖orderedSecondDuhamel P V W t + orderedSecondDuhamel P W V t‖
      ≤ 2 * ‖V‖ * ‖W‖ * simplexConvolution P t := by
  calc
    ‖orderedSecondDuhamel P V W t + orderedSecondDuhamel P W V t‖
        ≤ ‖orderedSecondDuhamel P V W t‖ +
          ‖orderedSecondDuhamel P W V t‖ := norm_add_le _ _
    _ ≤ (‖V‖ * ‖W‖ * simplexConvolution P t) +
          (‖W‖ * ‖V‖ * simplexConvolution P t) := by
      gcongr
      · exact norm_orderedSecondDuhamel_le_convolution
          P V W t ht hinner houter
      · exact norm_orderedSecondDuhamel_le_convolution
          P W V t ht hinner houter
    _ = 2 * ‖V‖ * ‖W‖ * simplexConvolution P t := by ring

/-- A time-ordered second response occupies one simplex of area t squared
over two. -/
theorem norm_orderedSecondDuhamel_le
    (P : ℝ → A) (V W : A) (t M ω : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hP : ∀ r, 0 ≤ r → ‖P r‖ ≤ M * Real.exp (ω * r)) :
    ‖orderedSecondDuhamel P V W t‖
      ≤ M ^ 3 * t ^ 2 / 2 * Real.exp (ω * t) * ‖V‖ * ‖W‖ := by
  unfold orderedSecondDuhamel
  let C := M ^ 3 * Real.exp (ω * t) * ‖V‖ * ‖W‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ s ∈ Ι (0 : ℝ) t, ∀ r ∈ Ι (0 : ℝ) s,
      ‖P (t - s) * V * P (s - r) * W * P r‖ ≤ C := by
    intro s hs r hr
    rw [uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s ≤ t := hs.2
    rw [uIoc_of_le hs0] at hr
    have hr0 : 0 ≤ r := hr.1.le
    have hrs : r ≤ s := hr.2
    calc
      ‖P (t - s) * V * P (s - r) * W * P r‖
          ≤ ‖P (t - s)‖ * ‖V‖ * ‖P (s - r)‖ * ‖W‖ * ‖P r‖ := by
        calc
          ‖P (t - s) * V * P (s - r) * W * P r‖
              ≤ ‖P (t - s) * V * P (s - r) * W‖ * ‖P r‖ :=
            norm_mul_le _ _
          _ ≤ (‖P (t - s) * V * P (s - r)‖ * ‖W‖) * ‖P r‖ := by
            gcongr
            exact norm_mul_le _ _
          _ ≤ ((‖P (t - s) * V‖ * ‖P (s - r)‖) * ‖W‖) * ‖P r‖ := by
            gcongr
            exact norm_mul_le _ _
          _ ≤ (((‖P (t - s)‖ * ‖V‖) * ‖P (s - r)‖) * ‖W‖) * ‖P r‖ := by
            gcongr
            exact norm_mul_le _ _
      _ ≤ (M * Real.exp (ω * (t - s))) * ‖V‖ *
            (M * Real.exp (ω * (s - r))) * ‖W‖ *
            (M * Real.exp (ω * r)) := by
        gcongr
        · exact hP (t - s) (sub_nonneg.mpr hst)
        · exact hP (s - r) (sub_nonneg.mpr hrs)
        · exact hP r hr0
      _ = C := by
        dsimp [C]
        calc
          (M * Real.exp (ω * (t - s))) * ‖V‖ *
                (M * Real.exp (ω * (s - r))) * ‖W‖ *
                (M * Real.exp (ω * r))
              = M ^ 3 * ‖V‖ * ‖W‖ *
                (Real.exp (ω * (t - s)) *
                  Real.exp (ω * (s - r)) * Real.exp (ω * r)) := by ring
          _ = M ^ 3 * ‖V‖ * ‖W‖ *
                Real.exp (ω * (t - s) + ω * (s - r) + ω * r) := by
            rw [Real.exp_add, Real.exp_add]
          _ = M ^ 3 * Real.exp (ω * t) * ‖V‖ * ‖W‖ := by
            rw [show ω * (t - s) + ω * (s - r) + ω * r = ω * t by ring]
            ring
  have htriangle := norm_triangleIntegral_le
    (F := fun s r => P (t - s) * V * P (s - r) * W * P r)
    t C ht hC (by
      intro s hs r hr
      exact hpoint s hs r hr)
  calc
    ‖∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s,
        P (t - s) * V * P (s - r) * W * P r‖
        ≤ C * t ^ 2 / 2 := htriangle
    _ = M ^ 3 * t ^ 2 / 2 * Real.exp (ω * t) * ‖V‖ * ‖W‖ := by
      dsimp [C]
      ring

/-- The symmetric pair response is the sum of the two insertion orders. -/
noncomputable def symmetricSecondDuhamel
    (P : ℝ → A) (V W : A) (t : ℝ) : A :=
  orderedSecondDuhamel P V W t + orderedSecondDuhamel P W V t

/-- Exact symmetric pair-response exponential-growth estimate. -/
theorem norm_symmetricSecondDuhamel_le
    (P : ℝ → A) (V W : A) (t M ω : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hP : ∀ r, 0 ≤ r → ‖P r‖ ≤ M * Real.exp (ω * r)) :
    ‖symmetricSecondDuhamel P V W t‖
      ≤ M ^ 3 * t ^ 2 * Real.exp (ω * t) * ‖V‖ * ‖W‖ := by
  unfold symmetricSecondDuhamel
  calc
    ‖orderedSecondDuhamel P V W t + orderedSecondDuhamel P W V t‖
        ≤ ‖orderedSecondDuhamel P V W t‖ +
          ‖orderedSecondDuhamel P W V t‖ := norm_add_le _ _
    _ ≤ (M ^ 3 * t ^ 2 / 2 * Real.exp (ω * t) * ‖V‖ * ‖W‖) +
          (M ^ 3 * t ^ 2 / 2 * Real.exp (ω * t) * ‖W‖ * ‖V‖) := by
      gcongr
      · exact norm_orderedSecondDuhamel_le P V W t M ω ht hM hP
      · exact norm_orderedSecondDuhamel_le P W V t M ω ht hM hP
    _ = M ^ 3 * t ^ 2 * Real.exp (ω * t) * ‖V‖ * ‖W‖ := by ring

end WeightedDuhamelConvolutionBounds

end NCG
