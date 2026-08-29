/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Insertion-path locality

This file proves `thm:GTLOC-insertion-path`.  A block collar for a semigroup
is propagated through one- and two-insertion Duhamel words.  The second-order
constant is the exact volume `t² / 2` of the ordered time simplex.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace NCG
namespace InsertionPathLocality

universe u v

variable {Region : Type u}
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Semigroup blocks between physical regions, together with the metric used
by the collar estimate.  The theorem only needs the compressed blocks, so it
does not impose an artificial global projection model. -/
structure BlockPacket (Region : Type u) (E : Type v)
    [NormedAddCommGroup E] [NormedSpace ℂ E] where
  block : Region → Region → ℝ → (E →L[ℂ] E)
  dist : Region → Region → ℝ

/-- The manuscript's `(C, ω, α)` block-collar condition. -/
def HasBlockCollar (P : BlockPacket Region E) (C omega alpha : ℝ) : Prop :=
  ∀ X Y : Region, ∀ r : ℝ, 0 ≤ r →
    ‖P.block Y X r‖ ≤ C * Real.exp (omega * r - alpha * P.dist X Y)

/-- The compressed word with one insertion supported in `Z`. -/
def firstWord (P : BlockPacket Region E) (Y Z X : Region)
    (V : E →L[ℂ] E) (t s : ℝ) : E →L[ℂ] E :=
  ((P.block Y Z (t - s)).comp V).comp (P.block Z X s)

/-- First Duhamel response compressed from `X` to `Y`. -/
def firstResponse (P : BlockPacket Region E) (Y Z X : Region)
    (V : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  ∫ s in 0..t, firstWord P Y Z X V t s

/-- The ordered two-insertion word which visits `ZW` first and `ZV` second. -/
def orderedPairWord (P : BlockPacket Region E) (Y ZV ZW X : Region)
    (V W : E →L[ℂ] E) (t u s : ℝ) : E →L[ℂ] E :=
  ((((P.block Y ZV (t - u)).comp V).comp
      (P.block ZV ZW (u - s))).comp W).comp (P.block ZW X s)

/-- Ordered second Duhamel response over `0 ≤ s ≤ u ≤ t`. -/
def orderedPairResponse (P : BlockPacket Region E) (Y ZV ZW X : Region)
    (V W : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  ∫ u in 0..t, ∫ s in 0..u, orderedPairWord P Y ZV ZW X V W t u s

/-- Symmetric pair response: the sum of the two insertion orders. -/
def pairResponse (P : BlockPacket Region E) (Y ZV ZW X : Region)
    (V W : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  orderedPairResponse P Y ZV ZW X V W t +
    orderedPairResponse P Y ZW ZV X W V t

/-- Length of the ordered route `X → ZW → ZV → Y`. -/
def orderedPathLength (P : BlockPacket Region E) (Y ZV ZW X : Region) : ℝ :=
  P.dist ZV Y + P.dist ZW ZV + P.dist X ZW

private theorem firstWord_norm_bound
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C)
    (hcollar : HasBlockCollar P C omega alpha)
    (Y Z X : Region) (V : E →L[ℂ] E) (t s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) t) :
    ‖firstWord P Y Z X V t s‖ ≤
      C ^ 2 * Real.exp (omega * t) * ‖V‖ *
        Real.exp (-alpha * (P.dist Z Y + P.dist X Z)) := by
  have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
  have hs0 : 0 ≤ s := hs.1
  have hA := hcollar Z Y (t - s) hts
  have hB := hcollar X Z s hs0
  have ha : 0 ≤ C * Real.exp (omega * (t - s) - alpha * P.dist Z Y) :=
    mul_nonneg hC (Real.exp_pos _).le
  calc
    ‖firstWord P Y Z X V t s‖
        ≤ (‖P.block Y Z (t - s)‖ * ‖V‖) * ‖P.block Z X s‖ := by
          unfold firstWord
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (C * Real.exp (omega * (t - s) - alpha * P.dist Z Y) * ‖V‖) *
          (C * Real.exp (omega * s - alpha * P.dist X Z)) := by
          exact (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (norm_nonneg V)) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hB (mul_nonneg ha (norm_nonneg V)))
    _ = C ^ 2 * Real.exp (omega * t) * ‖V‖ *
          Real.exp (-alpha * (P.dist Z Y + P.dist X Z)) := by
          calc
            _ = C ^ 2 * ‖V‖ *
                (Real.exp (omega * (t - s) - alpha * P.dist Z Y) *
                  Real.exp (omega * s - alpha * P.dist X Z)) := by ring
            _ = C ^ 2 * ‖V‖ * Real.exp
                ((omega * (t - s) - alpha * P.dist Z Y) +
                  (omega * s - alpha * P.dist X Z)) := by rw [Real.exp_add]
            _ = _ := by
              rw [show (omega * (t - s) - alpha * P.dist Z Y) +
                    (omega * s - alpha * P.dist X Z) =
                    omega * t + (-alpha * (P.dist Z Y + P.dist X Z)) by ring,
                  Real.exp_add]
              ring

/-- **First insertion-path bound.**  A supported insertion forces the route
`X → Z → Y`, so the two collar exponents add. -/
theorem first_response_bound
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C) (hcollar : HasBlockCollar P C omega alpha)
    (Y Z X : Region) (V : E →L[ℂ] E) (t : ℝ) (ht : 0 ≤ t) :
    ‖firstResponse P Y Z X V t‖ ≤
      C ^ 2 * t * Real.exp (omega * t) * ‖V‖ *
        Real.exp (-alpha * (P.dist Z Y + P.dist X Z)) := by
  rw [firstResponse]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t)
    (C := C ^ 2 * Real.exp (omega * t) * ‖V‖ *
      Real.exp (-alpha * (P.dist Z Y + P.dist X Z)))
    (f := fun s => firstWord P Y Z X V t s)
    (fun s hs => firstWord_norm_bound P C omega alpha hC hcollar Y Z X V t s
      (by
        have hs' : s ∈ Ioc (0 : ℝ) t := by simpa [uIoc_of_le ht] using hs
        exact ⟨hs'.1.le, hs'.2⟩))
  simp only [sub_zero, abs_of_nonneg ht] at h
  calc
    ‖∫ s in 0..t, firstWord P Y Z X V t s‖
        ≤ (C ^ 2 * Real.exp (omega * t) * ‖V‖ *
            Real.exp (-alpha * (P.dist Z Y + P.dist X Z))) * t := h
    _ = C ^ 2 * t * Real.exp (omega * t) * ‖V‖ *
          Real.exp (-alpha * (P.dist Z Y + P.dist X Z)) := by ring

private theorem orderedPairWord_norm_bound
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C)
    (hcollar : HasBlockCollar P C omega alpha)
    (Y ZV ZW X : Region) (V W : E →L[ℂ] E) (t u s : ℝ)
    (hu : u ∈ Icc (0 : ℝ) t) (hs : s ∈ Icc (0 : ℝ) u) :
    ‖orderedPairWord P Y ZV ZW X V W t u s‖ ≤
      C ^ 3 * Real.exp (omega * t) * ‖V‖ * ‖W‖ *
        Real.exp (-alpha * orderedPathLength P Y ZV ZW X) := by
  have htu : 0 ≤ t - u := sub_nonneg.mpr hu.2
  have hus : 0 ≤ u - s := sub_nonneg.mpr hs.2
  have hs0 : 0 ≤ s := hs.1
  have hA := hcollar ZV Y (t - u) htu
  have hB := hcollar ZW ZV (u - s) hus
  have hD := hcollar X ZW s hs0
  have ha : 0 ≤ C * Real.exp (omega * (t - u) - alpha * P.dist ZV Y) :=
    mul_nonneg hC (Real.exp_pos _).le
  calc
    ‖orderedPairWord P Y ZV ZW X V W t u s‖
        ≤ (((‖P.block Y ZV (t - u)‖ * ‖V‖) *
            ‖P.block ZV ZW (u - s)‖) * ‖W‖) * ‖P.block ZW X s‖ := by
          unfold orderedPairWord
          calc
            ‖(((((P.block Y ZV (t - u)).comp V).comp
                (P.block ZV ZW (u - s))).comp W).comp (P.block ZW X s))‖
                ≤ ‖((((P.block Y ZV (t - u)).comp V).comp
                    (P.block ZV ZW (u - s))).comp W)‖ * ‖P.block ZW X s‖ :=
                      ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ (‖(((P.block Y ZV (t - u)).comp V).comp
                    (P.block ZV ZW (u - s)))‖ * ‖W‖) * ‖P.block ZW X s‖ := by
                      gcongr
                      exact ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ ((‖(P.block Y ZV (t - u)).comp V‖ *
                    ‖P.block ZV ZW (u - s)‖) * ‖W‖) * ‖P.block ZW X s‖ := by
                      gcongr
                      exact ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ (((‖P.block Y ZV (t - u)‖ * ‖V‖) *
                    ‖P.block ZV ZW (u - s)‖) * ‖W‖) * ‖P.block ZW X s‖ := by
                      gcongr
                      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (((C * Real.exp (omega * (t - u) - alpha * P.dist ZV Y) * ‖V‖) *
          (C * Real.exp (omega * (u - s) - alpha * P.dist ZW ZV))) * ‖W‖) *
          (C * Real.exp (omega * s - alpha * P.dist X ZW)) := by
          have h1 := mul_le_mul_of_nonneg_right hA (norm_nonneg V)
          have h1 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (P.block ZV ZW (u - s)))
          have h1 := mul_le_mul_of_nonneg_right h1 (norm_nonneg W)
          have h1 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (P.block ZW X s))
          have h2 := mul_le_mul_of_nonneg_left hB (mul_nonneg ha (norm_nonneg V))
          have h2 := mul_le_mul_of_nonneg_right h2 (norm_nonneg W)
          have h2 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (P.block ZW X s))
          have habvw : 0 ≤ ((C * Real.exp (omega * (t - u) - alpha * P.dist ZV Y) * ‖V‖) *
              (C * Real.exp (omega * (u - s) - alpha * P.dist ZW ZV))) * ‖W‖ := by
            positivity
          have h3 := mul_le_mul_of_nonneg_left hD habvw
          exact h1.trans (h2.trans h3)
    _ = C ^ 3 * Real.exp (omega * t) * ‖V‖ * ‖W‖ *
          Real.exp (-alpha * orderedPathLength P Y ZV ZW X) := by
          unfold orderedPathLength
          calc
            _ = C ^ 3 * ‖V‖ * ‖W‖ *
                (Real.exp (omega * (t - u) - alpha * P.dist ZV Y) *
                  Real.exp (omega * (u - s) - alpha * P.dist ZW ZV) *
                  Real.exp (omega * s - alpha * P.dist X ZW)) := by ring
            _ = C ^ 3 * ‖V‖ * ‖W‖ * Real.exp
                ((omega * (t - u) - alpha * P.dist ZV Y) +
                  (omega * (u - s) - alpha * P.dist ZW ZV) +
                  (omega * s - alpha * P.dist X ZW)) := by
                    rw [Real.exp_add, Real.exp_add]
            _ = _ := by
              rw [show (omega * (t - u) - alpha * P.dist ZV Y) +
                    (omega * (u - s) - alpha * P.dist ZW ZV) +
                    (omega * s - alpha * P.dist X ZW) =
                    omega * t +
                      (-alpha * (P.dist ZV Y + P.dist ZW ZV + P.dist X ZW)) by ring,
                  Real.exp_add]
              ring

private theorem ordered_pair_response_bound
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C) (hcollar : HasBlockCollar P C omega alpha)
    (Y ZV ZW X : Region) (V W : E →L[ℂ] E) (t : ℝ) (ht : 0 ≤ t) :
    ‖orderedPairResponse P Y ZV ZW X V W t‖ ≤
      (C ^ 3 * Real.exp (omega * t) * ‖V‖ * ‖W‖ *
        Real.exp (-alpha * orderedPathLength P Y ZV ZW X)) * (t ^ 2 / 2) := by
  let M : ℝ := C ^ 3 * Real.exp (omega * t) * ‖V‖ * ‖W‖ *
    Real.exp (-alpha * orderedPathLength P Y ZV ZW X)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hinner : ∀ u ∈ Icc (0 : ℝ) t,
      ‖∫ s in 0..u, orderedPairWord P Y ZV ZW X V W t u s‖ ≤ M * u := by
    intro u hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := u) (C := M)
      (f := fun s => orderedPairWord P Y ZV ZW X V W t u s)
      (fun s hs => orderedPairWord_norm_bound P C omega alpha hC hcollar
        Y ZV ZW X V W t u s hu (by
          have hs' : s ∈ Ioc (0 : ℝ) u := by simpa [uIoc_of_le hu.1] using hs
          exact ⟨hs'.1.le, hs'.2⟩))
    simp only [sub_zero, abs_of_nonneg hu.1] at h
    exact h
  rw [orderedPairResponse]
  have hbound : IntervalIntegrable (fun u : ℝ => M * u) volume 0 t := by
    exact (continuous_const.mul continuous_id).intervalIntegrable 0 t
  have h := intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall fun u hu => hinner u ⟨hu.1.le, hu.2⟩) hbound
  rw [intervalIntegral.integral_const_mul, integral_id] at h
  simpa [M] using h

/-- **Pair insertion-path bound.**  The two orders follow the two ordered
routes.  Each ordered simplex has volume `t²/2`; adding their norm bounds gives
exactly the manuscript's parenthesized sum of route weights. -/
theorem pair_response_bound
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C) (hcollar : HasBlockCollar P C omega alpha)
    (Y ZV ZW X : Region) (V W : E →L[ℂ] E) (t : ℝ) (ht : 0 ≤ t) :
    ‖pairResponse P Y ZV ZW X V W t‖ ≤
      (C ^ 3 * t ^ 2 * Real.exp (omega * t) / 2) * ‖V‖ * ‖W‖ *
        (Real.exp (-alpha * orderedPathLength P Y ZV ZW X) +
          Real.exp (-alpha * orderedPathLength P Y ZW ZV X)) := by
  calc
    ‖pairResponse P Y ZV ZW X V W t‖
        ≤ ‖orderedPairResponse P Y ZV ZW X V W t‖ +
            ‖orderedPairResponse P Y ZW ZV X W V t‖ := by
              unfold pairResponse
              exact norm_add_le _ _
    _ ≤ (C ^ 3 * Real.exp (omega * t) * ‖V‖ * ‖W‖ *
            Real.exp (-alpha * orderedPathLength P Y ZV ZW X)) * (t ^ 2 / 2) +
          (C ^ 3 * Real.exp (omega * t) * ‖W‖ * ‖V‖ *
            Real.exp (-alpha * orderedPathLength P Y ZW ZV X)) * (t ^ 2 / 2) := by
              gcongr
              · exact ordered_pair_response_bound P C omega alpha hC hcollar
                  Y ZV ZW X V W t ht
              · exact ordered_pair_response_bound P C omega alpha hC hcollar
                  Y ZW ZV X W V t ht
    _ = (C ^ 3 * t ^ 2 * Real.exp (omega * t) / 2) * ‖V‖ * ‖W‖ *
          (Real.exp (-alpha * orderedPathLength P Y ZV ZW X) +
            Real.exp (-alpha * orderedPathLength P Y ZW ZV X)) := by ring

/-- Bundled exact realization of `thm:GTLOC-insertion-path`. -/
theorem insertion_path_locality
    (P : BlockPacket Region E) (C omega alpha : ℝ)
    (hC : 0 ≤ C) (hcollar : HasBlockCollar P C omega alpha)
    (Y Z ZV ZW X : Region) (V W : E →L[ℂ] E) (t : ℝ) (ht : 0 ≤ t) :
    ‖firstResponse P Y Z X V t‖ ≤
        C ^ 2 * t * Real.exp (omega * t) * ‖V‖ *
          Real.exp (-alpha * (P.dist Z Y + P.dist X Z)) ∧
    ‖pairResponse P Y ZV ZW X V W t‖ ≤
        (C ^ 3 * t ^ 2 * Real.exp (omega * t) / 2) * ‖V‖ * ‖W‖ *
          (Real.exp (-alpha * orderedPathLength P Y ZV ZW X) +
            Real.exp (-alpha * orderedPathLength P Y ZW ZV X)) :=
  ⟨first_response_bound P C omega alpha hC hcollar Y Z X V t ht,
    pair_response_bound P C omega alpha hC hcollar Y ZV ZW X V W t ht⟩

end InsertionPathLocality
end NCG
