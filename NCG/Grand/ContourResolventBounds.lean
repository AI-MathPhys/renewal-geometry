/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BanachAlgebraResolventStability
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Uniform resolvent bounds on compact contours

A resolvent is continuous on the resolvent set.  Hence a compact contour contained in that set
automatically carries a finite uniform resolvent bound.  This file removes the corresponding
manual limit-bound premise from compact-screen applications.
-/

open Complex Set Filter Topology

noncomputable section

namespace NCG.ResolventStability

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A circle contained in the resolvent set admits a nonnegative uniform resolvent-norm bound. -/
theorem exists_circle_resolvent_norm_bound
    (a : A) (center : ℂ) (radius : ℝ)
    (hunit : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ a) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Metric.sphere center radius, ‖resolvent a z‖ ≤ M := by
  have hcontinuous : ContinuousOn (fun z ↦ ‖resolvent a z‖)
      (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hunit z hz)).continuousAt.norm.continuousWithinAt
  have hbounded : BddAbove
      ((fun z ↦ ‖resolvent a z‖) '' Metric.sphere center radius) :=
    (isCompact_sphere center radius).bddAbove_image hcontinuous
  obtain ⟨M, hM⟩ := hbounded
  refine ⟨max M 0, le_max_right M 0, ?_⟩
  intro z hz
  exact (hM ⟨z, hz, rfl⟩).trans (le_max_left M 0)

/-- Norm convergence makes a uniformly bounded limiting circle resolvent uniformly bounded
and defined at every sufficiently late cutoff. This is the quantitative Neumann-series step. -/
theorem eventually_circle_resolvent_bound_of_tendsto
    {I : Type*} {l : Filter I} (aSeq : I → A) (a : A)
    (ha : Tendsto aSeq l (nhds a))
    (center : ℂ) (radius M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ a)
    (hbound : ∀ z ∈ Metric.sphere center radius, ‖resolvent a z‖ ≤ M) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ᶠ i in l, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (aSeq i) ∧ ‖resolvent (aSeq i) z‖ ≤ N := by
  let B : ℝ := M + 1
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hdiff : ∀ᶠ i in l, ‖aSeq i - a‖ < 1 / (2 * B) := by
    have hzero : Tendsto (fun i ↦ ‖aSeq i - a‖) l (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp ha
    exact hzero.eventually (gt_mem_nhds (by positivity : 0 < 1 / (2 * B)))
  refine ⟨(‖(1 : A)‖ + 1) * B, by positivity, ?_⟩
  filter_upwards [hdiff] with i hi
  intro z hz
  let b : A := algebraMap ℂ A z - a
  let d : A := aSeq i - a
  let r : A := resolvent a z
  let x : A := r * d
  have hb : IsUnit b := hunit z hz
  have hbr : b * r = 1 := by
    exact Ring.mul_inverse_cancel b hb
  have hrbound : ‖r‖ ≤ B := (hbound z hz).trans (by dsimp [B]; linarith)
  have hdbound : ‖d‖ < 1 / (2 * B) := by simpa [d] using hi
  have hxhalf : ‖x‖ < 1 / 2 := by
    calc
      ‖x‖ ≤ ‖r‖ * ‖d‖ := norm_mul_le _ _
      _ ≤ B * ‖d‖ := mul_le_mul_of_nonneg_right hrbound (norm_nonneg d)
      _ < B * (1 / (2 * B)) := mul_lt_mul_of_pos_left hdbound hBpos
      _ = 1 / 2 := by field_simp
  have hx : ‖x‖ < 1 := hxhalf.trans (by norm_num)
  have hfactor :
      algebraMap ℂ A z - aSeq i = b * (1 - x) := by
    calc
      algebraMap ℂ A z - aSeq i = b - d := by simp [b, d]
      _ = b - (b * r) * d := by rw [hbr, one_mul]
      _ = b * (1 - x) := by simp only [mul_sub, mul_one, x, mul_assoc]
  have hone : IsUnit (1 - x) := isUnit_one_sub_of_norm_lt_one hx
  have hstage : z ∈ resolventSet ℂ (aSeq i) := by
    change IsUnit (algebraMap ℂ A z - aSeq i)
    rw [hfactor]
    exact hb.mul hone
  refine ⟨hstage, ?_⟩
  have hinvOne : ‖Ring.inverse (1 - x)‖ ≤ ‖(1 : A)‖ + 1 := by
    rw [← geom_series_eq_inverse x hx]
    have hgeom := tsum_geometric_le_of_norm_lt_one x hx
    have hinv : (1 - ‖x‖)⁻¹ ≤ (2 : ℝ) := by
      apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr hx)).mpr
      nlinarith
    exact hgeom.trans (by linarith)
  rw [resolvent, hfactor, Ring.inverse_mul (Or.inl hb)]
  calc
    ‖Ring.inverse (1 - x) * Ring.inverse b‖ ≤
        ‖Ring.inverse (1 - x)‖ * ‖Ring.inverse b‖ := norm_mul_le _ _
    _ ≤ (‖(1 : A)‖ + 1) * B := by
      apply mul_le_mul hinvOne
      · simpa [r, resolvent, b] using hrbound
      · exact norm_nonneg _
      · positivity
end NCG.ResolventStability
