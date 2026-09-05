/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform continuity from a bounded periodic fundamental domain

A continuous periodic field is uniformly continuous when every point can be
translated into one fixed bounded set. The proof uses Heine--Cantor on an
enlarged compact ball, and translates both nearby points by the same period.
-/

open Metric

namespace NCG.PeriodicUniformContinuity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [PseudoMetricSpace F]

theorem uniformContinuous_of_bounded_periodic_cover
    (P : AddSubgroup E) (f : E → F) (hf : Continuous f)
    (hperiod : ∀ p : P, ∀ x : E, f (x + p) = f x)
    (R : ℝ) (hcover : ∀ x : E, ∃ p : P, ‖x - p‖ ≤ R) :
    UniformContinuous f := by
  obtain ⟨p₀, hp₀⟩ := hcover 0
  have hR : 0 ≤ R := (norm_nonneg _).trans hp₀
  have huc := (isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
    hf.continuousOn
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro x y hxy
  obtain ⟨p, hp⟩ := hcover x
  have hx : x - p ∈ closedBall (0 : E) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hdist : dist (x - p) (y - p) = dist x y := by
    simp only [dist_eq_norm]
    congr 1
    abel
  have hy : y - p ∈ closedBall (0 : E) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    have htri : ‖y - p‖ ≤ ‖y - x‖ + ‖x - p‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (y - x) (x - p)
    have hnear : ‖y - x‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact lt_of_lt_of_le hxy (min_le_right _ _)
    linarith
  have hsmall : dist (x - p) (y - p) < δ := by
    rw [hdist]
    exact lt_of_lt_of_le hxy (min_le_left _ _)
  have hresult := hmod (x - p) hx (y - p) hy hsmall
  have hxperiod : f (x - p) = f x := by
    simpa only [sub_add_cancel] using (hperiod p (x - p)).symm
  have hyperiod : f (y - p) = f y := by
    simpa only [sub_add_cancel] using (hperiod p (y - p)).symm
  simpa only [hxperiod, hyperiod] using hresult

end NCG.PeriodicUniformContinuity
