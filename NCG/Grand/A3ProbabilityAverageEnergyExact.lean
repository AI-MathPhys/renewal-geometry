/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3FiniteDifferenceConsistencyExact
import Mathlib

/-!
# Probability averaging preserves the sharp A3 finite-difference energy bound

The twelve difference quotients form a Euclidean vector. Its Bochner average
commutes with taking difference quotients, and its norm is at most the common
bound. This retains the exact energy constant one, with no dimension loss.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace NCG.A3ProbabilityAverageEnergy

open A3FiniteDifferenceConsistency

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rootDifference_integral
    (μ : Measure Ω) (F : Ω → Space → ℝ)
    (hF : ∀ p, Integrable (fun ω => F ω p) μ) (p : Space) (h : ℝ) (r : Fin 12) :
    rootDifference (fun x => ∫ ω, F ω x ∂μ) p h r =
      ∫ ω, rootDifference (F ω) p h r ∂μ := by
  unfold rootDifference
  rw [integral_div, integral_sub (hF _) (hF _)]

theorem sampledEnergy_probability_average_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Space → ℝ)
    (hF : ∀ p, Integrable (fun ω => F ω p) μ) (p : Space) (h : ℝ)
    (henergy : ∀ᵐ ω ∂μ, sampledEnergy (F ω) p h ≤ 1) :
    sampledEnergy (fun x => ∫ ω, F ω x ∂μ) p h ≤ 1 := by
  let A : Ω → EuclideanSpace ℝ (Fin 12) :=
    fun ω => WithLp.toLp 2 (rootDifference (F ω) p h)
  let B : EuclideanSpace ℝ (Fin 12) :=
    WithLp.toLp 2 (rootDifference (fun x => ∫ ω, F ω x ∂μ) p h)
  have hAi (r : Fin 12) : Integrable (fun ω => A ω r) μ :=
    ((hF (p + h • root r)).sub (hF p)).div_const h
  have hB : B = ∫ ω, A ω ∂μ := by
    ext r
    rw [eval_integral_piLp hAi]
    exact rootDifference_integral μ F hF p h r
  have hsq (ω : Ω) : ‖A ω‖ ^ 2 = 8 * sampledEnergy (F ω) p h := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ r, rootDifference (F ω) p h r ^ 2) =
      8 * ((∑ r, rootDifference (F ω) p h r ^ 2) / 8)
    ring
  have hBs : ‖B‖ ^ 2 = 8 * sampledEnergy (fun x => ∫ ω, F ω x ∂μ) p h := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ r, rootDifference (fun x => ∫ ω, F ω x ∂μ) p h r ^ 2) =
      8 * ((∑ r, rootDifference (fun x => ∫ ω, F ω x ∂μ) p h r ^ 2) / 8)
    ring
  have hsqrt : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hAbound : ∀ᵐ ω ∂μ, ‖A ω‖ ≤ Real.sqrt 8 := by
    filter_upwards [henergy] with ω hω
    have hs := hsq ω
    nlinarith [norm_nonneg (A ω), Real.sqrt_nonneg 8]
  have hnorm : ‖B‖ ≤ Real.sqrt 8 := by
    rw [hB]
    simpa using norm_integral_le_of_norm_le_const hAbound
  nlinarith [norm_nonneg B]

end

end NCG.A3ProbabilityAverageEnergy
