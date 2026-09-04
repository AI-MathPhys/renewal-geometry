/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3FiniteDifferenceConsistencyExact
import NCG.Grand.UniformFiniteDifferenceRemainderExact

/-!
# Uniform consistency of the A3 square-root energy

The twelve-root square-root energy converges uniformly over all base points
when the actual derivative is uniformly continuous. A finite-channel reverse
triangle estimate prevents any hidden dependence on the size of the gradient.
The missing periodic interpolation/compactness argument for arbitrary discrete
unit-ball functions is separate from this smooth-test consistency theorem.
-/

open Filter
open scoped Topology BigOperators

namespace NCG.A3UniformEnergyConsistency

open A3FiniteDifferenceConsistency UniformFiniteDifferenceRemainder

noncomputable section

theorem root_norm_sq (r : Fin 12) : ‖root r‖ ^ 2 = 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases r <;> norm_num [root, a3Roots, Fin.sum_univ_succ]

theorem root_norm_le_two (r : Fin 12) : ‖root r‖ ≤ 2 := by
  have := root_norm_sq r
  nlinarith [norm_nonneg (root r)]

/-- Stability in the twelve difference-quotient channels, uniformly in the gradient. -/
theorem sqrt_energy_error_le
    (f : Space → ℝ) (x v : Space) (h ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ r, |rootDifference f x h r - inner ℝ v (root r)| ≤ ε) :
    |Real.sqrt (sampledEnergy f x h) - ‖v‖| ≤ 2 * ε := by
  let a : EuclideanSpace ℝ (Fin 12) := WithLp.toLp 2 (rootDifference f x h)
  let b : EuclideanSpace ℝ (Fin 12) := WithLp.toLp 2 (fun r => inner ℝ v (root r))
  have ha : ‖a‖ ^ 2 = 8 * sampledEnergy f x h := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ r, rootDifference f x h r ^ 2) = 8 * ((∑ r, rootDifference f x h r ^ 2) / 8)
    ring
  have hb : ‖b‖ ^ 2 = 8 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have ht := tight_frame_energy v
    change (∑ r, (inner ℝ v (root r)) ^ 2) = 8 * ‖v‖ ^ 2
    linarith
  have hdiff : ‖a - b‖ ^ 2 ≤ 12 * ε ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin 12, ε ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        change (rootDifference f x h r - inner ℝ v (root r)) ^ 2 ≤ ε ^ 2
        have he := herr r
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr he
      _ = 12 * ε ^ 2 := by simp
  have hdiff' : ‖a - b‖ ≤ 4 * ε := by
    nlinarith [norm_nonneg (a - b)]
  have hc : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hcpos : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  have hclower : 2 ≤ Real.sqrt 8 := by nlinarith
  have henergy : Real.sqrt (sampledEnergy f x h) ^ 2 = sampledEnergy f x h :=
    Real.sq_sqrt (sampledEnergy_nonneg f x h)
  have hna : ‖a‖ = Real.sqrt 8 * Real.sqrt (sampledEnergy f x h) := by
    apply (sq_eq_sq₀ (norm_nonneg a) (mul_nonneg hcpos (Real.sqrt_nonneg _))).mp
    rw [mul_pow, hc, henergy]
    exact ha
  have hnb : ‖b‖ = Real.sqrt 8 * ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg b) (mul_nonneg hcpos (norm_nonneg v))).mp
    rw [mul_pow, hc]
    exact hb
  have hnorm := (abs_norm_sub_norm_le a b).trans hdiff'
  rw [hna, hnb, ← mul_sub, abs_mul, abs_of_nonneg hcpos] at hnorm
  nlinarith [abs_nonneg (Real.sqrt (sampledEnergy f x h) - ‖v‖)]

/-- A uniform estimate for all spatial base points at sufficiently small positive mesh. -/
theorem uniform_sqrt_energy_consistency
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : UniformContinuous (fun x => innerSL ℝ (v x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ x : Space,
      |Real.sqrt (sampledEnergy f x h) - ‖v x‖| < ε := by
  obtain ⟨δ, hδ, hbound⟩ := uniform_bounded_direction_difference f
    (fun x => innerSL ℝ (v x)) hf hdf 2 (by norm_num) (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hsmall x
  have herr : ∀ r, |rootDifference f x h r - inner ℝ (v x) (root r)| ≤ ε / 3 := by
    intro r
    simpa only [rootDifference, innerSL_apply_apply] using
      hbound h hh hsmall x (root r) (root_norm_le_two r)
  exact (sqrt_energy_error_le f x (v x) h (ε / 3) (by positivity) herr).trans_lt (by linarith)

theorem tendstoUniformly_sqrt_sampledEnergy
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : UniformContinuous (fun x => innerSL ℝ (v x))) :
    TendstoUniformly (fun h x => Real.sqrt (sampledEnergy f x h))
      (fun x => ‖v x‖) (𝓝[>] (0 : ℝ)) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := uniform_sqrt_energy_consistency f v hf hdf ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hsmall
  intro x
  simpa only [Real.dist_eq, abs_sub_comm] using hbound h hh hsmall x

end

end NCG.A3UniformEnergyConsistency
