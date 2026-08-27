/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mixed marginals and absolute reflected kernels

This file gives the two explicit counterexamples used in the conditional-Gaussian part of the
Gran-Tensor manuscript.  The first keeps both scalar marginals fixed while changing their coupling;
the second keeps every normalized fermionic datum fixed while its positive line weight diverges.
-/

open scoped BigOperators Topology

namespace NCG.SMQGMarginalAndAbsoluteKernelCounterexamples

/-- Bosonic line weights in the two-history example. -/
def alignedWeight : Fin 2 → ℝ := ![1, 2]

/-- The same bosonic marginal in the crossed coupling. -/
def crossedWeight : Fin 2 → ℝ := ![1, 2]

/-- Two distinct positive scalar covariance packets. -/
def alignedCovariance : Fin 2 → ℝ := ![1, 3]

/-- The covariance packets coupled in the opposite order. -/
def crossedCovariance : Fin 2 → ℝ := ![3, 1]

/-- The two couplings have identical marginals (hence identical separate one-point statistics),
but their mixed reflected coefficient is different.  This is the finite witness in
`cth:SMQG-marginals-no-mixture`. -/
theorem separate_marginals_do_not_determine_mixture :
    (∀ f : ℝ → ℝ,
      ∑ i, f (alignedWeight i) = ∑ i, f (crossedWeight i)) ∧
    (∀ g : ℝ → ℝ,
      ∑ i, g (alignedCovariance i) = ∑ i, g (crossedCovariance i)) ∧
    (∀ i, 0 < alignedWeight i ∧ 0 < crossedWeight i ∧
      0 < alignedCovariance i ∧ 0 < crossedCovariance i) ∧
    (∑ i, alignedWeight i * alignedCovariance i) ≠
      ∑ i, crossedWeight i * crossedCovariance i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    simp [alignedWeight, crossedWeight, Fin.sum_univ_two]
  · intro g
    simp [alignedCovariance, crossedCovariance, Fin.sum_univ_two, add_comm]
  · intro i
    fin_cases i <;>
      norm_num [alignedWeight, crossedWeight, alignedCovariance, crossedCovariance]
  · norm_num [alignedWeight, crossedWeight, alignedCovariance, crossedCovariance,
      Fin.sum_univ_two]

/-- The normalized covariance and word map are constant in the absolute-kernel counterexample. -/
def normalizedKernel (_ : ℕ) : ℝ := 1

/-- The unnormalized positive line weight `q_n = exp n`. -/
noncomputable def absoluteLineWeight (n : ℕ) : ℝ := Real.exp n

/-- The corresponding unnormalized reflected kernel. -/
noncomputable def absoluteKernel (n : ℕ) : ℝ :=
  absoluteLineWeight n * normalizedKernel n

/-- Every normalized kernel is constant, while the unnormalized reflected kernel tends to infinity.
This is the exact scalar mechanism of `cth:SMQG-normalized-no-absolute`. -/
theorem normalized_convergence_does_not_control_absolute_kernel :
    (∀ n, normalizedKernel n = 1) ∧
      Filter.Tendsto absoluteKernel Filter.atTop Filter.atTop := by
  constructor
  · intro n
    rfl
  · unfold absoluteKernel absoluteLineWeight normalizedKernel
    simp only [mul_one]
    exact Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop

end NCG.SMQGMarginalAndAbsoluteKernelCounterexamples
