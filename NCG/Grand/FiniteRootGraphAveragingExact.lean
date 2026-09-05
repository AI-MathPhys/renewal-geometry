/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRootGraphEnergyExact
import NCG.Grand.FiniteConnesDistanceAttainmentExact
import Mathlib

/-!
# Probability averaging preserves the finite root-graph commutator unit ball

Translation invariance is proved from the actual root-difference energy.
Convex combinations are controlled by the actual matrix-gradient norm.
Consequently discrete probability convolution is a contraction for the
graph Lipschitz seminorm, a prerequisite for sharp continuum smoothing.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.FiniteRootGraphAveraging

open FiniteWeightedGraphHodgeDirac FiniteConnesDistanceAttainment FiniteRootGraphEnergy

noncomputable section

theorem graphLipschitz_probability_average_le_one
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : I → V → ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hf : ∀ i, graphLipschitz mass conductance (f i) ≤ 1) :
    graphLipschitz mass conductance (∑ i, w i • f i) ≤ 1 := by
  rw [graphLipschitz_eq_norm_gradient, map_sum]
  simp only [map_smul]
  calc
    _ ≤ ∑ i, ‖w i • gradientLinear mass conductance (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i),
        ← graphLipschitz_eq_norm_gradient]
      nlinarith [hf i, hw i]
    _ = 1 := hsum

theorem graphLipschitz_translate
    {G R : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype R]
    (direction : R → G) (κ h : ℝ) (hκ : 0 ≤ κ) (hh : 0 < h)
    (f : G → ℝ) (g : G) :
    graphLipschitz (fun _ => h ^ 3) (rootConductance (fun x r => x + direction r) κ h)
      (fun x => f (x + g)) =
    graphLipschitz (fun _ => h ^ 3) (rootConductance (fun x r => x + direction r) κ h) f := by
  have hsq :
      graphLipschitz (fun _ => h ^ 3) (rootConductance (fun x r => x + direction r) κ h)
        (fun x => f (x + g)) ^ 2 =
      graphLipschitz (fun _ => h ^ 3) (rootConductance (fun x r => x + direction r) κ h) f ^ 2 := by
    rw [graphLipschitz_sq_eq_root_difference_norm _ κ h hκ hh,
      graphLipschitz_sq_eq_root_difference_norm _ κ h hκ hh]
    have hp := (Equiv.addRight g).surjective.pi_norm_comp
      (fun x => κ * ∑ r, ((f (x + direction r) - f x) / h) ^ 2)
    change ‖fun x => κ * ∑ r, ((f (x + g + direction r) - f (x + g)) / h) ^ 2‖ = _ at hp
    simpa only [add_right_comm] using hp
  have hn₁ : 0 ≤ graphLipschitz (fun _ => h ^ 3)
      (rootConductance (fun x r => x + direction r) κ h) (fun x => f (x + g)) := norm_nonneg _
  have hn₂ : 0 ≤ graphLipschitz (fun _ => h ^ 3)
      (rootConductance (fun x r => x + direction r) κ h) f := norm_nonneg _
  nlinarith

/-- Discrete convolution needs no analytic regularity hypothesis. -/
theorem probability_convolution_preserves_unit_ball
    {G R I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype R] [Fintype I]
    (direction : R → G) (κ h : ℝ) (hκ : 0 ≤ κ) (hh : 0 < h)
    (f : G → ℝ) (shift : I → G) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hf : graphLipschitz (fun _ => h ^ 3)
      (rootConductance (fun x r => x + direction r) κ h) f ≤ 1) :
    graphLipschitz (fun _ => h ^ 3) (rootConductance (fun x r => x + direction r) κ h)
      (∑ i, w i • (fun x => f (x + shift i))) ≤ 1 := by
  apply graphLipschitz_probability_average_le_one _ _ _ w hw hsum
  intro i
  rw [graphLipschitz_translate direction κ h hκ hh]
  exact hf

end

end NCG.FiniteRootGraphAveraging
