/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedGraphHodgeDiracExact

/-!
# Exact graph energy of a finite root-direction packet

Parallel directions are counted with multiplicity, so the construction remains
valid at small periods where different roots share a target. Vertex mass is
`h^3` and each direction contributes conductance `κ*h`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.FiniteRootGraphEnergy

open FiniteWeightedGraphHodgeDirac

noncomputable section

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R]

def rootConductance (step : V → R → V) (κ h : ℝ) (x y : V) : ℝ :=
  ∑ r, if step x r = y then κ * h else 0

theorem rootConductance_nonneg
    (step : V → R → V) (κ h : ℝ) (hκ : 0 ≤ κ) (hh : 0 ≤ h) (x y : V) :
    0 ≤ rootConductance step κ h x y := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs <;> positivity

/-- The genuine weighted graph energy equals the root finite-difference energy exactly. -/
theorem localEnergy_eq_root_difference_sum
    (step : V → R → V) (κ h : ℝ) (hκ : 0 ≤ κ) (hh : 0 < h)
    (f : V → ℝ) (x : V) :
    localEnergy (fun _ => h ^ 3) (rootConductance step κ h) f x =
      κ * ∑ r, ((f (step x r) - f x) / h) ^ 2 := by
  rw [localEnergy_eq_conductance_formula _ _ f (fun _ => pow_pos hh 3)
    (rootConductance_nonneg step κ h hκ hh.le)]
  simp only [rootConductance, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ r, (∑ y, (if step x r = y then κ * h else 0) / h ^ 3 *
      (f y - f x) ^ 2) = κ * ((f (step x r) - f x) / h) ^ 2 := by
    intro r
    simp only [ite_div, zero_div, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    field_simp [hh.ne']
    <;> ring
  simp only [hinner, Finset.mul_sum]

/-- Exact squared commutator norm for the finite direction-packet graph. -/
theorem graphLipschitz_sq_eq_root_difference_norm
    (step : V → R → V) (κ h : ℝ) (hκ : 0 ≤ κ) (hh : 0 < h) (f : V → ℝ) :
    graphLipschitz (fun _ => h ^ 3) (rootConductance step κ h) f ^ 2 =
      ‖fun x => κ * ∑ r, ((f (step x r) - f x) / h) ^ 2‖ := by
  rw [graphLipschitz, norm_sq_dirac_commutator]
  congr 1
  funext x
  exact localEnergy_eq_root_difference_sum step κ h hκ hh f x

end

end NCG.FiniteRootGraphEnergy
