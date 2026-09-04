/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRootGraphEnergyExact

/-!
# Mesh-scale edge control for the graph commutator unit ball

An arbitrary discrete unit-seminorm function, not merely a smooth sampled
field, has an `O(h)` difference across each retained root edge. The coarse
constant three is enough for compactness; the sharp continuum constant must
still be recovered from the full tight-frame energy constraint.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.FiniteRootGraphUnitBallBounds

open FiniteRootGraphEnergy FiniteWeightedGraphHodgeDirac

noncomputable section

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R]

theorem localEnergy_le_graphLipschitz_sq
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) (x : V) :
    localEnergy mass conductance f x ≤ graphLipschitz mass conductance f ^ 2 := by
  rw [graphLipschitz, norm_sq_dirac_commutator]
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (localEnergy mass conductance f) x)

/-- The twelve-root normalization forces a uniform mesh-scale edge bound. -/
theorem root_step_difference_le_three_mesh
    (step : V → R → V) (h : ℝ) (hh : 0 < h) (f : V → ℝ)
    (hf : graphLipschitz (fun _ => h ^ 3) (rootConductance step (1 / 8) h) f ≤ 1)
    (x : V) (r : R) : |f (step x r) - f x| ≤ 3 * h := by
  have hLpos : 0 ≤ graphLipschitz (fun _ => h ^ 3)
      (rootConductance step (1 / 8) h) f := norm_nonneg _
  have hLsq : graphLipschitz (fun _ => h ^ 3)
      (rootConductance step (1 / 8) h) f ^ 2 ≤ 1 := by nlinarith
  have hlocal := (localEnergy_le_graphLipschitz_sq (fun _ => h ^ 3)
    (rootConductance step (1 / 8) h) f x).trans hLsq
  rw [localEnergy_eq_root_difference_sum step (1 / 8) h (by norm_num) hh] at hlocal
  have hterm : ((f (step x r) - f x) / h) ^ 2 ≤
      ∑ s : R, ((f (step x s) - f x) / h) ^ 2 :=
    Finset.single_le_sum (fun s _ => sq_nonneg ((f (step x s) - f x) / h))
      (Finset.mem_univ r)
  have hquot : |(f (step x r) - f x) / h| ≤ 3 := by
    have habs := sq_abs ((f (step x r) - f x) / h)
    nlinarith [abs_nonneg ((f (step x r) - f x) / h)]
  rw [abs_div, abs_of_pos hh] at hquot
  exact (div_le_iff₀ hh).mp hquot

end

end NCG.FiniteRootGraphUnitBallBounds
