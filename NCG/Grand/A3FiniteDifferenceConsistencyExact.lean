/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalFlatVacuum
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean consistency of the twelve-root A3 energy

The roots are the manuscript's concrete twelve vectors, with normalization
`1/8`. The actual finite-difference energy of a differentiable scalar field
converges to the squared Euclidean gradient norm. This is a local consistency
result, not yet the uniform periodic Connes-distance convergence theorem.
-/

open Filter
open scoped Topology BigOperators

namespace NCG.A3FiniteDifferenceConsistency

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The existing explicit A3 root packet in the Euclidean Hilbert norm. -/
def root (r : Fin 12) : Space := WithLp.toLp 2 (a3Roots r)

theorem tight_frame_energy (v : Space) :
    (∑ r : Fin 12, (inner ℝ v (root r)) ^ 2) / 8 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [root, a3Roots, PiLp.inner_apply, Fin.sum_univ_succ]
  <;> ring

/-- A directional difference quotient along one of the actual roots. -/
def rootDifference (f : Space → ℝ) (x : Space) (h : ℝ) (r : Fin 12) : ℝ :=
  (f (x + h • root r) - f x) / h

/-- The local energy for rate `1/(8h^2)` in each of the twelve root directions. -/
def sampledEnergy (f : Space → ℝ) (x : Space) (h : ℝ) : ℝ :=
  (∑ r : Fin 12, rootDifference f x h r ^ 2) / 8

theorem sampledEnergy_nonneg (f : Space → ℝ) (x : Space) (h : ℝ) :
    0 ≤ sampledEnergy f x h := by
  unfold sampledEnergy
  positivity

theorem tendsto_rootDifference
    (f : Space → ℝ) (x v : Space) (hf : HasFDerivAt f (innerSL ℝ v) x)
    (r : Fin 12) :
    Tendsto (fun h => rootDifference f x h r) (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ v (root r))) := by
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const (root r)).const_add x
  have hcomp := hf.comp_hasDerivAt_of_eq 0 hline (by simp)
  simpa [Function.comp_def, rootDifference, innerSL_apply_apply, div_eq_inv_mul]
    using hcomp.tendsto_slope_zero_right

/-- Local consistency at every differentiability point, with the actual gradient norm. -/
theorem tendsto_sampledEnergy
    (f : Space → ℝ) (x v : Space) (hf : HasFDerivAt f (innerSL ℝ v) x) :
    Tendsto (sampledEnergy f x) (𝓝[>] (0 : ℝ)) (𝓝 (‖v‖ ^ 2)) := by
  have hsum := tendsto_finsetSum Finset.univ
    (fun r _ => (tendsto_rootDifference f x v hf r).pow 2)
  have hdiv := hsum.div_const 8
  rw [tight_frame_energy] at hdiv
  exact hdiv

theorem tendsto_sqrt_sampledEnergy
    (f : Space → ℝ) (x v : Space) (hf : HasFDerivAt f (innerSL ℝ v) x) :
    Tendsto (fun h => Real.sqrt (sampledEnergy f x h)) (𝓝[>] (0 : ℝ)) (𝓝 ‖v‖) := by
  have h := (Real.continuous_sqrt.tendsto (‖v‖ ^ 2)).comp (tendsto_sampledEnergy f x v hf)
  rw [Real.sqrt_sq (norm_nonneg v)] at h
  exact h

/-- Affine fields have exactly the continuum energy at every nonzero mesh size. -/
theorem sampledEnergy_affine (v x : Space) (b h : ℝ) (hh : h ≠ 0) :
    sampledEnergy (fun y => inner ℝ v y + b) x h = ‖v‖ ^ 2 := by
  have hdiff : ∀ r, rootDifference (fun y => inner ℝ v y + b) x h r =
      inner ℝ v (root r) := by
    intro r
    unfold rootDifference
    dsimp only
    rw [inner_add_right, real_inner_smul_right]
    field_simp [hh]
    <;> ring
  simp only [sampledEnergy, hdiff, tight_frame_energy]

end

end NCG.A3FiniteDifferenceConsistency
