/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weak closure and ancient constant counterexamples

The oscillatory sequence used to separate weak closure from strong residual
control, and the constant-field core of the ancient Navier--Stokes
nontriviality counterexample.
-/

open Filter Topology MeasureTheory
open scoped Interval

namespace NCG
namespace WeakClosureAndAncientConstantCounterexamples

noncomputable def oscillatoryWeakSequence (N : ℕ) (t : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * Real.sin ((((N + 1 : ℕ) : ℝ) ^ 2) * t)

/-- Uniform-amplitude estimate for u_N. -/
theorem oscillatoryWeakSequence_abs_le (N : ℕ) (t : ℝ) :
    |oscillatoryWeakSequence N t| ≤ (((N + 1 : ℕ) : ℝ))⁻¹ := by
  rw [oscillatoryWeakSequence, abs_mul, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg (N + 1))]
  calc
    (↑(N + 1))⁻¹ * |Real.sin (↑(N + 1) ^ 2 * t)|
        ≤ (↑(N + 1))⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = (↑(N + 1))⁻¹ := mul_one _

/-- The uniform amplitude tends to zero. -/
theorem oscillatoryWeakSequence_uniformly_to_zero :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  simpa only [Nat.cast_add, Nat.cast_one] using hinv

/-- Exact derivative `u_N'= (N+1) cos((N+1)^2 t)`. -/
theorem oscillatoryWeakSequence_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (oscillatoryWeakSequence N)
      (((N + 1 : ℕ) : ℝ) *
        Real.cos ((((N + 1 : ℕ) : ℝ) ^ 2) * t)) t := by
  let a : ℝ := ((N + 1 : ℕ) : ℝ)
  have ha : a ≠ 0 := by positivity
  have hinner : HasDerivAt (fun s : ℝ => a ^ 2 * s) (a ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (a ^ 2)
  have hsin := hinner.sin.const_mul a⁻¹
  have hcoef : a⁻¹ * (Real.cos (a ^ 2 * t) * a ^ 2) =
      a * Real.cos (a ^ 2 * t) := by
    field_simp [ha]
  rw [hcoef] at hsin
  change HasDerivAt (fun y : ℝ => a⁻¹ * Real.sin (a ^ 2 * y))
    (a * Real.cos (a ^ 2 * t)) t
  exact hsin

/-- At the origin the derivative magnitude is exactly N+1, so the strong
differential defect is unbounded even though the functions converge uniformly. -/
theorem oscillatoryWeakSequence_derivative_at_zero (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) *
      Real.cos ((((N + 1 : ℕ) : ℝ) ^ 2) * 0) = (N + 1 : ℕ) := by
  simp

/-- The displayed strong derivative witness tends to infinity. -/
theorem oscillatoryWeakSequence_strong_defect_unbounded :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
  simpa [Nat.cast_add, Nat.cast_one] using
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- A nonzero constant vector has positive cubic mass density and zero spatial
derivative; these are the two decisive facts in `cth:NS-ancient-nontrivial`. -/
theorem nonzero_constant_ancient_core {d : Type*} [Fintype d]
    (c : EuclideanSpace ℝ d) (hc : c ≠ 0) :
    0 < ‖c‖ ^ 3
      ∧ (∀ x : EuclideanSpace ℝ d,
        HasFDerivAt (fun _ : EuclideanSpace ℝ d => c)
          (0 : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) x) := by
  constructor
  · positivity
  · intro x
    exact hasFDerivAt_const c x

end WeakClosureAndAncientConstantCounterexamples
end NCG
