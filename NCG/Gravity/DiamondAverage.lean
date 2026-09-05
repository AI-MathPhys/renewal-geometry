/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reflection-symmetric diamond averaging
  (`lem:line-integral`, GR_emergence)

The cancellation mechanism of the scalar-drift diamond bound: for a
normalized reflection-invariant profile, the average of a function
whose deviation from `constant + linear + odd` is quadratically
bounded is within the quadratic moment of the constant — the linear
term and the curvature-linear odd term vanish by symmetry, giving
the `O(τ³)` bound `⟨∫_γ Σ⟩ - ⟨∫_γ Σ⟩^flat = O(τ³(‖Σ‖_{C²} + ‖Riem‖))`.

* `symmetric_average_bound` — the discrete-profile form: weights
  `w ≥ 0` summing to `1`, a linear-plus-odd part `L` averaging to
  zero by reflection invariance, and the pointwise Taylor bound
  `|f x - c₀ - L x| ≤ K·q x` give `|⟨f⟩ - c₀| ≤ K·⟨q⟩`.

The identification of `c₀ = Σ₀(p)·T`, `L` = the gradient plus
curvature-linear odd terms (odd by `lem:curvature-free`), and
`K·⟨q⟩ = Cτ³(‖Σ‖_{C²} + ‖Riem‖)` is the disclosed WKB layer.
-/

namespace NCG

open Finset

/-- `lem:line-integral` (cancellation core): a normalized profile
average of a function with symmetric linear/odd part `L` and
quadratic remainder is within the quadratic moment of the constant
term. -/
theorem symmetric_average_bound {ι : Type*} [Fintype ι]
    {w : ι → ℝ} {x : ι → ℝ} {f L q : ℝ → ℝ} {c0 K : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hnorm : ∑ i, w i = 1)
    (hsym : ∑ i, w i * L (x i) = 0)
    (_hq : ∀ i, 0 ≤ q (x i))
    (htaylor : ∀ i, |f (x i) - c0 - L (x i)| ≤ K * q (x i)) :
    |∑ i, w i * f (x i) - c0| ≤ K * ∑ i, w i * q (x i) := by
  have hsplit : ∑ i, w i * f (x i) - c0
      = ∑ i, w i * (f (x i) - c0 - L (x i)) := by
    have h1 : ∑ i, w i * c0 = c0 := by
      rw [← Finset.sum_mul, hnorm, one_mul]
    have h3 : ∀ i ∈ Finset.univ,
        w i * (f (x i) - c0 - L (x i))
          = w i * f (x i) - w i * c0 - w i * L (x i) := by
      intro i _
      ring
    rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, h1, hsym]
    ring
  rw [hsplit]
  calc |∑ i, w i * (f (x i) - c0 - L (x i))|
      ≤ ∑ i, |w i * (f (x i) - c0 - L (x i))| :=
        Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ i, w i * (K * q (x i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (htaylor i) (hw i)
  _ = K * ∑ i, w i * q (x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end NCG
