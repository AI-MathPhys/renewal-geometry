/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Collision lower bound for a stable separating polynomial
  (`prop:cluster-collision-lower-master`, flagship manuscript)

* `separator_slope_bound`: the mean-value step — a differentiable
  filter separating two values (`|p(x) - 1| ≤ ε`, `|p(y)| ≤ ε`,
  `ε < 1/2`) at distance `Δ` attains slope at least
  `(1 - 2ε)/Δ` somewhere between;
* `cluster_collision_lower`: the boxed degree bound — combining
  the slope bound with the Markov brothers' derivative inequality
  `‖p'‖ ≤ 2n²‖p‖/R` on the spectral window (the displayed
  classical input `hMarkov`) gives
  `n ≥ √(R(1 - 2ε)/(2Δ))`,
  so two clusters whose gap tends to zero require a diverging
  stable filter degree.

Rendering disclosed: the Markov brothers' polynomial inequality
is the displayed classical input (not in Mathlib); the
mean-value extraction, the separation arithmetic, and the square
root bookkeeping are proved here.
-/

namespace NCG

/-- Mean-value step: a separating filter attains slope
`≥ (1-2ε)/Δ` between the two clusters. -/
theorem separator_slope_bound (p p' : ℝ → ℝ) (x y Δ ε : ℝ)
    (hΔ : 0 < Δ)
    (hderiv : ∀ t, HasDerivAt p (p' t) t)
    (hxy : |x - y| = Δ)
    (hx : |p x - 1| ≤ ε) (hy : |p y| ≤ ε) :
    ∃ ξ, (1 - 2 * ε) / Δ ≤ |p' ξ| := by
  have hne : x ≠ y := by
    intro h
    rw [h, sub_self, abs_zero] at hxy
    linarith
  have hsep : 1 - 2 * ε ≤ |p x - p y| := by
    have h1 := abs_le.mp hx
    have h2 := abs_le.mp hy
    refine le_trans ?_ (le_abs_self _)
    linarith [h1.1, h2.2]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope p p' hlt
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hderiv t)
    refine ⟨ξ, ?_⟩
    rw [hξ, abs_div]
    have habs : |y - x| = Δ := by
      rw [abs_sub_comm]
      exact hxy
    rw [habs]
    have hsep' : 1 - 2 * ε ≤ |p y - p x| := by
      rw [abs_sub_comm]
      exact hsep
    exact div_le_div_of_nonneg_right hsep' hΔ.le
  · obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope p p' hgt
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hderiv t)
    refine ⟨ξ, ?_⟩
    rw [hξ, abs_div]
    rw [hxy]
    exact div_le_div_of_nonneg_right hsep hΔ.le

/-- `prop:cluster-collision-lower-master`, boxed bound: with the
Markov brothers' inequality displayed, the stable separating
degree satisfies `n ≥ √(R(1-2ε)/(2Δ))`. -/
theorem cluster_collision_lower (p p' : ℝ → ℝ) (n : ℕ)
    (x y Δ ε R : ℝ) (hΔ : 0 < Δ) (hR : 0 < R)
    (_hε2 : ε < 1 / 2)
    (hderiv : ∀ t, HasDerivAt p (p' t) t)
    (hxy : |x - y| = Δ)
    (hx : |p x - 1| ≤ ε) (hy : |p y| ≤ ε)
    (hMarkov : ∀ t, |p' t| ≤ 2 * (n : ℝ) ^ 2 / R) :
    Real.sqrt (R * (1 - 2 * ε) / (2 * Δ)) ≤ n := by
  obtain ⟨ξ, hξ⟩ := separator_slope_bound p p' x y Δ ε hΔ
    hderiv hxy hx hy
  have hchain : (1 - 2 * ε) / Δ ≤ 2 * (n : ℝ) ^ 2 / R :=
    le_trans hξ (hMarkov ξ)
  have hsq : R * (1 - 2 * ε) / (2 * Δ) ≤ (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hΔ hR] at hchain
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.sqrt (R * (1 - 2 * ε) / (2 * Δ))
      ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = n := by
        rw [Real.sqrt_sq (Nat.cast_nonneg n)]

end NCG
