/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Real-rooted approximation implies RH
  (`thm:v002-hurwitz-rh`, arithmetic manuscript)

If nonzero entire functions `Dₙ` with only real zeros converge
locally uniformly to `Ξ ≢ 0`, then every zero of `Ξ` is real.

The proof follows the manuscript exactly.  Suppose `Ξ(z₀) = 0`
with `z₀` nonreal.  The closed ball of radius `|Im z₀|/2` around
`z₀` avoids the real axis, so every `Dₙ` is zero-free on it (their
zeros are real).  Hurwitz's dichotomy — the locally uniform limit
of zero-free holomorphic functions on a ball is zero-free or
identically zero there — yields either a contradiction with
`Ξ(z₀) = 0` or, via the identity theorem for the entire function
`Ξ` (proved here through
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`),
a contradiction with `Ξ ≢ 0`.

Disclosure: Hurwitz's dichotomy itself enters as the displayed
hypothesis `hHurwitz` (it is not yet in Mathlib — no argument
principle/Rouché machinery is available); the disk selection, the
zero-freeness transfer from the real-rootedness of the `Dₙ`, and
the identity-theorem branch are proved in full.
-/

open Metric Set Filter Topology

namespace NCG

theorem hurwitz_real_rooted_rh
    (Ξ : ℂ → ℂ) (D : ℕ → ℂ → ℂ)
    (hΞdiff : Differentiable ℂ Ξ)
    (hDzeros : ∀ n z, D n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformly D Ξ atTop)
    (hΞne : ∃ w, Ξ w ≠ 0)
    (hHurwitz : ∀ (z₀ : ℂ) (r : ℝ), 0 < r →
      TendstoLocallyUniformly D Ξ atTop →
      (∀ n, ∀ z ∈ closedBall z₀ r, D n z ≠ 0) →
      (∀ z ∈ ball z₀ r, Ξ z ≠ 0) ∨ (∀ z ∈ ball z₀ r, Ξ z = 0)) :
    ∀ z, Ξ z = 0 → z.im = 0 := by
  intro z₀ hz₀
  by_contra him
  -- the ball of radius |Im z₀|/2 avoids the real axis
  set r : ℝ := |z₀.im| / 2 with hr_def
  have hr : 0 < r := by
    rw [hr_def]
    have : z₀.im ≠ 0 := him
    positivity
  have hball_im : ∀ z ∈ closedBall z₀ r, z.im ≠ 0 := by
    intro z hz
    have h1 : dist z z₀ ≤ r := mem_closedBall.mp hz
    have h2 : |z.im - z₀.im| ≤ dist z z₀ :=
      (Complex.abs_im_le_norm (z - z₀)).trans_eq
        (by rw [Complex.dist_eq]) |>.trans_eq' (by
          rw [Complex.sub_im])
    intro hzim
    rw [hzim, zero_sub, abs_neg] at h2
    have h3 : |z₀.im| ≤ r := le_trans h2 h1
    rw [hr_def] at h3
    have h4 : 0 < |z₀.im| := abs_pos.mpr him
    linarith
  -- every approximant is zero-free on the ball
  have hDfree : ∀ n, ∀ z ∈ closedBall z₀ r, D n z ≠ 0 := by
    intro n z hz hDz
    exact hball_im z hz (hDzeros n z hDz)
  -- Hurwitz dichotomy
  rcases hHurwitz z₀ r hr hconv hDfree with hfree | hvan
  · exact hfree z₀ (mem_ball_self hr) hz₀
  · -- identity theorem: Ξ vanishes identically, contradiction
    obtain ⟨w, hw⟩ := hΞne
    have hΞan : AnalyticOnNhd ℂ Ξ Set.univ :=
      hΞdiff.differentiableOn.analyticOnNhd isOpen_univ
    have hloc : Ξ =ᶠ[nhds z₀] 0 := by
      filter_upwards [ball_mem_nhds z₀ hr] with z hz
      exact hvan z hz
    have hzero := hΞan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z₀) hloc
    exact hw (hzero (Set.mem_univ w))

end NCG
