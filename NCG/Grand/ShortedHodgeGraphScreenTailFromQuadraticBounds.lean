/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ShortedHodgeGraphScreenTail

/-!
# Shorted-Hodge graph-screen tails from quadratic bounds

Global quadratic estimates for the action and coefficient energy become the uniform constants
needed by the shorted-Hodge screen theorem on any norm-bounded output set.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u

variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A bounded output set and global quadratic action/coefficient estimates supply all uniform
bounds in the shorted-Hodge graph-screen argument. -/
theorem graphScreenTail_of_shortedHodgeSobolevBound_of_quadraticBounds
    {i : Type*} [Fintype i]
    (ell : i → ℝ) (screen : ℕ → G →L[ℂ] G) (S : Set G)
    (coeff : G → i → ℂ) (action : G → ℝ)
    (s c C0 actionConstant coeffConstant radius : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hs : 0 < s) (hc : 0 < c)
    (hC0 : 0 ≤ C0) (hactionConstant : 0 ≤ actionConstant)
    (hcoeffConstant : 0 ≤ coeffConstant) (hradius : 0 ≤ radius)
    (hbounded : S ⊆ Metric.closedBall 0 radius)
    (haction : ∀ y, action y ≤ actionConstant * ‖y‖ ^ 2)
    (hcoeff : ∀ y, ∑ j, Complex.normSq (coeff y j) ≤ coeffConstant * ‖y‖ ^ 2)
    (hcoercive : ∀ y ∈ S,
      c * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell s (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ action y)
    (hscreen : ∀ R y, y ∈ S →
      ‖y - screen R y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (R : ℝ) (coeff y)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  apply graphScreenTail_of_shortedHodgeSobolevBound
    ell screen S coeff action s c C0
      (actionConstant * radius ^ 2) (coeffConstant * radius ^ 2)
      hell hs hc hC0
  · intro y hy
    have hynorm : ‖y‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbounded hy
    have hsq : ‖y‖ ^ 2 ≤ radius ^ 2 := by
      nlinarith [norm_nonneg y]
    exact (haction y).trans (mul_le_mul_of_nonneg_left hsq hactionConstant)
  · intro y hy
    have hynorm : ‖y‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbounded hy
    have hsq : ‖y‖ ^ 2 ≤ radius ^ 2 := by
      nlinarith [norm_nonneg y]
    exact (hcoeff y).trans (mul_le_mul_of_nonneg_left hsq hcoeffConstant)
  · exact hcoercive
  · exact hscreen

end NCG.VaryingHilbert
