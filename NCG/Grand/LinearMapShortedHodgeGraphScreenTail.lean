/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ShortedHodgeGraphScreenTailFromQuadraticBounds

/-!
# Linear-map shorted-Hodge graph-screen tails

For continuous linear coefficient and action maps, the quadratic estimates in the compact-screen
argument follow automatically from their operator norms.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The squared norm of a continuous linear map is bounded by its squared operator norm. -/
theorem normSq_apply_le_opNorm_sq_mul_norm_sq (T : G →L[ℂ] E) (y : G) :
    ‖T y‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖y‖ ^ 2 := by
  have hmap := T.le_opNorm y
  have hright : 0 ≤ ‖T‖ * ‖y‖ := mul_nonneg (norm_nonneg T) (norm_nonneg y)
  nlinarith [norm_nonneg (T y)]

/-- The coordinate energy of a continuous linear Euclidean-valued coefficient map is bounded by
its squared operator norm. -/
theorem coefficientEnergy_le_opNorm_sq_mul_norm_sq
    {i : Type*} [Fintype i] (T : G →L[ℂ] EuclideanSpace ℂ i) (y : G) :
    ∑ j, Complex.normSq (T y j) ≤ ‖T‖ ^ 2 * ‖y‖ ^ 2 := by
  calc
    ∑ j, Complex.normSq (T y j) = ∑ j, ‖T y j‖ ^ 2 := by
      simp only [Complex.normSq_eq_norm_sq]
    _ = ‖T y‖ ^ 2 := (EuclideanSpace.norm_sq_eq (T y)).symm
    _ ≤ ‖T‖ ^ 2 * ‖y‖ ^ 2 := normSq_apply_le_opNorm_sq_mul_norm_sq T y

/-- On a bounded set, continuous linear coefficient and action maps automatically supply the
quadratic hypotheses for the shorted-Hodge graph-screen theorem. -/
theorem graphScreenTail_of_linearMap_shortedHodgeSobolevBound
    {i : Type*} [Fintype i]
    (ell : i → ℝ) (screen : ℕ → G →L[ℂ] G) (S : Set G)
    (coeff : G →L[ℂ] EuclideanSpace ℂ i) (action : G →L[ℂ] E)
    (s c C0 radius : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hs : 0 < s) (hc : 0 < c)
    (hC0 : 0 ≤ C0) (hradius : 0 ≤ radius)
    (hbounded : S ⊆ Metric.closedBall 0 radius)
    (hcoercive : ∀ y ∈ S,
      c * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell s (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ ‖action y‖ ^ 2)
    (hscreen : ∀ R y, y ∈ S →
      ‖y - screen R y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (R : ℝ) (coeff y)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  apply graphScreenTail_of_shortedHodgeSobolevBound_of_quadraticBounds
    ell screen S (fun y ↦ coeff y) (fun y ↦ ‖action y‖ ^ 2)
      s c C0 (‖action‖ ^ 2) (‖coeff‖ ^ 2) radius
      hell hs hc hC0 (sq_nonneg _) (sq_nonneg _) hradius hbounded
  · exact normSq_apply_le_opNorm_sq_mul_norm_sq action
  · exact coefficientEnergy_le_opNorm_sq_mul_norm_sq coeff
  · exact hcoercive
  · exact hscreen

end NCG.VaryingHilbert
