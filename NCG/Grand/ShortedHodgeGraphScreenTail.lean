/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GraphScreenTailFromSquaredError
import NCG.Grand.RenewalShortedHodgeAndCompactScreen

/-!
# Shorted-Hodge estimates imply graph-screen tails

The diagonal shorted-Hodge Sobolev estimate becomes the exact epsilon-form
graph-screen hypothesis once the screen error is identified with the spectral
tail and the coefficient norm and action are uniformly bounded.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u

variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The manuscript's common compact-screen estimate, together with the
coordinate realization of the screen error, supplies uniform graph-screen
tail exhaustion. -/
theorem graphScreenTail_of_shortedHodgeSobolevBound
    {i : Type*} [Fintype i]
    (ell : i → ℝ) (screen : ℕ → G →L[ℂ] G) (S : Set G)
    (coeff : G → i → ℂ) (action : G → ℝ)
    (s c C0 E B : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hs : 0 < s) (hc : 0 < c)
    (hC0 : 0 ≤ C0)
    (haction : ∀ y ∈ S, action y ≤ E)
    (hcoeff : ∀ y ∈ S, ∑ j, Complex.normSq (coeff y j) ≤ B)
    (hcoercive : ∀ y ∈ S,
      c * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell s (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ action y)
    (hscreen : ∀ R y, y ∈ S →
      ‖y - screen R y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (R : ℝ) (coeff y)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ S, ‖y - screen R y‖ < ε := by
  apply graphScreenTail_of_polynomialSquaredError
    screen S (E + C0 * B) c s hc hs
  intro R y hy
  rw [hscreen R y hy]
  have hraw :=
    NCG.RenewalShortedHodgeAndCompactScreen.common_compact_screen_bound
      ell (coeff y) (R : ℝ) s c C0 E (action y)
      hell (Nat.cast_nonneg R) hs hc (haction y hy) (hcoercive y hy)
  refine hraw.trans ?_
  have hden : 0 ≤ c * (1 + (R : ℝ)) ^ s := by positivity
  apply div_le_div_of_nonneg_right _ hden
  simpa [add_comm] using
    (add_le_add_left
      (mul_le_mul_of_nonneg_left (hcoeff y hy) hC0) E)

end NCG.VaryingHilbert
