/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphResolventGraphScreen
import NCG.Grand.ShortedHodgeGraphScreenTailFromQuadraticBounds

/-!
# Joint-commutator shorted-Hodge screens from quadratic bounds

The canonical weak-resolvent graph estimate makes the embedded graph-output set explicitly
bounded.  Thus global quadratic action and coefficient bounds directly imply the compact-screen
tail required by the continuum Howe compiler.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Global quadratic shorted-Hodge estimates imply the literal joint-commutator graph-screen
tail, with the graph-output radius discharged by the weak resolvent equation. -/
theorem jointCommutator_graphScreenTail_of_shortedHodgeSobolevBound_of_quadraticBounds
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {q : ℕ}
    (c : ∀ cutoff, Fin q → Matrix (d cutoff) (d cutoff) ℂ)
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin q × (d cutoff × d cutoff)))))
    (a : ℝ) (ha : 0 < a)
    {i : Type*} [Fintype i]
    (ell : i → ℝ)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (coeff : WithLp 2 (H × F) → i → ℂ)
    (action : WithLp 2 (H × F) → ℝ)
    (sSob cSob C0 actionConstant coeffConstant : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hsSob : 0 < sSob) (hcSob : 0 < cSob)
    (hC0 : 0 ≤ C0) (hactionConstant : 0 ≤ actionConstant)
    (hcoeffConstant : 0 ≤ coeffConstant)
    (haction : ∀ y, action y ≤ actionConstant * ‖y‖ ^ 2)
    (hcoeff : ∀ y,
      ∑ j, Complex.normSq (coeff y j) ≤ coeffConstant * ‖y‖ ^ 2)
    (hcoercive : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      cSob * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell sSob (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ action y)
    (hscreen : ∀ R y, y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)) →
      ‖y - screen R y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (R : ℝ) (coeff y)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen R y‖ < ε := by
  apply NCG.VaryingHilbert.graphScreenTail_of_shortedHodgeSobolevBound_of_quadraticBounds
    ell screen _ coeff action sSob cSob C0 actionConstant coeffConstant
      (2 * (1 + 1 / a)) hell hsSob hcSob hC0 hactionConstant hcoeffConstant
      (by positivity)
  · exact embeddedUnitBallOutputs_operatorGraphResolventHilbertGraph_subset_closedBall
      L
      (fun _ ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ (d _ × d _))))
      (fun cutoff ↦ boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
      (NCG.jointCommutatorResolventFamily c a) a ha
      (NCG.jointCommutatorResolventFamily_resolventEquation c a ha)
  · exact haction
  · exact hcoeff
  · exact hcoercive
  · exact hscreen

end NCG.VaryingHilbert.System
