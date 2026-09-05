/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactScreenCollectiveCompactness
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.ShortedHodgeGraphScreenTail
import NCG.Grand.OperatorGraphResolventGraphMap

/-!
# Shorted-Hodge screens for joint-commutator graph outputs

This specializes the abstract shorted-Hodge spectral-tail estimate to the literal graph-output
family of the finite joint commutator.  Its conclusion is definitionally the compact graph-screen
tail premise used by the continuum Howe eigenvalue compiler.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A shorted-Hodge Sobolev estimate on the embedded joint-commutator graph unit balls supplies
the exact uniform compact-screen tail required by the Howe compiler. -/
theorem jointCommutator_graphScreenTail_of_shortedHodgeSobolevBound
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
    (s cSob C0 E B : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hs : 0 < s) (hcSob : 0 < cSob)
    (hC0 : 0 ≤ C0)
    (haction : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      action y ≤ E)
    (hcoeff : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ∑ j, Complex.normSq (coeff y j) ≤ B)
    (hcoercive : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      cSob * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell s (coeff y) -
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
  exact NCG.VaryingHilbert.graphScreenTail_of_shortedHodgeSobolevBound
    ell screen _ coeff action s cSob C0 E B hell hs hcSob hC0
      haction hcoeff hcoercive hscreen

end NCG.VaryingHilbert.System
