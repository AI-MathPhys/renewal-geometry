/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphNormShortedHodgeCompactScreen
import NCG.Grand.JointCommutatorResolventFamily

/-!
# Joint-commutator compactness from full graph-energy screens

This is the model-facing specialization of the graph-norm shorted-Hodge
compiler.  Its coercivity and tail-identification hypotheses are imposed on
the entire embedded graph-energy unit-ball union, rather than only on
resolvent images.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shorted-Hodge control on the full finite joint-commutator graph-energy
unit balls implies collective compactness of the physical resolvents. -/
theorem jointCommutatorResolvent_collectivelyCompact_of_graphNorm_shortedHodge
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {q : ℕ}
    (c : ∀ cutoff, Fin q → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin q × (d cutoff × d cutoff)))))
    (a : ℝ) (ha : 0 < a)
    {ι : Type x} [Fintype ι]
    (ell : ι → ℝ)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (coeff : WithLp 2 (H × F) →L[ℂ] EuclideanSpace ℂ ι)
    (action : WithLp 2 (H × F) →L[ℂ] E)
    (sSob cSob C0 : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hsSob : 0 < sSob) (hcSob : 0 < cSob)
    (hC0 : 0 ≤ C0)
    (hcoercive : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphNormInclusion
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))),
      cSob * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell sSob (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ ‖action y‖ ^ 2)
    (hscreen : ∀ radius y, y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphNormInclusion
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))) →
      ‖y - screen radius y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (radius : ℝ) (coeff y))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ cutoff y,
      J.embedding cutoff y.fst = (L.embedding cutoff y).fst) :
    J.CollectivelyCompact (NCG.jointCommutatorResolventFamily c a) := by
  apply J.operatorGraphResolvent_collectivelyCompact_of_graphNorm_shortedHodge
    L
    (fun _ ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ (d _ × d _))))
    (fun cutoff ↦ boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
    (NCG.jointCommutatorResolventFamily c a) a ha
    (NCG.jointCommutatorResolventFamily_resolventEquation c a ha)
    ell screen coeff action sSob cSob C0
    hell hsSob hcSob hC0 hcoercive hscreen hcompact hfst

end NCG.VaryingHilbert.System
