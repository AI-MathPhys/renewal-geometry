/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorCofinalMoscoFromOneStrongResolvent
import NCG.Grand.JointCommutatorMoscoCompactHeat

/-!
# Compact joint-commutator heat from one resolvent and graph screens

For a bounded continuum commutator operator, cofinal convergence at one
positive resolvent shift generates the Mosco hypothesis.  The normal equation
generates the continuum weak equation.  Compact graph screens then imply
compactness of every positive-time canonical heat operator.
-/

open Filter Set
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Cofinal one-shift convergence and compact graph screens imply compactness
of every positive-time heat operator of the limiting bounded commutator. -/
theorem jointCommutator_canonicalHeat_isCompact_of_oneStrongResolvent_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      (J.reindex φ).StrongOperatorConverges (J.reindex φ)
        (fun cutoff ↦
          NCG.jointCommutatorResolventFamily c lam0 (φ cutoff))
        (T lam0))
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + (lam : ℂ) • T lam f = f)
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation
          c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst =
      (L.embedding cutoff y).fst)
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    IsCompactOperator (operatorGraphResolventHeat (T b) b t) := by
  have hmoscoEnergy :=
    J.jointCommutatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent
      c A T hdense lam0 hlam0 hT0 hlimitNormal
  have hmoscoGraph : J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealOperatorGraphEnergy
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff))))
      (ennrealOperatorGraphEnergy (⊤ : Submodule ℂ H)
        (boundedOperatorGraphMap A)) := by
    simpa only [ennrealOperatorGraphEnergy_top] using hmoscoEnergy
  exact J.jointCommutatorMosco_canonicalHeat_isCompact_of_graphScreens
    c L (⊤ : Submodule ℂ H) (boundedOperatorGraphMap A) T
    hmoscoGraph
    (fun lam hlam f ↦
      boundedOperatorGraph_resolventEquation_of_normalEquation
        A lam f (T lam f) (hlimitNormal lam hlam f))
    a ha screen hcompact htail hfst hdense b t hb ht

end NCG.VaryingHilbert.System
