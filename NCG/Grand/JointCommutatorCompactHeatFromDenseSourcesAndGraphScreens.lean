/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorCompactHeatFromOneStrongResolventAndGraphScreens
import NCG.Grand.JointCommutatorResolventDenseSourceConvergence
import NCG.Grand.VaryingHilbertAsymptoticDensityFromDenseSources

/-!
# Compact joint-commutator heat from dense sources and graph screens

This is the dense-core form of the continuum heat compiler.  Compatible lifts
of a dense source set supply asymptotic density, convergence of the canonical
resolvent on those lifts supplies cofinal strong convergence, and compact graph
screens then imply compactness of every positive-time limiting heat operator.
-/

open Filter Set Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Dense-core convergence of one canonical resolvent and compact graph
screens imply compactness of every positive-time continuum heat operator. -/
theorem jointCommutator_canonicalHeat_isCompact_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hcore : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source x cutoff))
      (T lam0 x))
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
  have hdense := J.isAsymptoticallyDense_of_denseSources
    D hD source hsource
  have hT0 :=
    J.jointCommutatorResolvent_cofinalStrongOperatorConverges_of_denseSources
      c (T lam0) lam0 hlam0 D hD source hsource hcore
  exact J.jointCommutator_canonicalHeat_isCompact_of_oneStrongResolvent_of_graphScreens
    c L A T hdense lam0 hlam0 hT0 hlimitNormal
    a ha screen hcompact htail hfst b t hb ht

end NCG.VaryingHilbert.System
