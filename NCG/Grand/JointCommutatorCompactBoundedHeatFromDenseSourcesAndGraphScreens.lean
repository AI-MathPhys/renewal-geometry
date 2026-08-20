/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventFamily
import NCG.Grand.JointCommutatorCompactHeatFromDenseSourcesAndGraphScreens

/-!
# Compact bounded continuum heat from dense joint-commutator sources

Both the finite and continuum resolvents are canonical shifted normal inverses.
Dense-core convergence at one positive shift and a compact graph-screen tail
therefore imply compactness of every positive-time continuum heat operator,
without separately postulating Mosco convergence or resolvent equations.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Dense-core convergence to the canonical bounded normal resolvent and
compact graph screens imply compact canonical continuum heat. -/
theorem jointCommutator_boundedCanonicalHeat_isCompact_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hcore : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source x cutoff))
      (boundedOperatorNormalResolventFamily A lam0 x))
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
    IsCompactOperator
      (operatorGraphResolventHeat
        (boundedOperatorNormalResolventFamily A b) b t) := by
  exact J.jointCommutator_canonicalHeat_isCompact_of_denseSources_of_graphScreens
    c L A (boundedOperatorNormalResolventFamily A)
    lam0 hlam0 D hD source hsource hcore
    (boundedOperatorNormalResolventFamily_normalEquation A)
    a ha screen hcompact htail hfst b t hb ht

end NCG.VaryingHilbert.System
