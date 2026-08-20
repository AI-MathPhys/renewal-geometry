/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphMoscoCompactHeatFromGraphScreens

/-!
# Compact continuum heat for joint-commutator cutoffs

This is the model-facing specialization of the graph-screen heat compiler.
The finite cutoff graph operators and all of their positive-shift resolvent
equations are the canonical joint-commutator constructions; only the continuum
operator, its weak resolvent equation, Mosco convergence, and the compact
screen tail remain as analytic inputs.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v z

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Compact graph screens for a Mosco-convergent family of finite joint
commutator energies imply compactness of every positive-time canonical limit
heat operator. -/
theorem jointCommutatorMosco_canonicalHeat_isCompact_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealOperatorGraphEnergy
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff))))
      (ennrealOperatorGraphEnergy D A))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
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
    (hdense : J.IsAsymptoticallyDense)
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    IsCompactOperator (operatorGraphResolventHeat (R b) b t) := by
  exact J.operatorGraphMosco_canonicalHeat_isCompact_of_graphScreens
    L
    (fun cutoff ↦
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff))))
    (fun cutoff ↦ boundedOperatorGraphMap
      (NCG.jointCommutatorCLM (c cutoff)))
    D A (NCG.jointCommutatorResolventFamily c) R
    hmosco
    (fun lam hlam cutoff f ↦
      NCG.jointCommutatorResolventFamily_resolventEquation
        c lam hlam cutoff f)
    hlimitEquation a ha screen hcompact htail hfst hdense b t hb ht

end NCG.VaryingHilbert.System
