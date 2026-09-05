/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventGraphScreen
import NCG.Grand.OperatorGraphMoscoCompactHeat

/-!
# Compact graph-Mosco heat from graph screens

This compiler accepts the manuscript's graph-screen input directly.  The
canonical weak-resolvent graph maps turn the screen tail condition into
collective compactness at one positive shift; graph Mosco convergence and the
resolvent calculus then give compactness of every positive-time limit heat
operator.
-/

open Filter Set Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w z z'

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Graph Mosco convergence and a compact screen for the canonical graph
outputs at one positive shift imply compactness of every positive-time
canonical limit heat operator. -/
theorem operatorGraphMosco_canonicalHeat_isCompact_of_graphScreens
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (Rn : ℝ → ∀ n, Hn n →L[ℂ] Hn n) (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ cutoff, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn a n) a ha (hstageEquation a ha n)),
      ‖y - screen cutoff y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (hdense : J.IsAsymptoticallyDense)
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    IsCompactOperator (operatorGraphResolventHeat (R b) b t) := by
  have haCollectivelyCompact : J.CollectivelyCompact (Rn a) :=
    J.operatorGraphResolvent_collectivelyCompact_of_graphScreenTails
      L Dn An (Rn a) a ha (hstageEquation a ha) screen
        hcompact htail hfst
  exact J.operatorGraphMosco_canonicalHeat_isCompact
    Dn An D A Rn R hmosco hstageEquation hlimitEquation
      a ha hdense haCollectivelyCompact b t hb ht

end NCG.VaryingHilbert.System
