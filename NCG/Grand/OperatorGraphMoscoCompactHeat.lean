/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphMoscoResolventConvergence
import NCG.Grand.OperatorGraphResolventCompactHeat
import NCG.Grand.CompressedOperatorNormConvergence
import NCG.Grand.CollectivelyCompactLimit

/-!
# Compact canonical heat operators from graph-Mosco collective compactness

One collectively compact cutoff resolvent family has a compact limit under graph-Mosco strong
resolvent convergence.  Weak graph identities propagate compactness to every positive limit
shift, and the one-resolvent Euler calculus then makes every positive-time canonical heat
operator compact.
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
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Cofinal graph-Mosco convergence and collective compactness at one positive cutoff-resolvent
shift make every positive-time canonical limit heat operator compact. -/
theorem operatorGraphMosco_canonicalHeat_isCompact
    (J : System (K := ℂ) (H := H) (Hn := Hn))
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
    (hdense : J.IsAsymptoticallyDense)
    (haCompact : J.CollectivelyCompact (Rn a))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    IsCompactOperator (operatorGraphResolventHeat (R b) b t) := by
  have haStrong : J.StrongOperatorConverges J (Rn a) (R a) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A Rn R hmosco hstageEquation hlimitEquation a ha
  have haCompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator (Rn a) n y) atTop (nhds (R a y)) :=
    J.compressedOperator_tendsto (Rn a) (R a) hdense haStrong
  have haCompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator (Rn a)) :=
    haCompact.compressedOperator J (Rn a)
  have hRaCompact : IsCompactOperator (R a) :=
    haCompressedCompact.isCompactOperator_limit
      (J.compressedOperator (Rn a)) (R a) haCompressedStrong
  have hRbCompact : IsCompactOperator (R b) :=
    operatorGraphResolvent_isCompact_of_oneShift
      D A R hlimitEquation a ha hRaCompact b hb
  exact operatorGraphResolventHeat_isCompact_of_oneShift
    D A R hlimitEquation b t hb ht hRbCompact

end NCG.VaryingHilbert.System
