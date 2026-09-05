/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphMoscoConverseFromOneShift
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer

/-!
# Operator-graph Mosco converse from weak resolvent equations

The weak graph resolvent equation automatically gives both domain-valued ranges and the
variational minimizer inequalities.  This wrapper reduces a concrete operator-graph Mosco proof
to one positive-shift strong limit, weak resolvent equations, and closed dense limit-form data.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [NormedSpace ℝ F] [IsScalarTower ℝ K F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ K (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- One positive-shift strong limit and the weak graph resolvent equations imply Mosco
convergence of the associated extended squared graph energies. -/
theorem ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_of_weakEquation
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (D : Submodule K H) (A : D →ₗ[K] F)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Tn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (T lam f))
    (hls : LowerSemicontinuous (ennrealOperatorGraphEnergy D A))
    (hdom : Dense (D : Set H))
    (hrealInner : ∀ x y : H,
      inner ℝ x y = RCLike.re (inner K x y)) :
    J.MoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A) := by
  exact ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent J
    Dn An D A Tn T hdense lam0 hlam0 hT0
      (fun lam hlam n f ↦ (hstageEquation lam hlam n f).mem)
      (fun lam hlam f ↦ (hlimitEquation lam hlam f).mem)
      (fun lam hlam n f ↦
        operatorGraph_resolventObjective_minimizer
          (Dn n) (An n) lam hlam.le f (Tn lam n f)
            (hstageEquation lam hlam n f))
      (fun lam hlam f ↦
        operatorGraph_resolventObjective_minimizer
          D A lam hlam.le f (T lam f) (hlimitEquation lam hlam f))
      hls hdom hrealInner

end NCG.VaryingHilbert.System
