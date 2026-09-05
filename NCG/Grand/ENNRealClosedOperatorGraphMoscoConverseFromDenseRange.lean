/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedOperatorGraphMoscoConverseFromOneShift
import NCG.Grand.OperatorGraphDenseDomainFromResolvent

/-!
# Closed-operator graph Mosco convergence from a dense-range resolvent

For a closed operator graph, dense range of one weak resolvent automatically supplies density of
the operator domain.  Hence one-shift strong resolvent convergence and the weak stage/limit
equations suffice for Mosco convergence without a separate dense-domain hypothesis.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A closed graph, weak resolvent equations, dense range of the limit resolvent at one positive
shift, and strong convergence at that shift imply Mosco convergence of the graph energies. -/
theorem ennrealClosedOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_of_denseRange
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
    (hclosed : (operatorLinearPMap D A).IsClosed)
    (hDenseRange : DenseRange (T lam0)) :
    J.MoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A) := by
  apply ennrealClosedOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent J
    Dn An D A Tn T hdense lam0 hlam0 hT0 hstageEquation hlimitEquation hclosed
  exact dense_operatorDomain_of_denseRange_resolvent D A lam0 (T lam0)
    (hlimitEquation lam0 hlam0) hDenseRange

end NCG.VaryingHilbert.System
