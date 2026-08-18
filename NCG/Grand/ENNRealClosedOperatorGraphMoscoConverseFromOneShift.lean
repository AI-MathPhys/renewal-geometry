/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphMoscoConverseCanonicalRealification
import NCG.Grand.ENNRealClosedOperatorGraphEnergyLowerSemicontinuity

/-!
# One-shift Mosco converse for closed operator graphs

For a densely defined closed limit operator, lower semicontinuity of its extended graph energy is
automatic.  Thus the graph-form converse only needs weak resolvent equations and strong resolvent
convergence at one positive shift.
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

/-- A one-shift strong resolvent limit plus weak graph-resolvent equations imply Mosco convergence
when the limit operator is closed and densely defined. -/
theorem ennrealClosedOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent
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
    (hdom : Dense (D : Set H)) :
    J.MoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A) := by
  exact ennrealOperatorGraphEnergy_moscoConverges_of_oneStrongResolvent_canonicalReal J
    Dn An D A Tn T hdense lam0 hlam0 hT0 hstageEquation hlimitEquation
      (lowerSemicontinuous_ennrealOperatorGraphEnergy_of_isClosed D A hclosed) hdom

end NCG.VaryingHilbert.System
