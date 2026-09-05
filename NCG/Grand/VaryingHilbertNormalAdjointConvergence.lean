/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertNormalOperatorConvergence
import NCG.Grand.VaryingHilbertAdjointConvergenceFromNorms

/-!
# Adjoint convergence for normal varying-Hilbert operators

Strong convergence of normal operators automatically carries their adjoints with it.  The proof
first obtains weak convergence of the adjoint outputs by testing against asymptotically dense
moving vectors and using the adjoint identity.  Normality identifies the norms of operator and
adjoint outputs, so varying-space Radon--Riesz upgrades the weak convergence to strong
convergence.
-/

open Filter Topology
open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- A strongly convergent normal varying-space family has a strongly convergent adjoint family.
This removes the separate adjoint-convergence premise from normal compact-screen arguments. -/
theorem StrongOperatorConverges.adjoint_of_isStarNormal
    (J : System (K := K) (H := H) (Hn := Hn))
    {Tn : ∀ n, Hn n →L[K] Hn n} {T : H →L[K] H}
    (hT : J.StrongOperatorConverges J Tn T)
    (hdense : J.IsAsymptoticallyDense)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T) :
    J.StrongOperatorConverges J
      (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
      (ContinuousLinearMap.adjoint T) := by
  apply hT.adjoint_of_norm_tendsto J hdense
  intro x xlim hx
  have hnorm := (hT x xlim hx).norm
  convert hnorm using 1
  · funext n
    simpa using (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp
      (hnormal n) (x n)).symm
  · simpa using (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp
      hlimNormal xlim).symm

end NCG.VaryingHilbert.System
