/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Normal operators on varying Hilbert spaces

Strong convergence of an operator family and of its adjoints is stable under
composition.  In particular the normal operators converge strongly.  This is
the reusable first-order-to-energy bridge for graph and commutator limits.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w x y

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Hn : ℕ → Type x} {Fn : ℕ → Type y}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
  [∀ n, CompleteSpace (Fn n)]

/-- If a varying operator family and its adjoints both converge strongly, then
the corresponding normal operators converge strongly. -/
theorem StrongOperatorConverges.adjoint_comp_self
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := F) (Hn := Fn))
    {An : ∀ n, Hn n →L[K] Fn n} {A : H →L[K] F}
    (hA : J.StrongOperatorConverges L An A)
    (hAdjoint : L.StrongOperatorConverges J
      (fun n ↦ ContinuousLinearMap.adjoint (An n))
      (ContinuousLinearMap.adjoint A)) :
    J.StrongOperatorConverges J
      (fun n ↦ (ContinuousLinearMap.adjoint (An n)).comp (An n))
      ((ContinuousLinearMap.adjoint A).comp A) :=
  StrongOperatorConverges.comp J hAdjoint hA

end NCG.VaryingHilbert.System

