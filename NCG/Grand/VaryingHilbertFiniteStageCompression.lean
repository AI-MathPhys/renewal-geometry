/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedOperators
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-stage compressions

An isometric stage embedding is split by its Hilbert adjoint.  Hence a compressed
operator agrees with the original stage operator on embedded vectors.  When the
stage is finite-dimensional, every such common-carrier compression is compact.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The adjoint lift is a left inverse to the isometric stage embedding. -/
@[simp] theorem adjointLift_embedding (n : ℕ) (x : Hn n) :
    J.adjointLift n (J.embedding n x) = x := by
  change
    ContinuousLinearMap.adjoint (J.embedding n).toContinuousLinearMap
      ((J.embedding n).toContinuousLinearMap x) = x
  have h := congrArg (fun T : Hn n →L[K] Hn n ↦ T x)
    (J.embedding n).adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h

/-- Compression recovers the stage operator on every embedded stage vector. -/
@[simp] theorem compressedOperator_embedding
    (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) (x : Hn n) :
    J.compressedOperator Tn n (J.embedding n x) =
      J.embedding n (Tn n x) := by
  simp [compressedOperator]

/-- Every common-carrier compression through a finite-dimensional stage is compact. -/
theorem compressedOperator_isCompactOperator_of_finiteDimensional
    [∀ n, FiniteDimensional K (Hn n)]
    (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    IsCompactOperator (J.compressedOperator Tn n : H → H) := by
  letI : ProperSpace (Hn n) := FiniteDimensional.proper_rclike K (Hn n)
  have hcompact : IsCompactOperator
      ((Tn n).comp (J.adjointLift n) : H → Hn n) :=
    isCompactOperator_of_locallyCompactSpace_dom
      ((Tn n).comp (J.adjointLift n))
  change IsCompactOperator
    (fun x ↦ J.embedding n (Tn n (J.adjointLift n x)))
  exact hcompact.clm_comp (J.embedding n).toContinuousLinearMap

end NCG.VaryingHilbert.System
