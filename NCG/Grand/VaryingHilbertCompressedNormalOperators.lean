/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompressedOperatorNormConvergenceFromAdjoints

/-!
# Normality of varying-Hilbert compressions

Literal compression by an isometric stage embedding identifies a stage operator with its direct
sum with zero on the orthogonal complement.  In particular it preserves normality.
-/

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

/-- Compression by an isometric stage embedding preserves star-normality. -/
theorem compressedOperator_isStarNormal
    (J : System (K := K) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[K] Hn n)
    (hnormal : ∀ n, IsStarNormal (Tn n)) (n : ℕ) :
    IsStarNormal (J.compressedOperator Tn n) := by
  apply ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
  intro x
  rw [J.adjoint_compressedOperator Tn n]
  change
    ‖J.embedding n (Tn n (J.adjointLift n x))‖ =
      ‖J.embedding n
        (ContinuousLinearMap.adjoint (Tn n) (J.adjointLift n x))‖
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  exact ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp
    (hnormal n) (J.adjointLift n x)

end NCG.VaryingHilbert.System
