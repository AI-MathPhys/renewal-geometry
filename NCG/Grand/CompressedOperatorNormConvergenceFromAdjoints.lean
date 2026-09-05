/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompressedOperatorNormConvergence
import NCG.Grand.CollectivelyCompactStrongAdjointToNorm

/-!
# Norm convergence of compressed operators from convergence of adjoints

This file lifts the non-selfadjoint collectively compact convergence theorem to varying Hilbert
spaces.  Compression by an isometric stage embedding commutes with adjoints.  Consequently,
varying-space strong convergence of both a family and its adjoint family gives operator-norm
convergence of the literal common-carrier compressions `Jₙ Tₙ Jₙ†`.
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
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Taking the adjoint commutes with literal common-carrier compression. -/
theorem adjoint_compressedOperator
    (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    (J.compressedOperator Tn n)† =
      J.compressedOperator (fun m ↦ ContinuousLinearMap.adjoint (Tn m)) n := by
  simp only [compressedOperator, adjointLift, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  rw [ContinuousLinearMap.comp_assoc]

/-- Collective compactness and varying-space strong convergence of a family and its adjoints
imply compactness of the common-space limit and operator-norm convergence of the literal
compressions. -/
theorem compressedOperator_tendsto_operatorNorm_of_adjointStrong
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hadjointStrong :
      J.StrongOperatorConverges J
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T))
    (hcompact : J.CollectivelyCompact Tn) :
    IsCompactOperator T ∧ Tendsto (J.compressedOperator Tn) atTop (nhds T) := by
  have hcompressedStrong : ∀ x : H,
      Tendsto (fun n ↦ J.compressedOperator Tn n x) atTop (𝓝 (T x)) :=
    J.compressedOperator_tendsto Tn T hdense hstrong
  have hadjointCompressedStrong : ∀ y : H,
      Tendsto
        (fun n ↦ ContinuousLinearMap.adjoint (J.compressedOperator Tn n) y)
        atTop (𝓝 (ContinuousLinearMap.adjoint T y)) := by
    intro y
    simpa only [J.adjoint_compressedOperator Tn] using
      J.compressedOperator_tendsto
        (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
        (ContinuousLinearMap.adjoint T) hdense hadjointStrong y
  exact tendsto_operatorNorm_of_collectivelyCompact_of_adjointStrong
    (J.compressedOperator Tn) T (hcompact.compressedOperator J Tn)
      hcompressedStrong hadjointCompressedStrong

end NCG.VaryingHilbert.System
