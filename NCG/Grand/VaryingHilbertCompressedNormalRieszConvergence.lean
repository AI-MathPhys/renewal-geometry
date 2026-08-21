/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedRieszConvergenceFromAdjoints
import NCG.Grand.VaryingHilbertNormalAdjointConvergence

/-!
# Compressed Riesz convergence for normal varying-Hilbert operators

Normality makes the adjoint-convergence premise in the general non-selfadjoint compact-screen
pipeline automatic.  This file provides the resulting direct interfaces for norm convergence,
circle Riesz convergence, and finite-source Gram convergence.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w x

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- A collectively compact strongly convergent normal family has a compact limit and its literal
common-carrier compressions converge in operator norm. -/
theorem compressedOperator_tendsto_operatorNorm_of_isStarNormal
    (J : System (K := K) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T) :
    IsCompactOperator T ∧ Tendsto (J.compressedOperator Tn) atTop (𝓝 T) := by
  have hadjointStrong :=
    hstrong.adjoint_of_isStarNormal J hdense hnormal hlimNormal
  exact J.compressedOperator_tendsto_operatorNorm_of_adjointStrong
    Tn T hdense hstrong hadjointStrong hcompact

section Complex

variable {HC : Type v} [NormedAddCommGroup HC] [InnerProductSpace ℂ HC]
  [CompleteSpace HC]
variable {HCn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (HCn n)] [∀ n, InnerProductSpace ℂ (HCn n)]
  [∀ n, CompleteSpace (HCn n)]

/-- Normal varying-space convergence gives compressed Riesz convergence on every limiting
resolvent circle. -/
theorem compressedOperator_circleRieszProjection_tendsto_of_isStarNormal
    (J : System (K := ℂ) (H := HC) (Hn := HCn))
    (Tn : ∀ n, HCn n →L[ℂ] HCn n) (T : HC →L[ℂ] HC)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) := by
  have hadjointStrong :=
    hstrong.adjoint_of_isStarNormal J hdense hnormal hlimNormal
  exact J.compressedOperator_circleRieszProjection_tendsto_of_adjointStrong
    Tn T hdense hstrong hadjointStrong hcompact center radius hradius hcontour

/-- The normal-family Riesz theorem also transports every finite projected-source Gram matrix. -/
theorem compressedOperator_rieszAndSourceGram_tendsto_of_isStarNormal
    {ι : Type x}
    (J : System (K := ℂ) (H := HC) (Hn := HCn))
    (Tn : ∀ n, HCn n →L[ℂ] HCn n) (T : HC →L[ℂ] HC)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (source : ℕ → ι → HC) (sourceLim : ι → HC)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Tn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Tn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  have hadjointStrong :=
    hstrong.adjoint_of_isStarNormal J hdense hnormal hlimNormal
  exact J.compressedOperator_rieszAndSourceGram_tendsto_of_adjointStrong
    Tn T hdense hstrong hadjointStrong hcompact center radius hradius hcontour
      source sourceLim hsource

end Complex

end NCG.VaryingHilbert.System
