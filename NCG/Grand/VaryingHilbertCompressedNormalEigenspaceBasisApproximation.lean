/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSourceGramConvergence
import NCG.Grand.VaryingHilbertCompressedNormalSpectralSubspaces
import NCG.Grand.CompactNormalRieszEigenspace
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Eigenspace basis approximation for compressed normal operators

Projecting a finite basis of an isolated nonzero limit eigenspace by the stage Riesz projections
eventually gives a basis of the complete enclosed stage eigencluster. Gram stability supplies
linear independence, while exact algebraic-multiplicity stability supplies spanning.
-/

open Complex Filter Topology Module
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- For a basis of a nonzero limiting eigenspace, the stage Riesz images are eventually linearly
independent and span the exact sum of all stage eigenspaces in the automatic isolating disc. -/
theorem compressedOperator_eigenspaceBasis_automaticCircle_of_isStarNormal
    {ι : Type x} [Finite ι]
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (hcenter : center ≠ 0)
    (b : Basis ι ℂ (Module.End.eigenspace T.toLinearMap center)) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      ∀ᶠ n in atTop,
        LinearIndependent ℂ
          (fun i ↦ circleRieszProjection
            (J.compressedOperator Tn n) center radius (b i : H)) ∧
        Submodule.span ℂ
            (Set.range fun i ↦ circleRieszProjection
              (J.compressedOperator Tn n) center radius (b i : H)) =
          ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
            Module.End.eigenspace
              (J.compressedOperator Tn n).toLinearMap μ := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨hTcompact, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
      T hTcompact hlimNormal center hcenter
  obtain ⟨_, _, hproj⟩ :=
    J.compressedOperator_circleRieszProjection_tendsto_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR.le hcontour
  let E : Submodule ℂ H := Module.End.eigenspace T.toLinearMap center
  let P : H →L[ℂ] H := circleRieszProjection T center radius
  have hPidem : IsIdempotentElem P.toLinearMap := by
    dsimp [P]
    exact circleRieszProjection_isIdempotentElem_of_compact_of_isStarNormal
      T hTcompact hlimNormal center radius hR hcontour
  have hPfix (i : ι) : P (b i : H) = (b i : H) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff hPidem).mp
    rw [hrange]
    exact (b i).property
  have hbAmbient : LinearIndependent ℂ (fun i ↦ (b i : H)) :=
    b.linearIndependent.map' E.subtype (Submodule.ker_subtype E)
  have hlimitIndependent : LinearIndependent ℂ (fun i ↦ P (b i : H)) := by
    simpa only [hPfix] using hbAmbient
  have hlinearIndependent : ∀ᶠ n in atTop,
      LinearIndependent ℂ
        (fun i ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius (b i : H)) :=
    NCG.SpectralApproximation.eventually_linearIndependent_projected_sources
      (T := fun n ↦ circleRieszProjection
        (J.compressedOperator Tn n) center radius)
      (Tlim := P)
      (v := fun _ i ↦ (b i : H)) (vlim := fun i ↦ (b i : H))
      hproj (fun _ ↦ tendsto_const_nhds) hlimitIndependent
  obtain ⟨hlimitSum, hstage⟩ :=
    J.compressedOperator_circleRieszProjection_spectralSubspaces_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR hzero hcontour
  have hsumLimit :
      ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
        Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ H) = E := by
    exact hlimitSum.symm.trans hrange
  obtain ⟨M, hM, hlimitBound⟩ :=
    exists_circle_resolvent_norm_bound T center radius hcontour
  obtain ⟨N, hN, hstageBound⟩ := eventually_circle_resolvent_bound_of_tendsto
    (J.compressedOperator Tn) T hop center radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
      z ∈ resolventSet ℂ (J.compressedOperator Tn n) :=
    hstageBound.mono fun n hn z hz ↦ (hn z hz).1
  have hcompressedCollective := hcompact.compressedOperator J Tn
  have hstageCompact (n : ℕ) :
      IsCompactOperator ((J.compressedOperator Tn n : H →L[ℂ] H) : H → H) := by
    simpa [embeddedOperator, constantSystem] using
      CollectivelyCompact.isCompactOperator_embedded
        (constantSystem ℂ H) hcompressedCollective n
  refine ⟨radius, hR, hzero, hcontour, hrange, ?_⟩
  filter_upwards [hlinearIndependent, hstage, hstageContour] with
      n hnIndependent hnStage hnContour
  refine ⟨hnIndependent, ?_⟩
  let Sn : Submodule ℂ H :=
    ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
      Module.End.eigenspace (J.compressedOperator Tn n).toLinearMap μ
  have hstageRange :
      LinearMap.range
          (circleRieszProjection
            (J.compressedOperator Tn n) center radius).toLinearMap = Sn := by
    simpa [Sn] using hnStage.1
  letI : FiniteDimensional ℂ Sn := by
    rw [← hstageRange]
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isStarNormal
      (J.compressedOperator Tn n) (hstageCompact n)
      (J.compressedOperator_isStarNormal Tn hnormal n)
      center radius hR hzero hnContour
  have hspanLe : Submodule.span ℂ
      (Set.range fun i ↦ circleRieszProjection
        (J.compressedOperator Tn n) center radius (b i : H)) ≤ Sn := by
    apply Submodule.span_le.2
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [← hstageRange]
    exact ⟨(b i : H), rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq hspanLe
  rw [finrank_span_eq_card hnIndependent]
  have hstageRank : Module.finrank ℂ Sn = Module.finrank ℂ E := by
    change Module.finrank ℂ
        ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
          Module.End.eigenspace
            (J.compressedOperator Tn n).toLinearMap μ) : Submodule ℂ H) =
      Module.finrank ℂ E
    rw [← hsumLimit]
    exact hnStage.2
  rw [hstageRank, Module.finrank_eq_card_basis b]

end NCG.VaryingHilbert.System
