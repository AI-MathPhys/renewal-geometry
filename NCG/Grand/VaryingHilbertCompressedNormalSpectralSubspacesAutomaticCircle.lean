/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalRieszEigenspace
import NCG.Grand.VaryingHilbertCompressedNormalSpectralSubspaces

/-!
# Automatic isolated spectral subspaces for compressed normal operators

Every nonzero target for a collectively compact normal varying-Hilbert family has an automatically
selected circle on which stable Riesz rank is exactly stable total algebraic multiplicity. The
limiting enclosed spectral subspace is precisely the target eigenspace.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Around any nonzero center, an automatic isolating circle identifies the limiting spectral
subspace with the center eigenspace. Every sufficiently late stage Riesz range is the sum of its
enclosed eigenspaces, whose total multiplicity equals the limiting center multiplicity. -/
theorem compressedOperator_spectralSubspaces_automaticCircle_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (hcenter : center ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      ∀ᶠ n in atTop,
        LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius).toLinearMap =
            ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
              Module.End.eigenspace
                (J.compressedOperator Tn n).toLinearMap μ ∧
        Module.finrank ℂ
            ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
              Module.End.eigenspace
                (J.compressedOperator Tn n).toLinearMap μ) : Submodule ℂ H) =
          Module.finrank ℂ (Module.End.eigenspace T.toLinearMap center) := by
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
      T hTcompact hlimNormal center hcenter
  obtain ⟨hlimitSum, hstage⟩ :=
    J.compressedOperator_circleRieszProjection_spectralSubspaces_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR hzero hcontour
  have hsumLimit :
      ((⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
        Module.End.eigenspace T.toLinearMap μ) : Submodule ℂ H) =
        Module.End.eigenspace T.toLinearMap center :=
    hlimitSum.symm.trans hrange
  refine ⟨radius, hR, hzero, hcontour, hrange, ?_⟩
  filter_upwards [hstage] with n hn
  refine ⟨hn.1, ?_⟩
  rw [← hsumLimit]
  exact hn.2

end NCG.VaryingHilbert.System
