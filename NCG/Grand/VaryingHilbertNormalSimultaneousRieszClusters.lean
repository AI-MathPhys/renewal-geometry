/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalSpectrumAwayFromZero
import NCG.Grand.VaryingHilbertCompressedNormalSpectralSubspacesSmallCircle

/-!
# Simultaneous Riesz clusters away from zero

For a compact normal limit, only finitely many spectral points lie outside a prescribed
zero-neighborhood. Therefore the automatic small-circle theorem can be applied to all of them
with one common late-stage threshold. Each selected circle identifies the exact limit eigenspace,
the exact late-stage enclosed eigencluster, and its stable total algebraic multiplicity.
-/

open Complex Filter Topology Set Module End
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
/-- The part of an operator spectrum whose points have norm at least `r`. -/
abbrev spectrumAwayFromZero (T : H →L[ℂ] H) (r : ℝ) : Set ℂ :=
  {μ ∈ spectrum ℂ T | r ≤ ‖μ‖}

/-- All limiting spectral points bounded away from zero admit exact small Riesz clusters whose
stage identifications and multiplicities hold simultaneously after one cutoff. -/
theorem eventually_simultaneous_Riesz_clusters_away_from_zero_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (r : ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ radius : spectrumAwayFromZero T r → ℝ,
      (∀ μ : spectrumAwayFromZero T r,
        0 < radius μ ∧ radius μ < δ ∧
        (0 : ℂ) ∉ Metric.closedBall (μ : ℂ) (radius μ) ∧
        (∀ z ∈ Metric.sphere (μ : ℂ) (radius μ), z ∈ resolventSet ℂ T) ∧
        LinearMap.range (circleRieszProjection T (μ : ℂ) (radius μ)).toLinearMap =
          eigenspace T.toLinearMap (μ : ℂ)) ∧
      ∀ᶠ n in atTop, ∀ μ : spectrumAwayFromZero T r,
        LinearMap.range
            (circleRieszProjection
              (J.compressedOperator Tn n) (μ : ℂ) (radius μ)).toLinearMap =
            ⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) (radius μ)),
              eigenspace (J.compressedOperator Tn n).toLinearMap ν ∧
        Module.finrank ℂ
            ((⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) (radius μ)),
              eigenspace
                (J.compressedOperator Tn n).toLinearMap ν) : Submodule ℂ H) =
          Module.finrank ℂ (eigenspace T.toLinearMap (μ : ℂ)) := by
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  have hSfinite : Set.Finite (spectrumAwayFromZero T r) := by
    simpa [spectrumAwayFromZero] using
      finite_spectrum_norm_ge_of_compact_of_isStarNormal
        T hTcompact hlimNormal r hr
  letI : Fintype (spectrumAwayFromZero T r) := hSfinite.fintype
  have hμ0 (μ : spectrumAwayFromZero T r) : (μ : ℂ) ≠ 0 := by
    intro hzero
    have hnorm : r ≤ ‖(μ : ℂ)‖ := μ.property.2
    rw [hzero, norm_zero] at hnorm
    linarith
  have hcluster (μ : spectrumAwayFromZero T r) :
      ∃ radius : ℝ, 0 < radius ∧ radius < δ ∧
        (0 : ℂ) ∉ Metric.closedBall (μ : ℂ) radius ∧
        (∀ z ∈ Metric.sphere (μ : ℂ) radius, z ∈ resolventSet ℂ T) ∧
        LinearMap.range (circleRieszProjection T (μ : ℂ) radius).toLinearMap =
          eigenspace T.toLinearMap (μ : ℂ) ∧
        ∀ᶠ n in atTop,
          LinearMap.range
              (circleRieszProjection
                (J.compressedOperator Tn n) (μ : ℂ) radius).toLinearMap =
              ⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) radius),
                eigenspace (J.compressedOperator Tn n).toLinearMap ν ∧
          Module.finrank ℂ
              ((⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) radius),
                eigenspace
                  (J.compressedOperator Tn n).toLinearMap ν) : Submodule ℂ H) =
            Module.finrank ℂ (eigenspace T.toLinearMap (μ : ℂ)) := by
    exact J.compressedOperator_spectralSubspaces_smallCircle_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      (μ : ℂ) (hμ0 μ) δ hδ
  choose radius hradius using hcluster
  have hlimit : ∀ μ : spectrumAwayFromZero T r, 0 < radius μ ∧ radius μ < δ ∧
      (0 : ℂ) ∉ Metric.closedBall (μ : ℂ) (radius μ) ∧
      (∀ z ∈ Metric.sphere (μ : ℂ) (radius μ), z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T (μ : ℂ) (radius μ)).toLinearMap =
        eigenspace T.toLinearMap (μ : ℂ) := by
    intro μ
    rcases hradius μ with ⟨hpos, hsmall, hzero, hcontour, hrange, _⟩
    exact ⟨hpos, hsmall, hzero, hcontour, hrange⟩
  have hstage (μ : spectrumAwayFromZero T r) : ∀ᶠ n in atTop,
      LinearMap.range
          (circleRieszProjection
            (J.compressedOperator Tn n) (μ : ℂ) (radius μ)).toLinearMap =
          ⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) (radius μ)),
            eigenspace (J.compressedOperator Tn n).toLinearMap ν ∧
      Module.finrank ℂ
          ((⨆ ν : ℂ, ⨆ (_ : ν ∈ Metric.ball (μ : ℂ) (radius μ)),
            eigenspace
              (J.compressedOperator Tn n).toLinearMap ν) : Submodule ℂ H) =
        Module.finrank ℂ (eigenspace T.toLinearMap (μ : ℂ)) := by
    rcases hradius μ with ⟨_, _, _, _, _, hstage⟩
    exact hstage
  exact ⟨radius, hlimit, Filter.eventually_all.mpr hstage⟩

end NCG.VaryingHilbert.System
