/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedEigenvalue
import NCG.Grand.VaryingHilbertCompressedNormalRieszConvergence
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform upper spectral semicontinuity for normal varying-Hilbert operators

Operator-norm convergence of the literal compressions and upper hemicontinuity of Banach-algebra
spectrum imply a uniform no-pollution region: every nonzero eigenvalue of every sufficiently late
original stage lies in any prescribed open neighborhood of the limiting spectrum.
-/

open Complex Filter Topology Set Module End

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Every open neighborhood of the limiting spectrum contains the spectra of all sufficiently
late literal common-carrier compressions. -/
theorem compressedOperator_eventually_spectrum_subset_open_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (U : Set ℂ) (hU : IsOpen U) (hspectrum : spectrum ℂ T ⊆ U) :
    ∀ᶠ n in atTop, spectrum ℂ (J.compressedOperator Tn n) ⊆ U := by
  have hop : Tendsto (J.compressedOperator Tn) atTop (𝓝 T) :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).2
  have hupper : UpperHemicontinuousAt
      (spectrum ℂ : (H →L[ℂ] H) → Set ℂ) T :=
    (upperHemicontinuous_spectrum ℂ (H →L[ℂ] H)).upperHemicontinuousAt T
  exact hop.eventually (hupper.forall_isOpen U hU hspectrum)

/-- Uniform no-pollution region for the original varying carriers: every nonzero eigenvalue of
every sufficiently late stage lies in any prescribed open neighborhood of the limit spectrum. -/
theorem eventually_nonzero_stage_eigenvalues_mem_open_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (U : Set ℂ) (hU : IsOpen U) (hspectrum : spectrum ℂ T ⊆ U) :
    ∀ᶠ n in atTop, ∀ μ : ℂ, μ ≠ 0 → HasEigenvalue (Tn n).toLinearMap μ → μ ∈ U := by
  have hcompressed :=
    J.compressedOperator_eventually_spectrum_subset_open_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal U hU hspectrum
  filter_upwards [hcompressed] with n hn
  intro μ hμ hμEigen
  have hcompressedEigen :
      HasEigenvalue (J.compressedOperator Tn n).toLinearMap μ :=
    (J.hasEigenvalue_compressedOperator_iff Tn n μ hμ).mpr hμEigen
  apply hn
  rw [ContinuousLinearMap.spectrum_eq]
  exact hcompressedEigen.mem_spectrum

/-- Quantitative uniform no-pollution form: every nonzero eigenvalue of every sufficiently late
stage has distance less than `ε` from the limiting spectrum. -/
theorem eventually_nonzero_stage_eigenvalues_infDist_spectrum_lt_of_isStarNormal
    [Nontrivial H]
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ μ : ℂ, μ ≠ 0 → HasEigenvalue (Tn n).toLinearMap μ →
      Metric.infDist μ (spectrum ℂ T) < ε := by
  have hnear :=
    J.eventually_nonzero_stage_eigenvalues_mem_open_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      (Metric.thickening ε (spectrum ℂ T)) Metric.isOpen_thickening
      (Metric.self_subset_thickening hε (spectrum ℂ T))
  have hspectrumNonempty : (spectrum ℂ T).Nonempty := spectrum.nonempty T
  filter_upwards [hnear] with n hn
  intro μ hμ hμEigen
  exact (Metric.mem_thickening_iff_infDist_lt hspectrumNonempty).mp
    (hn μ hμ hμEigen)

end NCG.VaryingHilbert.System
