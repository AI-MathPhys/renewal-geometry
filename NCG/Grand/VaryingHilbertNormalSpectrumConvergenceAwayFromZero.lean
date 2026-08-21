/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalSpectrumAwayFromZero
import NCG.Grand.VaryingHilbertNormalSpectralExactness
import NCG.Grand.VaryingHilbertNormalSpectrumUpperSemicontinuity

/-!
# Uniform spectral convergence away from zero on varying Hilbert spaces

For collectively compact normal families, pointwise approximation of nonzero limit eigenvalues
uniformizes on every region bounded away from zero: a compact normal operator has only finitely
many spectral points there. Combined with upper spectral semicontinuity, this gives both halves of
spectral convergence using one sufficiently late cutoff.
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

/-- Uniform lower spectral inclusion away from zero: one late-stage threshold works for every
limit spectral point whose norm is at least `r`. -/
theorem eventually_limit_spectrum_away_from_zero_approximated_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ μ ∈ spectrum ℂ T, r ≤ ‖μ‖ →
      ∃ ν : ℂ, ν ≠ 0 ∧ HasEigenvalue (Tn n).toLinearMap ν ∧ dist ν μ < ε := by
  let S : Set ℂ := {μ ∈ spectrum ℂ T | r ≤ ‖μ‖}
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  have hSfinite : Set.Finite S := by
    simpa [S] using
      NCG.ResolventStability.finite_spectrum_norm_ge_of_compact_of_isStarNormal
        T hTcompact hlimNormal r hr
  let δ : ℝ := min ε (r / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hε (by linarith)
  have hpointwise : ∀ μ ∈ S, ∀ᶠ n in atTop,
      ∃ ν : ℂ, ν ≠ 0 ∧ HasEigenvalue (Tn n).toLinearMap ν ∧ dist ν μ < ε := by
    intro μ hμ
    have hμ0 : μ ≠ 0 := by
      intro hzero
      subst μ
      have : r ≤ 0 := by simpa using hμ.2
      linarith
    have hμEigen : HasEigenvalue T.toLinearMap μ :=
      (hTcompact.hasEigenvalue_iff_mem_spectrum hμ0).mpr hμ.1
    have hnear := J.eventually_exists_stage_eigenvalue_near_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      μ hμ0 hμEigen δ hδ
    filter_upwards [hnear] with n hn
    obtain ⟨ν, hνEigen, hνNear⟩ := hn
    have hν0 : ν ≠ 0 := by
      intro hzero
      subst ν
      have hsmall : ‖μ‖ < r / 2 := by
        have := hνNear.trans_le (by
          dsimp [δ]
          exact min_le_right _ _)
        simpa [dist_zero_left] using this
      linarith [hμ.2]
    exact ⟨ν, hν0, hνEigen, hνNear.trans_le (by
      dsimp [δ]
      exact min_le_left _ _)⟩
  have huniform := hSfinite.eventually_all.mpr hpointwise
  filter_upwards [huniform] with n hn
  intro μ hμSpectrum hμNorm
  exact hn μ ⟨hμSpectrum, hμNorm⟩

/-- Two-sided uniform spectral exactness off zero. One late-stage threshold simultaneously
approximates every limiting spectral point of norm at least `r`, while every nonzero stage
eigenvalue lies within `ε` of the limiting spectrum. -/
theorem eventually_two_sided_spectrum_approximation_away_from_zero_of_isStarNormal
    [Nontrivial H]
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (∀ μ ∈ spectrum ℂ T, r ≤ ‖μ‖ →
        ∃ ν : ℂ, ν ≠ 0 ∧ HasEigenvalue (Tn n).toLinearMap ν ∧ dist ν μ < ε) ∧
      (∀ ν : ℂ, ν ≠ 0 → HasEigenvalue (Tn n).toLinearMap ν →
        Metric.infDist ν (spectrum ℂ T) < ε) := by
  have hlower :=
    J.eventually_limit_spectrum_away_from_zero_approximated_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal r hr ε hε
  have hupper :=
    J.eventually_nonzero_stage_eigenvalues_infDist_spectrum_lt_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal ε hε
  filter_upwards [hlower, hupper] with n hnLower hnUpper
  exact ⟨hnLower, hnUpper⟩

end NCG.VaryingHilbert.System
