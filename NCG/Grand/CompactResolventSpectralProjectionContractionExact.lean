/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactResolventDiracSpectralScreensExact

/-! # Contraction of compact-resolvent spectral projections -/

open Complex Module Set

noncomputable section

namespace NCG.CompactResolventSpectralProjectionContractionExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open NCG.CompactResolventDiracSpectralScreensExact

/-- Orthogonal resolvent screens are contractions. -/
theorem norm_diracSpectralScreen_apply_le
    (S : SpectralTriple A H) (s : Finset ℂ) (x : H) :
    ‖diracSpectralScreen S s x‖ ≤ ‖x‖ := by
  let P := (diracSpectralScreen S s).toLinearMap
  have hp : P.IsSymmetricProjection :=
    diracSpectralScreen_isSymmetricProjection S s
  obtain ⟨hproj, heq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp
  letI : (LinearMap.range P).HasOrthogonalProjection := hproj
  change ‖P x‖ ≤ ‖x‖
  rw [heq]
  exact (LinearMap.range P).norm_starProjection_apply_le x

end NCG.CompactResolventSpectralProjectionContractionExact
