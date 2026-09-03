/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactResolventSpectralProjectionContractionExact

/-!
# Strong transfer through compact-resolvent spectral projections

The finite resolvent spectral screens are orthogonal contractions converging
strongly to the identity.  Therefore they may be applied to any convergent
net of vectors without changing its limit.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace NCG.CompactResolventSpectralProjectionTransferExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open NCG.CompactResolventDiracSpectralScreensExact
open NCG.CompactResolventSpectralProjectionContractionExact

/-- A strongly convergent family of orthogonal projections may be applied to
a convergent net of vectors without changing its limit. -/
theorem tendsto_diracSpectralScreen_apply_of_tendsto
    (S : SpectralTriple A H) {f : Finset ℂ → H} {x : H}
    (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun s => diracSpectralScreen S s (f s)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfNorm : Tendsto (fun s => ‖f s - x‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hf
  have hscreenNorm : Tendsto
      (fun s => ‖diracSpectralScreen S s x - x‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      (tendsto_diracSpectralScreen_apply S x)
  have hsum : Tendsto
      (fun s => ‖f s - x‖ + ‖diracSpectralScreen S s x - x‖)
      atTop (𝓝 0) := by
    simpa using hfNorm.add hscreenNorm
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hsum
  calc
    ‖diracSpectralScreen S s (f s) - x‖ =
        ‖diracSpectralScreen S s (f s - x) +
          (diracSpectralScreen S s x - x)‖ := by
            congr 1
            rw [map_sub]
            abel
    _ ≤ ‖diracSpectralScreen S s (f s - x)‖ +
        ‖diracSpectralScreen S s x - x‖ := norm_add_le _ _
    _ ≤ ‖f s - x‖ + ‖diracSpectralScreen S s x - x‖ :=
      add_le_add (norm_diracSpectralScreen_apply_le S s (f s - x)) le_rfl

end NCG.CompactResolventSpectralProjectionTransferExact
