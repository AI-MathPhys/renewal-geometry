/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3UniformEnergyConsistencyExact

/-!
# Operator derivative control from the full A3 energy constraint

Riesz representation converts an actual scalar derivative to the Euclidean
gradient used by the twelve-root tight frame. A uniform channel error epsilon
and mesh energy at most one imply derivative norm at most one plus 2 epsilon.
-/

namespace NCG.A3DerivativeEnergyComparison

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency

noncomputable section

def derivativeVector (L : Space →L[ℝ] ℝ) : Space :=
  (InnerProductSpace.toDual ℝ Space).symm L

theorem inner_derivativeVector (L : Space →L[ℝ] ℝ) (v : Space) :
    inner ℝ (derivativeVector L) v = L v := InnerProductSpace.toDual_symm_apply

theorem norm_derivativeVector (L : Space →L[ℝ] ℝ) : ‖derivativeVector L‖ = ‖L‖ :=
  (InnerProductSpace.toDual ℝ Space).symm.norm_map L

theorem norm_derivative_le_of_energy_and_channel_error
    (f : Space → ℝ) (p : Space) (h : ℝ) (L : Space →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (henergy : sampledEnergy f p h ≤ 1)
    (herr : ∀ r, |rootDifference f p h r - L (root r)| ≤ ε) :
    ‖L‖ ≤ 1 + 2 * ε := by
  have herror := sqrt_energy_error_le f p (derivativeVector L) h ε hε (fun r => by
    simpa only [inner_derivativeVector] using herr r)
  rw [norm_derivativeVector, abs_le] at herror
  have hsq := Real.sq_sqrt (sampledEnergy_nonneg f p h)
  have hn := Real.sqrt_nonneg (sampledEnergy f p h)
  nlinarith

end

end NCG.A3DerivativeEnergyComparison
