/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressEulerRow
import RenewalGeometry.Continuum.NativeModelExample

/-!
# Non-vacuity of the coframe row (bridge step P3-stress of `thm:native-closure`)

The hypotheses of `NativeStressEuler.coframe_row`, `coframe_row_einstein` and
`einstein_equation_iff` are satisfiable: on the concrete native model
`NativeModelExample.diracModel` (Dirac matrices with the Clifford relations checked entrywise,
`σ(ω) = ¼ω_{ab}γ^aγ^b`, `κ = 1`) and the flat vacuum `flat` (`e = 1`, all matter fields zero),
which is `L`-periodic for every `L > 0`, every hypothesis is discharged.
-/

namespace RenewalGeometry

namespace NativeStressExample

open NativeModel NativeModelExample NativeStressEuler NativeBosonicEuler PalatiniEuler
open NativeScaling (Mat eta)
open DiscreteEulerConsistency (R4 jet1 contEuler)
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem flat_periodic (L : ℝ) : IsLPeriodic L (eF flat) := fun _ _ => rfl

/-- `coframe_row` on the flat vacuum of `diracModel`, all hypotheses discharged. -/
theorem flat_coframe_row (z : R4) {S : Mat} (hS : (eta * S)ᵀ = eta * S) :
    contEuler (L0 diracModel.toData) flat z (coframeDir (S * (flat z).1)) =
      einsteinCov diracModel.κ diracModel.Λ (eF flat) z (S * (flat z).1) +
        NativeDensity.volume (flat z).1 / 2 * ∑ a, ∑ b,
          smStressUp diracModel.toData (jet1 flat z) a b *
            metricVarM (flat z).1 (S * (flat z).1) a b :=
  coframe_row diracModel.toData diracModel.cliff diracModel.sigma_eq flat_smooth one_pos
    (flat_periodic 1) flat_det z hS

/-- `einstein_equation_iff` on the flat vacuum of `diracModel` (`κ = 1 ≠ 0`). -/
theorem flat_einstein_iff (z : R4) :
    (∀ S : Mat, (eta * S)ᵀ = eta * S →
        contEuler (L0 diracModel.toData) flat z (coframeDir (S * (flat z).1)) = 0) ↔
      ∀ a b, einsteinRes diracModel.toData flat z a b +
        einsteinRes diracModel.toData flat z b a = 0 :=
  einstein_equation_iff diracModel.toData diracModel.cliff diracModel.sigma_eq
    (by norm_num [diracModel]) flat_smooth one_pos (flat_periodic 1) flat_det z

end

end NativeStressExample

end RenewalGeometry
