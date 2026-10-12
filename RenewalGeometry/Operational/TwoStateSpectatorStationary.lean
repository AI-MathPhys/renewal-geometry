/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.Stochastics.QuantumInformation.SpectatorProduct
import RenewalGeometry.Renewal.TwoStateRenewal
open MathPhys
/-!
# Two-cell spectator stationarity for the two-state renewal

Split out of `RenewalGeometry.Operational.SpectatorProduct` (`thm:renewal-spectator-product`,
Gran-Tensor manuscript): the product stationary state `π ⊗ π` of the two-cell transfer
`M₀ ⊗ M₀` of the exact two-state renewal `TwoStateRenewal`.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry

/-- The product stationary state `π ⊗ π` of the two-cell
transfer `M₀ ⊗ M₀`. -/
theorem two_state_spectator_stationary :
    ((fun q : Fin 2 × Fin 2 =>
        (![5/11, 6/11] : Fin 2 → ℝ) q.1 * ![5/11, 6/11] q.2)
      ᵥ* (renM0 ⊗ₖ renM0))
    = fun q : Fin 2 × Fin 2 =>
        (![5/11, 6/11] : Fin 2 → ℝ) q.1 * ![5/11, 6/11] q.2 := by
  rw [kronecker_vecMul_prod]
  rw [two_state_active_renewal.2.2.1]

end RenewalGeometry
