/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CriticalWeightedResponseLocality

/-!
# Weighted Cauchy bounds for critical responses

Exact wrapper for the updated Gran--Tensor weighted-holomorphy theorem.
The vector-valued Cauchy argument is supplied by
`CriticalWeightedResponseLocality`; here its parameters are specialized to
the manuscript's polydisc supremum M_alpha,t.
-/

namespace NCG
namespace WeightedCauchyCriticalResponses

open CriticalWeightedResponseLocality

universe u v w

variable {Q : Type u} [Nonempty Q]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {Region : Type w}

/-- Exact first and mixed weighted Cauchy estimates in the updated notation. -/
theorem weighted_cauchy_bounds
    (P : Packet Q F Region) {rhoZ rhoW M : ℝ}
    (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (holo : HolomorphicOnClosedPolydisc P rhoZ rhoW)
    (hM : HasWeightedCollar P rhoZ rhoW M 0 0) :
    weightedNorm (fun q => P.weight q P.firstResponse) ≤ M / rhoZ ∧
    weightedNorm (fun q => P.weight q P.pairResponse) ≤
      M / (rhoZ * rhoW) := by
  have h := critical_weighted_bounds P hrhoZ hrhoW holo hM
  simpa using h

/-- The same Cauchy estimates together with every physical exponential
collar compression. -/
theorem weighted_cauchy_quasilocality
    (P : Packet Q F Region) {rhoZ rhoW M mu : ℝ}
    (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW) (hmu : 0 ≤ mu)
    (holo : HolomorphicOnClosedPolydisc P rhoZ rhoW)
    (hM : HasWeightedCollar P rhoZ rhoW M 0 0)
    (X Y : Region) :
    weightedNorm (fun q => P.weight q P.firstResponse) ≤ M / rhoZ ∧
    weightedNorm (fun q => P.weight q P.pairResponse) ≤
      M / (rhoZ * rhoW) ∧
    ‖P.compress X Y P.firstResponse‖ ≤
      (M / rhoZ) * Real.exp (-mu * P.distance X Y) ∧
    ‖P.compress X Y P.pairResponse‖ ≤
      (M / (rhoZ * rhoW)) * Real.exp (-mu * P.distance X Y) := by
  have h := critical_weighted_first_pair_locality
    P hrhoZ hrhoW hmu holo hM X Y
  simpa using h

end WeightedCauchyCriticalResponses
end NCG
