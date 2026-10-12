/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.OperatorAlgebras.CommonCentre
import RenewalGeometry.Commutant.LoadedHoweDualityPacketExact
open MathPhys

/-!
# Common centre for source-complete joint duality packets

Split out of `RenewalGeometry.Commutant.CommonCentre`: the packet form
`packet_common_centre` of the common-centre clause `eq:common-centre` of the
spacetime–gauge duality paper, for the action and multiplicity algebras of a
`SourceCompleteJointDualityPacket`.
-/

open Matrix

namespace RenewalGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`eq:common-centre`.**  For every source-complete joint duality packet,
`Z(𝒜_act) = Z(𝓜_type) = 𝒜_act ∩ 𝓜_type`. -/
theorem packet_common_centre {r QEnd : Type*} [Fintype r] [DecidableEq r] [Semiring QEnd]
    [Algebra ℂ QEnd] (P : SourceCompleteJointDualityPacket n r QEnd) :
    matCentre (P.actionAlgebra : Set (Matrix n n ℂ)) =
        (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) ∧
      matCentre (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
        (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) ∧
      matCentre (P.actionAlgebra : Set (Matrix n n ℂ)) =
        matCentre (P.multiplicityAlgebra : Set (Matrix n n ℂ)) := by
  have h := sourceCompleteJointPacket_loadedHoweDuality P
  exact common_centre _ _ h.1 h.2.1

end RenewalGeometry
