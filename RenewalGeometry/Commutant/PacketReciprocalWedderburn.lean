/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.OperatorAlgebras.ReciprocalWedderburnKronecker
import RenewalGeometry.Commutant.PacketCommonCentre
open MathPhys

/-!
# Reciprocal Wedderburn decomposition for source-complete joint duality packets

Split out of `RenewalGeometry.Commutant.ReciprocalWedderburnKronecker`:
`packet_reciprocal_wedderburn`, the packet form of `cor:reciprocal-wedderburn`, with the
common-centre identity `eq:common-centre` and the shared central sector projections
(`sectorProjection_mem`).
-/

open MathPhys

open Matrix Kronecker

namespace RenewalGeometry

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **`cor:reciprocal-wedderburn` for packets.**  For every source-complete joint duality
packet (the hypotheses of `thm:main-duality`), the action algebra and the multiplicity
algebra are simultaneously unitarily equivalent to the reciprocal Kronecker algebras
`⊕_b M_{I b} ⊗ 1` and `⊕_b 1 ⊗ M_{J b}` on `⊕_b ℂ^{I b} ⊗ ℂ^{J b}`
(`eq:wedderburn-H`, `eq:wedderburn-action`, `eq:wedderburn-multiplicity`), the common
centre is `𝒜_act ∩ 𝓜_type` (`eq:common-centre`), and every sector projection is a common
central projection of both algebras. -/
theorem packet_reciprocal_wedderburn {r QEnd : Type*} [Fintype r] [DecidableEq r]
    [Semiring QEnd] [Algebra ℂ QEnd] (P : SourceCompleteJointDualityPacket n r QEnd) :
    (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (fun x => Wᴴ * x * W) '' (P.actionAlgebra : Set (Matrix n n ℂ)) = actionBlockSet I J ∧
      (fun x => Wᴴ * x * W) '' (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
        multBlockSet I J ∧
      (∀ b, sectorProjection I J b ∈ actionBlockSet I J ∧
        sectorProjection I J b ∈ multBlockSet I J ∧
        sectorProjection I J b ∈ matCentre (actionBlockSet I J) ∧
        sectorProjection I J b ∈ matCentre (multBlockSet I J))) ∧
    matCentre (P.actionAlgebra : Set (Matrix n n ℂ)) =
      (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) ∧
    matCentre (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
      (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) := by
  obtain ⟨ι, _, _, I, J, _, _, _, _, W, hW1, hW2, hNI, hNJ, hA, hM⟩ :=
    reciprocal_wedderburn P.actionAlgebra P.action_starClosed
  refine ⟨⟨ι, inferInstance, inferInstance, I, J, inferInstance, inferInstance, inferInstance,
    inferInstance, W, hW1, hW2, hNI, hNJ, hA, ?_, ?_⟩, (packet_common_centre P).1,
    (packet_common_centre P).2.1⟩
  · rw [← P.edgeCommutant]
    exact hM
  · intro b
    obtain ⟨h1, h2⟩ := sectorProjection_mem (I := I) (J := J) b
    refine ⟨h1, h2, ⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
    · rw [matCommutant_actionBlockSet]
      exact h2
    · rw [matCommutant_multBlockSet]
      exact h1

end RenewalGeometry
