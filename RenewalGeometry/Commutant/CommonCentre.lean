/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.LoadedHoweDualityPacketExact

/-!
# Common centre of mutual commutants and its unitary transport

Covers the common-centre clause `eq:common-centre` and the unitary-covariance clause of
`cor:reciprocal-wedderburn` of the spacetime–gauge duality paper.

* `matCentre S = S ∩ S'` is the centre of a set of matrices.
* `common_centre`: if `A' = M` and `M' = A` then `Z(A) = Z(M) = A ∩ M`.
* `packet_common_centre`: the same for the action and multiplicity algebras of a
  `SourceCompleteJointDualityPacket` (`eq:common-centre`).
* `conjSet u S = u S u⁻¹`, `matCommutant_conjSet`, `common_centre_transport`: a similarity
  (in particular a unitary equivalence) transports the two algebras, the mutual-commutant
  identities and the common centre simultaneously.

The reciprocal Kronecker form `𝒜 ≅ ⊕ B(H^act) ⊗ I`, `𝓜 ≅ ⊕ I ⊗ B(H^mult)` of the corollary
is not formalised here.
-/

open Matrix

namespace RenewalGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The centre `Z(S) = S ∩ S'` of a set of matrices. -/
def matCentre (S : Set (Matrix n n ℂ)) : Set (Matrix n n ℂ) :=
  S ∩ matCommutant S

/-- **Common centre of mutual commutants.**  If `A' = M` and `M' = A` then
`Z(A) = Z(M) = A ∩ M`. -/
theorem common_centre (A M : Set (Matrix n n ℂ)) (hA : matCommutant A = M)
    (hM : matCommutant M = A) :
    matCentre A = A ∩ M ∧ matCentre M = A ∩ M ∧ matCentre A = matCentre M := by
  unfold matCentre
  rw [hA, hM, Set.inter_comm M A]
  exact ⟨rfl, rfl, rfl⟩

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

/-! ### Transport along a similarity -/

/-- Conjugation `x ↦ u x u⁻¹` by an invertible matrix. -/
def conjMap (u : (Matrix n n ℂ)ˣ) (x : Matrix n n ℂ) : Matrix n n ℂ :=
  (u : Matrix n n ℂ) * x * (↑u⁻¹ : Matrix n n ℂ)

/-- The image `u S u⁻¹` of a set of matrices under a similarity. -/
def conjSet (u : (Matrix n n ℂ)ˣ) (S : Set (Matrix n n ℂ)) : Set (Matrix n n ℂ) :=
  conjMap u '' S

theorem conjMap_injective (u : (Matrix n n ℂ)ˣ) : Function.Injective (conjMap u) := by
  intro x y hxy
  have h := congrArg (fun z => (↑u⁻¹ : Matrix n n ℂ) * z * (u : Matrix n n ℂ)) hxy
  simpa [conjMap, mul_assoc] using h

/-- The commutant of a conjugated set is the conjugated commutant:
`(u S u⁻¹)' = u S' u⁻¹`. -/
theorem matCommutant_conjSet (u : (Matrix n n ℂ)ˣ) (S : Set (Matrix n n ℂ)) :
    matCommutant (conjSet u S) = conjSet u (matCommutant S) := by
  ext T
  constructor
  · intro hT
    refine ⟨(↑u⁻¹ : Matrix n n ℂ) * T * (u : Matrix n n ℂ), fun a ha => ?_, by
      simp [conjMap, mul_assoc]⟩
    have h := hT _ ⟨a, ha, rfl⟩
    simp only [conjMap] at h
    calc (↑u⁻¹ : Matrix n n ℂ) * T * (u : Matrix n n ℂ) * a
        = (↑u⁻¹ : Matrix n n ℂ) * (T * ((u : Matrix n n ℂ) * a * (↑u⁻¹ : Matrix n n ℂ))) *
            (u : Matrix n n ℂ) := by simp [mul_assoc]
      _ = (↑u⁻¹ : Matrix n n ℂ) * (((u : Matrix n n ℂ) * a * (↑u⁻¹ : Matrix n n ℂ)) * T) *
            (u : Matrix n n ℂ) := by rw [h]
      _ = a * ((↑u⁻¹ : Matrix n n ℂ) * T * (u : Matrix n n ℂ)) := by simp [mul_assoc]
  · rintro ⟨S', hS', rfl⟩ _ ⟨a, ha, rfl⟩
    have h := hS' a ha
    simp only [conjMap]
    calc (u : Matrix n n ℂ) * S' * (↑u⁻¹ : Matrix n n ℂ) *
          ((u : Matrix n n ℂ) * a * (↑u⁻¹ : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * (S' * a) * (↑u⁻¹ : Matrix n n ℂ) := by simp [mul_assoc]
      _ = (u : Matrix n n ℂ) * (a * S') * (↑u⁻¹ : Matrix n n ℂ) := by rw [h]
      _ = (u : Matrix n n ℂ) * a * (↑u⁻¹ : Matrix n n ℂ) *
            ((u : Matrix n n ℂ) * S' * (↑u⁻¹ : Matrix n n ℂ)) := by simp [mul_assoc]

/-- The centre of a conjugated set is the conjugated centre. -/
theorem matCentre_conjSet (u : (Matrix n n ℂ)ˣ) (S : Set (Matrix n n ℂ)) :
    matCentre (conjSet u S) = conjSet u (matCentre S) := by
  unfold matCentre
  rw [matCommutant_conjSet]
  unfold conjSet
  rw [← Set.image_inter (conjMap_injective u)]

/-- **Simultaneous transport (`cor:reciprocal-wedderburn`, covariance clause).**  A
similarity `u` (in particular a unitary equivalence of packets) transports mutual
commutants to mutual commutants and the common centre to the common centre. -/
theorem common_centre_transport (u : (Matrix n n ℂ)ˣ) (A M : Set (Matrix n n ℂ))
    (hA : matCommutant A = M) (hM : matCommutant M = A) :
    matCommutant (conjSet u A) = conjSet u M ∧
      matCommutant (conjSet u M) = conjSet u A ∧
      matCentre (conjSet u A) = conjSet u (matCentre A) ∧
      matCentre (conjSet u M) = conjSet u (matCentre A) ∧
      matCentre (conjSet u A) = conjSet u A ∩ conjSet u M := by
  have hc := common_centre A M hA hM
  refine ⟨by rw [matCommutant_conjSet, hA], by rw [matCommutant_conjSet, hM],
    matCentre_conjSet u A, ?_, ?_⟩
  · rw [matCentre_conjSet, hc.2.2]
  · rw [matCentre_conjSet, hc.1]
    exact Set.image_inter (conjMap_injective u)

end RenewalGeometry
