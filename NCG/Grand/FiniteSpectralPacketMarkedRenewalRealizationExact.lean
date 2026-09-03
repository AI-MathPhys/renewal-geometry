/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCStarAlgebraControlledUnitaryGenerationExact
import NCG.Grand.FiniteControlledUnitaryProcessCombExact
import NCG.Grand.FiniteDiracCalibratedUnitaryCurveExact
import NCG.Grand.FiniteSpectralPacketGradingRealOperationsExact
import NCG.Grand.FiniteSpectralCommutatorGramCarrierExact

/-!
# Finite spectral packets have marked Renewal realizations

This module assembles the finite essential-surjectivity construction.  The
selected reference corner is the full matrix algebra on the packet's finite
Hilbert carrier.  A finite bank of controlled unitaries spans that corner; an
extra identity control makes the mark type nonempty even for a degenerate
carrier.  Equal-amplitude branches form a positive deterministic process comb
with canonical support-minimal purification.  The same realization carries
the exact Dirac tangent, source-minimal commutator Gram, grading, and conjugate
port certificates.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG.FiniteSpectralPacketMarkedRenewalRealizationExact

noncomputable section

open NCG.FiniteCStarAlgebraControlledUnitaryGenerationExact
open NCG.FiniteDiracCalibratedUnitaryCurveExact
open NCG.FiniteSpectralCommutatorGramCarrierExact
open NCG.FiniteSpectralPacketGradingRealOperationsExact
open NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet

variable {A I J : Type} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

abbrev HIndex (I J : Type) := I ⊕ J

/-- The finite control bank of the full selected matrix corner, augmented by
one identity mark so it is nonempty without a nondegeneracy assumption. -/
abbrev MarkIndex (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] :=
  Option (ControlIndex (Matrix (HIndex I J) (HIndex I J) ℂ))

local instance markIndexDecidableEq : DecidableEq (MarkIndex I J) :=
  Classical.decEq _

/-- Matrix carried by a marked control. -/
noncomputable def markedControlUnitary :
    MarkIndex I J → Matrix (HIndex I J) (HIndex I J) ℂ
  | none => 1
  | some q =>
      (controlledUnitary
        (Matrix (HIndex I J) (HIndex I J) ℂ) q :
        Matrix (HIndex I J) (HIndex I J) ℂ)

/-- Every marked control is two-sided unitary. -/
theorem markedControlUnitary_twoSided
    (m : MarkIndex I J) :
    markedControlUnitary (I := I) (J := J) m *
        (markedControlUnitary (I := I) (J := J) m)ᴴ = 1 ∧
      (markedControlUnitary (I := I) (J := J) m)ᴴ *
        markedControlUnitary (I := I) (J := J) m = 1 := by
  cases m with
  | none => simp [markedControlUnitary]
  | some q =>
      constructor
      · simpa [markedControlUnitary, Matrix.star_eq_conjTranspose] using
          Unitary.mul_star_self_of_mem
            (controlledUnitary
              (Matrix (HIndex I J) (HIndex I J) ℂ) q).prop
      · simpa [markedControlUnitary, Matrix.star_eq_conjTranspose] using
          Unitary.star_mul_self_of_mem
            (controlledUnitary
              (Matrix (HIndex I J) (HIndex I J) ℂ) q).prop

/-- The augmented bank still spans the entire selected full matrix corner. -/
theorem markedControlUnitary_span :
    Submodule.span ℂ (Set.range
      (markedControlUnitary (I := I) (J := J))) = ⊤ := by
  let B := Matrix (HIndex I J) (HIndex I J) ℂ
  have hbase : Submodule.span ℂ (Set.range fun q : ControlIndex B =>
      (controlledUnitary B q : B)) = ⊤ :=
    finite_controlled_unitaries_span B
  apply top_unique
  rw [← hbase]
  apply Submodule.span_mono
  rintro X ⟨q, rfl⟩
  exact ⟨some q, rfl⟩

/-- A legitimate finite marked Renewal realization of a packet: a finite
spanning control panel, a deterministic comb with its derived minimal
purification, and exact certificates for all declared spectral operations. -/
structure MarkedRenewalRealization
    (P : NCG.FiniteRealEvenSpectralizationExact.Packet
      (A := A) (I := I) (J := J)) where
  amplitude : MarkIndex I J → ℂ
  comb : NCG.FiniteDeterministicComb
    (NCG.controlledUnitaryOneStepPrefixes amplitude
      (markedControlUnitary (I := I) (J := J))) 1
  controlsSpan : Submodule.span ℂ (Set.range
    (markedControlUnitary (I := I) (J := J))) = ⊤
  diracTangent :
    (∀ t : ℝ,
      star (calibratedUnitaryCurve P.dirac t) *
          calibratedUnitaryCurve P.dirac t = 1 ∧
      calibratedUnitaryCurve P.dirac t *
          star (calibratedUnitaryCurve P.dirac t) = 1) ∧
    Complex.I • deriv (calibratedUnitaryCurve P.dirac) 0 = P.dirac
  diracOdd :
    P.dirac * P.grading + P.grading * P.dirac = 0
  commutatorCarrier :
    let G := commutatorGram P.dirac
      (markedControlUnitary (I := I) (J := J))
    G.PosSemidef ∧
    (∀ c, G *ᵥ c = 0 ↔
      commutatorSynthesis P.dirac
        (markedControlUnitary (I := I) (J := J)) *ᵥ c = 0) ∧
    (G = (CFC.sqrt G)ᴴ * CFC.sqrt G ∧
      (∀ {C : Type} [Fintype C]
        (S : Matrix C (MarkIndex I J) ℂ),
        G = Sᴴ * S → G.rank ≤ Fintype.card C) ∧
      (CFC.sqrt G).rank = G.rank)
  gradingReal :
    (P.gradingᴴ * P.grading = 1 ∧ P.grading * P.gradingᴴ = 1) ∧
    (∀ (z : ℂ) (x : P.HIndex → ℂ),
      NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P
        (z • x) = star z •
          NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P x) ∧
    (∀ x : P.HIndex → ℂ,
      NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P
        (NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P x) = x) ∧
    (∀ x : P.HIndex → ℂ,
      NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P
        (P.dirac *ᵥ x) = P.dirac *ᵥ
          NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P x) ∧
    (∀ x : P.HIndex → ℂ,
      NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P
        (P.grading *ᵥ x) = P.grading *ᵥ
          NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P x) ∧
    (∀ (b : A) (x : P.HIndex → ℂ),
      NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P
      (P.representation (star b) *ᵥ
        NCG.FiniteSpectralPacketGradingRealOperationsExact.Packet.realOperation P x) =
        P.oppositeRepresentation b *ᵥ x)

/-- Essential-image alternative I1: every finite packet has a finite marked
Renewal realization. -/
theorem finiteSpectralPacket_has_finiteMarkedRenewalRealization
    (P : NCG.FiniteRealEvenSpectralizationExact.Packet
      (A := A) (I := I) (J := J)) :
    Nonempty (MarkedRenewalRealization P) := by
  let U := markedControlUnitary (I := I) (J := J)
  have hU : ∀ m, U m * (U m)ᴴ = 1 :=
    fun m => (markedControlUnitary_twoSided (I := I) (J := J) m).1
  obtain ⟨c, ⟨C⟩⟩ := NCG.exists_controlledUnitary_finiteDeterministicComb U hU
  refine ⟨{
    amplitude := c
    comb := C
    controlsSpan := markedControlUnitary_span (I := I) (J := J)
    diracTangent := finiteSpectralization_dirac_controlled_unitary_tangent P
    diracOdd := P.dirac_odd
    commutatorCarrier := ?_
    gradingReal := finiteSpectralization_grading_real_operations_exact P }⟩
  exact finite_spectral_commutator_gram_carrier_exact P.dirac U

end

end NCG.FiniteSpectralPacketMarkedRenewalRealizationExact
