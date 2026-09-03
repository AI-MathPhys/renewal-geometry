/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCStarAlgebraControlledUnitaryGenerationExact
import NCG.Grand.FiniteControlledUnitaryProcessCombExact
import NCG.Grand.FiniteDiracCalibratedUnitaryCurveExact
import NCG.Grand.FiniteSpectralCommutatorGramCarrierExact

/-!
# Marked Renewal realization of an arbitrary coordinate finite spectral packet

This is the target-independent finite essential-surjectivity theorem.  A
finite spectral packet is supplied in a chosen orthonormal coordinate basis,
together with its declared Dirac, grading, and real-operation identities.
The construction adds a finite spanning bank of physical unitary controls, a
positive deterministic marked process comb with support-minimal
purification, the exact calibrated Dirac tangent, and the source-minimal
commutator Gram carrier.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact

noncomputable section

universe u

open NCG.FiniteCStarAlgebraControlledUnitaryGenerationExact
open NCG.FiniteDiracCalibratedUnitaryCurveExact
open NCG.FiniteSpectralCommutatorGramCarrierExact

variable {A : Type u} {K : Type} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype K] [DecidableEq K]

/-- A finite spectral packet in a chosen orthonormal coordinate basis. -/
structure CoordinateFiniteSpectralPacket (A : Type u) (K : Type)
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Fintype K] [DecidableEq K] where
  representation : A → Matrix K K ℂ
  dirac : Matrix K K ℂ
  dirac_isHermitian : dirac.IsHermitian

/-- A finite real-even spectral packet, extending the plain packet by the
declared grading, real operation, and opposite representation. -/
structure CoordinateFiniteRealEvenSpectralPacket (A : Type u) (K : Type)
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Fintype K] [DecidableEq K] where
  representation : A → Matrix K K ℂ
  oppositeRepresentation : A → Matrix K K ℂ
  dirac : Matrix K K ℂ
  dirac_isHermitian : dirac.IsHermitian
  grading : Matrix K K ℂ
  grading_unitary :
    gradingᴴ * grading = 1 ∧ grading * gradingᴴ = 1
  dirac_odd : dirac * grading + grading * dirac = 0
  realOperation : (K → ℂ) → (K → ℂ)
  realOperation_smul : ∀ (z : ℂ) (x : K → ℂ),
    realOperation (z • x) = star z • realOperation x
  realOperation_involutive : ∀ x : K → ℂ,
    realOperation (realOperation x) = x
  realOperation_dirac : ∀ x : K → ℂ,
    realOperation (dirac *ᵥ x) = dirac *ᵥ realOperation x
  realOperation_grading : ∀ x : K → ℂ,
    realOperation (grading *ᵥ x) = grading *ᵥ realOperation x
  realOperation_representation : ∀ (b : A) (x : K → ℂ),
    realOperation (representation (star b) *ᵥ realOperation x) =
      oppositeRepresentation b *ᵥ x

/-- The full matrix control bank, augmented by an identity mark so that the
mark type remains inhabited for a zero-dimensional carrier. -/
abbrev MarkIndex (K : Type) [Fintype K] [DecidableEq K] :=
  Option (ControlIndex (Matrix K K ℂ))

local instance markIndexDecidableEq : DecidableEq (MarkIndex K) :=
  Classical.decEq _

/-- Matrix implemented by a marked finite control. -/
def markedControlUnitary : MarkIndex K → Matrix K K ℂ
  | none => 1
  | some q =>
      (controlledUnitary (Matrix K K ℂ) q : Matrix K K ℂ)

theorem markedControlUnitary_twoSided (m : MarkIndex K) :
    markedControlUnitary (K := K) m *
        (markedControlUnitary (K := K) m)ᴴ = 1 ∧
      (markedControlUnitary (K := K) m)ᴴ *
        markedControlUnitary (K := K) m = 1 := by
  cases m with
  | none => simp [markedControlUnitary]
  | some q =>
      constructor
      · simpa [markedControlUnitary, Matrix.star_eq_conjTranspose] using
          Unitary.mul_star_self_of_mem
            (controlledUnitary (Matrix K K ℂ) q).prop
      · simpa [markedControlUnitary, Matrix.star_eq_conjTranspose] using
          Unitary.star_mul_self_of_mem
            (controlledUnitary (Matrix K K ℂ) q).prop

theorem markedControlUnitary_span :
    Submodule.span ℂ (Set.range
      (markedControlUnitary (K := K))) = ⊤ := by
  let B := Matrix K K ℂ
  have hbase : Submodule.span ℂ (Set.range fun q : ControlIndex B =>
      (controlledUnitary B q : B)) = ⊤ :=
    finite_controlled_unitaries_span B
  apply top_unique
  rw [← hbase]
  apply Submodule.span_mono
  rintro X ⟨q, rfl⟩
  exact ⟨some q, rfl⟩

/-- A finite marked Renewal realization of a plain coordinate spectral
packet. -/
structure MarkedRenewalRealization
    (P : CoordinateFiniteSpectralPacket A K) where
  amplitude : MarkIndex K → ℂ
  comb : NCG.FiniteDeterministicComb
    (NCG.controlledUnitaryOneStepPrefixes amplitude
      (markedControlUnitary (K := K))) 1
  controlsSpan : Submodule.span ℂ (Set.range
    (markedControlUnitary (K := K))) = ⊤
  diracTangent :
    (∀ t : ℝ,
      star (calibratedUnitaryCurve P.dirac t) *
          calibratedUnitaryCurve P.dirac t = 1 ∧
      calibratedUnitaryCurve P.dirac t *
          star (calibratedUnitaryCurve P.dirac t) = 1) ∧
    Complex.I • deriv (calibratedUnitaryCurve P.dirac) 0 = P.dirac
  commutatorCarrier :
    let G := commutatorGram P.dirac
      (markedControlUnitary (K := K))
    G.PosSemidef ∧
    (∀ c, G *ᵥ c = 0 ↔
      commutatorSynthesis P.dirac
        (markedControlUnitary (K := K)) *ᵥ c = 0) ∧
    (G = (CFC.sqrt G)ᴴ * CFC.sqrt G ∧
      (∀ {C : Type} [Fintype C]
        (S : Matrix C (MarkIndex K) ℂ),
        G = Sᴴ * S → G.rank ≤ Fintype.card C) ∧
      (CFC.sqrt G).rank = G.rank)

/-- A finite marked Renewal realization carrying every declared real-even
spectral operation and the source-minimal one-form carrier. -/
structure RealEvenMarkedRenewalRealization
    (P : CoordinateFiniteRealEvenSpectralPacket A K) where
  amplitude : MarkIndex K → ℂ
  comb : NCG.FiniteDeterministicComb
    (NCG.controlledUnitaryOneStepPrefixes amplitude
      (markedControlUnitary (K := K))) 1
  controlsSpan : Submodule.span ℂ (Set.range
    (markedControlUnitary (K := K))) = ⊤
  diracTangent :
    (∀ t : ℝ,
      star (calibratedUnitaryCurve P.dirac t) *
          calibratedUnitaryCurve P.dirac t = 1 ∧
      calibratedUnitaryCurve P.dirac t *
          star (calibratedUnitaryCurve P.dirac t) = 1) ∧
    Complex.I • deriv (calibratedUnitaryCurve P.dirac) 0 = P.dirac
  diracOdd : P.dirac * P.grading + P.grading * P.dirac = 0
  commutatorCarrier :
    let G := commutatorGram P.dirac
      (markedControlUnitary (K := K))
    G.PosSemidef ∧
    (∀ c, G *ᵥ c = 0 ↔
      commutatorSynthesis P.dirac
        (markedControlUnitary (K := K)) *ᵥ c = 0) ∧
    (G = (CFC.sqrt G)ᴴ * CFC.sqrt G ∧
      (∀ {C : Type} [Fintype C]
        (S : Matrix C (MarkIndex K) ℂ),
        G = Sᴴ * S → G.rank ≤ Fintype.card C) ∧
      (CFC.sqrt G).rank = G.rank)
  gradingReal :
    (P.gradingᴴ * P.grading = 1 ∧ P.grading * P.gradingᴴ = 1) ∧
    (∀ (z : ℂ) (x : K → ℂ), P.realOperation (z • x) =
      star z • P.realOperation x) ∧
    (∀ x : K → ℂ, P.realOperation (P.realOperation x) = x) ∧
    (∀ x : K → ℂ, P.realOperation (P.dirac *ᵥ x) =
      P.dirac *ᵥ P.realOperation x) ∧
    (∀ x : K → ℂ, P.realOperation (P.grading *ᵥ x) =
      P.grading *ᵥ P.realOperation x) ∧
    (∀ (b : A) (x : K → ℂ), P.realOperation
      (P.representation (star b) *ᵥ P.realOperation x) =
        P.oppositeRepresentation b *ᵥ x)

/-- Essential-image alternative I1: every plain coordinate finite spectral
packet has a legitimate finite marked Renewal realization. -/
theorem every_finiteSpectralPacket_has_finiteMarkedRenewalRealization
    (P : CoordinateFiniteSpectralPacket A K) :
    Nonempty (MarkedRenewalRealization P) := by
  let U := markedControlUnitary (K := K)
  have hU : ∀ m, U m * (U m)ᴴ = 1 :=
    fun m => (markedControlUnitary_twoSided (K := K) m).1
  obtain ⟨c, ⟨C⟩⟩ :=
    NCG.exists_controlledUnitary_finiteDeterministicComb U hU
  have hDstar : star P.dirac = P.dirac := by
    change P.diracᴴ = P.dirac
    exact P.dirac_isHermitian.eq
  refine ⟨{
    amplitude := c
    comb := C
    controlsSpan := markedControlUnitary_span (K := K)
    diracTangent := ⟨fun t => ⟨
      star_calibratedUnitaryCurve_mul P.dirac hDstar t,
      calibratedUnitaryCurve_mul_star P.dirac hDstar t⟩,
      calibratedUnitaryCurve_recovers_generator P.dirac⟩
    commutatorCarrier :=
      finite_spectral_commutator_gram_carrier_exact P.dirac U }⟩

/-- The same construction transports every declared grading and real
operation of a finite real-even packet. -/
theorem every_finiteRealEvenSpectralPacket_has_finiteMarkedRenewalRealization
    (P : CoordinateFiniteRealEvenSpectralPacket A K) :
    Nonempty (RealEvenMarkedRenewalRealization P) := by
  let U := markedControlUnitary (K := K)
  have hU : ∀ m, U m * (U m)ᴴ = 1 :=
    fun m => (markedControlUnitary_twoSided (K := K) m).1
  obtain ⟨c, ⟨C⟩⟩ :=
    NCG.exists_controlledUnitary_finiteDeterministicComb U hU
  have hDstar : star P.dirac = P.dirac := by
    change P.diracᴴ = P.dirac
    exact P.dirac_isHermitian.eq
  refine ⟨{
    amplitude := c
    comb := C
    controlsSpan := markedControlUnitary_span (K := K)
    diracTangent := ⟨fun t => ⟨
      star_calibratedUnitaryCurve_mul P.dirac hDstar t,
      calibratedUnitaryCurve_mul_star P.dirac hDstar t⟩,
      calibratedUnitaryCurve_recovers_generator P.dirac⟩
    diracOdd := P.dirac_odd
    commutatorCarrier :=
      finite_spectral_commutator_gram_carrier_exact P.dirac U
    gradingReal := ⟨P.grading_unitary, P.realOperation_smul,
      P.realOperation_involutive, P.realOperation_dirac,
      P.realOperation_grading, P.realOperation_representation⟩ }⟩

end

end NCG.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
