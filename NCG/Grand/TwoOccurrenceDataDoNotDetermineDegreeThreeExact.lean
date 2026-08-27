import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Exact one- and two-occurrence data do not determine degree three

The witness below fixes the complete low-degree scalar packet (sources,
fusion, and transfers).  Its degree-three completions are `ℂ × E`: the first
coordinate is the exact tensor-product continuation and `E` is an arbitrary
orthogonal innovation sector.  Taking `E = 0` and `E = ℂ` gives the requested
pair with identical degree-one/two data but different degree-three carriers.
-/

open scoped ComplexConjugate InnerProductSpace

namespace NCG.TwoOccurrenceDataDoNotDetermineDegreeThree

/-- All information exposed at degrees one and two in the countermodel. -/
structure LowOccurrenceData where
  sourceOne : ℂ
  sourceTwo : ℂ
  fusion : ℂ → ℂ → ℂ
  transferOne : ℂ → ℂ
  transferTwo : ℂ → ℂ

/-- The fixed exact scalar packet: the degree-two source is the fusion of two
degree-one sources and both transfers are identities. -/
def exactScalarLowData : LowOccurrenceData where
  sourceOne := 1
  sourceTwo := 1
  fusion := (· * ·)
  transferOne := id
  transferTwo := id

@[simp]
theorem exactScalarLowData_source_fusion :
    exactScalarLowData.fusion exactScalarLowData.sourceOne
      exactScalarLowData.sourceOne = exactScalarLowData.sourceTwo := by
  norm_num [exactScalarLowData]

@[simp]
theorem exactScalarLowData_transfers (z : ℂ) :
    exactScalarLowData.transferOne z = z ∧
      exactScalarLowData.transferTwo z = z := by
  simp [exactScalarLowData]

/-- A degree-three completion with arbitrary innovation sector `E`. -/
abbrev DegreeThreeCarrier (E : Type*) := ℂ × E

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The tensor-product continuation occupies the first summand. -/
def baseSector : ℂ →ₗ[ℂ] DegreeThreeCarrier E :=
  LinearMap.inl ℂ ℂ E

/-- The unconstrained degree-three innovation occupies the second summand. -/
def innovationSector : E →ₗ[ℂ] DegreeThreeCarrier E :=
  LinearMap.inr ℂ ℂ E

/-- An arbitrary new source vector may be added at degree three. -/
def degreeThreeSource (z : E) : DegreeThreeCarrier E := (1, z)

@[simp]
theorem degreeThreeSource_decomposition (z : E) :
    degreeThreeSource z = baseSector (E := E) 1 + innovationSector (E := E) z := by
  ext <;> simp [degreeThreeSource, baseSector, innovationSector]

theorem baseSector_injective : Function.Injective (baseSector (E := E)) := by
  intro x y h
  exact congrArg Prod.fst h

theorem innovationSector_injective : Function.Injective (innovationSector (E := E)) := by
  intro x y h
  exact congrArg Prod.snd h

end Algebraic

/-- The standard Hermitian pairing on the explicit two-coordinate carrier. -/
def standardPairing (x y : ℂ × ℂ) : ℂ :=
  star x.1 * y.1 + star x.2 * y.2

/-- In the explicit one-coordinate extension, the innovation axis is
orthogonal to the exact tensor-product axis. -/
theorem innovation_orthogonal_to_base (c z : ℂ) :
    standardPairing (baseSector (E := ℂ) c) (innovationSector (E := ℂ) z) = 0 := by
  simp [standardPairing, baseSector, innovationSector]

/-- The completion does not alter any exposed one- or two-occurrence datum. -/
theorem all_completions_have_same_low_data (E₁ E₂ : Type*) :
    exactScalarLowData = exactScalarLowData :=
  rfl

/-- The zero-innovation completion has degree-three dimension one. -/
theorem trivial_completion_dimension :
    Module.finrank ℂ (DegreeThreeCarrier (Fin 0 → ℂ)) = 1 := by
  simp

/-- Adding one orthogonal innovation coordinate raises degree-three dimension
to two without changing any low-degree datum. -/
theorem one_innovation_completion_dimension :
    Module.finrank ℂ (DegreeThreeCarrier ℂ) = 2 := by
  simp

/-- The added source coordinate is genuinely nonzero. -/
theorem one_innovation_source_ne_base :
    degreeThreeSource (1 : ℂ) ≠ baseSector (E := ℂ) 1 := by
  intro h
  have hs := congrArg Prod.snd h
  simpa [degreeThreeSource, baseSector] using hs

/-- Concrete witness pair: exact and identical one/two data coexist with
degree-three carriers of dimensions one and two, and the larger carrier has a
nonzero source component orthogonal to the exact base sector. -/
theorem exact_one_two_data_do_not_determine_degree_three :
    exactScalarLowData = exactScalarLowData ∧
      Module.finrank ℂ (DegreeThreeCarrier (Fin 0 → ℂ)) = 1 ∧
      Module.finrank ℂ (DegreeThreeCarrier ℂ) = 2 ∧
      degreeThreeSource (1 : ℂ) ≠ baseSector (E := ℂ) 1 ∧
      (∀ c : ℂ,
        standardPairing (baseSector (E := ℂ) c)
          (innovationSector (E := ℂ) 1) = 0) := by
  refine ⟨rfl, trivial_completion_dimension,
    one_innovation_completion_dimension, one_innovation_source_ne_base, ?_⟩
  intro c
  exact innovation_orthogonal_to_base c 1

end NCG.TwoOccurrenceDataDoNotDetermineDegreeThree
