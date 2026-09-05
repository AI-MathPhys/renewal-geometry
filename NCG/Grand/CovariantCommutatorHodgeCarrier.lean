/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandCommutatorHodge
import NCG.Grand.GrandSMEasy

/-!
# Covariant commutator--Hodge carrier

This file proves the writer-independent part of
`thm:SM-commutator-Hodge` from the Gran--Tensor manuscript.  The earlier
file `GrandCommutatorHodge` performs the calculation for the standard Pauli
writer.  Here the writer is arbitrary: only tracelessness and its scaled
trace pairing are used.

The key two-by-two identity is the polarized Cayley--Hamilton identity

`τ₂(C(A,B) C(D,E)) = τ₂(A D) τ₂(B E) - τ₂(A E) τ₂(B D)`

for traceless matrices, where `C(A,B) = -(i/2)[A,B]`.  Substitution of the
writer Gram therefore gives exactly `λ²` times the exterior-square Gram.
-/

open Matrix

namespace NCG

/-- The normalized trace pairing used on two-by-two matrix writers. -/
noncomputable def normalizedTracePairing
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (A * B).trace / 2

/-- The Hermitian commutator carrier associated with two writer values. -/
noncomputable def matrixCommutatorCarrier
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-(Complex.I / 2)) • (A * B - B * A)

/-- Polarized Cayley--Hamilton in the form needed for the commutator--Hodge
metric.  Hermiticity is not needed for this algebraic identity. -/
theorem normalizedTracePairing_commutatorCarrier
    (A B D E : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0)
    (hD : D.trace = 0) (hE : E.trace = 0) :
    normalizedTracePairing (matrixCommutatorCarrier A B)
        (matrixCommutatorCarrier D E) =
      normalizedTracePairing A D * normalizedTracePairing B E -
        normalizedTracePairing A E * normalizedTracePairing B D := by
  rw [Matrix.trace_fin_two] at hA hB hD hE
  have hA' : A 1 1 = -A 0 0 := by linear_combination hA
  have hB' : B 1 1 = -B 0 0 := by linear_combination hB
  have hD' : D 1 1 = -D 0 0 := by linear_combination hD
  have hE' : E 1 1 = -E 0 0 := by linear_combination hE
  simp [normalizedTracePairing, matrixCommutatorCarrier,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, hA', hB', hD', hE']
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Scalars pull out of both slots of the normalized trace pairing. -/
theorem normalizedTracePairing_smul
    (a b : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizedTracePairing (a • A) (b • B) =
      a * b * normalizedTracePairing A B := by
  simp [normalizedTracePairing, Matrix.trace_smul, smul_eq_mul]
  ring

theorem normalizedTracePairing_add_left
    (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizedTracePairing (A + B) D =
      normalizedTracePairing A D + normalizedTracePairing B D := by
  simp [normalizedTracePairing, Matrix.add_mul, Matrix.trace_add]
  ring

theorem normalizedTracePairing_add_right
    (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizedTracePairing A (B + D) =
      normalizedTracePairing A B + normalizedTracePairing A D := by
  simp [normalizedTracePairing, Matrix.mul_add, Matrix.trace_add]
  ring

theorem normalizedTracePairing_smul_left
    (a : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizedTracePairing (a • A) B =
      a * normalizedTracePairing A B := by
  simpa using normalizedTracePairing_smul a 1 A B

theorem normalizedTracePairing_smul_right
    (a : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizedTracePairing A (a • B) =
      a * normalizedTracePairing A B := by
  simpa using normalizedTracePairing_smul 1 a A B

/-- The Euclidean pairing on the coordinate model `W₀ ≃ ℝ³`. -/
def euclideanPairing (x y : Fin 3 → ℝ) : ℝ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- The exterior-square pairing evaluated on decomposable bivectors. -/
def exteriorSquarePairing
    (x y x' y' : Fin 3 → ℝ) : ℝ :=
  euclideanPairing x x' * euclideanPairing y y' -
    euclideanPairing x y' * euclideanPairing y x'

/-- `thm:SM-commutator-Hodge`, covariant metric clause.  Every traceless
two-by-two writer with Gram `λ ⟨-,-⟩` has commutator Gram equal to `λ²`
times the exterior-square Gram. -/
theorem covariantCommutatorHodge_pairing
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (scale : ℝ)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ))
    (x y x' y' : Fin 3 → ℝ) :
    normalizedTracePairing
        (matrixCommutatorCarrier (F x) (F y))
        (matrixCommutatorCarrier (F x') (F y')) =
      (((scale ^ 2) * exteriorSquarePairing x y x' y' : ℝ) : ℂ) := by
  rw [normalizedTracePairing_commutatorCarrier _ _ _ _
    (htrace x) (htrace y) (htrace x') (htrace y'),
    hpair x x', hpair y y', hpair x y', hpair y x']
  push_cast
  simp only [exteriorSquarePairing]
  norm_cast
  ring

/-- The cross-product realization of the exterior-square pairing. -/
theorem crossVec_pairing_eq_exteriorSquarePairing
    (x y x' y' : Fin 3 → ℝ) :
    euclideanPairing (crossVec x y) (crossVec x' y') =
      exteriorSquarePairing x y x' y' := by
  simp [euclideanPairing, exteriorSquarePairing, crossVec]
  ring

/-- The standard coordinate vectors in the three-dimensional model of
`W₀`. -/
def coordinateUnit (i : Fin 3) : Fin 3 → ℝ :=
  fun j => if j = i then 1 else 0

/-- First vectors of the three oriented coordinate two-planes. -/
def hodgePlaneFirst (i : Fin 3) : Fin 3 → ℝ :=
  ![coordinateUnit 1, coordinateUnit 2, coordinateUnit 0] i

/-- Second vectors of the three oriented coordinate two-planes. -/
def hodgePlaneSecond (i : Fin 3) : Fin 3 → ℝ :=
  ![coordinateUnit 2, coordinateUnit 0, coordinateUnit 1] i

/-- The three commutators of the oriented coordinate two-planes. -/
noncomputable def commutatorHodgeBasis
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  matrixCommutatorCarrier (F (hodgePlaneFirst i)) (F (hodgePlaneSecond i))

/-- The commutator--Hodge map after the identification
`Λ²W₀ ≃ ℝ³`. -/
noncomputable def covariantCommutatorHodge
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ξ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (ξ 0 : ℂ) • commutatorHodgeBasis F 0 +
    (ξ 1 : ℂ) • commutatorHodgeBasis F 1 +
    (ξ 2 : ℂ) • commutatorHodgeBasis F 2

/-- The oriented coordinate planes are an orthonormal exterior-square
basis. -/
theorem hodgePlane_exteriorSquarePairing (i j : Fin 3) :
    exteriorSquarePairing (hodgePlaneFirst i) (hodgePlaneSecond i)
        (hodgePlaneFirst j) (hodgePlaneSecond j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [hodgePlaneFirst, hodgePlaneSecond, coordinateUnit,
      exteriorSquarePairing, euclideanPairing]

/-- The three oriented commutator planes have Gram `scale² I₃`. -/
theorem commutatorHodgeBasis_pairing
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (scale : ℝ)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ))
    (i j : Fin 3) :
    normalizedTracePairing (commutatorHodgeBasis F i)
        (commutatorHodgeBasis F j) =
      (((scale ^ 2) * (if i = j then 1 else 0) : ℝ) : ℂ) := by
  rw [commutatorHodgeBasis, commutatorHodgeBasis,
    covariantCommutatorHodge_pairing F scale htrace hpair,
    hodgePlane_exteriorSquarePairing]

/-- The full Hodge-coordinate map has Gram `scale²` times the Euclidean
Gram, not only on individual decomposable coordinate planes. -/
theorem covariantCommutatorHodge_coordinatePairing
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (scale : ℝ)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ))
    (ξ η : Fin 3 → ℝ) :
    normalizedTracePairing (covariantCommutatorHodge F ξ)
        (covariantCommutatorHodge F η) =
      (((scale ^ 2) * euclideanPairing ξ η : ℝ) : ℂ) := by
  simp only [covariantCommutatorHodge, normalizedTracePairing_add_left,
    normalizedTracePairing_add_right, normalizedTracePairing_smul_left,
    normalizedTracePairing_smul_right]
  rw [commutatorHodgeBasis_pairing F scale htrace hpair 0 0,
    commutatorHodgeBasis_pairing F scale htrace hpair 0 1,
    commutatorHodgeBasis_pairing F scale htrace hpair 0 2,
    commutatorHodgeBasis_pairing F scale htrace hpair 1 0,
    commutatorHodgeBasis_pairing F scale htrace hpair 1 1,
    commutatorHodgeBasis_pairing F scale htrace hpair 1 2,
    commutatorHodgeBasis_pairing F scale htrace hpair 2 0,
    commutatorHodgeBasis_pairing F scale htrace hpair 2 1,
    commutatorHodgeBasis_pairing F scale htrace hpair 2 2]
  simp [euclideanPairing]
  ring

/-- Positivity of the writer scale makes the Hodge-coordinate carrier
injective, hence its three coordinate histories are independent. -/
theorem covariantCommutatorHodge_injective
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (scale : ℝ)
    (hscale : 0 < scale)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ)) :
    Function.Injective (covariantCommutatorHodge F) := by
  intro ξ η hξη
  have hmap : covariantCommutatorHodge F (ξ - η) = 0 := by
    ext i j
    have hij := congr_fun (congr_fun hξη i) j
    simp [covariantCommutatorHodge, Pi.sub_apply, Matrix.add_apply,
      Matrix.smul_apply] at hij ⊢
    linear_combination hij
  have hzero := covariantCommutatorHodge_coordinatePairing
    F scale htrace hpair (ξ - η) (ξ - η)
  rw [hmap] at hzero
  have hcast :
      (((scale ^ 2) * euclideanPairing (ξ - η) (ξ - η) : ℝ) : ℂ) = 0 := by
    simpa [normalizedTracePairing] using hzero
  have hreal : scale ^ 2 * euclideanPairing (ξ - η) (ξ - η) = 0 := by
    exact_mod_cast hcast
  have hsquare : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hnorm : euclideanPairing (ξ - η) (ξ - η) = 0 := by
    nlinarith
  funext i
  fin_cases i <;>
    simp [euclideanPairing, Pi.sub_apply] at hnorm ⊢ <;>
    nlinarith [sq_nonneg (ξ 0 - η 0), sq_nonneg (ξ 1 - η 1),
      sq_nonneg (ξ 2 - η 2)]

/-- After division by the positive writer scale, the commutator carrier has
the unscaled exterior-square metric. -/
theorem normalizedCovariantCommutatorHodge_pairing
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (scale : ℝ)
    (hscale : 0 < scale)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ))
    (x y x' y' : Fin 3 → ℝ) :
    normalizedTracePairing
        ((scale⁻¹ : ℂ) • matrixCommutatorCarrier (F x) (F y))
        ((scale⁻¹ : ℂ) • matrixCommutatorCarrier (F x') (F y')) =
      ((exteriorSquarePairing x y x' y' : ℝ) : ℂ) := by
  have hscale0 : (scale : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hscale
  rw [normalizedTracePairing_smul]
  rw [covariantCommutatorHodge_pairing F scale htrace hpair x y x' y']
  push_cast
  field_simp

/-- The occurrence row transports the Hodge carrier into the physical
history space with the manuscript's `κ⁻¹/²` normalization. -/
noncomputable def physicalOccurrenceCommutatorHodge
    {Y : Type*} [Fintype Y]
    (C0 : Matrix Y (Fin 2) ℂ) (κ : ℝ)
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ξ : Fin 3 → ℝ) : Matrix Y (Fin 2) ℂ :=
  ((Real.sqrt κ : ℂ))⁻¹ • (C0 * covariantCommutatorHodge F ξ)

/-- A normalized occurrence row does not collapse any generation
direction of a positive-scale commutator--Hodge carrier. -/
theorem physicalOccurrenceCommutatorHodge_injective
    {Y : Type*} [Fintype Y]
    (C0 : Matrix Y (Fin 2) ℂ) (κ scale : ℝ)
    (hκ : 0 < κ) (hC : C0ᴴ * C0 = (κ : ℂ) • 1)
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hscale : 0 < scale)
    (htrace : ∀ x, (F x).trace = 0)
    (hpair : ∀ x y,
      normalizedTracePairing (F x) (F y) =
        ((scale * euclideanPairing x y : ℝ) : ℂ)) :
    Function.Injective (physicalOccurrenceCommutatorHodge C0 κ F) := by
  exact (principal_matter_module C0 κ hκ hC).2.comp
    (covariantCommutatorHodge_injective F scale hscale htrace hpair)

/-- The six oriented physical edge histories: three Hodge basis histories
and their reverse orientations. -/
noncomputable def sixPhysicalCommutatorEdgeHistories
    {Y : Type*} [Fintype Y]
    (C0 : Matrix Y (Fin 2) ℂ) (κ : ℝ)
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) :
    Fin 6 → Matrix Y (Fin 2) ℂ :=
  ![physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 0),
    physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 1),
    physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 2),
    -physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 0),
    -physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 1),
    -physicalOccurrenceCommutatorHodge C0 κ F (coordinateUnit 2)]

/-- The six edge histories span exactly the transported three-coordinate
carrier: every transported history is a linear combination of the first
three, while the last three are their reversed orientations. -/
theorem sixPhysicalCommutatorEdgeHistories_span_carrier
    {Y : Type*} [Fintype Y]
    (C0 : Matrix Y (Fin 2) ℂ) (κ : ℝ)
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ξ : Fin 3 → ℝ) :
    physicalOccurrenceCommutatorHodge C0 κ F ξ =
      (ξ 0 : ℂ) • sixPhysicalCommutatorEdgeHistories C0 κ F 0 +
      (ξ 1 : ℂ) • sixPhysicalCommutatorEdgeHistories C0 κ F 1 +
      (ξ 2 : ℂ) • sixPhysicalCommutatorEdgeHistories C0 κ F 2 := by
  ext i j
  simp [physicalOccurrenceCommutatorHodge,
    sixPhysicalCommutatorEdgeHistories, covariantCommutatorHodge,
    coordinateUnit, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

/-- Reversing any of the three edge orientations negates its physical
history. -/
theorem sixPhysicalCommutatorEdgeHistories_reverse
    {Y : Type*} [Fintype Y]
    (C0 : Matrix Y (Fin 2) ℂ) (κ : ℝ)
    (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 3) :
    sixPhysicalCommutatorEdgeHistories C0 κ F (Fin.natAdd 3 i) =
      -sixPhysicalCommutatorEdgeHistories C0 κ F (Fin.castAdd 3 i) := by
  fin_cases i <;> simp [sixPhysicalCommutatorEdgeHistories]

end NCG
