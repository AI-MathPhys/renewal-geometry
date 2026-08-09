/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FiniteAnchorHowe

/-!
# Exact EASY 58: carrier transport for finite-anchor Howe locking

The perturbation, anchor-floor, summable-tail, and kernel-locking clauses were
already proved.  This file closes the remaining common-carrier bookkeeping:
unitary transport preserves operator norms, tuple distances, and commutants.
-/

namespace NCG

variable {A : Type*} [CStarAlgebra A]

/-- Transport an operator to a unitarily identified screened carrier. -/
def unitaryCarrierTransport (U : unitary A) (a : A) : A :=
  (U : A) * a * (star U : A)

/-- Unitary carrier transport is isometric for the operator norm. -/
theorem norm_unitaryCarrierTransport (U : unitary A) (a : A) :
    ‖unitaryCarrierTransport U a‖ = ‖a‖ := by
  calc
    ‖unitaryCarrierTransport U a‖ = ‖(U : A) * a‖ := by
      exact CStarRing.norm_mul_coe_unitary ((U : A) * a) (star U)
    _ = ‖a‖ := CStarRing.norm_coe_unitary_mul U a

/-- Hence the transported cutoff-to-cutoff tuple distance is exactly the
original one. -/
theorem norm_unitaryCarrierTransport_sub (U : unitary A) (a b : A) :
    ‖unitaryCarrierTransport U a - unitaryCarrierTransport U b‖
      = ‖a - b‖ := by
  have hsub : unitaryCarrierTransport U a - unitaryCarrierTransport U b
      = unitaryCarrierTransport U (a - b) := by
    simp only [unitaryCarrierTransport, mul_sub, sub_mul]
  rw [hsub, norm_unitaryCarrierTransport]

/-- Carrier transport respects products. -/
theorem unitaryCarrierTransport_mul (U : unitary A) (a b : A) :
    unitaryCarrierTransport U (a * b)
      = unitaryCarrierTransport U a * unitaryCarrierTransport U b := by
  simp only [unitaryCarrierTransport, mul_assoc]
  rw [← mul_assoc (star U : A) (U : A) (b * (star U : A)),
    Unitary.coe_star_mul_self, one_mul]

/-- Transport by the adjoint unitary is the inverse carrier identification. -/
theorem unitaryCarrierTransport_star_apply (U : unitary A) (a : A) :
    unitaryCarrierTransport (star U) (unitaryCarrierTransport U a) = a := by
  simp only [unitaryCarrierTransport, Unitary.coe_star, star_star]
  calc
    (star U : A) * ((U : A) * a * (star U : A)) * (U : A) =
        ((star U : A) * (U : A)) * a * ((star U : A) * (U : A)) := by
          simp only [mul_assoc]
    _ = a := by rw [Unitary.coe_star_mul_self, one_mul, mul_one]

/-- A unitary carrier identification is injective. -/
theorem unitaryCarrierTransport_injective (U : unitary A) :
    Function.Injective (unitaryCarrierTransport U) := by
  intro a b h
  have h' := congrArg (unitaryCarrierTransport (star U)) h
  simpa only [unitaryCarrierTransport_star_apply] using h'

/-- Commutation is invariant under unitary carrier transport. -/
theorem unitaryCarrierTransport_commute_iff
    (U : unitary A) (a b : A) :
    unitaryCarrierTransport U a * unitaryCarrierTransport U b
        = unitaryCarrierTransport U b * unitaryCarrierTransport U a
      ↔ a * b = b * a := by
  rw [← unitaryCarrierTransport_mul, ← unitaryCarrierTransport_mul]
  exact (unitaryCarrierTransport_injective U).eq_iff

/-- Exact tuple-commutant invariance under the common-carrier transport. -/
theorem unitaryCarrierTransport_tuple_commutant
    {J : Type*} (U : unitary A) (c : J → A) (x : A) :
    (∀ j, unitaryCarrierTransport U x * unitaryCarrierTransport U (c j)
        = unitaryCarrierTransport U (c j) * unitaryCarrierTransport U x)
      ↔ ∀ j, x * c j = c j * x := by
  constructor <;> intro h j
  · exact (unitaryCarrierTransport_commute_iff U x (c j)).mp (h j)
  · exact (unitaryCarrierTransport_commute_iff U x (c j)).mpr (h j)

end NCG
