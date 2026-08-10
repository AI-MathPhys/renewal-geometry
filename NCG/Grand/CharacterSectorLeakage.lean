/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.CharacterHankelSectorSaturation
import NCG.Grand.MomentLeakageUnwhitening

/-!
# Exact leakage from a character-projected Krylov sector

This module specializes support-unwhitened moment leakage to the projected
controllability synthesis used by the character Hankel construction.  It also
makes the manuscript's singular-vector witness explicit: a nonzero eigenvector
of the leakage Gram with nonzero eigenvalue is sent by the tail map to a
nonzero vector in the next missing Krylov component.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

namespace NCG
namespace CharacterSectorLeakage

/-- The support-whitened compressed transition. -/
def compressedTransition {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq k] (C : Matrix h k ℂ) (R : Matrix k k ℂ)
    (T : Matrix h h ℂ) : Matrix k k ℂ :=
  R * (Cᴴ * T * C) * R

/-- The exact support-whitened sector leakage matrix. -/
def sectorLeakage {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq k] (C : Matrix h k ℂ) (R : Matrix k k ℂ)
    (T : Matrix h h ℂ) : Matrix k k ℂ :=
  R * (Cᴴ * (T * T) * C) * R
    - compressedTransition C R T * compressedTransition C R T

/-- The head-to-tail map whose range is the next missing sector component. -/
def sectorTailMap {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq h] [DecidableEq k]
    (C : Matrix h k ℂ) (R : Matrix k k ℂ) (T : Matrix h h ℂ) :
    Matrix h k ℂ :=
  let W := C * R
  (1 - W * Wᴴ) * T * W

/-- Exact singular-support leakage: factorization, positivity, norm, the
new-component dimension, one-step Krylov growth, and saturation are all
identified from the displayed moment formula. -/
theorem characterSectorLeakage_exact {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h] [DecidableEq k]
    (C : Matrix h k ℂ) (R : Matrix k k ℂ) (T : Matrix h h ℂ)
    (hR : Rᴴ = R) (hwhite : R * (Cᴴ * C) * R = 1)
    (hT : Tᴴ = T) :
    let W := C * R
    let V := sectorLeakage C R T
    let X := sectorTailMap C R T
    V = Xᴴ * X
      ∧ V.PosSemidef
      ∧ ‖V‖ = ‖X‖ ^ 2
      ∧ V.rank = Module.finrank ℂ (momentLeakageNewComponent W T)
      ∧ V.rank = (Matrix.fromCols W (T * W)).rank - W.rank
      ∧ (V = 0 ↔ X = 0) := by
  simpa only [sectorLeakage, compressedTransition, sectorTailMap] using
    universal_moment_leakage_exact C R T hR hwhite hT

/-- Every nonzero leakage eigenvector with nonzero eigenvalue produces an
explicit nonzero vector in the next missing source component. -/
theorem nonzero_leakage_eigenvector_produces_missing_direction
    {h k : Type*} [Fintype h] [Fintype k]
    (V : Matrix k k ℂ) (X : Matrix h k ℂ)
    (hfactor : V = Xᴴ * X) (v : k → ℂ) (lambda : ℂ)
    (hv : v ≠ 0) (hlambda : lambda ≠ 0)
    (heigen : V *ᵥ v = lambda • v) :
    X *ᵥ v ≠ 0
      ∧ X *ᵥ v ∈ LinearMap.range (Matrix.mulVecLin X) := by
  have hnonzero : X *ᵥ v ≠ 0 := by
    intro hX
    have hVzero : V *ᵥ v = 0 := by
      rw [hfactor, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero]
    have hscaled : lambda • v = 0 := heigen.symm.trans hVzero
    exact hv ((smul_eq_zero.mp hscaled).resolve_left hlambda)
  refine ⟨hnonzero, ?_⟩
  exact ⟨v, Matrix.mulVecLin_apply X v⟩

end CharacterSectorLeakage
end NCG
