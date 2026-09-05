/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PhaseGradingRoute
import NCG.Flagship.ClockQuarterRoot

/-!
# Explicit selected Store-phase odd route

The selected signed-return coefficient lives on the protected two-point phase
carrier.  This file performs the finite carrier computation omitted by the
earlier umbrella theorem: the coefficient is off diagonal, hence
anticommutes with the protected sign without assuming that relation; a
nonzero coefficient has a nonzero cross-support corner; and each nonzero
multiplicity-one corner has a unique normalized polar route.
-/

open Matrix

namespace NCG

/-- Left protected phase support; `clockP0` is the right support. -/
def clockP1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The coefficient selected by the signed-return phase has only cross-sign
entries. -/
def selectedSignedReturnCoefficient (a b : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := !![0, a; b, 0]

/-- The protected sign is the difference of its two phase supports. -/
theorem clockZ_eq_supportDifference : clockZ = clockP0 - clockP1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, clockP0, clockP1]

/-- The selected signed-return coefficient is genuinely grading odd; no
anticommutation hypothesis is used. -/
theorem selectedSignedReturnCoefficient_anticommutes (a b : ℂ) :
    clockZ * selectedSignedReturnCoefficient a b +
      selectedSignedReturnCoefficient a b * clockZ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, selectedSignedReturnCoefficient, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Reusing either protected sign convention preserves the derived
anticommutation relation. -/
theorem selectedSignedReturnCoefficient_anticommutes_reusedSign
    (ε a b : ℂ) :
    (ε • clockZ) * selectedSignedReturnCoefficient a b +
      selectedSignedReturnCoefficient a b * (ε • clockZ) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
    selectedSignedReturnCoefficient_anticommutes, smul_zero]

/-- The two cross-support corners recover the two selected coefficients
exactly. -/
theorem selectedSignedReturnCoefficient_crossCorners (a b : ℂ) :
    clockP0 * selectedSignedReturnCoefficient a b * clockP1 =
        !![0, a; 0, 0]
    ∧ clockP1 * selectedSignedReturnCoefficient a b * clockP0 =
        !![0, 0; b, 0] := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [clockP0, clockP1, selectedSignedReturnCoefficient,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- A nonzero selected odd coefficient has at least one nonzero protected
cross-support corner. -/
theorem selectedSignedReturnCoefficient_nonzero_crossCorner
    (a b : ℂ) (h : selectedSignedReturnCoefficient a b ≠ 0) :
    clockP0 * selectedSignedReturnCoefficient a b * clockP1 ≠ 0 ∨
      clockP1 * selectedSignedReturnCoefficient a b * clockP0 ≠ 0 := by
  obtain ⟨hcornerR, hcornerL⟩ :=
    selectedSignedReturnCoefficient_crossCorners a b
  rw [hcornerR, hcornerL]
  by_contra hzero
  push Not at hzero
  apply h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [selectedSignedReturnCoefficient]
  · have ha := congrFun (congrFun hzero.1 0) 1
    simpa [selectedSignedReturnCoefficient] using ha
  · have hb := congrFun (congrFun hzero.2 1) 0
    simpa [selectedSignedReturnCoefficient] using hb
  · simp [selectedSignedReturnCoefficient]

/-- Canonical polar phase of a nonzero multiplicity-one corner. -/
noncomputable def normalizedScalarRoute (z : ℂ) : ℂ :=
  ((‖z‖ : ℂ)⁻¹) * z

/-- The scalar polar route is normalized. -/
theorem norm_normalizedScalarRoute (z : ℂ) (hz : z ≠ 0) :
    ‖normalizedScalarRoute z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [normalizedScalarRoute, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
    inv_mul_cancel₀ hn]

/-- The multiplicity-one polar phase is the unique normalized route whose
positive modulus reconstruction equals the selected corner. -/
theorem normalizedScalarRoute_unique (z u : ℂ) (hz : z ≠ 0)
    (hreconstruct : z = u * (‖z‖ : ℂ)) :
    u = normalizedScalarRoute z := by
  have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
  let r : ℂ := (‖z‖ : ℂ)
  have hr : r ≠ 0 := hnC
  have hzur : z = u * r := hreconstruct
  calc
    u = r⁻¹ * (u * r) := by field_simp
    _ = r⁻¹ * z := by rw [hzur]
    _ = normalizedScalarRoute z := rfl

/-- Complete concrete source-native route on the selected two-point phase
carrier: derived oddness, a nonzero cross corner, and unique normalized polar
routes for each nonzero multiplicity-one corner. -/
theorem selectedStorePhaseOddRoute
    (ε a b : ℂ) (hcoeff : selectedSignedReturnCoefficient a b ≠ 0) :
    ((ε • clockZ) * selectedSignedReturnCoefficient a b +
        selectedSignedReturnCoefficient a b * (ε • clockZ) = 0)
    ∧ (clockP0 * selectedSignedReturnCoefficient a b * clockP1 ≠ 0 ∨
       clockP1 * selectedSignedReturnCoefficient a b * clockP0 ≠ 0)
    ∧ (∀ z ∈ ({a, b} : Set ℂ), z ≠ 0 →
        ‖normalizedScalarRoute z‖ = 1 ∧
        ∀ u, z = u * (‖z‖ : ℂ) → u = normalizedScalarRoute z) := by
  refine ⟨selectedSignedReturnCoefficient_anticommutes_reusedSign ε a b,
    selectedSignedReturnCoefficient_nonzero_crossCorner a b hcoeff, ?_⟩
  intro z _ hz
  exact ⟨norm_normalizedScalarRoute z hz,
    fun u hu => normalizedScalarRoute_unique z u hz hu⟩

end NCG
