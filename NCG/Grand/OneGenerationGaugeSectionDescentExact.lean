/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AnomalyFreeFieldShellGaugeQuotientExact

/-!
# Gauge descent of the one-generation determinant section

This file proves `thm:SMFS-gauge-descent`.  Determinants turn the finite
chiral covariance law into the ratio of the two unitary determinant
characters.  Triviality of the complete-generation character makes the
section and its positive norm-square invariant, and a generic quotient lift
then gives the descended finite section and metric.
-/

open Matrix

namespace NCG
namespace OneGenerationGaugeSectionDescent

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Determinant-line section represented in fixed top-wedge frames. -/
noncomputable def determinantSection (D : Matrix n n ℂ) : ℂ := D.det

/-- Ratio of the target and source determinant characters. -/
noncomputable def sectionCocycle
    (Uminus Uplus : Matrix.unitaryGroup n ℂ) : ℂ :=
  Uminus.1.det / Uplus.1.det

/-- The determinant of the inverse unitary is the inverse determinant. -/
theorem det_unitary_inv (U : Matrix.unitaryGroup n ℂ) :
    (U⁻¹).1.det = (U.1.det)⁻¹ := by
  have h := congrArg Subtype.val (map_inv (unitaryDetHom n) U)
  simpa [unitaryDetHom, Unitary.coe_inv] using h

/-- Taking the top exterior power of the gauge covariance law gives the
section transformation cocycle `det U₋ / det U₊`. -/
theorem determinantSection_gauge_cocycle
    (D Dg : Matrix n n ℂ)
    (Uminus Uplus : Matrix.unitaryGroup n ℂ)
    (hcov : Dg = Uminus.1 * D * (Uplus⁻¹).1) :
    determinantSection Dg =
      sectionCocycle Uminus Uplus * determinantSection D := by
  unfold determinantSection sectionCocycle
  rw [hcov, Matrix.det_mul, Matrix.det_mul, det_unitary_inv]
  ring

/-- Equal target/source determinant characters make the one-generation
section invariant. -/
theorem determinantSection_gauge_invariant
    (D Dg : Matrix n n ℂ)
    (Uminus Uplus : Matrix.unitaryGroup n ℂ)
    (hcov : Dg = Uminus.1 * D * (Uplus⁻¹).1)
    (hchar : Uminus.1.det = Uplus.1.det) :
    determinantSection Dg = determinantSection D := by
  rw [determinantSection_gauge_cocycle D Dg Uminus Uplus hcov]
  have hdet : Uplus.1.det ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit Uplus).ne_zero
  rw [sectionCocycle, hchar, div_self hdet, one_mul]

/-- The induced positive determinant-line metric is gauge invariant as well. -/
theorem determinantMetric_gauge_invariant
    (D Dg : Matrix n n ℂ)
    (Uminus Uplus : Matrix.unitaryGroup n ℂ)
    (hcov : Dg = Uminus.1 * D * (Uplus⁻¹).1)
    (hchar : Uminus.1.det = Uplus.1.det) :
    Complex.normSq (determinantSection Dg) =
      Complex.normSq (determinantSection D) := by
  rw [determinantSection_gauge_invariant D Dg Uminus Uplus hcov hchar]

/-- An invariant finite section descends through any presented gauge-orbit
setoid. -/
noncomputable def descendedSection {Φ : Type*} (r : Setoid Φ)
    (sigma : Φ → ℂ) (hinv : ∀ x y, x ≈ y → sigma x = sigma y) :
    Quotient r → ℂ :=
  Quotient.lift sigma hinv

@[simp] theorem descendedSection_mk {Φ : Type*} (r : Setoid Φ)
    (sigma : Φ → ℂ) (hinv : ∀ x y, x ≈ y → sigma x = sigma y)
    (x : Φ) :
    descendedSection r sigma hinv (Quotient.mk r x) = sigma x := rfl

/-- The positive metric descends simultaneously with an invariant section. -/
theorem descendedSection_and_metric {Φ : Type*} (r : Setoid Φ)
    (sigma : Φ → ℂ) (hinv : ∀ x y, x ≈ y → sigma x = sigma y) :
    ∃ (sigmaBar : Quotient r → ℂ) (metricBar : Quotient r → ℝ),
      (∀ x, sigmaBar (Quotient.mk r x) = sigma x) ∧
      (∀ x, metricBar (Quotient.mk r x) = Complex.normSq (sigma x)) := by
  refine ⟨descendedSection r sigma hinv,
    fun q => Complex.normSq (descendedSection r sigma hinv q), ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl

/-- **`thm:SMFS-gauge-descent`.**  Exact determinant cocycle, invariance under
the anomaly-free equal-character condition, and quotient descent of both the
section and its positive metric. -/
theorem smfs_one_generation_gauge_descent
    (D Dg : Matrix n n ℂ)
    (Uminus Uplus : Matrix.unitaryGroup n ℂ)
    (hcov : Dg = Uminus.1 * D * (Uplus⁻¹).1)
    (hchar : Uminus.1.det = Uplus.1.det) :
    determinantSection Dg =
        sectionCocycle Uminus Uplus * determinantSection D ∧
      sectionCocycle Uminus Uplus = 1 ∧
      determinantSection Dg = determinantSection D ∧
      Complex.normSq (determinantSection Dg) =
        Complex.normSq (determinantSection D) := by
  refine ⟨determinantSection_gauge_cocycle D Dg Uminus Uplus hcov,
    ?_, determinantSection_gauge_invariant D Dg Uminus Uplus hcov hchar,
    determinantMetric_gauge_invariant D Dg Uminus Uplus hcov hchar⟩
  unfold sectionCocycle
  rw [hchar]
  exact div_self (Matrix.UnitaryGroup.det_isUnit Uplus).ne_zero

end OneGenerationGaugeSectionDescent
end NCG
