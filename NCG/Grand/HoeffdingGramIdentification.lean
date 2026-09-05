/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PrimitiveHoeffdingCarrier
import NCG.Grand.SupportPrototype

/-!
# four-cell Hoeffding Gram identification

The canonical Hoeffding projections are connected-support shorts.  This file
packages their response decomposition and positive support Grams, completing
the identification needed by the four-cell orbit audit.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

abbrev PrimitiveFourCarrier := Fin 4 × Fin 4 × Fin 4 × Fin 4

noncomputable def canonicalHoeffdingComponent {k : Type*} [Fintype k]
    (F : Matrix PrimitiveFourCarrier k ℂ)
    (m : Bool × Bool × Bool × Bool) : Matrix PrimitiveFourCarrier k ℂ :=
  hoeffP primitiveConstant primitiveScoreProjection m * F

noncomputable def canonicalHoeffdingGram {k : Type*} [Fintype k]
    (F : Matrix PrimitiveFourCarrier k ℂ)
    (m : Bool × Bool × Bool × Bool) : Matrix k k ℂ :=
  (canonicalHoeffdingComponent F m)ᴴ * canonicalHoeffdingComponent F m

lemma primitiveConstant_hermitian : primitiveConstantᴴ = primitiveConstant := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [primitiveConstant, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · have hji : j ≠ i := Ne.symm h
    simp [primitiveConstant, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      h, hji]

lemma primitiveScoreProjection_hermitian :
    primitiveScoreProjectionᴴ = primitiveScoreProjection := by
  rw [primitiveScoreProjection, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, primitiveConstant_hermitian]

theorem canonical_hoeffding_projection_hermitian
    (m : Bool × Bool × Bool × Bool) :
    (hoeffP primitiveConstant primitiveScoreProjection m)ᴴ
      = hoeffP primitiveConstant primitiveScoreProjection m := by
  rcases m with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [hoeffP, hoeffPick, Matrix.conjTranspose_kronecker,
      primitiveConstant_hermitian, primitiveScoreProjection_hermitian]

theorem canonical_hoeffding_response_decomposition {k : Type*} [Fintype k]
    (F : Matrix PrimitiveFourCarrier k ℂ) :
    (∑ m : Bool × Bool × Bool × Bool, canonicalHoeffdingComponent F m = F)
    ∧ (∀ m, (canonicalHoeffdingGram F m).PosSemidef)
    ∧ (∀ m, canonicalHoeffdingGram F m = 0
        ↔ canonicalHoeffdingComponent F m = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [canonicalHoeffdingComponent]
    rw [← Matrix.sum_mul]
    rw [primitive_hoeffding_support_canonical.2.1, Matrix.one_mul]
  · intro m
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · intro m
    exact Matrix.conjTranspose_mul_self_eq_zero

/-- Distinct canonical support components are Hilbert--Schmidt orthogonal. -/
theorem canonical_hoeffding_components_orthogonal {k : Type*} [Fintype k]
    (F : Matrix PrimitiveFourCarrier k ℂ)
    (m m' : Bool × Bool × Bool × Bool) (hne : m ≠ m') :
    (canonicalHoeffdingComponent F m)ᴴ
        * canonicalHoeffdingComponent F m' = 0 := by
  rw [canonicalHoeffdingComponent, canonicalHoeffdingComponent,
    Matrix.conjTranspose_mul, canonical_hoeffding_projection_hermitian]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (hoeffP primitiveConstant primitiveScoreProjection m)
    (hoeffP primitiveConstant primitiveScoreProjection m')]
  rw [primitive_hoeffding_support_canonical.1 m m' hne]
  simp

end NCG
