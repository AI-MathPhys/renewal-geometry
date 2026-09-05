/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GeneratedAlgebraFlatness

/-!
# Reconstruction from one flat finite moment window

Unlike the older all-moments Kalman formulation, this module uses only the
depth-`r+1` Gram equality.  Flatness and source generation are used upstream
to make the two finite word syntheses onto; the theorem below then constructs
the unique unitary and transports every source multiplication operator from
the finite word-step equations.
-/

open Matrix

namespace NCG
namespace FlatFiniteWindowReconstruction

/-- Equality of one saturated finite Gram window constructs the unique
unitary carrying the first word synthesis to the second. -/
theorem unique_unitary_of_equal_flat_gram
    {n : Type*} [Fintype n] [DecidableEq n]
    (W₁ W₂ : Matrix n n ℂ)
    (hW₁ : IsUnit W₁.det)
    (hGram : W₁ᴴ * W₁ = W₂ᴴ * W₂) :
    ∃! U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * W₁ = W₂ := by
  let V : Matrix n n ℂ := W₁⁻¹
  let U : Matrix n n ℂ := W₂ * V
  have hVW : V * W₁ = 1 := Matrix.nonsing_inv_mul W₁ hW₁
  have hWV : W₁ * V = 1 := Matrix.mul_nonsing_inv W₁ hW₁
  have hVstarWstar : Vᴴ * W₁ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hWV, Matrix.conjTranspose_one]
  have hUW : U * W₁ = W₂ := by
    simp only [U, V, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul W₁ hW₁, Matrix.mul_one]
  have hUunitary : Uᴴ * U = 1 := by
    change (W₂ * V)ᴴ * (W₂ * V) = 1
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W₂ᴴ W₂ V]
    rw [← hGram]
    rw [Matrix.mul_assoc W₁ᴴ W₁ V,
      ← Matrix.mul_assoc Vᴴ W₁ᴴ (W₁ * V),
      hVstarWstar, Matrix.one_mul, hWV]
  refine ⟨U, ⟨hUunitary, hUW⟩, ?_⟩
  intro U' hU'
  calc
    U' = U' * W₁ * V := by rw [Matrix.mul_assoc, hWV, Matrix.mul_one]
    _ = W₂ * V := by rw [hU'.2]
    _ = U := rfl

/-- The unitary obtained from the finite Gram window intertwines every source
left-multiplication operator, using only the depth-`r` to depth-`r+1` word-step
identities. -/
theorem flat_window_transports_source_multiplication
    {n e : Type*} [Fintype n] [DecidableEq n]
    (W₁ W₂ U : Matrix n n ℂ)
    (hW₁ : IsUnit W₁.det) (hUW : U * W₁ = W₂)
    (T₁ T₂ : e → Matrix n n ℂ) (shift : e → Matrix n n ℂ)
    (hstep₁ : ∀ x, T₁ x * W₁ = W₁ * shift x)
    (hstep₂ : ∀ x, T₂ x * W₂ = W₂ * shift x) :
    ∀ x, U * T₁ x = T₂ x * U := by
  intro x
  let V : Matrix n n ℂ := W₁⁻¹
  have hWV : W₁ * V = 1 := Matrix.mul_nonsing_inv W₁ hW₁
  have hprod : (U * T₁ x) * W₁ = (T₂ x * U) * W₁ := by
    calc
    (U * T₁ x) * W₁ = U * (T₁ x * W₁) := by
      rw [Matrix.mul_assoc]
    _ = U * (W₁ * shift x) := by rw [hstep₁]
    _ = W₂ * shift x := by rw [← Matrix.mul_assoc, hUW]
    _ = T₂ x * W₂ := (hstep₂ x).symm
    _ = (T₂ x * U) * W₁ := by rw [Matrix.mul_assoc, hUW]
  calc
    U * T₁ x = (U * T₁ x) * W₁ * V := by
      rw [Matrix.mul_assoc, hWV, Matrix.mul_one]
    _ = (T₂ x * U) * W₁ * V := by rw [hprod]
    _ = T₂ x * U := by rw [Matrix.mul_assoc, hWV, Matrix.mul_one]

/-- Finite-window reconstruction bundle: the single Gram equality gives the
unique unitary, and the same unitary transports all source generators. -/
theorem flat_finite_window_reconstruction
    {n e : Type*} [Fintype n] [DecidableEq n]
    (W₁ W₂ : Matrix n n ℂ)
    (hW₁ : IsUnit W₁.det)
    (hGram : W₁ᴴ * W₁ = W₂ᴴ * W₂)
    (T₁ T₂ : e → Matrix n n ℂ) (shift : e → Matrix n n ℂ)
    (hstep₁ : ∀ x, T₁ x * W₁ = W₁ * shift x)
    (hstep₂ : ∀ x, T₂ x * W₂ = W₂ * shift x) :
    ∃! U : Matrix n n ℂ,
      Uᴴ * U = 1 ∧ U * W₁ = W₂ ∧
        ∀ x, U * T₁ x = T₂ x * U := by
  obtain ⟨U, ⟨hUunitary, hUW⟩, hunique⟩ :=
    unique_unitary_of_equal_flat_gram W₁ W₂ hW₁ hGram
  refine ⟨U, ⟨hUunitary, hUW,
    flat_window_transports_source_multiplication W₁ W₂ U hW₁ hUW
      T₁ T₂ shift hstep₁ hstep₂⟩, ?_⟩
  intro U' hU'
  exact hunique U' ⟨hU'.1, hU'.2.1⟩

/-- Version fed directly by the output of flatness exhaustion: surjectivity of
the depth-`r` word synthesis is converted to the nonsingularity needed above. -/
theorem flat_finite_window_reconstruction_of_surjective
    {n e : Type*} [Fintype n] [DecidableEq n]
    (W₁ W₂ : Matrix n n ℂ)
    (honto : Function.Surjective W₁.mulVec)
    (hGram : W₁ᴴ * W₁ = W₂ᴴ * W₂)
    (T₁ T₂ : e → Matrix n n ℂ) (shift : e → Matrix n n ℂ)
    (hstep₁ : ∀ x, T₁ x * W₁ = W₁ * shift x)
    (hstep₂ : ∀ x, T₂ x * W₂ = W₂ * shift x) :
    ∃! U : Matrix n n ℂ,
      Uᴴ * U = 1 ∧ U * W₁ = W₂ ∧
        ∀ x, U * T₁ x = T₂ x * U := by
  have hunit : IsUnit W₁ := Matrix.mulVec_surjective_iff_isUnit.mp honto
  have hdet : IsUnit W₁.det := (Matrix.isUnit_iff_isUnit_det W₁).mp hunit
  exact flat_finite_window_reconstruction W₁ W₂ hdet hGram
    T₁ T₂ shift hstep₁ hstep₂

end FlatFiniteWindowReconstruction
end NCG
