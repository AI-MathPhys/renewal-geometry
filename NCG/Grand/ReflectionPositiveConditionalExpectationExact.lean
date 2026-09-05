/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reflection positivity from a Markov boundary factorization

This file isolates the measure-theoretic core of the Osterwalder--Schrader
identity (RP.10).  The Markov property factors a past--future product through
conditional expectations on the time-zero sigma algebra.  Reflection
invariance identifies the two boundary conditional expectations.  Their
product is therefore an absolute square, so its integral is nonnegative.
-/

open MeasureTheory

noncomputable section

namespace NCG.ReflectionPositiveConditionalExpectation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Conditional expectation onto `m0`, explicitly retaining `mΩ` as the
ambient sigma algebra. -/
def boundaryConditionalExpectation
    (μ : Measure Ω) (m0 : MeasurableSpace Ω) (F : Ω → ℂ) : Ω → ℂ :=
  @MeasureTheory.condExp Ω ℂ m0 mΩ _ _ μ F

/-- The real squared norm of the boundary conditional expectation.  Naming
this quantity also fixes the ambient measurable-space instance explicitly;
the conditioning sigma algebra `m0` is not the ambient one. -/
def boundarySquare (μ : Measure Ω) (m0 : MeasurableSpace Ω) (F : Ω → ℂ) : ℝ :=
  @MeasureTheory.integral Ω ℝ _ _ mΩ μ fun ω ↦
    Complex.normSq (boundaryConditionalExpectation (mΩ := mΩ) μ m0 F ω)

/-- The reflected complex pairing, with its ambient measurable space fixed. -/
def reflectionPairing (μ : Measure Ω) (Fpast Ffuture : Ω → ℂ) : ℂ :=
  @MeasureTheory.integral Ω ℂ _ _ mΩ μ fun ω ↦ star (Fpast ω) * Ffuture ω

/-- A conditional product factorization together with equality of the two
boundary conditional expectations gives the exact OS square identity. -/
theorem os_identity_of_markov_reflection
    (μ : Measure Ω) (m0 : MeasurableSpace Ω) (Fpast Ffuture : Ω → ℂ)
    (hmarkov :
      reflectionPairing (mΩ := mΩ) μ Fpast Ffuture =
        reflectionPairing (mΩ := mΩ) μ
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Fpast)
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture))
    (hreflection : boundaryConditionalExpectation (mΩ := mΩ) μ m0 Fpast =ᵐ[μ]
      boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture) :
    reflectionPairing (mΩ := mΩ) μ Fpast Ffuture =
        (boundarySquare (mΩ := mΩ) μ m0 Ffuture : ℂ) ∧
      0 ≤ boundarySquare (mΩ := mΩ) μ m0 Ffuture := by
  have hsquare :
      reflectionPairing (mΩ := mΩ) μ
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Fpast)
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture) =
        @MeasureTheory.integral Ω ℂ _ _ mΩ μ
          (fun ω ↦ (Complex.normSq
            (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture ω) : ℂ)) := by
    unfold reflectionPairing
    apply integral_congr_ae
    filter_upwards [hreflection] with ω hω
    rw [hω]
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self
        (z := boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture ω)).symm
  constructor
  · calc
      reflectionPairing (mΩ := mΩ) μ Fpast Ffuture =
          reflectionPairing (mΩ := mΩ) μ
            (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Fpast)
            (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture) := hmarkov
      _ = @MeasureTheory.integral Ω ℂ _ _ mΩ μ
          (fun ω ↦ (Complex.normSq
            (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture ω) : ℂ)) := hsquare
      _ = (boundarySquare (mΩ := mΩ) μ m0 Ffuture : ℂ) := by
        unfold boundarySquare
        exact @integral_complex_ofReal Ω mΩ μ
          (fun ω ↦ Complex.normSq
            (boundaryConditionalExpectation (mΩ := mΩ) μ m0 Ffuture ω))
  · unfold boundarySquare
    exact integral_nonneg fun ω ↦ Complex.normSq_nonneg _

/-- **(RP.10)** in reflection notation.  Here `F ∘ Θ` is the past writer,
`F` is the future writer, and `m0` is the time-zero sigma algebra. -/
theorem os_identity
    (μ : Measure Ω) (m0 : MeasurableSpace Ω) (Θ : Ω → Ω) (F : Ω → ℂ)
    (hmarkov :
      reflectionPairing (mΩ := mΩ) μ (F ∘ Θ) F =
        reflectionPairing (mΩ := mΩ) μ
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 (F ∘ Θ))
          (boundaryConditionalExpectation (mΩ := mΩ) μ m0 F))
    (hreflection : boundaryConditionalExpectation (mΩ := mΩ) μ m0 (F ∘ Θ) =ᵐ[μ]
      boundaryConditionalExpectation (mΩ := mΩ) μ m0 F) :
    reflectionPairing (mΩ := mΩ) μ (F ∘ Θ) F =
        (boundarySquare (mΩ := mΩ) μ m0 F : ℂ) ∧
      0 ≤ boundarySquare (mΩ := mΩ) μ m0 F := by
  simpa [Function.comp_apply] using
    os_identity_of_markov_reflection (mΩ := mΩ) μ m0 (F ∘ Θ) F hmarkov hreflection

end NCG.ReflectionPositiveConditionalExpectation
