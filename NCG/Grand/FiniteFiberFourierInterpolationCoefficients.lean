/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFiberTorusFourierEquiv
import NCG.Grand.FiniteTorusFourierInterpolationCoefficients

/-!
# Coefficients of finite-fibre Fourier interpolation

Composing finite-fibre interpolation with the continuum torus Fourier unitary
gives a canonical isometric embedding of the finite lattice space in the
common integer-frequency carrier.  Its centered coefficients are exactly the
normalized finite Fourier transform, and all other coefficients vanish.
-/

noncomputable section

local instance finiteFiberInterpolationCoefficientsMeasureSpace :
    MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance finiteFiberInterpolationCoefficientsIsAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteFiberInterpolationCoefficientsIsProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

open scoped lp

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type*} [Fintype r]

/-- Finite-fibre interpolation represented on the common vector-valued
integer-frequency carrier. -/
def finiteFiberCenteredCoefficientEmbedding :
    FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →ₗᵢ[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r) :=
  finiteFiberTorusFourierEquiv.toLinearIsometry.comp
    finiteFiberFourierInterpolationLinearIsometry

/-- At a represented centered frequency, the coefficient embedding is the
coordinatewise normalized finite Fourier transform. -/
@[simp]
theorem finiteFiberCenteredCoefficientEmbedding_apply_centered
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r))
    (q : d → ZMod N) (a : r) :
    finiteFiberCenteredCoefficientEmbedding Phi
        (finiteTorusCenteredFrequency q) a =
      finiteTorusNormalizedFourier (Phi a) q := by
  change finiteFiberTorusFourierEquiv
      (finiteFiberFourierInterpolationLinearIsometry Phi)
      (finiteTorusCenteredFrequency q) a = _
  rw [
    finiteFiberTorusFourierEquiv_apply,
    finiteFiberFourierInterpolationLinearIsometry_apply,
    finiteTorusFourierInterpolationLinearIsometry_apply,
    mFourierCoeff_finiteTorusFourierInterpolation_centered]

/-- The coefficient embedding vanishes outside the centered frequency
window. -/
theorem finiteFiberCenteredCoefficientEmbedding_apply_eq_zero_of_not_mem_range
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r))
    (k : d → ℤ)
    (hk : k ∉ Set.range
      (finiteTorusCenteredFrequency (N := N) (d := d))) :
    finiteFiberCenteredCoefficientEmbedding Phi k = 0 := by
  apply WithLp.ofLp_injective
  funext a
  change finiteFiberTorusFourierEquiv
      (finiteFiberFourierInterpolationLinearIsometry Phi) k a = 0
  rw [
    finiteFiberTorusFourierEquiv_apply,
    finiteFiberFourierInterpolationLinearIsometry_apply,
    finiteTorusFourierInterpolationLinearIsometry_apply,
    mFourierCoeff_finiteTorusFourierInterpolation_eq_zero_of_not_mem_range
      (Phi a) k hk]

/-- The centered coefficient embedding as a continuous linear map. -/
def finiteFiberCenteredCoefficientEmbeddingCLM :
    FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →L[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r) :=
  finiteFiberCenteredCoefficientEmbedding.toContinuousLinearMap

/-- The adjoint of the centered coefficient embedding. -/
def finiteFiberCenteredCoefficientExtractionCLM :
    ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
      FiniteFiberLatticeL2 (N := N) (d := d) (r := r) :=
  finiteFiberCenteredCoefficientEmbeddingCLM.adjoint

/-- Extracting after embedding is the identity on the finite lattice
carrier. -/
@[simp]
theorem finiteFiberCenteredCoefficientExtraction_apply_embedding
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r)) :
    finiteFiberCenteredCoefficientExtractionCLM
        (finiteFiberCenteredCoefficientEmbeddingCLM Phi) = Phi := by
  change finiteFiberCenteredCoefficientEmbedding.toContinuousLinearMap.adjoint
      (finiteFiberCenteredCoefficientEmbedding.toContinuousLinearMap Phi) = Phi
  have h := congrArg
    (fun T : FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →L[ℂ]
        FiniteFiberLatticeL2 (N := N) (d := d) (r := r) ↦ T Phi)
    finiteFiberCenteredCoefficientEmbedding.adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h

end NCG
