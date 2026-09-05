/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFiberFourierInterpolation

/-!
# Fourier coefficients of finite-torus interpolation

The literal interpolation has exactly the normalized discrete Fourier
coefficients at centered lattice frequencies and vanishes at every continuum
frequency outside that finite window.  These identities characterize its
range and provide the coefficientwise bridge for covariant symbols.
-/

noncomputable section

local instance : MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Hilbert-basis coefficient of an interpolant at a centered lattice
frequency is its normalized discrete Fourier coefficient. -/
theorem finiteTorusFourierInterpolation_repr_centered
    (Phi : (d → ZMod N) → ℂ) (k : d → ZMod N) :
    UnitAddTorus.mFourierBasis.repr
        (finiteTorusFourierInterpolation Phi)
        (finiteTorusCenteredFrequency k) =
      finiteTorusNormalizedFourier Phi k := by
  rw [HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis]
  unfold finiteTorusFourierInterpolation
  exact finiteTorusCenteredModes_orthonormal.inner_right_fintype
    (finiteTorusNormalizedFourier Phi) k

/-- The continuum Fourier coefficient of an interpolant at a centered lattice
frequency is the normalized discrete Fourier coefficient. -/
theorem mFourierCoeff_finiteTorusFourierInterpolation_centered
    (Phi : (d → ZMod N) → ℂ) (k : d → ZMod N) :
    UnitAddTorus.mFourierCoeff
        (finiteTorusFourierInterpolation Phi)
        (finiteTorusCenteredFrequency k) =
      finiteTorusNormalizedFourier Phi k := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact finiteTorusFourierInterpolation_repr_centered Phi k

/-- Hilbert-basis coefficients vanish outside the centered finite-frequency
window. -/
theorem finiteTorusFourierInterpolation_repr_eq_zero_of_not_mem_range
    (Phi : (d → ZMod N) → ℂ) (n : d → ℤ)
    (hn : n ∉ Set.range
      (finiteTorusCenteredFrequency (N := N) (d := d))) :
    UnitAddTorus.mFourierBasis.repr
        (finiteTorusFourierInterpolation Phi) n = 0 := by
  rw [HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis]
  unfold finiteTorusFourierInterpolation
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [inner_smul_right]
  have hne : n ≠ finiteTorusCenteredFrequency k := by
    intro h
    exact hn ⟨k, h.symm⟩
  rw [UnitAddTorus.orthonormal_mFourier.2 hne]
  simp

/-- Continuum Fourier coefficients vanish outside the centered
finite-frequency window. -/
theorem mFourierCoeff_finiteTorusFourierInterpolation_eq_zero_of_not_mem_range
    (Phi : (d → ZMod N) → ℂ) (n : d → ℤ)
    (hn : n ∉ Set.range
      (finiteTorusCenteredFrequency (N := N) (d := d))) :
    UnitAddTorus.mFourierCoeff
        (finiteTorusFourierInterpolation Phi) n = 0 := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact finiteTorusFourierInterpolation_repr_eq_zero_of_not_mem_range
    Phi n hn

/-- Coefficientwise intertwining of an unscaled covariant difference with its
operator-valued symbol under literal continuum interpolation. -/
theorem mFourierCoeff_interpolation_covariantDifference_centered
    (j : d) (U : ℂ →L[ℂ] ℂ) (Phi : (d → ZMod N) → ℂ)
    (k : d → ZMod N) :
    UnitAddTorus.mFourierCoeff
        (finiteTorusFourierInterpolation
          (finiteTorusCovariantDifference j U Phi))
        (finiteTorusCenteredFrequency k) =
      (ZMod.stdAddChar (k j) • (1 : ℂ →L[ℂ] ℂ) - U)
        (finiteTorusNormalizedFourier Phi k) := by
  rw [mFourierCoeff_finiteTorusFourierInterpolation_centered]
  unfold finiteTorusNormalizedFourier
  rw [finiteTorusFourier_covariantDifference]
  simp only [map_smul]

/-- Coefficientwise intertwining of the mesh-scaled covariant difference
with its exact centered continuum Fourier symbol. -/
theorem mFourierCoeff_interpolation_scaledCovariantDifference_centered
    (h : ℝ) (j : d) (U : ℂ →L[ℂ] ℂ)
    (Phi : (d → ZMod N) → ℂ) (k : d → ZMod N) :
    UnitAddTorus.mFourierCoeff
        (finiteTorusFourierInterpolation
          (fun x => (h⁻¹ : ℂ) •
            finiteTorusCovariantDifference j U Phi x))
        (finiteTorusCenteredFrequency k) =
      (h⁻¹ : ℂ) •
        ((ZMod.stdAddChar (k j) • (1 : ℂ →L[ℂ] ℂ) - U)
          (finiteTorusNormalizedFourier Phi k)) := by
  rw [mFourierCoeff_finiteTorusFourierInterpolation_centered]
  unfold finiteTorusNormalizedFourier
  rw [finiteTorusFourier_scaledCovariantDifference]
  simp only [map_smul, smul_smul]
  congr 1
  ring

end NCG
