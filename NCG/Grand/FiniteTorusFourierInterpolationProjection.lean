/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusFourierInterpolation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The finite Fourier-mode projection on continuum torus L²

The discrete Fourier interpolation isometry has a Hilbert adjoint.  Their
two compositions are respectively the identity on the finite lattice space
and the orthogonal projection onto the centered finite-mode subspace of
continuum torus `L²`.
-/

noncomputable section

open scoped ComplexConjugate

/-- Use the normalized Haar probability measure underlying the torus Fourier
basis. -/
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

/-- The interpolation isometry as a continuous linear map. -/
noncomputable def finiteTorusFourierInterpolationCLM :
    EuclideanSpace ℂ (d → ZMod N) →L[ℂ]
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) :=
  (finiteTorusFourierInterpolationLinearIsometry
    (N := N) (d := d)).toContinuousLinearMap

/-- Hilbert adjoint of discrete Fourier interpolation. -/
noncomputable def finiteTorusFourierInterpolationAdjoint :
    MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) →L[ℂ]
      EuclideanSpace ℂ (d → ZMod N) :=
  (finiteTorusFourierInterpolationCLM (N := N) (d := d)).adjoint

/-- Orthogonal projection onto the centered finite Fourier-mode subspace. -/
noncomputable def finiteTorusFourierInterpolationProjection :
    MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) →L[ℂ]
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) :=
  (finiteTorusFourierInterpolationCLM (N := N) (d := d)).comp
    (finiteTorusFourierInterpolationAdjoint
      (N := N) (d := d))

/-- The adjoint is a left inverse to the interpolation isometry. -/
@[simp]
theorem finiteTorusFourierInterpolationAdjoint_apply_interpolation
    (Phi : EuclideanSpace ℂ (d → ZMod N)) :
    finiteTorusFourierInterpolationAdjoint (N := N) (d := d)
        (finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi) = Phi := by
  change (finiteTorusFourierInterpolationLinearIsometry
      (N := N) (d := d)).toContinuousLinearMap.adjoint
      ((finiteTorusFourierInterpolationLinearIsometry
        (N := N) (d := d)).toContinuousLinearMap Phi) = Phi
  have h := congrArg
    (fun T : EuclideanSpace ℂ (d → ZMod N) →L[ℂ]
        EuclideanSpace ℂ (d → ZMod N) => T Phi)
    (finiteTorusFourierInterpolationLinearIsometry
      (N := N) (d := d)).adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply,
    one_apply_eq_self] using h

/-- The finite-mode projection fixes every interpolated lattice vector. -/
@[simp]
theorem finiteTorusFourierInterpolationProjection_apply_interpolation
    (Phi : EuclideanSpace ℂ (d → ZMod N)) :
    finiteTorusFourierInterpolationProjection (N := N) (d := d)
        (finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi) =
      finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi := by
  change finiteTorusFourierInterpolationCLM (N := N) (d := d)
      (finiteTorusFourierInterpolationAdjoint (N := N) (d := d)
        (finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi)) =
    finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi
  rw [finiteTorusFourierInterpolationAdjoint_apply_interpolation]

/-- The finite-mode projection is idempotent. -/
theorem finiteTorusFourierInterpolationProjection_idempotent :
    finiteTorusFourierInterpolationProjection (N := N) (d := d) ∘L
        finiteTorusFourierInterpolationProjection (N := N) (d := d) =
      finiteTorusFourierInterpolationProjection (N := N) (d := d) := by
  apply ContinuousLinearMap.ext
  intro f
  change finiteTorusFourierInterpolationCLM (N := N) (d := d)
      (finiteTorusFourierInterpolationAdjoint (N := N) (d := d)
        (finiteTorusFourierInterpolationCLM (N := N) (d := d)
          (finiteTorusFourierInterpolationAdjoint (N := N) (d := d) f))) =
    finiteTorusFourierInterpolationCLM (N := N) (d := d)
      (finiteTorusFourierInterpolationAdjoint (N := N) (d := d) f)
  rw [finiteTorusFourierInterpolationAdjoint_apply_interpolation]

/-- The finite-mode projection is self-adjoint. -/
theorem finiteTorusFourierInterpolationProjection_adjoint :
    (finiteTorusFourierInterpolationProjection
      (N := N) (d := d)).adjoint =
        finiteTorusFourierInterpolationProjection (N := N) (d := d) := by
  unfold finiteTorusFourierInterpolationProjection
  rw [ContinuousLinearMap.adjoint_comp]
  unfold finiteTorusFourierInterpolationAdjoint
  rw [ContinuousLinearMap.adjoint_adjoint]

end NCG
