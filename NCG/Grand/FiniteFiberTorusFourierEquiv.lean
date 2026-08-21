/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFiberFourierInterpolation
import NCG.Grand.L2EuclideanFubini

/-!
# Fourier unitary for finite-fibre torus L²

The scalar torus Fourier-basis representation is amplified coordinatewise
over a finite fibre and then composed with the ℓ²/Euclidean Fubini swap.  The
result is the literal unitary equivalence

`L²(T^d; ℂ^r) ≃ ℓ²(ℤ^d; ℂ^r)`.
-/

noncomputable section

local instance finiteFiberTorusFourierMeasureSpace :
    MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance finiteFiberTorusFourierIsAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteFiberTorusFourierIsProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

open scoped lp

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type*} [Fintype r]

/-- Coordinatewise scalar Fourier representation of finite-fibre torus
functions. -/
def finiteFiberTorusCoordinateFourierEquiv :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : r ↦ ℓ²(d → ℤ, ℂ)) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : r ↦ UnitAddTorus.mFourierBasis.repr)

@[simp]
theorem finiteFiberTorusCoordinateFourierEquiv_apply
    (f : FiniteFiberContinuumTorusL2 (d := d) (r := r))
    (a : r) (k : d → ℤ) :
    finiteFiberTorusCoordinateFourierEquiv f a k =
      UnitAddTorus.mFourierCoeff (f a) k := by
  rw [finiteFiberTorusCoordinateFourierEquiv,
    LinearIsometryEquiv.piLpCongrRight_apply]
  exact UnitAddTorus.mFourierBasis_repr (f a) k

@[simp]
theorem l2EuclideanToPiL2Equiv_symm_apply
    (g : PiLp 2 (fun _ : r ↦ ℓ²(d → ℤ, ℂ)))
    (k : d → ℤ) (a : r) :
    (l2EuclideanToPiL2Equiv.symm g) k a = g a k := by
  have h := (l2EuclideanToPiL2Equiv
    (ι := d → ℤ) (r := r)).apply_symm_apply g
  have hcoord := congrArg (fun q ↦ q a k) h
  simpa only [l2EuclideanToPiL2Equiv_apply] using hcoord

/-- Unitary Fourier representation of finite-fibre torus `L²` on the
vector-valued integer coefficient carrier. -/
def finiteFiberTorusFourierEquiv :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) ≃ₗᵢ[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r) :=
  finiteFiberTorusCoordinateFourierEquiv.trans
    l2EuclideanToPiL2Equiv.symm

@[simp]
theorem finiteFiberTorusFourierEquiv_apply
    (f : FiniteFiberContinuumTorusL2 (d := d) (r := r))
    (k : d → ℤ) (a : r) :
    finiteFiberTorusFourierEquiv f k a =
      UnitAddTorus.mFourierCoeff (f a) k := by
  rw [finiteFiberTorusFourierEquiv, LinearIsometryEquiv.trans_apply,
    l2EuclideanToPiL2Equiv_symm_apply,
    finiteFiberTorusCoordinateFourierEquiv_apply]

end NCG
