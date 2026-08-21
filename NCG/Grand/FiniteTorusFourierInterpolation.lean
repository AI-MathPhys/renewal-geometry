/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusFourierPlancherel
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Discrete Fourier interpolation into the continuum torus

Centered representatives embed the finite frequency torus `(ZMod N)^d`
injectively into the integer frequency lattice.  Synthesizing the normalized
discrete Fourier coefficients against mathlib's multidimensional torus Fourier
basis gives the literal interpolation map into `L²(T^d)`.  It preserves the
finite counting `L²` energy exactly.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

/-- Use the same normalized Haar probability measure as mathlib's
multidimensional torus Fourier basis. -/
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

/-- Coordinatewise centered integer representative of a finite-torus
frequency. -/
def finiteTorusCenteredFrequency (k : d → ZMod N) : d → ℤ :=
  fun j => (k j).valMinAbs

/-- Centered representatives embed the finite frequency torus injectively
into the continuum integer frequency lattice. -/
theorem finiteTorusCenteredFrequency_injective :
    Function.Injective (finiteTorusCenteredFrequency (N := N) (d := d)) := by
  intro k l h
  funext j
  exact ZMod.injective_valMinAbs (congrFun h j)

/-- The continuum Fourier modes selected by centered finite-torus
frequencies are orthonormal. -/
theorem finiteTorusCenteredModes_orthonormal :
    Orthonormal ℂ
      (fun k : d → ZMod N =>
        UnitAddTorus.mFourierLp 2 (finiteTorusCenteredFrequency k)) := by
  change Orthonormal ℂ
    (UnitAddTorus.mFourierLp 2 ∘
      finiteTorusCenteredFrequency (N := N) (d := d))
  exact UnitAddTorus.orthonormal_mFourier.comp _
    finiteTorusCenteredFrequency_injective

/-- Literal discrete Fourier interpolation into scalar-valued
`L²(UnitAddTorus d)`. -/
noncomputable def finiteTorusFourierInterpolation
    (Phi : (d → ZMod N) → ℂ) :
    MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) :=
  ∑ k, finiteTorusNormalizedFourier Phi k •
    UnitAddTorus.mFourierLp 2 (finiteTorusCenteredFrequency k)

/-- Inner product of two interpolants is the finite coefficient inner
product. -/
theorem inner_finiteTorusFourierInterpolation
    (Phi Psi : (d → ZMod N) → ℂ) :
    inner ℂ (finiteTorusFourierInterpolation Phi)
        (finiteTorusFourierInterpolation Psi) =
      ∑ k, star (finiteTorusNormalizedFourier Phi k) *
        finiteTorusNormalizedFourier Psi k := by
  classical
  simpa [finiteTorusFourierInterpolation] using
    finiteTorusCenteredModes_orthonormal.inner_sum
      (finiteTorusNormalizedFourier Phi)
      (finiteTorusNormalizedFourier Psi) Finset.univ

/-- The literal interpolation preserves finite counting `L²` energy exactly. -/
theorem norm_sq_finiteTorusFourierInterpolation
    (Phi : (d → ZMod N) → ℂ) :
    ‖finiteTorusFourierInterpolation Phi‖ ^ 2 =
      ∑ x, ‖Phi x‖ ^ 2 := by
  have hinner := inner_finiteTorusFourierInterpolation Phi Phi
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hcoeff :
      (∑ k, star (finiteTorusNormalizedFourier Phi k) *
          finiteTorusNormalizedFourier Phi k) =
        ((∑ k, ‖finiteTorusNormalizedFourier Phi k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [show star (finiteTorusNormalizedFourier Phi k) =
        conj (finiteTorusNormalizedFourier Phi k) from rfl,
      RCLike.conj_mul]
    rfl
  rw [hcoeff, sum_norm_sq_finiteTorusNormalizedFourier] at hinner
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact hinner

/-- Fourier interpolation is additive. -/
theorem finiteTorusFourierInterpolation_add
    (Phi Psi : (d → ZMod N) → ℂ) :
    finiteTorusFourierInterpolation (Phi + Psi) =
      finiteTorusFourierInterpolation Phi +
        finiteTorusFourierInterpolation Psi := by
  classical
  have hcoeff (k : d → ZMod N) :
      finiteTorusNormalizedFourier (Phi + Psi) k =
        finiteTorusNormalizedFourier Phi k +
          finiteTorusNormalizedFourier Psi k := by
    unfold finiteTorusNormalizedFourier finiteTorusFourier
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  unfold finiteTorusFourierInterpolation
  simp_rw [hcoeff, add_smul]
  exact Finset.sum_add_distrib

/-- Fourier interpolation commutes with complex scalar multiplication. -/
theorem finiteTorusFourierInterpolation_smul
    (c : ℂ) (Phi : (d → ZMod N) → ℂ) :
    finiteTorusFourierInterpolation (c • Phi) =
      c • finiteTorusFourierInterpolation Phi := by
  classical
  have hcoeff (k : d → ZMod N) :
      finiteTorusNormalizedFourier (c • Phi) k =
        c • finiteTorusNormalizedFourier Phi k := by
    unfold finiteTorusNormalizedFourier
    change _ • finiteTorusFourier (fun x => c • Phi x) k = _
    rw [finiteTorusFourier_const_smul]
    simp only [smul_smul]
    congr 1
    exact mul_comm _ _
  unfold finiteTorusFourierInterpolation
  simp_rw [hcoeff, smul_assoc]
  rw [smul_sum]

/-- Discrete Fourier interpolation bundled as a genuine linear isometry from
the finite counting `L²` space into continuum torus `L²`. -/
noncomputable def finiteTorusFourierInterpolationLinearIsometry :
    EuclideanSpace ℂ (d → ZMod N) →ₗᵢ[ℂ]
      MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)) where
  toFun Phi := finiteTorusFourierInterpolation Phi
  map_add' Phi Psi := by
    simpa only [WithLp.ofLp_add] using
      finiteTorusFourierInterpolation_add
        (WithLp.ofLp Phi) (WithLp.ofLp Psi)
  map_smul' c Phi := by
    simpa only [WithLp.ofLp_smul, RingHom.id_apply] using
      finiteTorusFourierInterpolation_smul c (WithLp.ofLp Phi)
  norm_map' Phi := by
    change ‖finiteTorusFourierInterpolation (WithLp.ofLp Phi)‖ = ‖Phi‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      norm_sq_finiteTorusFourierInterpolation,
      EuclideanSpace.norm_sq_eq]

@[simp]
theorem finiteTorusFourierInterpolationLinearIsometry_apply
    (Phi : EuclideanSpace ℂ (d → ZMod N)) :
    finiteTorusFourierInterpolationLinearIsometry Phi =
      finiteTorusFourierInterpolation Phi := rfl

/-- In particular the interpolation is injective. -/
theorem finiteTorusFourierInterpolation_injective :
    Function.Injective
      (finiteTorusFourierInterpolationLinearIsometry
        (N := N) (d := d)) :=
  LinearIsometry.injective _

end NCG
