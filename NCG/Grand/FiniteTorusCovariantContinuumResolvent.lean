/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFiberTorusFourierEquiv
import NCG.Grand.FiniteTorusCovariantCoefficientResolvent
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Finite-torus covariant resolvents on continuum torus L²

The coefficient-space covariant resolvents are transported through the
finite-fibre torus Fourier unitary.  This realizes both the finite-stage
zero-extended resolver and its continuum limit as bounded operators on the
literal physical carrier `L²(T^d; ℂ^r)`, and upgrades the coefficient-space
theorem to operator-norm convergence there.
-/

open Filter Topology
open scoped InnerProduct lp

noncomputable section

local instance finiteTorusCovariantContinuumResolverMeasureSpace :
    MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance finiteTorusCovariantContinuumResolverIsAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteTorusCovariantContinuumResolverIsProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type} [Fintype r] [Nonempty r]

/-- Conjugation of a coefficient-space operator by the finite-fibre torus
Fourier unitary. -/
def conjugateByFiniteFiberTorusFourierEquiv
    (T : ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r)) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  finiteFiberTorusFourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp
      finiteFiberTorusFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Unitary conjugation is continuous in the operator norm. -/
theorem continuous_conjugateByFiniteFiberTorusFourierEquiv :
    Continuous (conjugateByFiniteFiberTorusFourierEquiv (d := d) (r := r)) := by
  exact
    (ContinuousLinearMap.compL ℂ
      (FiniteFiberContinuumTorusL2 (d := d) (r := r))
      (ℓ²(d → ℤ, EuclideanSpace ℂ r))
      (FiniteFiberContinuumTorusL2 (d := d) (r := r))
      finiteFiberTorusFourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap).continuous.comp
      (((ContinuousLinearMap.compL ℂ
        (FiniteFiberContinuumTorusL2 (d := d) (r := r))
        (ℓ²(d → ℤ, EuclideanSpace ℂ r))
        (ℓ²(d → ℤ, EuclideanSpace ℂ r))).flip
        finiteFiberTorusFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap).continuous)

/-- The finite-stage covariant resolver, extended by zero off its centered
frequency window and represented on continuum torus `L²`. -/
def finiteTorusCovariantEmbeddedResolver
    (N : ℕ) (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  conjugateByFiniteFiberTorusFourierEquiv
    (finiteTorusCovariantCoefficientResolver
      (d := d) (E := EuclideanSpace ℂ r) N B lam hlam)

/-- The continuum covariant resolver represented on continuum torus `L²`. -/
def continuumTorusCovariantResolver
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  conjugateByFiniteFiberTorusFourierEquiv
    (continuumCovariantCoefficientResolver
      (d := d) (E := EuclideanSpace ℂ r) B lam hlam)

/-- Operator-norm convergence of the embedded finite covariant resolvents on
the literal continuum torus carrier. -/
theorem finiteTorusCovariantEmbeddedResolver_tendsto
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun N ↦ finiteTorusCovariantEmbeddedResolver N B lam hlam)
      atTop
      (nhds (continuumTorusCovariantResolver B lam hlam)) := by
  have hcoeff := finiteTorusCovariantCoefficientResolver_tendsto
    (d := d) (E := EuclideanSpace ℂ r) B lam hlam
  have hconj :
      Tendsto
        (conjugateByFiniteFiberTorusFourierEquiv (d := d) (r := r))
        (nhds (continuumCovariantCoefficientResolver
          (d := d) (E := EuclideanSpace ℂ r) B lam hlam))
        (nhds (conjugateByFiniteFiberTorusFourierEquiv
          (continuumCovariantCoefficientResolver
            (d := d) (E := EuclideanSpace ℂ r) B lam hlam))) :=
    (continuous_conjugateByFiniteFiberTorusFourierEquiv
      (d := d) (r := r)).continuousAt
  exact hconj.comp hcoeff

end NCG
