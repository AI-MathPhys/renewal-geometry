/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveVacuumWeightedL2Exact
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Gauge-equivariance of the physical vacuum unitary

An invariant measurable density preserves a measure-preserving transformation.
For an almost-everywhere nonvanishing invariant vacuum, multiplication by the
vacuum intertwines the actual weighted and physical L² pullbacks. Consequently
the vacuum unitary identifies their full fixed spaces, without defining either
space as a closure of continuous writers.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG.InvariantVacuumPullback

open PositiveVacuumWeightedL2

noncomputable section

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem measurePreserving_withDensity {f : X → X}
    (hf : MeasurePreserving f ν ν) {w : X → ℝ≥0∞} (hw : Measurable w)
    (hinvariant : (fun x => w (f x)) =ᵐ[ν] w) :
    MeasurePreserving f (ν.withDensity w) (ν.withDensity w) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs,
    withDensity_apply _ (hs.preimage hf.measurable), withDensity_apply _ hs]
  calc
    ∫⁻ x in f ⁻¹' s, w x ∂ν = ∫⁻ x in f ⁻¹' s, w (f x) ∂ν :=
      lintegral_congr_ae (ae_restrict_of_ae hinvariant.symm)
    _ = ∫⁻ x in s, w x ∂ν := hf.setLIntegral_comp_preimage hs hw

variable (ν) (Omega : X → ℂ) (hOmega : Measurable Omega)

include hOmega in
theorem measurePreserving_vacuumMeasure {f : X → X}
    (hf : MeasurePreserving f ν ν)
    (hinvariant : (fun x => Omega (f x)) =ᵐ[ν] Omega) :
    MeasurePreserving f (vacuumMeasure ν Omega) (vacuumMeasure ν Omega) := by
  apply measurePreserving_withDensity hf (hOmega.enorm.pow_const 2)
  filter_upwards [hinvariant] with x hx
  rw [hx]

variable (hnonzero : ∀ᵐ x ∂ν, Omega x ≠ 0)

/-- The physical vacuum map commutes with each invariant measure-preserving
transformation on actual L² equivalence classes. -/
theorem vacuumUnitary_intertwines_pullback {f : X → X}
    (hf : MeasurePreserving f ν ν)
    (hinvariant : (fun x => Omega (f x)) =ᵐ[ν] Omega)
    (v : Lp ℂ 2 (vacuumMeasure ν Omega)) :
    Lp.compMeasurePreserving f hf (vacuumUnitary ν Omega hOmega hnonzero v) =
      vacuumUnitary ν Omega hOmega hnonzero
        (Lp.compMeasurePreserving f
          (measurePreserving_vacuumMeasure ν Omega hOmega hf hinvariant) v) := by
  apply Lp.ext
  have hweighted := measurePreserving_vacuumMeasure ν Omega hOmega hf hinvariant
  have hleft := Lp.coeFn_compMeasurePreserving (vacuumUnitary ν Omega hOmega hnonzero v) hf
  have hmulLeft := hf.quasiMeasurePreserving.ae_eq_comp
    (vacuumMul_ae ν Omega hOmega hnonzero v)
  have hright := vacuumMul_ae ν Omega hOmega hnonzero
    (Lp.compMeasurePreserving f hweighted v)
  have hcomp := (absolutelyContinuous_vacuumMeasure ν Omega hOmega hnonzero).ae_eq
    (Lp.coeFn_compMeasurePreserving v hweighted)
  filter_upwards [hleft, hmulLeft, hright, hcomp, hinvariant] with x h1 h2 h3 h4 h5
  change Lp.compMeasurePreserving f hf (vacuumUnitary ν Omega hOmega hnonzero v) x =
    vacuumMul ν Omega hOmega hnonzero (Lp.compMeasurePreserving f hweighted v) x
  simp only [Function.comp_apply] at h1 h2 h4
  rw [h1]
  change vacuumMul ν Omega hOmega hnonzero v (f x) = _
  rw [h2, h3, h4, h5]

/-- The unitary identifies full invariant vectors for any family of invariant
measure-preserving transformations. -/
theorem vacuumUnitary_fixed_iff {I : Type*} (act : I → X → X)
    (hpres : ∀ i, MeasurePreserving (act i) ν ν)
    (hinvariant : ∀ i, (fun x => Omega (act i x)) =ᵐ[ν] Omega)
    (v : Lp ℂ 2 (vacuumMeasure ν Omega)) :
    (∀ i, Lp.compMeasurePreserving (act i)
      (measurePreserving_vacuumMeasure ν Omega hOmega (hpres i) (hinvariant i)) v = v) ↔
    (∀ i, Lp.compMeasurePreserving (act i) (hpres i)
      (vacuumUnitary ν Omega hOmega hnonzero v) = vacuumUnitary ν Omega hOmega hnonzero v) := by
  constructor
  · intro hv i
    rw [vacuumUnitary_intertwines_pullback ν Omega hOmega hnonzero
      (hpres i) (hinvariant i) v, hv i]
  · intro hv i
    apply (vacuumUnitary ν Omega hOmega hnonzero).injective
    rw [← vacuumUnitary_intertwines_pullback ν Omega hOmega hnonzero
      (hpres i) (hinvariant i) v]
    exact hv i

end

end NCG.InvariantVacuumPullback
