/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveVacuumWeightedL2Exact
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Physical vacuum cyclicity and orthogonal centering

Uniformly dense continuous writers have dense physical vacuum orbit for a
measurable almost-everywhere nonvanishing vacuum. The orbit is explicitly
identified with pointwise multiplication by the vacuum. Orthogonal projection
onto the vacuum complement transports this density to the centered orbit.
Uniform closure equality also transports to equality of closed physical orbits,
which is the form needed for gauge-invariant selected sectors.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG.PositiveVacuumCyclicity

open PositiveVacuumWeightedL2

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) (Omega : X → ℂ)
variable (hOmega : Measurable Omega) (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0)
variable [IsFiniteMeasure (vacuumMeasure μ Omega)]

/-- Continuous writers acting on the physical vacuum. -/
def vacuumOrbit : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ :=
  (vacuumUnitary μ Omega hOmega hnonzero).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure μ Omega) ℂ)

/-- This orbit is the actual pointwise writer-times-vacuum product. -/
theorem vacuumOrbit_ae (f : C(X, ℂ)) :
    vacuumOrbit μ Omega hOmega hnonzero f =ᵐ[μ] (fun x => Omega x * f x) := by
  have h1 := vacuumMul_ae μ Omega hOmega hnonzero
    (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure μ Omega) ℂ f)
  have h2 := (absolutelyContinuous_vacuumMeasure μ Omega hOmega hnonzero).ae_eq
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (vacuumMeasure μ Omega) f)
  filter_upwards [h1, h2] with x hx hy
  change vacuumMul μ Omega hOmega hnonzero
    (ContinuousMap.toLp (E := ℂ) 2 (vacuumMeasure μ Omega) ℂ f) x = _
  rw [hx, hy]

/-- Uniform closure equality gives equality of closed physical source orbits.
In particular this can be applied to Haar-averaged invariant writers. -/
theorem closure_vacuumOrbit_image_of_closure_eq
    (writers sector : Set C(X, ℂ)) (hclosure : closure writers = sector) :
    closure (vacuumOrbit μ Omega hOmega hnonzero '' writers) =
      closure (vacuumOrbit μ Omega hOmega hnonzero '' sector) := by
  rw [← hclosure, closure_image_closure (vacuumOrbit μ Omega hOmega hnonzero).continuous]

variable [(vacuumMeasure μ Omega).WeaklyRegular]

theorem vacuumOrbit_denseRange : DenseRange (vacuumOrbit μ Omega hOmega hnonzero) := by
  have hU : DenseRange (vacuumUnitary μ Omega hOmega hnonzero) :=
    (vacuumUnitary μ Omega hOmega hnonzero).surjective.denseRange
  exact hU.comp (ContinuousMap.toLp_denseRange ℂ (vacuumMeasure μ Omega) ℂ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    (vacuumUnitary μ Omega hOmega hnonzero).continuous

/-- A dense continuous writer family is genuinely cyclic for the physical
vacuum representation, not just the weighted constant-vector model. -/
theorem vacuumOrbit_dense (writers : Set C(X, ℂ)) (hdense : Dense writers) :
    Dense (vacuumOrbit μ Omega hOmega hnonzero '' writers) :=
  (vacuumOrbit_denseRange μ Omega hOmega hnonzero).dense_image
    (vacuumOrbit μ Omega hOmega hnonzero).continuous hdense

/-- Centering removes exactly the chosen vacuum line: the projected source
orbit is dense in its orthogonal complement. The projection is the actual
Hilbert-space orthogonal projection, not a formal centering predicate. -/
theorem centered_vacuumOrbit_dense (vacuum : Lp ℂ 2 μ)
    (writers : Set C(X, ℂ)) (hdense : Dense writers) :
    Dense (((Submodule.span ℂ {vacuum})ᗮ.orthogonalProjectionOnto ∘
      vacuumOrbit μ Omega hOmega hnonzero) '' writers) := by
  let K : Submodule ℂ (Lp ℂ 2 μ) := (Submodule.span ℂ {vacuum})ᗮ
  have hsurj : Function.Surjective K.orthogonalProjectionOnto := by
    intro v
    exact ⟨v.val, K.orthogonalProjectionOnto_mem_subspace_eq_self v⟩
  have hrange : DenseRange
      (K.orthogonalProjectionOnto ∘ vacuumOrbit μ Omega hOmega hnonzero) :=
    hsurj.denseRange.comp (vacuumOrbit_denseRange μ Omega hOmega hnonzero)
      K.orthogonalProjectionOnto.continuous
  exact hrange.dense_image
    (K.orthogonalProjectionOnto.continuous.comp
      (vacuumOrbit μ Omega hOmega hnonzero).continuous) hdense

end

end NCG.PositiveVacuumCyclicity
