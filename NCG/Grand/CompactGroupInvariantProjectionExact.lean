/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Averaging onto the full invariant Banach subspace

For a strongly continuous contractive right representation of a compact group,
the actual Bochner average is a continuous projection onto its fixed vectors.
Its image of every dense family is dense in the entire fixed subspace, not
merely in a sector defined as the closure of a selected orbit.

The multiplication convention matches Koopman pullbacks of left actions:
`U (g * h) = U h ∘ U g`.
-/

open MeasureTheory

namespace NCG.CompactGroupInvariantProjection

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable (U : G → H →L[ℂ] H) (μ : Measure G) [IsProbabilityMeasure μ]
variable (hcontinuous : ∀ v, Continuous (fun g => U g v))

include hcontinuous in
theorem integrable_orbit (v : H) : Integrable (fun g => U g v) μ :=
  (hcontinuous v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable (hcontractive : ∀ g v, ‖U g v‖ ≤ ‖v‖)

/-- Haar averaging on the actual Banach space. -/
def mean : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun v := ∫ g, U g v ∂μ
      map_add' := by
        intro v w
        simp only [map_add]
        exact integral_add (integrable_orbit U μ hcontinuous v)
          (integrable_orbit U μ hcontinuous w)
      map_smul' := by
        intro c v
        simp only [map_smul]
        exact integral_smul c (fun g => U g v) }
    1 (fun v => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := μ) (Filter.Eventually.of_forall fun g => hcontractive g v))

@[simp] theorem mean_apply (v : H) :
    mean U μ hcontinuous hcontractive v = ∫ g, U g v ∂μ := rfl

/-- Fixed vectors are defined by the representation, independently of any
writer bank or averaging construction. -/
def fixedSet : Set H := {v | ∀ g, U g v = v}

theorem isClosed_fixedSet : IsClosed (fixedSet U) := by
  have heq : fixedSet U = ⋂ g : G, {v | U g v = v} := by
    ext v
    simp [fixedSet]
  rw [heq]
  exact isClosed_iInter fun g => isClosed_eq (U g).continuous continuous_id

theorem mean_eq_self {v : H} (hv : v ∈ fixedSet U) :
    mean U μ hcontinuous hcontractive v = v :=
  integral_eq_const (Filter.Eventually.of_forall hv)

variable [Measure.IsMulRightInvariant μ]
variable (hmul : ∀ g h v, U (g * h) v = U h (U g v))

include hmul in
theorem mean_mem_fixedSet (v : H) : mean U μ hcontinuous hcontractive v ∈ fixedSet U := by
  intro h
  rw [mean_apply, ← (U h).integral_comp_comm (integrable_orbit U μ hcontinuous v)]
  simp_rw [← hmul]
  exact integral_mul_right_eq_self (fun g => U g v) h

include hmul in
theorem mean_idempotent (v : H) :
    mean U μ hcontinuous hcontractive (mean U μ hcontinuous hcontractive v) =
      mean U μ hcontinuous hcontractive v :=
  mean_eq_self U μ hcontinuous hcontractive
    (mean_mem_fixedSet U μ hcontinuous hcontractive hmul v)

include hmul in
/-- The full fixed-vector space is recovered by averaging any dense family. -/
theorem closure_mean_image_eq_fixedSet (writers : Set H) (hdense : Dense writers) :
    closure (mean U μ hcontinuous hcontractive '' writers) = fixedSet U := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨v, _, rfl⟩
      exact mean_mem_fixedSet U μ hcontinuous hcontractive hmul v
    · exact isClosed_fixedSet U
  · intro v hv
    have h := image_closure_subset_closure_image
      (mean U μ hcontinuous hcontractive).continuous ⟨v, hdense v, rfl⟩
    rwa [mean_eq_self U μ hcontinuous hcontractive hv] at h

end

end NCG.CompactGroupInvariantProjection
