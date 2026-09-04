/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Haar averaging preserves density in the invariant continuous functions

The averaging operator is constructed as an actual Bochner integral, not
postulated as a projection. It is a contractive continuous linear map; its
range is exactly the invariant functions. Consequently averaging any uniformly
dense writer family gives a dense family in the invariant sector.
-/

open MeasureTheory

namespace NCG.CompactGaugeAveragingDensity

noncomputable section

variable {G X : Type*}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable [SecondCountableTopology G]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [FirstCountableTopology X]
variable (act : G → X → X) (hact : Continuous (Function.uncurry act))
variable (μ : Measure G) [IsProbabilityMeasure μ]

include hact in
theorem integrable_orbit (f : C(X, ℂ)) (x : X) :
    Integrable (fun g => f (act g x)) μ :=
  Continuous.integrable_of_hasCompactSupport
    (f.continuous.comp (hact.comp (continuous_id.prodMk continuous_const)))
    (HasCompactSupport.of_compactSpace _)

/-- Actual normalized Haar average, as a continuous function. -/
def average (f : C(X, ℂ)) : C(X, ℂ) where
  toFun x := ∫ g, f (act g x) ∂μ
  continuous_toFun := by
    have hc : Continuous (fun z : X × G => f (act z.2 z.1)) :=
      f.continuous.comp (hact.comp continuous_swap)
    simpa using continuous_parametric_integral_of_continuous hc
      (isCompact_univ : IsCompact (Set.univ : Set G))

@[simp] theorem average_apply (f : C(X, ℂ)) (x : X) :
    average act hact μ f x = ∫ g, f (act g x) ∂μ := rfl

theorem average_norm_le (f : C(X, ℂ)) : ‖average act hact μ f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  simpa using (norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun g => f (act g x))
    (Filter.Eventually.of_forall fun g => f.norm_coe_le_norm (act g x)))

/-- The contractive Reynolds operator on the continuous-function space. -/
def averageCLM : C(X, ℂ) →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous
    { toFun := average act hact μ
      map_add' := by
        intro f k
        ext x
        exact integral_add (integrable_orbit act hact μ f x)
          (integrable_orbit act hact μ k x)
      map_smul' := by
        intro c f
        ext x
        exact integral_smul c (fun g => f (act g x)) }
    1 (fun f => by simpa using average_norm_le act hact μ f)

/-- The concrete invariant sector, not an abstract supplied range. -/
def invariantSet : Set C(X, ℂ) := {f | ∀ g x, f (act g x) = f x}

theorem isClosed_invariantSet : IsClosed (invariantSet act) := by
  have heq : invariantSet act =
      ⋂ g : G, ⋂ x : X, {f : C(X, ℂ) | f (act g x) = f x} := by
    ext f
    simp [invariantSet]
  rw [heq]
  exact isClosed_iInter fun g => isClosed_iInter fun x =>
    isClosed_eq (continuous_eval_const (act g x)) (continuous_eval_const x)

theorem average_eq_self_of_invariant {f : C(X, ℂ)}
    (hf : f ∈ invariantSet act) : average act hact μ f = f := by
  ext x
  simp only [average_apply]
  exact integral_eq_const (Filter.Eventually.of_forall fun g => hf g x)

variable [Measure.IsMulRightInvariant μ]
variable (hact_mul : ∀ g h x, act (g * h) x = act g (act h x))

include hact_mul

/-- Right invariance of Haar measure proves gauge invariance of the integral. -/
theorem average_mem_invariantSet (f : C(X, ℂ)) :
    average act hact μ f ∈ invariantSet act := by
  intro h x
  change (∫ g, f (act g (act h x)) ∂μ) = ∫ g, f (act g x) ∂μ
  simp_rw [← hact_mul]
  exact integral_mul_right_eq_self (fun g => f (act g x)) h

theorem average_idempotent (f : C(X, ℂ)) :
    average act hact μ (average act hact μ f) = average act hact μ f :=
  average_eq_self_of_invariant act hact μ
    (average_mem_invariantSet act hact μ hact_mul f)

/-- Haar-averaged writers are dense in exactly the invariant sector. -/
theorem closure_average_image_eq_invariantSet
    (writers : Set C(X, ℂ)) (hdense : Dense writers) :
    closure (average act hact μ '' writers) = invariantSet act := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨f, _, rfl⟩
      exact average_mem_invariantSet act hact μ hact_mul f
    · exact isClosed_invariantSet act
  · intro f hf
    have hmem : average act hact μ f ∈ closure (average act hact μ '' writers) :=
      image_closure_subset_closure_image (averageCLM act hact μ).continuous
        ⟨f, hdense f, rfl⟩
    rwa [average_eq_self_of_invariant act hact μ hf] at hmem

end

end NCG.CompactGaugeAveragingDensity
