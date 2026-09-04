/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactGroupInvariantProjectionExact
import NCG.Grand.CompactGaugeAveragingDensityExact
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Continuous gauge invariants are dense in the full invariant L² space

For a continuous compact-group action preserving a finite regular Borel
measure, Koopman pullbacks are constructed on actual L² classes. Strong
continuity and the action law are proved from the point action. The Bochner
projection intertwines with continuous-function Haar averaging. Thus the
closure of continuous invariant functions equals the full measurable fixed
subspace, not a subspace defined by that closure.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG.CompactGaugeInvariantL2Density

noncomputable section

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X] [FirstCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]
variable (act : G → X → X) (hact : Continuous (Function.uncurry act))
variable (ν : Measure X) [IsFiniteMeasure ν] [ν.Regular]
variable (hpres : ∀ g, MeasurePreserving (act g) ν ν)

def actionMap (g : G) : C(X, X) :=
  ⟨act g, hact.comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_actionMap : Continuous (actionMap act hact) :=
  ContinuousMap.continuous_of_continuous_uncurry _ hact

/-- The actual isometric L² pullback induced by each gauge transformation. -/
def pullback (g : G) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℂ (act g) (hpres g)).toContinuousLinearMap

include hact in
theorem continuous_pullback_orbit (v : Lp ℂ 2 ν) :
    Continuous (fun g => pullback act ν hpres g v) :=
  continuous_const.compMeasurePreservingLp (continuous_actionMap act hact)
    hpres (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

theorem pullback_norm_le (g : G) (v : Lp ℂ 2 ν) :
    ‖pullback act ν hpres g v‖ ≤ ‖v‖ :=
  (Lp.norm_compMeasurePreserving v (hpres g)).le

variable (hmul : ∀ g h x, act (g * h) x = act g (act h x))

include hmul in
theorem pullback_mul (g h : G) (v : Lp ℂ 2 ν) :
    pullback act ν hpres (g * h) v = pullback act ν hpres h (pullback act ν hpres g v) := by
  change Lp.compMeasurePreserving (act (g * h)) _ v =
    Lp.compMeasurePreserving (act h) _ (Lp.compMeasurePreserving (act g) _ v)
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v (hpres (g * h)),
    Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving (act g) (hpres g) v) (hpres h),
    (hpres h).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving v (hpres g))]
    with x hx hy hz
  simp only [Function.comp_apply] at hx hy hz
  rw [hx, hy, hz, hmul]

def continuousPullback (g : G) (f : C(X, ℂ)) : C(X, ℂ) := f.comp (actionMap act hact g)

theorem continuous_continuousPullback (f : C(X, ℂ)) :
    Continuous (fun g => continuousPullback act hact g f) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (f.continuous.comp hact)

theorem toLp_continuousPullback (g : G) (f : C(X, ℂ)) :
    ContinuousMap.toLp (E := ℂ) 2 ν ℂ (continuousPullback act hact g f) =
      pullback act ν hpres g (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) := by
  apply Lp.ext
  have hp := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) (hpres g)
  have hf := (hpres g).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) ν f)
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) ν
    (continuousPullback act hact g f), hp, hf] with x hx hy hz
  change _ = Lp.compMeasurePreserving (act g) (hpres g)
    (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) x
  exact hx.trans (hz.symm.trans hy.symm)

variable (μ : Measure G) [IsProbabilityMeasure μ]

theorem integrable_continuousPullback (f : C(X, ℂ)) :
    Integrable (fun g => continuousPullback act hact g f) μ :=
  (continuous_continuousPullback act hact f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem continuous_average_eq_integral (f : C(X, ℂ)) :
    CompactGaugeAveragingDensity.average act hact μ f =
      ∫ g, continuousPullback act hact g f ∂μ := by
  ext x
  rw [ContinuousMap.integral_apply (integrable_continuousPullback act hact μ f)]
  rfl

/-- Haar projection on the full measurable L² carrier. -/
def mean : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  CompactGroupInvariantProjection.mean (pullback act ν hpres) μ
    (continuous_pullback_orbit act hact ν hpres) (pullback_norm_le act ν hpres)

/-- Continuous and measurable Haar averages agree under the actual L²
embedding, by commutation of a continuous linear map with Bochner integration. -/
theorem mean_toLp (f : C(X, ℂ)) :
    mean act hact ν hpres μ (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) =
      ContinuousMap.toLp (E := ℂ) 2 ν ℂ (CompactGaugeAveragingDensity.average act hact μ f) := by
  change (∫ g, pullback act ν hpres g (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) ∂μ) = _
  rw [continuous_average_eq_integral act hact μ f,
    ← (ContinuousMap.toLp (E := ℂ) 2 ν ℂ).integral_comp_comm
      (integrable_continuousPullback act hact μ f)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
    (toLp_continuousPullback act hact ν hpres g f).symm)

variable [Measure.IsMulRightInvariant μ]

include hmul hact μ in
/-- This equality identifies the continuous invariant closure with the full
measurable fixed space. The right-hand side is independently defined by every
Koopman pullback, not by source-orbit closure. -/
theorem closure_toLp_invariants_eq_fixedSet :
    closure (ContinuousMap.toLp (E := ℂ) 2 ν ℂ ''
      CompactGaugeAveragingDensity.invariantSet act) =
      CompactGroupInvariantProjection.fixedSet (pullback act ν hpres) := by
  have heq : mean act hact ν hpres μ ''
      Set.range (ContinuousMap.toLp (E := ℂ) 2 ν ℂ) =
      ContinuousMap.toLp (E := ℂ) 2 ν ℂ '' CompactGaugeAveragingDensity.invariantSet act := by
    ext v
    constructor
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨CompactGaugeAveragingDensity.average act hact μ f,
        CompactGaugeAveragingDensity.average_mem_invariantSet act hact μ hmul f,
        (mean_toLp act hact ν hpres μ f).symm⟩
    · rintro ⟨f, hf, rfl⟩
      refine ⟨ContinuousMap.toLp (E := ℂ) 2 ν ℂ f, ⟨f, rfl⟩, ?_⟩
      rw [mean_toLp, CompactGaugeAveragingDensity.average_eq_self_of_invariant act hact μ hf]
  rw [← heq]
  exact CompactGroupInvariantProjection.closure_mean_image_eq_fixedSet
    (pullback act ν hpres) μ (continuous_pullback_orbit act hact ν hpres)
    (pullback_norm_le act ν hpres) (pullback_mul act ν hpres hmul) _
    (ContinuousMap.toLp_denseRange ℂ ν ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))

end

end NCG.CompactGaugeInvariantL2Density
