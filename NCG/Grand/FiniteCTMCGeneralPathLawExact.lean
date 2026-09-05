/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCClockProjectionExact

/-!
# A genuine path law and Feynman--Kac formula for every finite generator

The physical law is the measurable projection of the Ionescu--Tulcea law
for the positive-escape clock lift. No physical escape-rate assumption is
made. The reward ignores invisible clock ticks, and the exact tilted
semigroup intertwining gives the original generator's Feynman--Kac formula.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.FiniteCTMCGeneralPathLaw

open DrivenProcess FiniteGeneratorPositiveEscapeLift FiniteCTMCClockProjection
open FiniteCTMCPathCarrierMeasurability FiniteCTMCPathEvaluationMeasurability
open FiniteCTMCAdmissiblePathLaw FiniteCTMCFeynmanKacPathMoment FiniteCTMCInitialMixture

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Initialize the independent clock in its false state. -/
def initialLift (p : S → ℝ) : Bool × S → ℝ := fun x => if x.1 = false then p x.2 else 0

theorem initialLift_nonneg (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ initialLift p x := by
  rintro ⟨b, i⟩
  cases b <;> simp [initialLift, hp]

theorem sum_initialLift (p : S → ℝ) : ∑ x, initialLift p x = ∑ x, p x := by
  simp [initialLift, Fintype.sum_prod_type]

/-- Genuine probability law of the positive-escape clock lift. -/
def liftedPathLaw (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ) :
    Measure (AdmissibleJumpSequence (S := Bool × S)) :=
  admissiblePathLaw (false, x₀) (initialLift p) (clockLift L)
    (clockLift_isGenerator L hL) (escapeRate_clockLift_pos L hL)

/-- The physical nonexplosive cadlag path law for an arbitrary finite generator. -/
def physicalPathLaw (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ) :
    Measure (AdmissibleJumpSequence (S := S)) :=
  (liftedPathLaw L hL x₀ p).map forgetClockPath

theorem liftedPathLaw_isProbabilityMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    IsProbabilityMeasure (liftedPathLaw L hL x₀ p) := by
  exact admissiblePathLaw_isProbabilityMeasure (false, x₀) (initialLift p)
    (initialLift_nonneg p hp) (by simpa only [sum_initialLift] using hsum)
    (clockLift L) (clockLift_isGenerator L hL) (escapeRate_clockLift_pos L hL)

theorem physicalPathLaw_isProbabilityMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    IsProbabilityMeasure (physicalPathLaw L hL x₀ p) := by
  letI := liftedPathLaw_isProbabilityMeasure L hL x₀ p hp hsum
  exact Measure.isProbabilityMeasure_map measurable_forgetClockPath.aemeasurable

/-- The manuscript's exponential reward times the physical terminal function. -/
def physicalIntegrand (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ)
    (z : AdmissibleJumpSequence (S := S)) : ℝ :=
  Real.exp (k * visibleReward v g T z) * f (admissibleStateAt z T)

theorem measurable_physicalIntegrand
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Measurable (physicalIntegrand v g k T f) :=
  measurable_feynmanKacIntegrand v (visibleJumpReward g) k T f hT

/-- Pathwise pullback of the integrand to the actual lifted process. -/
theorem physicalIntegrand_comp_forgetClockPath
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) :
    physicalIntegrand v g k T f ∘ forgetClockPath =
      feynmanKacIntegrand (liftFunction v) (liftJumpReward g) k T (liftFunction f) := rfl

/-- Genuine integrability of every bounded-terminal Feynman--Kac observable. -/
theorem integrable_physicalIntegrand
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (physicalIntegrand v g k T f) (physicalPathLaw L hL x₀ p) := by
  apply (integrable_map_measure (measurable_physicalIntegrand v g k T f hT).aestronglyMeasurable
    measurable_forgetClockPath.aemeasurable).mpr
  rw [physicalIntegrand_comp_forgetClockPath]
  exact integrable_feynmanKacIntegrand_initialLaw (clockLift L) (clockLift_isGenerator L hL)
    (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p)
    (liftFunction v) (liftJumpReward g) k T (liftFunction f) hT

/-- The actual physical path expectation, defined as an integral rather than a matrix expression. -/
def physicalPathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) : ℝ :=
  ∫ z, physicalIntegrand v g k T f z ∂physicalPathLaw L hL x₀ p

/-- Integration through the measurable physical projection gives the lifted moment. -/
theorem physicalPathMoment_eq_liftedPathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    physicalPathMoment L hL x₀ p v g k T f =
      pathMoment (false, x₀) (initialLift p) (clockLift L) (clockLift_isGenerator L hL)
        (escapeRate_clockLift_pos L hL) (liftFunction v) (liftJumpReward g) k T (liftFunction f) := by
  unfold physicalPathMoment physicalPathLaw
  rw [integral_map measurable_forgetClockPath.aemeasurable
    (measurable_physicalIntegrand v g k T f hT).aestronglyMeasurable]
  rfl

/-- Feynman--Kac for every finite generator, including absorbing states and
singleton carriers, with the original matrix and actual physical path reward. -/
theorem physicalPathMoment_eq_exponentialEntry_pairing
    (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) (p : S → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    physicalPathMoment L hL x₀ p v g k T f =
      ∑ x, p x * Matrix.mulVec (Matrix.exponentialEntry (T • tilt L v g k)) f x := by
  rw [physicalPathMoment_eq_liftedPathMoment L hL x₀ p v g k T f hT]
  rw [pathMoment_eq_exponentialEntry_pairing (clockLift L) (clockLift_isGenerator L hL)
    (escapeRate_clockLift_pos L hL) (false, x₀) (initialLift p) (initialLift_nonneg p hp)
    (liftFunction v) (liftJumpReward g) k T (liftFunction f) hT]
  rw [tilt_clockLift, exponentialEntry_clockLift_mulVec]
  simp [initialLift, liftFunction, Fintype.sum_prod_type]

end

end NCG.FiniteCTMCGeneralPathLaw
