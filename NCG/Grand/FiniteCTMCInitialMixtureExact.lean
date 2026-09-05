/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacBackwardEquationExact

/-!
# Initial-state mixtures of genuine finite-CTMC path laws

The actual Ionescu--Tulcea law is linear in its initial distribution. The
same mixture identity holds on the admissible carrier, independently of
the arbitrary off-event projection value. This extends the proved point-start
Feynman--Kac formula to arbitrary finite initial probability distributions.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

namespace NCG.FiniteCTMCInitialMixture

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCPathLawDisintegration FiniteCTMCHomogeneousRestartLaw
open FiniteCTMCPathCarrierMeasurability FiniteCTMCAdmissiblePathLaw
open FiniteCTMCFeynmanKacPathMoment FiniteCTMCFeynmanKacIntegrability
open FiniteCTMCFeynmanKacBackwardEquation QuantumCylinderInverseLimit

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- Genuine point-start path kernel indexed by its initial state. -/
def pointStartKernel : Kernel S (ℕ → ℝ × S) :=
  (continuationKernel L hL hescape 0).comap pointInitialPrefix (measurable_of_countable _)

theorem pointStartKernel_apply (x : S) :
    pointStartKernel L hL hescape x = jumpSequenceLaw (pointMass x) L hL hescape := by
  exact (jumpSequenceLaw_pointMass_eq_continuation L hL hescape x).symm

/-- Sampling the initial state and then its point-start kernel gives the
actual full jump-sequence law. -/
theorem jumpSequenceLaw_eq_pointStart_comp (p : S → ℝ) :
    jumpSequenceLaw p L hL hescape = pointStartKernel L hL hescape ∘ₘ discrete p := by
  letI : ∀ k, IsMarkovKernel (historyJumpKernel L k) :=
    fun k => historyJumpKernel_isMarkov L hL hescape k
  unfold jumpSequenceLaw Kernel.trajMeasure initialHoldingStateMeasure
  rw [Measure.dirac_prod, Measure.map_map (MeasurableEquiv.piUnique _).symm.measurable
    (measurable_prodMk_left (x := (0 : ℝ)))]
  change continuationKernel L hL hescape 0 ∘ₘ (discrete p).map pointInitialPrefix = _
  rw [← Measure.deterministic_comp_eq_map (measurable_of_countable pointInitialPrefix),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
  rfl

/-- Exact finite initial-state mixture of the full infinite-path measures. -/
theorem jumpSequenceLaw_eq_sum_pointMass (p : S → ℝ) :
    jumpSequenceLaw p L hL hescape =
      ∑ x, ENNReal.ofReal (p x) • jumpSequenceLaw (pointMass x) L hL hescape := by
  rw [jumpSequenceLaw_eq_pointStart_comp, Measure.comp_eq_sum_of_countable, Measure.sum_fintype]
  simp only [discrete_singleton, pointStartKernel_apply]

/-- The fallback initial state used outside the probability-one admissible
event does not change a point-start physical path law. -/
theorem map_admissibleProjection_pointMass (x₀ x : S) :
    (jumpSequenceLaw (pointMass x) L hL hescape).map (admissibleProjection x₀) =
      admissiblePathLaw x (pointMass x) L hL hescape := by
  letI : Nonempty S := ⟨x⟩
  unfold admissiblePathLaw
  apply Measure.map_congr
  have h₀ := ae_coe_admissibleProjection_eq_id x₀ (pointMass x) (pointMass_nonnegative x)
    (sum_pointMass x) L hL hescape
  have hx := ae_coe_admissibleProjection_eq_id x (pointMass x) (pointMass_nonnegative x)
    (sum_pointMass x) L hL hescape
  filter_upwards [h₀, hx] with z hz₀ hzx
  exact Subtype.ext (hz₀.trans hzx.symm)

/-- The same genuine mixture identity on the physical admissible carrier. -/
theorem admissiblePathLaw_eq_sum_pointMass (x₀ : S) (p : S → ℝ) :
    admissiblePathLaw x₀ p L hL hescape =
      ∑ x, ENNReal.ofReal (p x) • admissiblePathLaw x (pointMass x) L hL hescape := by
  unfold admissiblePathLaw at ⊢
  rw [jumpSequenceLaw_eq_sum_pointMass,
    Measure.map_finset_sum' (measurable_admissibleProjection x₀).aemeasurable]
  simp only [Measure.map_smul, map_admissibleProjection_pointMass]

/-- Finite exponential moments for the actual mixed initial-state path law. -/
theorem integrable_feynmanKacIntegrand_initialLaw
    (x₀ : S) (p : S → ℝ)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (feynmanKacIntegrand v g k T f)
      (admissiblePathLaw x₀ p L hL hescape) := by
  rw [admissiblePathLaw_eq_sum_pointMass, integrable_finsetSum_measure]
  intro x _
  exact (integrable_feynmanKacIntegrand L hL hescape x v g k T f hT).smul_measure
    ENNReal.ofReal_ne_top

/-- Exact initial-mixture identity for the actual Feynman--Kac expectation. -/
theorem pathMoment_eq_sum_conditionalPathMoment
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    pathMoment x₀ p L hL hescape v g k T f =
      ∑ x, p x * conditionalPathMoment L hL hescape v g k T f x := by
  unfold pathMoment
  rw [admissiblePathLaw_eq_sum_pointMass, integral_finsetSum_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (hp _), smul_eq_mul,
      conditionalPathMoment, pathMoment]
  · intro x _
    exact (integrable_feynmanKacIntegrand L hL hescape x v g k T f hT).smul_measure
      ENNReal.ofReal_ne_top

/-- The genuine finite-state Feynman--Kac formula for every nonnegative
initial weight vector (in particular every initial probability distribution). -/
theorem pathMoment_eq_exponentialEntry_pairing
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    pathMoment x₀ p L hL hescape v g k T f =
      ∑ x, p x * Matrix.mulVec (Matrix.exponentialEntry (T • tilt L v g k)) f x := by
  letI : Nonempty S := ⟨x₀⟩
  rw [pathMoment_eq_sum_conditionalPathMoment L hL hescape x₀ p hp v g k T f hT,
    conditionalPathMoment_eq_exponentialEntry_mulVec L hL hescape v g k T f hT]

end

end NCG.FiniteCTMCInitialMixture
