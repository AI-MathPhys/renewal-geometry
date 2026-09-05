/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteLatticeGaugeInvariantDensityExact
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Canonical Haar reference measure for finite lattice configurations

The normalized Haar reference measure and its gauge invariance are constructed,
rather than assumed. Right invariance follows from uniqueness of Haar
probability measure, without a commutativity assumption on the gauge group.
-/

open MeasureTheory

namespace NCG.FiniteLatticeHaarGaugeMeasure

open FiniteLatticeGaugeInvariantDensity

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

def normalizedHaar : Measure G := Measure.haarMeasure (wholeGroup G)

instance normalizedHaar_isProbability : IsProbabilityMeasure (normalizedHaar G) := by
  constructor
  simpa [normalizedHaar, wholeGroup] using
    (Measure.haarMeasure_self (K₀ := wholeGroup G))

instance normalizedHaar_isHaar : Measure.IsHaarMeasure (normalizedHaar G) := by
  unfold normalizedHaar
  infer_instance

instance normalizedHaar_isMulRightInvariant : Measure.IsMulRightInvariant (normalizedHaar G) := by
  constructor
  intro g
  have : IsProbabilityMeasure ((normalizedHaar G).map (· * g)) :=
    Measure.isProbabilityMeasure_map (continuous_mul_const g).measurable.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable {V E : Type*} [Fintype V] [Fintype E]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable (target source : E → V)

/-- Configuration Haar is the usual product of independent edge Haar laws. -/
theorem normalizedHaar_pi_eq :
    normalizedHaar (E → G) = Measure.pi (fun _ : E => normalizedHaar G) :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The exact vertex gauge action preserves the canonical configuration Haar
probability measure. -/
theorem measurePreserving_gaugeAction (h : V → G) :
    MeasurePreserving (gaugeAction G target source h)
      (normalizedHaar (E → G)) (normalizedHaar (E → G)) := by
  exact (measurePreserving_mul_right (normalizedHaar (E → G))
    (fun e => (h (source e))⁻¹)).comp
    (measurePreserving_mul_left (normalizedHaar (E → G)) (fun e => h (target e)))

end

end NCG.FiniteLatticeHaarGaugeMeasure
