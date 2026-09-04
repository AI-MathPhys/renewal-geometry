/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HolonomyCoordinateDensityExact
import NCG.Grand.CompactGaugeAveragingDensityExact
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic.Group

/-!
# Invariant density for finite lattice matrix holonomies

This specializes coordinate separation and Haar averaging to the actual
vertex gauge action `(h · U)e = h(t e) * U e * h(s e)⁻¹`. The measure used for
averaging is constructed here from normalized Haar measure on the compact
vertex gauge group. No separation, density, or averaging-projection premise
is assumed.

This proves the invariant-density mechanism for the bank containing all
retained edge matrix coefficients. Identifying a more restricted primitive
plaquette/current bank with that bank, and physical vacuum cyclicity, are not
asserted by this result.
-/

open MeasureTheory

namespace NCG.FiniteLatticeGaugeInvariantDensity

noncomputable section

section Haar

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The whole compact group is the normalization set. -/
def wholeGroup : TopologicalSpace.PositiveCompacts G :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- A canonical right-invariant probability Haar measure. -/
def rightHaarProbability : Measure G :=
  (Measure.haarMeasure (wholeGroup G)).inv

instance rightHaarProbability_isProbability :
    IsProbabilityMeasure (rightHaarProbability G) := by
  constructor
  change (Measure.haarMeasure (wholeGroup G)).inv Set.univ = 1
  simpa [wholeGroup] using
    (Measure.haarMeasure_self (K₀ := wholeGroup G))

instance rightHaarProbability_isMulRightInvariant :
    Measure.IsMulRightInvariant (rightHaarProbability G) := by
  unfold rightHaarProbability
  infer_instance

end Haar

section Lattice

variable {V E n : Type*} [Fintype V] [Fintype E] [Fintype n] [DecidableEq n]
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (target source : E → V)

/-- The vertex gauge action on the actual edge holonomies. -/
def gaugeAction (h : V → G) (U : E → G) : E → G :=
  fun e => h (target e) * U e * (h (source e))⁻¹

theorem continuous_gaugeAction :
    Continuous (Function.uncurry (gaugeAction G target source)) := by
  apply continuous_pi
  intro e
  exact (((continuous_apply (target e)).comp continuous_fst).mul
    ((continuous_apply e).comp continuous_snd)).mul
    (((continuous_apply (source e)).comp continuous_fst).inv)

theorem gaugeAction_mul (g h : V → G) (U : E → G) :
    gaugeAction G target source (g * h) U =
      gaugeAction G target source g (gaugeAction G target source h U) := by
  funext e
  simp only [gaugeAction, Pi.mul_apply, mul_inv_rev, mul_assoc]

/-- Haar averaging of an actual continuous lattice writer. -/
def gaugeAverage : C(E → G, ℂ) → C(E → G, ℂ) :=
  CompactGaugeAveragingDensity.average
    (gaugeAction G target source) (continuous_gaugeAction G target source)
    (rightHaarProbability (V → G))

variable (rho : G →* Matrix n n ℂ) (hcontinuous : Continuous rho)

/-- An actual matrix coefficient of the defining representation. -/
def matrixEntry (e : E) (i j : n) : C(E → G, ℂ) where
  toFun U := rho (U e) i j
  continuous_toFun := (hcontinuous.comp (continuous_apply e)).matrix_elem i j

/-- The concrete matrix-entry polynomial star algebra. -/
def matrixEntryAlgebra : StarSubalgebra ℂ C(E → G, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun a : E × n × n =>
    matrixEntry G rho hcontinuous a.1 a.2.1 a.2.2)

theorem matrixEntryAlgebra_separatesPoints (hfaithful : Function.Injective rho) :
    (matrixEntryAlgebra (E := E) G rho hcontinuous).SeparatesPoints := by
  intro U W hne
  have hex : ∃ e i j, rho (U e) i j ≠ rho (W e) i j := by
    by_contra h
    push Not at h
    apply hne
    funext e
    apply hfaithful
    funext i j
    exact h e i j
  obtain ⟨e, i, j, h⟩ := hex
  refine ⟨matrixEntry G rho hcontinuous e i j, ?_, h⟩
  exact ⟨matrixEntry G rho hcontinuous e i j,
    StarAlgebra.subset_adjoin ℂ _ ⟨(e, i, j), rfl⟩, rfl⟩

/-- Uniform density of the explicit gauge-averaged matrix-entry polynomials
in the full continuous gauge-invariant lattice sector. -/
theorem closure_gaugeAverage_coordinateAlgebra (hfaithful : Function.Injective rho) :
    closure (gaugeAverage G target source ''
      (matrixEntryAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      {f : C(E → G, ℂ) | ∀ h U, f (gaugeAction G target source h U) = f U} := by
  apply CompactGaugeAveragingDensity.closure_average_image_eq_invariantSet
    (gaugeAction G target source) (continuous_gaugeAction G target source)
    (rightHaarProbability (V → G))
    (gaugeAction_mul G target source)
  rw [dense_iff_closure_eq]
  change ((matrixEntryAlgebra (E := E) G rho hcontinuous).topologicalClosure :
    Set C(E → G, ℂ)) = Set.univ
  rw [ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (matrixEntryAlgebra_separatesPoints G rho hcontinuous hfaithful)]
  rfl

end Lattice

end

end NCG.FiniteLatticeGaugeInvariantDensity
