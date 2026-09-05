/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GartnerEllisOpenSetLowerBoundExact

/-!
# Finite-cover aggregation of exponential upper bounds

This file isolates the compactness bookkeeping in the upper-bound half of
Gartner--Ellis.  A finite cover whose members all have rate at least
`A + epsilon` has union mass at most `exp (-n A)` eventually: the finite
cardinality prefactor is absorbed into `exp (n epsilon)`.
-/

open MeasureTheory Filter Finset Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace NCG.FiniteExponentialCoverUpperBound

open NCG.ExponentialTiltLocalLowerBound

set_option linter.unusedSectionVars false

/-- On a measurable set, `originalMass` is exactly the real-valued measure. -/
theorem originalMass_eq_measureReal
    (μ : Measure ℝ) (s : Set ℝ) (_hs : MeasurableSet s) :
    originalMass μ s = μ.real s := by
  unfold originalMass
  exact setIntegral_one_eq_measureReal

/-- A finite family of eventual assertions holds simultaneously eventually.
Unlike the countable-intersection variant, this requires no countability
assumption on the ambient filter. -/
theorem eventually_finset_forall
    {X ι : Type*} (l : Filter X)
    (s : Finset ι) (P : X → ι → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in l, P x i) :
    ∀ᶠ x in l, ∀ i ∈ s, P x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haev : ∀ᶠ x in l, P x a := hP a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, ∀ᶠ x in l, P x i := by
        intro i hi
        exact hP i (Finset.mem_insert_of_mem hi)
      have hsev : ∀ᶠ x in l, ∀ i ∈ s, P x i := ih hrest
      filter_upwards [haev, hsev] with x hxa hxs
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hxa
      · exact hxs i hi

/-- A fixed finite prefactor is eventually bounded by an arbitrarily small
positive exponential correction. -/
theorem eventually_natCard_le_exp_nat_mul
    (m : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (m : ℝ) ≤ Real.exp ((n : ℝ) * epsilon) := by
  have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * epsilon))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hepsilon)
  exact htend.eventually (eventually_ge_atTop (m : ℝ))

/-- Finite-cover aggregation: local exponential estimates with a uniform
positive rate margin imply the desired estimate on every subset of their
union. -/
theorem eventually_originalMass_subset_finiteCover_le
    {ι : Type*}
    (μ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (μ n)]
    (K : Set ℝ) (cover : Finset ι) (U : ι → Set ℝ)
    (A epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hK : K ⊆ ⋃ i ∈ cover, U i)
    (hKmeas : MeasurableSet K)
    (hUmeas : ∀ i ∈ cover, MeasurableSet (U i))
    (hlocal : ∀ i ∈ cover, ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) (U i) ≤
        Real.exp (-(n : ℝ) * (A + epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) K ≤ Real.exp (-(n : ℝ) * A) := by
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i (hi : i ∈ cover),
      originalMass (μ n) (U i) ≤
        Real.exp (-(n : ℝ) * (A + epsilon)) := by
    exact eventually_finset_forall atTop cover
      (fun n i => originalMass (μ n) (U i) ≤
        Real.exp (-(n : ℝ) * (A + epsilon))) hlocal
  have hcard := eventually_natCard_le_exp_nat_mul
    cover.card epsilon hepsilon
  filter_upwards [hall, hcard] with n hn hcardn
  calc
    originalMass (μ n) K = (μ n).real K :=
      originalMass_eq_measureReal (μ n) K hKmeas
    _ ≤ (μ n).real (⋃ i ∈ cover, U i) :=
      measureReal_mono hK (measure_ne_top _ _)
    _ ≤ ∑ i ∈ cover, (μ n).real (U i) :=
      measureReal_biUnion_finset_le cover U
    _ = ∑ i ∈ cover, originalMass (μ n) (U i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [originalMass_eq_measureReal (μ n) (U i) (hUmeas i hi)]
    _ ≤ ∑ _i ∈ cover,
        Real.exp (-(n : ℝ) * (A + epsilon)) := by
      exact Finset.sum_le_sum fun i hi => hn i hi
    _ = (cover.card : ℝ) *
        Real.exp (-(n : ℝ) * (A + epsilon)) := by simp
    _ ≤ Real.exp ((n : ℝ) * epsilon) *
        Real.exp (-(n : ℝ) * (A + epsilon)) :=
      mul_le_mul_of_nonneg_right hcardn (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

end NCG.FiniteExponentialCoverUpperBound
