/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TrineComplexAcquisitionAndTransport
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Measure-level positive trine acquisition

This lifts the scalar-density algebra of `thm:GT-trine-complex-measure` to an
arbitrary reference measure.  The three nonnegative outcome densities define
honest positive measures whose sum is the carrier measure.  Positivity of the
balanced completion, uniqueness, isotropic slack, trace minimality, and the
Hilbert--Schmidt minimizer all hold almost everywhere; the last inequality is
also integrated whenever the two densities are integrable.
-/

open Finset Filter Set
open scoped ENNReal MeasureTheory

namespace NCG
namespace TrineMeasureAcquisition

open MeasureTheory
open PositiveCylinderAndTrine
open TrineComplexAcquisitionAndTransport

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Radon--Nikodym reduction of arbitrary positive outcomes -/

/-- The carrier of three arbitrary positive outcome measures. -/
noncomputable def trineCarrierMeasure (ρ : Fin 3 → Measure Ω) : Measure Ω :=
  ∑ k, ρ k

/-- The real RN density of outcome `k` with respect to the carrier sum. -/
noncomputable def trineRNDensity (ρ : Fin 3 → Measure Ω) (k : Fin 3) (ω : Ω) : ℝ :=
  ((ρ k).rnDeriv (trineCarrierMeasure ρ) ω).toReal

/-- Each positive outcome is dominated by the sum of all three outcomes. -/
theorem outcomeMeasure_le_trineCarrier (ρ : Fin 3 → Measure Ω) (k : Fin 3) :
    ρ k ≤ trineCarrierMeasure ρ := by
  unfold trineCarrierMeasure
  exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ k)

/-- Every finite positive outcome is exactly reconstructed from its RN density
with respect to the carrier sum. -/
theorem withDensity_rnDeriv_outcome_eq
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] (k : Fin 3) :
    (trineCarrierMeasure ρ).withDensity
        ((ρ k).rnDeriv (trineCarrierMeasure ρ)) = ρ k :=
  by
    letI : IsFiniteMeasure (trineCarrierMeasure ρ) := by
      unfold trineCarrierMeasure
      infer_instance
    exact Measure.withDensity_rnDeriv_eq _ _
      (Measure.absolutelyContinuous_of_le (outcomeMeasure_le_trineCarrier ρ k))

/-- The real-valued RN density gives the same positive measure after applying
`ENNReal.ofReal`; no mass is lost because RN derivatives are finite almost
everywhere for a finite carrier. -/
theorem withDensity_trineRNDensity_eq
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] (k : Fin 3) :
    (trineCarrierMeasure ρ).withDensity
        (fun ω => ENNReal.ofReal (trineRNDensity ρ k ω)) = ρ k := by
  letI : IsFiniteMeasure (trineCarrierMeasure ρ) := by
    unfold trineCarrierMeasure
    infer_instance
  calc
    (trineCarrierMeasure ρ).withDensity
          (fun ω => ENNReal.ofReal (trineRNDensity ρ k ω)) =
        (trineCarrierMeasure ρ).withDensity
          ((ρ k).rnDeriv (trineCarrierMeasure ρ)) := by
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top (ρ k) (trineCarrierMeasure ρ)] with ω hω
      exact ENNReal.ofReal_toReal hω.ne
    _ = ρ k := withDensity_rnDeriv_outcome_eq ρ k

/-- RN outcome densities are nonnegative everywhere. -/
theorem trineRNDensity_nonneg (ρ : Fin 3 → Measure Ω) (k : Fin 3) (ω : Ω) :
    0 ≤ trineRNDensity ρ k ω :=
  ENNReal.toReal_nonneg

/-- The three RN densities sum to one carrier-almost everywhere. -/
theorem ae_sum_trineRNDensity_eq_one
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    ∀ᵐ ω ∂trineCarrierMeasure ρ, ∑ k, trineRNDensity ρ k ω = 1 := by
  letI : IsFiniteMeasure (trineCarrierMeasure ρ) := by
    unfold trineCarrierMeasure
    infer_instance
  let τ := trineCarrierMeasure ρ
  have hτ : τ = ρ 0 + ρ 1 + ρ 2 := by
    simp [τ, trineCarrierMeasure, Fin.sum_univ_three]
  have h01 := Measure.rnDeriv_add (ρ 0) (ρ 1) τ
  have h012 := Measure.rnDeriv_add (ρ 0 + ρ 1) (ρ 2) τ
  have hself := Measure.rnDeriv_self τ
  have h0fin := Measure.rnDeriv_lt_top (ρ 0) τ
  have h1fin := Measure.rnDeriv_lt_top (ρ 1) τ
  have h2fin := Measure.rnDeriv_lt_top (ρ 2) τ
  filter_upwards [h01, h012, hself, h0fin, h1fin, h2fin] with
      ω h01ω h012ω hselfω h0ω h1ω h2ω
  simp only [trineRNDensity, Fin.sum_univ_three]
  have hsum :
      (ρ 0).rnDeriv τ ω + (ρ 1).rnDeriv τ ω + (ρ 2).rnDeriv τ ω = 1 := by
    simp only [Pi.add_apply] at h01ω h012ω
    rw [← h01ω, ← h012ω, ← hτ, hselfω]
  rw [← ENNReal.toReal_add h0ω.ne h1ω.ne,
    ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h0ω.ne, h1ω.ne⟩) h2ω.ne,
    hsum]
  norm_num

/-- The `k`th positive trine outcome as an RN density. -/
noncomputable def outcomeDensity (t x y : Ω → ℝ) (k : Fin 3) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (trineOutcome (t ω) (x ω) (y ω) k)

/-- The positive measure acquired in trine arm `k`. -/
noncomputable def outcomeMeasure (μ : Measure Ω) (t x y : Ω → ℝ) (k : Fin 3) :
    Measure Ω := μ.withDensity (outcomeDensity t x y k)

/-- The total carrier measure with RN density `t`. -/
noncomputable def carrierMeasure (μ : Measure Ω) (t : Ω → ℝ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (t ω)

/-- Measurable real trine coordinates give measurable RN densities. -/
theorem measurable_outcomeDensity
    {t x y : Ω → ℝ} (ht : Measurable t) (hx : Measurable x) (hy : Measurable y)
    (k : Fin 3) : Measurable (outcomeDensity t x y k) := by
  unfold outcomeDensity
  fin_cases k <;> simp [trineOutcome] <;> fun_prop

/-- The three acquired positive measures sum exactly to the carrier measure.
This is the measure-level version of `τ = ρ₀+ρ₁+ρ₂`. -/
theorem sum_outcomeMeasure_eq_carrier
    (t x y : Ω → ℝ)
    (ht : Measurable t) (hx : Measurable x) (hy : Measurable y)
    (hout : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ trineOutcome (t ω) (x ω) (y ω) k) :
    (∑ k : Fin 3, outcomeMeasure μ t x y k) = carrierMeasure μ t := by
  ext s hs
  rw [Measure.finsetSum_apply Finset.univ
    (fun k : Fin 3 => outcomeMeasure μ t x y k) s]
  simp only [outcomeMeasure, carrierMeasure, MeasureTheory.withDensity_apply _ hs]
  rw [← lintegral_finsetSum Finset.univ
    (fun k _ => measurable_outcomeDensity ht hx hy k)]
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.2 (fun k => ae_restrict_of_ae (hout k))] with ω hω
  simp only [outcomeDensity]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hω k)]
  simp only [trineOutcome_sum]

/-- The scalar trine positivity criterion is an almost-everywhere equivalence
on an arbitrary reference cylinder. -/
theorem ae_trine_positive_functional_iff
    (t x y : Ω → ℝ) (ht : ∀ᵐ ω ∂μ, 0 ≤ t ω) :
    (∀ᵐ ω ∂μ,
      ∑ k : Fin 3, trineOutcome (t ω) (x ω) (y ω) k ^ 2 ≤ t ω ^ 2 / 2) ↔
    (∀ᵐ ω ∂μ, PositiveTrineCompletion (t ω) (x ω) (y ω) 0) := by
  constructor
  · intro h
    filter_upwards [ht, h] with ω htω hω
    exact (trine_positive_functional_iff htω).mp hω
  · intro h
    filter_upwards [ht, h] with ω htω hω
    exact (trine_positive_functional_iff htω).mpr hω

/-- Equality of all three outcome density functions almost everywhere recovers
all three real target coordinates almost everywhere. -/
theorem ae_trine_representation_unique
    (t x y t' x' y' : Ω → ℝ)
    (h : ∀ᵐ ω ∂μ,
      trineOutcome (t ω) (x ω) (y ω) =
        trineOutcome (t' ω) (x' ω) (y' ω)) :
    (∀ᵐ ω ∂μ, t ω = t' ω) ∧
      (∀ᵐ ω ∂μ, x ω = x' ω) ∧
      (∀ᵐ ω ∂μ, Real.sqrt 3 * y ω = Real.sqrt 3 * y' ω) := by
  have hall : ∀ᵐ ω ∂μ,
      t ω = t' ω ∧ x ω = x' ω ∧
        Real.sqrt 3 * y ω = Real.sqrt 3 * y' ω := by
    filter_upwards [h] with ω hω
    exact trine_representation_unique hω
  exact ⟨hall.mono fun _ hω => hω.1,
    hall.mono fun _ hω => hω.2.1,
    hall.mono fun _ hω => hω.2.2⟩

/-- The balanced density is almost everywhere the unique pointwise
Hilbert--Schmidt minimizer among imbalanced completions. -/
theorem ae_balanced_completion_unique_minimizer
    (t x y d : Ω → ℝ) :
    (∀ᵐ ω ∂μ,
      completionHilbertSchmidtSq (t ω) (x ω) (y ω) 0 ≤
        completionHilbertSchmidtSq (t ω) (x ω) (y ω) (d ω)) ∧
      ((∀ᵐ ω ∂μ,
        completionHilbertSchmidtSq (t ω) (x ω) (y ω) (d ω) =
          completionHilbertSchmidtSq (t ω) (x ω) (y ω) 0) ↔
        ∀ᵐ ω ∂μ, d ω = 0) := by
  constructor
  · exact Filter.Eventually.of_forall fun ω =>
      (balanced_completion_unique_minimizer (t ω) (x ω) (y ω) (d ω)).1
  · constructor
    · intro h
      filter_upwards [h] with ω hω
      exact (balanced_completion_unique_minimizer
        (t ω) (x ω) (y ω) (d ω)).2.mp hω
    · intro h
      filter_upwards [h] with ω hω
      exact (balanced_completion_unique_minimizer
        (t ω) (x ω) (y ω) (d ω)).2.mpr hω

/-- Under `L¹` hypotheses the pointwise Hilbert--Schmidt minimizer inequality
integrates over the whole cylinder. -/
theorem integral_balanced_completion_minimal
    (t x y d : Ω → ℝ)
    (hbal : Integrable (fun ω =>
      completionHilbertSchmidtSq (t ω) (x ω) (y ω) 0) μ)
    (hd : Integrable (fun ω =>
      completionHilbertSchmidtSq (t ω) (x ω) (y ω) (d ω)) μ) :
    ∫ ω, completionHilbertSchmidtSq (t ω) (x ω) (y ω) 0 ∂μ ≤
      ∫ ω, completionHilbertSchmidtSq (t ω) (x ω) (y ω) (d ω) ∂μ := by
  apply MeasureTheory.integral_mono_ae hbal hd
  exact (ae_balanced_completion_unique_minimizer t x y d).1

/-- The coherent-plus-isotropic slack identity holds almost everywhere for
measurable or nonmeasurable densities alike (it is pointwise algebra). -/
theorem ae_balanced_slack_decomposition (t x y : Ω → ℝ) :
    ∀ᵐ ω ∂μ,
      t ω / 2 = Real.sqrt (x ω ^ 2 + y ω ^ 2) +
        (t ω - 2 * Real.sqrt (x ω ^ 2 + y ω ^ 2)) / 2 :=
  Filter.Eventually.of_forall fun ω => balanced_slack_decomposition (t ω) (x ω) (y ω)

/-- Every positive matrix-density completion has trace at least twice the
complex amplitude, almost everywhere. -/
theorem ae_trace_minimal_positive_lift
    (p q x y : Ω → ℝ)
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω) (hq : ∀ᵐ ω ∂μ, 0 ≤ q ω)
    (hdet : ∀ᵐ ω ∂μ, x ω ^ 2 + y ω ^ 2 ≤ p ω * q ω) :
    ∀ᵐ ω ∂μ,
      2 * Real.sqrt (x ω ^ 2 + y ω ^ 2) ≤ p ω + q ω := by
  filter_upwards [hp, hq, hdet] with ω hpω hqω hdetω
  exact trace_minimal_positive_lift hpω hqω hdetω

/-- Consolidated arbitrary-measure form of the positive trine acquisition
theorem. -/
theorem measure_level_trine_acquisition
    (t x y d : Ω → ℝ)
    (htm : Measurable t) (hxm : Measurable x) (hym : Measurable y)
    (hout : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ trineOutcome (t ω) (x ω) (y ω) k)
    (ht : ∀ᵐ ω ∂μ, 0 ≤ t ω) :
    (∑ k : Fin 3, outcomeMeasure μ t x y k) = carrierMeasure μ t ∧
      ((∀ᵐ ω ∂μ,
        ∑ k : Fin 3, trineOutcome (t ω) (x ω) (y ω) k ^ 2 ≤ t ω ^ 2 / 2) ↔
        ∀ᵐ ω ∂μ, PositiveTrineCompletion (t ω) (x ω) (y ω) 0) ∧
      (∀ᵐ ω ∂μ,
        completionHilbertSchmidtSq (t ω) (x ω) (y ω) 0 ≤
          completionHilbertSchmidtSq (t ω) (x ω) (y ω) (d ω)) := by
  exact ⟨sum_outcomeMeasure_eq_carrier t x y htm hxm hym hout,
    ae_trine_positive_functional_iff t x y ht,
    (ae_balanced_completion_unique_minimizer t x y d).1⟩

end TrineMeasureAcquisition
end NCG
