/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TargetNativeReadLayerExact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Phase-quenched polar decomposition on arbitrary measure spaces

This supplies the `L¹(ν)` layer of `cor:GT-phase-quenched-quotient`.  An
integrable complex density is normalized by its `L¹` norm to an honest
positive probability measure.  Its zero-safe polar phase is unimodular for
that law, reconstructs the original complex integral exactly, and yields the
usual visibility bound.
-/

open Filter Set
open scoped ENNReal MeasureTheory ComplexConjugate

namespace NCG
namespace PhaseQuenchedMeasure

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Total complex variation of a dominated density. -/
noncomputable def absoluteMass (w : Ω → ℂ) (μ : Measure Ω) : ℝ :=
  ∫ ω, ‖w ω‖ ∂μ

/-- The normalized positive density defining the phase-quenched law. -/
noncomputable def phaseQuenchedDensity (w : Ω → ℂ) (μ : Measure Ω) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (‖w ω‖ / absoluteMass w μ)

/-- The canonical phase-quenched positive measure. -/
noncomputable def phaseQuenchedMeasure (w : Ω → ℂ) (μ : Measure Ω) : Measure Ω :=
  μ.withDensity (phaseQuenchedDensity w μ)

/-- Zero-safe polar phase.  Its value on the zero set is immaterial to the
phase-quenched law and is chosen to be zero. -/
noncomputable def polarPhase (w : Ω → ℂ) (ω : Ω) : ℂ :=
  if w ω = 0 then 0 else w ω / ‖w ω‖

theorem measurable_phaseQuenchedDensity {w : Ω → ℂ} (hw : Measurable w) :
    Measurable (phaseQuenchedDensity w μ) := by
  unfold phaseQuenchedDensity
  fun_prop

/-- A nonzero integrable complex variation normalizes to total mass one. -/
theorem phaseQuenchedMeasure_univ
    {w : Ω → ℂ} (hw : Integrable w μ) (hwmeas : Measurable w)
    (hZ : 0 < absoluteMass w μ) :
    phaseQuenchedMeasure w μ Set.univ = 1 := by
  rw [phaseQuenchedMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [phaseQuenchedDensity]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · simp only [div_eq_inv_mul]
    rw [integral_const_mul]
    simp only [absoluteMass]
    rw [inv_mul_cancel₀ (by simpa only [absoluteMass] using hZ.ne')]
    norm_num
  · exact hw.norm.div_const _
  · exact Filter.Eventually.of_forall fun ω => div_nonneg (norm_nonneg _) hZ.le

/-- The polar phase is unit modulus almost everywhere for the phase-quenched
law (the zero set has zero phase-quenched mass). -/
theorem ae_norm_polarPhase_eq_one
    {w : Ω → ℂ} (hw : Measurable w) (hZ : 0 < absoluteMass w μ) :
    ∀ᵐ ω ∂phaseQuenchedMeasure w μ, ‖polarPhase w ω‖ = 1 := by
  rw [phaseQuenchedMeasure,
    MeasureTheory.ae_withDensity_iff (measurable_phaseQuenchedDensity hw)]
  exact Filter.Eventually.of_forall fun ω hρ => by
    have hw0 : w ω ≠ 0 := by
      intro hwzero
      simp [phaseQuenchedDensity, hwzero] at hρ
    simp [polarPhase, hw0, norm_div, norm_norm, norm_ne_zero_iff.mpr hw0]

/-- The normalized density and polar phase reconstruct the original complex
density pointwise after restoring the absolute mass. -/
theorem absoluteMass_mul_density_mul_phase
    (w : Ω → ℂ) (μ : Measure Ω) (hZ : 0 < absoluteMass w μ) (ω : Ω) :
    (absoluteMass w μ : ℂ) *
        ((phaseQuenchedDensity w μ ω).toReal : ℂ) * polarPhase w ω = w ω := by
  by_cases hw0 : w ω = 0
  · simp [phaseQuenchedDensity, polarPhase, hw0]
  · have hn : ‖w ω‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    have hq : 0 ≤ ‖w ω‖ / absoluteMass w μ := div_nonneg (norm_nonneg _) hZ.le
    rw [phaseQuenchedDensity, ENNReal.toReal_ofReal hq]
    simp only [polarPhase, if_neg hw0]
    push_cast
    field_simp [hZ.ne', hn]

/-- Exact polar reconstruction of the total complex amplitude. -/
theorem integral_polar_reconstruction
    {w : Ω → ℂ} (hw : Integrable w μ) (hwmeas : Measurable w)
    (hZ : 0 < absoluteMass w μ) :
    ∫ ω, w ω ∂μ =
      (absoluteMass w μ : ℂ) *
        ∫ ω, polarPhase w ω ∂phaseQuenchedMeasure w μ := by
  rw [phaseQuenchedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_phaseQuenchedDensity hwmeas)
    (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) (polarPhase w)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    simpa [smul_eq_mul, mul_assoc] using
      (absoluteMass_mul_density_mul_phase w μ hZ ω).symm

/-- Average-phase visibility never exceeds one. -/
theorem amplitude_norm_le_absoluteMass
    {w : Ω → ℂ} (hw : Integrable w μ) :
    ‖∫ ω, w ω ∂μ‖ ≤ absoluteMass w μ := by
  simpa only [absoluteMass] using norm_integral_le_integral_norm w

theorem phaseVisibility_le_one
    {w : Ω → ℂ} (hw : Integrable w μ) (hZ : 0 < absoluteMass w μ) :
    ‖∫ ω, w ω ∂μ‖ / absoluteMass w μ ≤ 1 := by
  exact (div_le_one hZ).2 (amplitude_norm_le_absoluteMass hw)

/-- The exact cancellation debit for a coarse conditional phase density. -/
theorem cancellation_debit
    {S : Type*} [MeasurableSpace S] (π : Measure S) [IsProbabilityMeasure π]
    (a : S → ℂ) (ha : Integrable a π) (Zabs : ℝ) :
    Zabs - Zabs * absoluteMass a π =
      Zabs * ∫ s, (1 - ‖a s‖) ∂π := by
  rw [integral_sub (integrable_const 1) ha.norm]
  simp only [integral_const, absoluteMass]
  have hπ : π.real Set.univ = 1 := by simp
  rw [hπ]
  ring

/-- Taking total variation of the coarse complex measure gives precisely the
positive density `Zabs * |a|`. -/
theorem coarse_complex_variation
    {S : Type*} [MeasurableSpace S] (π : Measure S)
    (a : S → ℂ) (ha : Integrable a π) (Zabs : ℝ) (hZ : 0 ≤ Zabs) :
    (π.withDensityᵥ (fun s => (Zabs : ℂ) * a s)).variation =
      π.withDensity (fun s => ENNReal.ofReal (Zabs * ‖a s‖)) := by
  rw [Measure.variation_withDensityᵥ (ha.const_mul (Zabs : ℂ))]
  congr 1
  funext s
  simp only [enorm_eq_nnnorm, nnnorm_mul, Complex.nnnorm_real]
  rw [ENNReal.ofReal_mul hZ, ← Real.enorm_eq_ofReal hZ, ofReal_norm]
  norm_cast

/-- Under conditional Jensen's bound `|a| ≤ 1`, cancellation vanishes exactly
when the phase is aligned in almost every quotient fibre. -/
theorem cancellation_debit_eq_zero_iff_aligned
    {S : Type*} [MeasurableSpace S] (π : Measure S) [IsProbabilityMeasure π]
    (a : S → ℂ) (ha : Integrable a π) (Zabs : ℝ) (hZ : 0 < Zabs)
    (haone : ∀ᵐ s ∂π, ‖a s‖ ≤ 1) :
    Zabs * ∫ s, (1 - ‖a s‖) ∂π = 0 ↔
      ∀ᵐ s ∂π, ‖a s‖ = 1 := by
  have hnonneg : ∀ᵐ s ∂π, 0 ≤ 1 - ‖a s‖ :=
    haone.mono fun _ hs => sub_nonneg.mpr hs
  have hint : Integrable (fun s => 1 - ‖a s‖) π :=
    (integrable_const 1).sub ha.norm
  constructor
  · intro h
    have hzero : ∫ s, (1 - ‖a s‖) ∂π = 0 :=
      (mul_eq_zero.mp h).resolve_left hZ.ne'
    have hae : ∀ᵐ s ∂π, 1 - ‖a s‖ = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    exact hae.mono fun _ hs => by linarith
  · intro h
    have hae : (fun s => 1 - ‖a s‖) =ᵐ[π] 0 :=
      h.mono fun _ hs => by simp [hs]
    rw [integral_eq_zero_of_ae hae, mul_zero]

/-- Consolidated arbitrary-measure phase-quenched packet. -/
theorem phase_quenched_measure_packet
    {w : Ω → ℂ} (hw : Integrable w μ) (hwmeas : Measurable w)
    (hZ : 0 < absoluteMass w μ) :
    phaseQuenchedMeasure w μ Set.univ = 1 ∧
      (∀ᵐ ω ∂phaseQuenchedMeasure w μ, ‖polarPhase w ω‖ = 1) ∧
      (∫ ω, w ω ∂μ =
        (absoluteMass w μ : ℂ) *
          ∫ ω, polarPhase w ω ∂phaseQuenchedMeasure w μ) ∧
      ‖∫ ω, w ω ∂μ‖ / absoluteMass w μ ≤ 1 :=
  ⟨phaseQuenchedMeasure_univ hw hwmeas hZ,
    ae_norm_polarPhase_eq_one hwmeas hZ,
    integral_polar_reconstruction hw hwmeas hZ,
    phaseVisibility_le_one hw hZ⟩

end PhaseQuenchedMeasure
end NCG
