/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TrineMatrixCarrierExact
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Complex vector measure reconstructed from three positive trine outcomes

This is the literal measure-theoretic Fourier layer of
`thm:GT-trine-complex-measure`.  Three arbitrary finite positive measures are
combined with the cubic phases into an honest complex vector measure.  Its
Radon--Nikodym density with respect to their carrier is the Fourier transform
of the three real RN densities, and the scalar trine formulas reconstruct the
complex coordinate `x + i y` exactly.
-/

open Finset Filter Set
open scoped ComplexConjugate ENNReal MeasureTheory

namespace NCG
namespace TrineComplexVectorMeasure

open MeasureTheory
open PositiveCylinderAndTrine
open TrineMeasureAcquisition

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The three phases `exp (-2 π i k / 3)`, written algebraically. -/
noncomputable def trineFourierPhase : Fin 3 → ℂ
  | 0 => 1
  | 1 => -(1 : ℂ) / 2 - Complex.I * (Real.sqrt 3 / 2)
  | 2 => -(1 : ℂ) / 2 + Complex.I * (Real.sqrt 3 / 2)

@[simp] theorem trineFourierPhase_zero : trineFourierPhase 0 = 1 := rfl

@[simp] theorem trineFourierPhase_one :
    trineFourierPhase 1 = -(1 : ℂ) / 2 - Complex.I * (Real.sqrt 3 / 2) := rfl

@[simp] theorem trineFourierPhase_two :
    trineFourierPhase 2 = -(1 : ℂ) / 2 + Complex.I * (Real.sqrt 3 / 2) := rfl

/-- Every cubic Fourier coefficient is unimodular. -/
theorem norm_trineFourierPhase (k : Fin 3) : ‖trineFourierPhase k‖ = 1 := by
  fin_cases k
  · simp
  · rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
      Complex.sq_norm, Complex.normSq_apply]
    simp [trineFourierPhase]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
      Complex.sq_norm, Complex.normSq_apply]
    simp [trineFourierPhase]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- Exact three-point Fourier reconstruction of the complex coordinate. -/
theorem trineFourier_reconstruct (t x y : ℝ) :
    ∑ k : Fin 3, trineFourierPhase k * (trineOutcome t x y k : ℂ) =
      (x : ℂ) + Complex.I * y := by
  rw [Fin.sum_univ_three]
  apply Complex.ext
  · simp [trineFourierPhase, trineOutcome]
    ring
  · simp [trineFourierPhase, trineOutcome]
    have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [congrArg (fun z : ℝ => z * y) hsqrt]

/-- Fourier transform of the three real RN densities. -/
noncomputable def trineComplexRNDensity (ρ : Fin 3 → Measure Ω) (ω : Ω) : ℂ :=
  ∑ k, trineFourierPhase k * (trineRNDensity ρ k ω : ℂ)

/-- Intrinsic complex vector measure `ζ = ∑ₖ exp(-2πik/3) ρₖ`. -/
noncomputable def trineComplexMeasure (ρ : Fin 3 → Measure Ω) : VectorMeasure Ω ℂ :=
  ∑ k, (ρ k).withDensityᵥ (fun _ => trineFourierPhase k)

/-- The Fourier RN density is integrable with respect to the finite carrier. -/
theorem integrable_trineComplexRNDensity
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    Integrable (trineComplexRNDensity ρ) (trineCarrierMeasure ρ) := by
  unfold trineComplexRNDensity trineRNDensity
  apply integrable_finsetSum
  intro k _
  exact ((Measure.integrable_toReal_rnDeriv
    (μ := ρ k) (ν := trineCarrierMeasure ρ))).ofReal.const_mul
      (trineFourierPhase k)

/-- The intrinsic complex measure has exactly the Fourier RN density with
respect to the carrier. -/
theorem withDensity_trineComplexRNDensity_eq
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    (trineCarrierMeasure ρ).withDensityᵥ (trineComplexRNDensity ρ) =
      trineComplexMeasure ρ := by
  letI : IsFiniteMeasure (trineCarrierMeasure ρ) := by
    unfold trineCarrierMeasure
    infer_instance
  ext s hs
  rw [MeasureTheory.withDensityᵥ_apply
    (integrable_trineComplexRNDensity ρ) hs]
  simp only [trineComplexRNDensity]
  rw [integral_finsetSum Finset.univ (by
    intro k _
    exact (((Measure.integrable_toReal_rnDeriv
      (μ := ρ k) (ν := trineCarrierMeasure ρ))).ofReal.const_mul
        (trineFourierPhase k)).integrableOn)]
  change (∑ k, ∫ x in s,
      trineFourierPhase k * (trineRNDensity ρ k x : ℂ) ∂trineCarrierMeasure ρ) =
    ∑ k, (ρ k).withDensityᵥ (fun _ => trineFourierPhase k) s
  apply Finset.sum_congr rfl
  intro k _
  unfold trineRNDensity
  rw [MeasureTheory.withDensityᵥ_apply
      (μ := ρ k) (f := fun _ => trineFourierPhase k)
      (integrable_const (c := trineFourierPhase k)) hs,
    MeasureTheory.integral_const_mul, integral_complex_ofReal,
    Measure.setIntegral_toReal_rnDeriv
      (Measure.absolutelyContinuous_of_le (outcomeMeasure_le_trineCarrier ρ k)) s]
  simp [Measure.real, mul_comm]

/-- On a trine density, the Fourier RN derivative is precisely `x + i y`. -/
theorem trineComplexRNDensity_of_outcomes (t x y : Ω → ℝ) (ω : Ω) :
    (∑ k : Fin 3,
      trineFourierPhase k * (trineOutcome (t ω) (x ω) (y ω) k : ℂ)) =
        (x ω : ℂ) + Complex.I * y ω :=
  trineFourier_reconstruct (t ω) (x ω) (y ω)

/-- The carrier RN densities satisfy the manuscript's exact quadratic Fourier
identity almost everywhere. -/
theorem ae_rn_quadratic_fourier_identity
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    ∀ᵐ ω ∂trineCarrierMeasure ρ,
      ∑ k, trineRNDensity ρ k ω ^ 2 =
        1 / 3 + 2 / 3 * ‖trineComplexRNDensity ρ ω‖ ^ 2 := by
  filter_upwards [ae_sum_trineRNDensity_eq_one ρ] with ω hsum
  let r0 := trineRNDensity ρ 0 ω
  let r1 := trineRNDensity ρ 1 ω
  let r2 := trineRNDensity ρ 2 ω
  have hsum' : r0 + r1 + r2 = 1 := by
    simpa [r0, r1, r2, Fin.sum_univ_three] using hsum
  simp only [trineComplexRNDensity, Fin.sum_univ_three]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [trineFourierPhase, r0, r1, r2] at *
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsqrt]
  nlinarith

/-- The manuscript quadratic RN test is exactly the half-unit disk condition
for the complex Fourier density. -/
theorem ae_rn_quadratic_iff_complex_bound
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    (∀ᵐ ω ∂trineCarrierMeasure ρ,
      ∑ k, trineRNDensity ρ k ω ^ 2 ≤ 1 / 2) ↔
    (∀ᵐ ω ∂trineCarrierMeasure ρ,
      2 * ‖trineComplexRNDensity ρ ω‖ ≤ 1) := by
  have hid := ae_rn_quadratic_fourier_identity ρ
  constructor
  · intro h
    filter_upwards [hid, h] with ω hidω hω
    have hn := norm_nonneg (trineComplexRNDensity ρ ω)
    nlinarith [sq_nonneg (2 * ‖trineComplexRNDensity ρ ω‖ - 1)]
  · intro h
    filter_upwards [hid, h] with ω hidω hω
    have hn := norm_nonneg (trineComplexRNDensity ρ ω)
    nlinarith [sq_nonneg (2 * ‖trineComplexRNDensity ρ ω‖ - 1)]

/-- The Fourier RN density is measurable. -/
theorem measurable_trineComplexRNDensity (ρ : Fin 3 → Measure Ω) :
    Measurable (trineComplexRNDensity ρ) := by
  unfold trineComplexRNDensity trineRNDensity
  fun_prop

/-- A measurable density produces a submeasure of its carrier exactly when
the density is at most one almost everywhere. -/
theorem withDensity_le_self_iff
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    μ.withDensity f ≤ μ ↔ f ≤ᵐ[μ] 1 := by
  constructor
  · intro hle
    have hrn := Measure.rnDeriv_le_one_of_le hle
    have heq := Measure.rnDeriv_withDensity μ hf
    filter_upwards [hrn, heq] with ω hω heqω
    simpa [heqω] using hω
  · intro h
    simpa only [MeasureTheory.withDensity_one] using
      (MeasureTheory.withDensity_mono (μ := μ) h)

/-- Literal measure form of `2 |ζ| ≤ τ`, using vector-measure variation for
the absolute value of the complex measure. -/
def TrineComplexMeasureDominated (ρ : Fin 3 → Measure Ω) : Prop :=
  (2 : ℝ≥0∞) • (trineComplexMeasure ρ).variation ≤ trineCarrierMeasure ρ

/-- The literal variation-measure domination is equivalent to the pointwise
RN disk bound. -/
theorem complex_measure_dominated_iff_ae_enorm_bound
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    TrineComplexMeasureDominated ρ ↔
      ∀ᵐ ω ∂trineCarrierMeasure ρ,
        (2 : ℝ≥0∞) * ‖trineComplexRNDensity ρ ω‖ₑ ≤ 1 := by
  letI : IsFiniteMeasure (trineCarrierMeasure ρ) := by
    unfold trineCarrierMeasure
    infer_instance
  unfold TrineComplexMeasureDominated
  rw [← withDensity_trineComplexRNDensity_eq ρ,
    Measure.variation_withDensityᵥ (integrable_trineComplexRNDensity ρ),
    ← MeasureTheory.withDensity_smul' (μ := trineCarrierMeasure ρ)
      (2 : ℝ≥0∞) (fun ω => ‖trineComplexRNDensity ρ ω‖ₑ) (by norm_num)]
  exact withDensity_le_self_iff (trineCarrierMeasure ρ)
    (fun ω => (2 : ℝ≥0∞) • ‖trineComplexRNDensity ρ ω‖ₑ)
    (by
      change Measurable
        ((fun _ : Ω => (2 : ℝ≥0∞)) * fun ω => ‖trineComplexRNDensity ρ ω‖ₑ)
      exact measurable_const.mul (measurable_trineComplexRNDensity ρ).enorm)

/-- The half-unit norm bound has the same content in `ℝ≥0∞` and `ℝ`. -/
theorem two_mul_enorm_le_one_iff (z : ℂ) :
    (2 : ℝ≥0∞) * ‖z‖ₑ ≤ 1 ↔ (2 : ℝ) * ‖z‖ ≤ 1 := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by norm_num)]
  simp [ENNReal.toReal_mul, toReal_enorm]

/-- Exact equivalence between the manuscript's measure inequality and its RN
quadratic criterion. -/
theorem complex_measure_dominated_iff_rn_quadratic
    (ρ : Fin 3 → Measure Ω) [∀ k, IsFiniteMeasure (ρ k)] :
    TrineComplexMeasureDominated ρ ↔
      ∀ᵐ ω ∂trineCarrierMeasure ρ,
        ∑ k, trineRNDensity ρ k ω ^ 2 ≤ 1 / 2 := by
  rw [complex_measure_dominated_iff_ae_enorm_bound,
    ae_rn_quadratic_iff_complex_bound]
  constructor <;> intro h
  · filter_upwards [h] with ω hω
    exact (two_mul_enorm_le_one_iff _).mp hω
  · filter_upwards [h] with ω hω
    exact (two_mul_enorm_le_one_iff _).mpr hω

end TrineComplexVectorMeasure
end NCG
