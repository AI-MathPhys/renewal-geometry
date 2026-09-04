/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# The weighted L² carrier of a nonvanishing vacuum

The vacuum measure is the actual density `|Omega|² dμ`. Multiplication by
`Omega` preserves the L² norm; division by a vacuum that is nonzero almost
everywhere gives the inverse. These facts are the measure-theoretic content
needed to transport cyclicity to the physical vacuum representation.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG.PositiveVacuumWeightedL2

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (Omega : X → ℂ)

def vacuumMeasure : Measure X := μ.withDensity (fun x => ‖Omega x‖ₑ ^ 2)

theorem vacuumMeasure_absolutelyContinuous : vacuumMeasure μ Omega ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_vacuumMeasure (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) : μ ≪ vacuumMeasure μ Omega := by
  apply withDensity_absolutelyContinuous' (hOmega.enorm.pow_const 2).aemeasurable
  filter_upwards [hnonzero] with x hx
  simpa using hx

/-- The squared vacuum density converts the weighted norm into the physical
norm of the product. This is an exact norm identity, not a supplied isometry. -/
theorem eLpNorm_vacuum_mul (hOmega : Measurable Omega) {f : X → ℂ}
    (hf : AEStronglyMeasurable f (vacuumMeasure μ Omega)) :
    eLpNorm (fun x => Omega x * f x) 2 μ = eLpNorm f 2 (vacuumMeasure μ Omega) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  congr 1
  rw [vacuumMeasure, lintegral_withDensity_eq_lintegral_mul₀'
    (hOmega.enorm.pow_const 2).aemeasurable (hf.enorm.pow_const 2)]
  congr 1
  funext x
  simp [Pi.mul_apply, enorm_mul, mul_pow]

theorem memLp_vacuum_mul (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) {f : X → ℂ}
    (hf : MemLp f 2 (vacuumMeasure μ Omega)) :
    MemLp (fun x => Omega x * f x) 2 μ := by
  refine ⟨hOmega.aestronglyMeasurable.mul
    (hf.1.mono_ac (absolutelyContinuous_vacuumMeasure μ Omega hOmega hnonzero)), ?_⟩
  rw [eLpNorm_vacuum_mul μ Omega hOmega hf.1]
  exact hf.2

/-- Division by the nonvanishing vacuum is square integrable for the weighted
measure, for every physical square-integrable vector. -/
theorem memLp_div_vacuum (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) {f : X → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x => f x / Omega x) 2 (vacuumMeasure μ Omega) := by
  have hm : AEStronglyMeasurable (fun x => f x / Omega x) (vacuumMeasure μ Omega) :=
    (hf.1.mul hOmega.inv.aestronglyMeasurable).mono_ac
      (vacuumMeasure_absolutelyContinuous μ Omega)
  refine ⟨hm, ?_⟩
  rw [← eLpNorm_vacuum_mul μ Omega hOmega hm]
  have heq : (fun x => Omega x * (f x / Omega x)) =ᵐ[μ] f := by
    filter_upwards [hnonzero] with x hx
    exact mul_div_cancel₀ (f x) hx
  rw [eLpNorm_congr_ae heq]
  exact hf.2

/-- Multiplication by the vacuum as a map of actual L² equivalence classes. -/
def vacuumMul (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0)
    (f : Lp ℂ 2 (vacuumMeasure μ Omega)) : Lp ℂ 2 μ :=
  (memLp_vacuum_mul μ Omega hOmega hnonzero (Lp.memLp f)).toLp
    (fun x => Omega x * f x)

theorem vacuumMul_ae (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0)
    (f : Lp ℂ 2 (vacuumMeasure μ Omega)) :
    vacuumMul μ Omega hOmega hnonzero f =ᵐ[μ] (fun x => Omega x * f x) :=
  MemLp.coeFn_toLp _

/-- The inverse division map on actual L² equivalence classes. -/
def vacuumDiv (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) (f : Lp ℂ 2 μ) :
    Lp ℂ 2 (vacuumMeasure μ Omega) :=
  (memLp_div_vacuum μ Omega hOmega hnonzero (Lp.memLp f)).toLp
    (fun x => f x / Omega x)

theorem vacuumDiv_ae (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) (f : Lp ℂ 2 μ) :
    vacuumDiv μ Omega hOmega hnonzero f =ᵐ[vacuumMeasure μ Omega]
      (fun x => f x / Omega x) := MemLp.coeFn_toLp _

theorem vacuumMul_add (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0)
    (f g : Lp ℂ 2 (vacuumMeasure μ Omega)) :
    vacuumMul μ Omega hOmega hnonzero (f + g) =
      vacuumMul μ Omega hOmega hnonzero f + vacuumMul μ Omega hOmega hnonzero g := by
  apply Lp.ext
  filter_upwards [vacuumMul_ae μ Omega hOmega hnonzero (f + g),
    (absolutelyContinuous_vacuumMeasure μ Omega hOmega hnonzero).ae_eq (Lp.coeFn_add f g),
    Lp.coeFn_add (vacuumMul μ Omega hOmega hnonzero f) (vacuumMul μ Omega hOmega hnonzero g),
    vacuumMul_ae μ Omega hOmega hnonzero f, vacuumMul_ae μ Omega hOmega hnonzero g]
    with x hfg hsum hout hf hg
  simp only [Pi.add_apply] at hsum hout
  rw [hfg, hsum, hout, hf, hg, mul_add]

theorem vacuumMul_smul (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0)
    (c : ℂ) (f : Lp ℂ 2 (vacuumMeasure μ Omega)) :
    vacuumMul μ Omega hOmega hnonzero (c • f) = c • vacuumMul μ Omega hOmega hnonzero f := by
  apply Lp.ext
  filter_upwards [vacuumMul_ae μ Omega hOmega hnonzero (c • f),
    (absolutelyContinuous_vacuumMeasure μ Omega hOmega hnonzero).ae_eq (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (vacuumMul μ Omega hOmega hnonzero f),
    vacuumMul_ae μ Omega hOmega hnonzero f] with x hcf hsmul hout hf
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul hout
  rw [hcf, hsmul, hout, hf]
  ring

theorem vacuumMul_norm (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) (f : Lp ℂ 2 (vacuumMeasure μ Omega)) :
    ‖vacuumMul μ Omega hOmega hnonzero f‖ = ‖f‖ := by
  rw [vacuumMul, Lp.norm_toLp,
    eLpNorm_vacuum_mul μ Omega hOmega (Lp.memLp f).1, Lp.norm_def]

theorem vacuumDiv_vacuumMul (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) (f : Lp ℂ 2 (vacuumMeasure μ Omega)) :
    vacuumDiv μ Omega hOmega hnonzero (vacuumMul μ Omega hOmega hnonzero f) = f := by
  apply Lp.ext
  filter_upwards [vacuumDiv_ae μ Omega hOmega hnonzero (vacuumMul μ Omega hOmega hnonzero f),
    (vacuumMeasure_absolutelyContinuous μ Omega).ae_eq (vacuumMul_ae μ Omega hOmega hnonzero f),
    (vacuumMeasure_absolutelyContinuous μ Omega).ae_le hnonzero] with x hdiv hmul hx
  rw [hdiv, hmul]
  field_simp [hx]

theorem vacuumMul_vacuumDiv (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) (f : Lp ℂ 2 μ) :
    vacuumMul μ Omega hOmega hnonzero (vacuumDiv μ Omega hOmega hnonzero f) = f := by
  apply Lp.ext
  filter_upwards [vacuumMul_ae μ Omega hOmega hnonzero (vacuumDiv μ Omega hOmega hnonzero f),
    (absolutelyContinuous_vacuumMeasure μ Omega hOmega hnonzero).ae_eq
      (vacuumDiv_ae μ Omega hOmega hnonzero f), hnonzero] with x hmul hdiv hx
  rw [hmul, hdiv]
  exact mul_div_cancel₀ (f x) hx

/-- The physical vacuum unitary, constructed from multiplication and division
by the measurable almost-everywhere nonvanishing vacuum. -/
def vacuumUnitary (hOmega : Measurable Omega)
    (hnonzero : ∀ᵐ x ∂μ, Omega x ≠ 0) :
    Lp ℂ 2 (vacuumMeasure μ Omega) ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := vacuumMul μ Omega hOmega hnonzero
  invFun := vacuumDiv μ Omega hOmega hnonzero
  left_inv := vacuumDiv_vacuumMul μ Omega hOmega hnonzero
  right_inv := vacuumMul_vacuumDiv μ Omega hOmega hnonzero
  map_add' := vacuumMul_add μ Omega hOmega hnonzero
  map_smul' := vacuumMul_smul μ Omega hOmega hnonzero
  norm_map' := vacuumMul_norm μ Omega hOmega hnonzero

end

end NCG.PositiveVacuumWeightedL2
