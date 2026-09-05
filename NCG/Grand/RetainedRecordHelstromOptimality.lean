/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FreshEndpointRetainedRecord
import NCG.Upstream.PrimitiveWeight
import NCG.Grand.LockedPrivateProvenanceCompiler

/-!
# Helstrom optimality for the retained private record

The two concrete pure record states have difference `Δ` with
`Δ² = (24/25)I`.  Explicit positive/negative decompositions therefore give
its Hermitian trace norm exactly.  Trace-norm duality then proves the upper
bound for every binary measurement effect, while the sign effect attains it.
-/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace RetainedRecordHelstromOptimality

open Upstream.PrimitiveWeight
open LockedPrivateProvenanceCompiler

/-- Difference of the two private pure states written by the reset channel. -/
def recordDifference : Matrix (Fin 2) (Fin 2) ℂ :=
  privateRecordState hubR0 - privateRecordState hubR1

/-- Positive spectral radius of the record difference. -/
def recordRadius : ℝ := 2 * Real.sqrt 6 / 5

theorem recordRadius_pos : 0 < recordRadius := by
  unfold recordRadius
  positivity

theorem recordRadius_sq : recordRadius ^ 2 = (24 / 25 : ℝ) := by
  unfold recordRadius
  have hs : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith

theorem recordDifference_eq : recordDifference =
    !![(24 / 25 : ℂ), (-(2 * Real.sqrt 6 / 25) : ℝ);
       (-(2 * Real.sqrt 6 / 25) : ℝ), (-24 / 25 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [recordDifference, privateRecordState, Matrix.sub_apply,
      Matrix.vecMulVec_apply, Pi.star_apply]
  all_goals
    simp [hubR0, hubR1, Complex.star_def]
  all_goals
    norm_num [div_eq_mul_inv]
  all_goals
    apply Complex.ext <;> norm_num <;> ring_nf <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]

theorem recordDifference_hermitian : recordDifferenceᴴ = recordDifference := by
  rw [recordDifference_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.star_def]

theorem recordDifference_sq :
    recordDifference * recordDifference =
      ((24 / 25 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  rw [recordDifference_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  all_goals
    have hs : (Real.sqrt 6) ^ 2 = 6 := by norm_num
    norm_num [Complex.ext_iff]
    nlinarith

/-- Positive and negative parts obtained directly from `Δ²=a²I`. -/
def recordPositivePart : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (((recordRadius : ℝ) : ℂ) • 1 + recordDifference)

def recordNegativePart : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (((recordRadius : ℝ) : ℂ) • 1 - recordDifference)

theorem recordDifference_eq_parts :
    recordDifference = recordPositivePart - recordNegativePart := by
  unfold recordPositivePart recordNegativePart
  module

theorem recordPositivePart_hermitian :
    recordPositivePartᴴ = recordPositivePart := by
  rw [recordPositivePart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, recordDifference_hermitian]
  norm_num

theorem recordNegativePart_hermitian :
    recordNegativePartᴴ = recordNegativePart := by
  rw [recordNegativePart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, recordDifference_hermitian]
  norm_num

theorem recordPositivePart_posSemidef : recordPositivePart.PosSemidef := by
  apply (finTwo_posSemidef_iff_trace_det_nonneg
    recordPositivePart recordPositivePart_hermitian).2
  constructor
  · have ht : recordPositivePart.trace = (recordRadius : ℂ) := by
      rw [recordPositivePart, recordDifference_eq]
      simp [Matrix.trace_fin_two]
      ring
    rw [ht]
    exact_mod_cast recordRadius_pos.le
  · have hd : recordPositivePart.det = 0 := by
      rw [recordPositivePart, recordDifference_eq]
      simp [Matrix.det_fin_two, recordRadius]
      apply Complex.ext <;> norm_num
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    rw [hd]

theorem recordNegativePart_posSemidef : recordNegativePart.PosSemidef := by
  apply (finTwo_posSemidef_iff_trace_det_nonneg
    recordNegativePart recordNegativePart_hermitian).2
  constructor
  · have ht : recordNegativePart.trace = (recordRadius : ℂ) := by
      rw [recordNegativePart, recordDifference_eq]
      simp [Matrix.trace_fin_two]
      ring
    rw [ht]
    exact_mod_cast recordRadius_pos.le
  · have hd : recordNegativePart.det = 0 := by
      rw [recordNegativePart, recordDifference_eq]
      simp [Matrix.det_fin_two, recordRadius]
      apply Complex.ext <;> norm_num
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    rw [hd]

theorem recordParts_trace_sum :
    (recordPositivePart.trace).re + (recordNegativePart.trace).re =
      2 * recordRadius := by
  rw [recordPositivePart, recordNegativePart, recordDifference_eq]
  simp [Matrix.trace_fin_two]
  ring

/-- The concrete private-state difference has trace norm `4√6/5`. -/
theorem recordDifference_trNorm :
    trNorm recordDifference = 2 * recordRadius := by
  let hΔ : recordDifference.IsHermitian := recordDifference_hermitian
  have hupp := trNorm_le_of_sub hΔ recordPositivePart_posSemidef
    recordNegativePart_posSemidef recordDifference_eq_parts
  change trNorm recordDifference ≤
    recordPositivePart.trace.re + recordNegativePart.trace.re at hupp
  rw [recordParts_trace_sum] at hupp
  let C : Matrix (Fin 2) (Fin 2) ℂ :=
    (((recordRadius : ℝ) : ℂ)⁻¹) • recordDifference
  have hCminus : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - C).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) - C =
        ((2 * recordRadius⁻¹ : ℝ) : ℂ) • recordNegativePart := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [C, recordNegativePart]
        field_simp [recordRadius_pos.ne']
      · simp [C, recordNegativePart, Matrix.one_apply_ne hij]
        field_simp [recordRadius_pos.ne']
    rw [heq]
    apply recordNegativePart_posSemidef.smul
    constructor
    · change (0 : ℝ) ≤ 2 * recordRadius⁻¹
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr recordRadius_pos.le)
    · simp
  have hCplus : ((1 : Matrix (Fin 2) (Fin 2) ℂ) + C).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) + C =
        ((2 * recordRadius⁻¹ : ℝ) : ℂ) • recordPositivePart := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [C, recordPositivePart]
        field_simp [recordRadius_pos.ne']
      · simp [C, recordPositivePart, Matrix.one_apply_ne hij]
        field_simp [recordRadius_pos.ne']
    rw [heq]
    apply recordPositivePart_posSemidef.smul
    constructor
    · change (0 : ℝ) ≤ 2 * recordRadius⁻¹
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr recordRadius_pos.le)
    · simp
  have hlow := re_trace_mul_le_trNorm hΔ hCminus hCplus
  have hCX : C * recordDifference =
      ((recordRadius : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp [C]
    rw [Matrix.smul_mul, recordDifference_sq, smul_smul]
    norm_cast
    rw [← recordRadius_sq]
    field_simp [recordRadius_pos.ne']
  rw [hCX, Matrix.trace_smul, Matrix.trace_one] at hlow
  norm_num at hlow
  exact le_antisymm hupp (by simpa [mul_comm] using hlow)

/-- Equal-prior success probability of the binary effect `E`, with the second
outcome represented by `I-E`. -/
def binaryRecordSuccess (E : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1 / 2 : ℝ) *
    ((E * privateRecordState hubR0).trace.re +
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) - E) *
        privateRecordState hubR1).trace.re)

theorem privateRecordState_trace (r : Fin 2 → ℂ)
    (hr : star r ⬝ᵥ r = 1) : (privateRecordState r).trace = 1 := by
  rw [show (privateRecordState r).trace = star r ⬝ᵥ r by
    simp [privateRecordState, Matrix.trace, dotProduct,
      Matrix.vecMulVec_apply]
    ring]
  exact hr

/-- Success is one half plus one quarter of the state difference tested
against the `±1` observable associated with the effect. -/
theorem binaryRecordSuccess_eq (E : Matrix (Fin 2) (Fin 2) ℂ) :
    binaryRecordSuccess E = 1 / 2 + (1 / 4) *
      ((((2 : ℂ) • E - 1) * recordDifference).trace.re) := by
  unfold binaryRecordSuccess
  have htrace0 : (privateRecordState hubR0).trace = 1 :=
    privateRecordState_trace hubR0 retained_private_records_normalized.1
  have htrace1 : (privateRecordState hubR1).trace = 1 :=
    privateRecordState_trace hubR1 retained_private_records_normalized.2
  simp only [recordDifference, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, htrace0, htrace1]
  norm_num
  ring

/-- Every binary effect is bounded by the Helstrom value. -/
theorem binaryRecordSuccess_le
    (E : Matrix (Fin 2) (Fin 2) ℂ)
    (hE : E.PosSemidef)
    (hEc : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - E).PosSemidef) :
    binaryRecordSuccess E ≤ (5 + 2 * Real.sqrt 6) / 10 := by
  let C : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ) • E - 1
  have hCm : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - C).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) - C =
        ((2 : ℝ) : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - E) := by
      dsimp [C]
      module
    rw [heq]
    exact hEc.smul (by norm_num)
  have hCp : ((1 : Matrix (Fin 2) (Fin 2) ℂ) + C).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) + C =
        ((2 : ℝ) : ℂ) • E := by
      dsimp [C]
      module
    rw [heq]
    exact hE.smul (by norm_num)
  have hdual := re_trace_mul_le_trNorm
    (show recordDifference.IsHermitian from recordDifference_hermitian)
    hCm hCp
  rw [recordDifference_trNorm] at hdual
  change (C * recordDifference).trace.re ≤ 2 * recordRadius at hdual
  rw [binaryRecordSuccess_eq]
  change 1 / 2 + 1 / 4 * (C * recordDifference).trace.re ≤ _
  calc
    1 / 2 + 1 / 4 * (C * recordDifference).trace.re
        ≤ 1 / 2 + 1 / 4 * (2 * recordRadius) := by gcongr
    _ = (5 + 2 * Real.sqrt 6) / 10 := by
      unfold recordRadius
      ring

/-- The sign effect is a valid binary measurement and attains the bound. -/
def helstromEffect : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ •
    (1 + Upstream.PrimitiveWeight.signOp
      (show recordDifference.IsHermitian from recordDifference_hermitian))

theorem helstromEffect_valid :
    helstromEffect.PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - helstromEffect).PosSemidef := by
  constructor
  · have h := one_add_signOp_posSemidef
      (show recordDifference.IsHermitian from recordDifference_hermitian)
    have heq : helstromEffect = ((1 / 2 : ℝ) : ℂ) •
        (1 + Upstream.PrimitiveWeight.signOp
          (show recordDifference.IsHermitian from
            recordDifference_hermitian)) := by
      unfold helstromEffect
      norm_num
    rw [heq]
    exact h.smul (by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  · have h := one_sub_signOp_posSemidef
      (show recordDifference.IsHermitian from recordDifference_hermitian)
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) - helstromEffect =
        ((1 / 2 : ℝ) : ℂ) •
          (1 - Upstream.PrimitiveWeight.signOp
            (show recordDifference.IsHermitian from
              recordDifference_hermitian)) := by
      unfold helstromEffect
      norm_num
      module
    rw [heq]
    exact h.smul (by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))

theorem helstromEffect_success :
    binaryRecordSuccess helstromEffect =
      (5 + 2 * Real.sqrt 6) / 10 := by
  rw [binaryRecordSuccess_eq]
  let hΔ : recordDifference.IsHermitian := recordDifference_hermitian
  have hattain := re_trace_signOp_mul hΔ
  rw [recordDifference_trNorm] at hattain
  change (Upstream.PrimitiveWeight.signOp hΔ *
    recordDifference).trace.re = 2 * recordRadius at hattain
  have hobs : (2 : ℂ) • helstromEffect - 1 =
      Upstream.PrimitiveWeight.signOp hΔ := by
    unfold helstromEffect
    module
  rw [hobs]
  change 1 / 2 + 1 / 4 *
    (Upstream.PrimitiveWeight.signOp hΔ * recordDifference).trace.re = _
  rw [hattain]
  unfold recordRadius
  ring

/-- The manuscript's number is the actual optimum over all binary effects. -/
theorem retained_private_record_helstrom_optimal :
    (∀ E : Matrix (Fin 2) (Fin 2) ℂ,
      E.PosSemidef →
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - E).PosSemidef →
      binaryRecordSuccess E ≤ (5 + 2 * Real.sqrt 6) / 10)
    ∧ ∃ E : Matrix (Fin 2) (Fin 2) ℂ,
      E.PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - E).PosSemidef ∧
      binaryRecordSuccess E = (5 + 2 * Real.sqrt 6) / 10 := by
  exact ⟨binaryRecordSuccess_le,
    ⟨helstromEffect, helstromEffect_valid.1,
      helstromEffect_valid.2, helstromEffect_success⟩⟩

end RetainedRecordHelstromOptimality
end NCG
