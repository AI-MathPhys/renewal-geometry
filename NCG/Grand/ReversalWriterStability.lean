/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LockedSignReversal
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Quantitative stability of the calibrated reversal writer

This module proves the perturbation clause of `thm:SMST-reversal-writer`.
The reversal-even and calibration residuals determine the two coordinate
errors explicitly.  Mathlib's product operator norm is the maximum of the two
coordinate norms, giving the manuscript estimate (in fact with the slightly
stronger calibration coefficient `1 / (2t)`).
-/

namespace NCG

variable {E Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Positive and negative coordinate maps of a writer. -/
def reversalWriterPlus (J : E →L[ℝ] E × E) : E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp J

def reversalWriterMinus (J : E →L[ℝ] E × E) : E →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ E E).comp J

/-- Reversal-even residual `J₊ + J₋`.  Its norm equals the norm of the full
residual `S J + J` for the max norm on `E × E`. -/
def reversalWriterOddResidual (J : E →L[ℝ] E × E) : E →L[ℝ] E :=
  reversalWriterPlus J + reversalWriterMinus J

/-- Half-step calibration residual `t(J₊-J₋)-I`. -/
def reversalWriterCalibrationResidual (t : ℝ)
    (J : E →L[ℝ] E × E) : E →L[ℝ] E :=
  t • (reversalWriterPlus J - reversalWriterMinus J)
    - ContinuousLinearMap.id ℝ E

/-- Canonical calibrated reversal writer. -/
noncomputable def calibratedReversalWriter (t : ℝ) : E →L[ℝ] E × E :=
  ((1 / (2 * t)) • ContinuousLinearMap.id ℝ E).prod
    (-((1 / (2 * t)) • ContinuousLinearMap.id ℝ E))

/-- Swapping and adding a writer has exactly the norm of its common
reversal-even coordinate. -/
theorem swap_add_writer_norm (J : E →L[ℝ] E × E) :
    ‖((reversalWriterMinus J + reversalWriterPlus J).prod
        (reversalWriterPlus J + reversalWriterMinus J))‖
      = ‖reversalWriterOddResidual J‖ := by
  rw [ContinuousLinearMap.opNorm_prod]
  simp [reversalWriterOddResidual, add_comm, Prod.norm_def]

/-- The writer is controlled by its reversal and calibration residuals.  This
is the quantitative heart of the manuscript estimate. -/
theorem calibratedReversalWriter_distance
    (t : ℝ) (ht : 0 < t) (J : E →L[ℝ] E × E) :
    ‖J - calibratedReversalWriter t‖
      ≤ ‖reversalWriterOddResidual J‖ / 2
        + ‖reversalWriterCalibrationResidual t J‖ / (2 * t) := by
  let jp := reversalWriterPlus J
  let jm := reversalWriterMinus J
  let s := reversalWriterOddResidual J
  let c := reversalWriterCalibrationResidual t J
  let α : ℝ := 1 / (2 * t)
  have htne : t ≠ 0 := ne_of_gt ht
  have htinv : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  have hcoefmul : (t⁻¹ * (2 : ℝ)⁻¹) * t = (2 : ℝ)⁻¹ := by
    field_simp [htne]
  have hJ : J = jp.prod jm := by
    ext x <;> rfl
  have hcan : calibratedReversalWriter t
      = (α • ContinuousLinearMap.id ℝ E).prod
          (-(α • ContinuousLinearMap.id ℝ E)) := by
    rfl
  have hplus : jp - α • ContinuousLinearMap.id ℝ E
      = (1 / 2 : ℝ) • s + (1 / (2 * t)) • c := by
    ext x
    simp [jp, jm, s, c, α, reversalWriterOddResidual,
      reversalWriterCalibrationResidual, reversalWriterPlus,
      reversalWriterMinus, htinv]
    rw [smul_sub, smul_smul, hcoefmul]
    module
  have hminus : jm - (-(α • ContinuousLinearMap.id ℝ E))
      = (1 / 2 : ℝ) • s - (1 / (2 * t)) • c := by
    ext x
    simp [jp, jm, s, c, α, reversalWriterOddResidual,
      reversalWriterCalibrationResidual, reversalWriterPlus,
      reversalWriterMinus, htinv]
    rw [smul_sub, smul_smul, hcoefmul]
    module
  have hcoef : 0 ≤ (1 / (2 * t) : ℝ) := by positivity
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hp : ‖jp - α • ContinuousLinearMap.id ℝ E‖
      ≤ ‖s‖ / 2 + ‖c‖ / (2 * t) := by
    rw [hplus]
    calc
      ‖(1 / 2 : ℝ) • s + (1 / (2 * t)) • c‖
          ≤ ‖(1 / 2 : ℝ) • s‖ + ‖(1 / (2 * t)) • c‖ := norm_add_le _ _
      _ = ‖s‖ / 2 + ‖c‖ / (2 * t) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hhalf, abs_of_nonneg hcoef]
        ring
  have hm : ‖jm - (-(α • ContinuousLinearMap.id ℝ E))‖
      ≤ ‖s‖ / 2 + ‖c‖ / (2 * t) := by
    rw [hminus]
    calc
      ‖(1 / 2 : ℝ) • s - (1 / (2 * t)) • c‖
          ≤ ‖(1 / 2 : ℝ) • s‖ + ‖(1 / (2 * t)) • c‖ := norm_sub_le _ _
      _ = ‖s‖ / 2 + ‖c‖ / (2 * t) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hhalf, abs_of_nonneg hcoef]
        ring
  rw [hJ, hcan]
  change ‖(jp - α • ContinuousLinearMap.id ℝ E).prod
      (jm - (-(α • ContinuousLinearMap.id ℝ E)))‖ ≤ _
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le hp hm

/-- Source-level perturbation bound with the manuscript's explicit constant. -/
theorem reversalWriter_source_stability
    (t : ℝ) (ht : 0 < t)
    (J : E →L[ℝ] E × E) (B : E × E →L[ℝ] Y) :
    ‖B.comp J - B.comp (calibratedReversalWriter t)‖
      ≤ ‖B‖ *
        (‖reversalWriterOddResidual J‖ / 2
          + ‖reversalWriterCalibrationResidual t J‖ /
              (Real.sqrt 2 * t)) := by
  let d := J - calibratedReversalWriter t
  have hd : ‖d‖ ≤ ‖reversalWriterOddResidual J‖ / 2
      + ‖reversalWriterCalibrationResidual t J‖ / (2 * t) :=
    calibratedReversalWriter_distance t ht J
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcalnonneg : 0 ≤ ‖reversalWriterCalibrationResidual t J‖ := norm_nonneg _
  have hden : ‖reversalWriterCalibrationResidual t J‖ / (2 * t)
      ≤ ‖reversalWriterCalibrationResidual t J‖ / (Real.sqrt 2 * t) := by
    apply div_le_div_of_nonneg_left hcalnonneg
    · positivity
    · nlinarith
  have hd' : ‖d‖ ≤ ‖reversalWriterOddResidual J‖ / 2
      + ‖reversalWriterCalibrationResidual t J‖ / (Real.sqrt 2 * t) :=
    hd.trans (add_le_add (le_refl _) hden)
  have hcomp : B.comp J - B.comp (calibratedReversalWriter t) = B.comp d := by
    ext x
    simp [d]
  rw [hcomp]
  refine (B.comp d).opNorm_le_bound (mul_nonneg (norm_nonneg _) ?_) ?_
  · exact add_nonneg (div_nonneg (norm_nonneg _) (by norm_num))
      (div_nonneg (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ht.le))
  · intro x
    calc
      ‖B (d x)‖ ≤ ‖B‖ * ‖d x‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (‖d‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (d.le_opNorm x) (norm_nonneg _)
      _ ≤ ‖B‖ *
          ((‖reversalWriterOddResidual J‖ / 2
            + ‖reversalWriterCalibrationResidual t J‖ /
                (Real.sqrt 2 * t)) * ‖x‖) := by
            gcongr
      _ = (‖B‖ *
          (‖reversalWriterOddResidual J‖ / 2
            + ‖reversalWriterCalibrationResidual t J‖ /
                (Real.sqrt 2 * t))) * ‖x‖ := by ring

/-- Exact completion bundle for the calibrated reversal writer. -/
theorem smst_reversal_writer_stability_exact
    (t : ℝ) (ht : 0 < t)
    (J : E →L[ℝ] E × E) (B : E × E →L[ℝ] Y) :
    ‖B.comp J - B.comp (calibratedReversalWriter t)‖
      ≤ ‖B‖ *
        (‖reversalWriterOddResidual J‖ / 2
          + ‖reversalWriterCalibrationResidual t J‖ /
              (Real.sqrt 2 * t)) :=
  reversalWriter_source_stability t ht J B

end NCG
