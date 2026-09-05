/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NaimarkPhaseSharpness
import NCG.Grand.TargetUnisolventCalibration

/-!
# Minimum-norm target-unisolvent calibration

The Moore--Penrose target decoder is the orthogonal acquired-range part of
every full extension.  Frobenius Pythagoras then proves its minimum-norm and
uniqueness properties.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace TargetUnisolventMinimumNorm

/-- Orthogonal projection on the acquired calibration-row space. -/
noncomputable def acquiredRangeProjection {d m : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (C * Cᴴ) * sourceGramPseudoinverse Cᴴ

/-- The acquired-row projection is Hermitian and idempotent. -/
theorem acquiredRangeProjection_isOrthogonalProjection {d m : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) :
    (acquiredRangeProjection C)ᴴ = acquiredRangeProjection C ∧
      acquiredRangeProjection C * acquiredRangeProjection C =
        acquiredRangeProjection C := by
  let X : Matrix (Fin m) (Fin m) ℂ := C * Cᴴ
  let J : Matrix (Fin m) (Fin m) ℂ := sourceGramPseudoinverse Cᴴ
  obtain ⟨hJH, hXJX, -, -, -, -⟩ := sourceGramPseudoinverse_projection Cᴴ
  change Jᴴ = J at hJH
  have hXJX' : X * J * X = X := by
    simpa only [X, J, Matrix.conjTranspose_conjTranspose] using hXJX
  have hXH : Xᴴ = X := by
    dsimp only [X]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hcomm : X * J = J * X := by
    simpa only [X, J, Matrix.conjTranspose_conjTranspose] using
      sourceGramPseudoinverse_commutes Cᴴ
  change (X * J)ᴴ = X * J ∧ (X * J) * (X * J) = X * J
  constructor
  · rw [Matrix.conjTranspose_mul, hJH, hXH, hcomm]
  · calc
      (X * J) * (X * J) = (X * J * X) * J := by
        simp only [Matrix.mul_assoc]
      _ = X * J := by rw [hXJX']

/-- Frobenius Pythagoras for right multiplication by an orthogonal
projection. -/
theorem hsFrobSq_right_projection_pythagoras
    {r m : Type*} [Fintype r] [Fintype m] [DecidableEq m]
    (A : Matrix r m ℂ) (P : Matrix m m ℂ)
    (hPH : Pᴴ = P) (hP2 : P * P = P) :
    hsFrobSq A = hsFrobSq (A * P) + hsFrobSq (A * (1 - P)) := by
  have hQH : (1 - P)ᴴ = (1 - P : Matrix m m ℂ) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = (1 - P : Matrix m m ℂ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hP2, sub_self, sub_zero]
  have hAP : hsFrobSq (A * P) =
      (Matrix.trace (P * (Aᴴ * A))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have heq : (A * P)ᴴ * (A * P) = (P * (Aᴴ * A)) * P := by
      rw [Matrix.conjTranspose_mul, hPH]
      simp only [Matrix.mul_assoc]
    rw [heq, Matrix.trace_mul_comm]
    congr 1
    rw [← Matrix.mul_assoc, hP2]
  have hAQ : hsFrobSq (A * (1 - P)) =
      (Matrix.trace ((1 - P) * (Aᴴ * A))).re := by
    rw [hsFrobSq_eq_re_trace]
    congr 1
    have heq : (A * (1 - P))ᴴ * (A * (1 - P)) =
        ((1 - P) * (Aᴴ * A)) * (1 - P) := by
      rw [Matrix.conjTranspose_mul, hQH]
      simp only [Matrix.mul_assoc]
    rw [heq, Matrix.trace_mul_comm]
    congr 1
    rw [← Matrix.mul_assoc, hQ2]
  rw [hAP, hAQ, hsFrobSq_eq_re_trace, ← Complex.add_re,
    ← Matrix.trace_add, ← Matrix.add_mul]
  congr 2
  rw [add_sub_cancel, Matrix.one_mul]

/-- Every full target extension projects to the canonical reduced decoder. -/
theorem extension_mul_acquiredRangeProjection {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (D : Matrix (Fin r) (Fin m) ℂ) (hDC : D * C = T) :
    D * acquiredRangeProjection C =
      TargetUnisolventCalibration.reducedDecoder C T := by
  unfold acquiredRangeProjection TargetUnisolventCalibration.reducedDecoder
  calc
    D * ((C * Cᴴ) * sourceGramPseudoinverse Cᴴ) =
        (D * C) * Cᴴ * sourceGramPseudoinverse Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = T * Cᴴ * sourceGramPseudoinverse Cᴴ := by rw [hDC]

/-- The Moore--Penrose decoder has no component perpendicular to the acquired
calibration-row range. -/
theorem reducedDecoder_mul_orthogonalComplement {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    TargetUnisolventCalibration.reducedDecoder C T *
        (1 - acquiredRangeProjection C) = 0 := by
  let X : Matrix (Fin m) (Fin m) ℂ := C * Cᴴ
  let J : Matrix (Fin m) (Fin m) ℂ := sourceGramPseudoinverse Cᴴ
  obtain ⟨-, -, hJXJ, -, -, -⟩ := sourceGramPseudoinverse_projection Cᴴ
  have hJXJ' : J * X * J = J := by
    simpa only [X, J, Matrix.conjTranspose_conjTranspose] using hJXJ
  unfold TargetUnisolventCalibration.reducedDecoder acquiredRangeProjection
  change (T * Cᴴ * J) * (1 - X * J) = 0
  rw [Matrix.mul_sub, Matrix.mul_one]
  have hfix : (T * Cᴴ * J) * (X * J) = T * Cᴴ * J := by
    calc
      (T * Cᴴ * J) * (X * J) = T * Cᴴ * (J * X * J) := by
        simp only [Matrix.mul_assoc]
      _ = T * Cᴴ * J := by rw [hJXJ']
  rw [hfix, sub_self]

/-- The canonical decoder is the minimum-Hilbert--Schmidt extension of the
target rows. -/
theorem reducedDecoder_hsFrobSq_le {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (D : Matrix (Fin r) (Fin m) ℂ) (hDC : D * C = T) :
    hsFrobSq (TargetUnisolventCalibration.reducedDecoder C T) ≤
      hsFrobSq D := by
  obtain ⟨hPH, hP2⟩ := acquiredRangeProjection_isOrthogonalProjection C
  have hsplit := hsFrobSq_right_projection_pythagoras
    D (acquiredRangeProjection C) hPH hP2
  rw [extension_mul_acquiredRangeProjection C T D hDC] at hsplit
  nlinarith [hsFrobSq_nonneg (D * (1 - acquiredRangeProjection C))]

/-- Equality in the minimum-norm inequality forces the extension to be the
canonical decoder. -/
theorem reducedDecoder_unique_minimum {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (D : Matrix (Fin r) (Fin m) ℂ) (hDC : D * C = T)
    (hmin : hsFrobSq D =
      hsFrobSq (TargetUnisolventCalibration.reducedDecoder C T)) :
    D = TargetUnisolventCalibration.reducedDecoder C T := by
  obtain ⟨hPH, hP2⟩ := acquiredRangeProjection_isOrthogonalProjection C
  have hsplit := hsFrobSq_right_projection_pythagoras
    D (acquiredRangeProjection C) hPH hP2
  rw [extension_mul_acquiredRangeProjection C T D hDC, hmin] at hsplit
  have hzero : hsFrobSq (D * (1 - acquiredRangeProjection C)) = 0 := by
    linarith
  have hperp : D * (1 - acquiredRangeProjection C) = 0 :=
    (hsFrobSq_eq_zero_iff _).mp hzero
  calc
    D = D * acquiredRangeProjection C +
        D * (1 - acquiredRangeProjection C) := by
      rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = TargetUnisolventCalibration.reducedDecoder C T := by
      rw [extension_mul_acquiredRangeProjection C T D hDC, hperp, add_zero]

/-- Complete minimum-Hilbert--Schmidt clause: the reduced decoder extends the
target bank on the unisolvent branch, is no larger than any extension, and is
the unique extension attaining its norm. -/
theorem target_unisolvent_minimum_hilbertSchmidt {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (hzero : TargetUnisolventCalibration.targetCalibrationResidual C T = 0) :
    TargetUnisolventCalibration.reducedDecoder C T * C = T ∧
      (∀ D : Matrix (Fin r) (Fin m) ℂ, D * C = T →
        hsFrobSq (TargetUnisolventCalibration.reducedDecoder C T) ≤ hsFrobSq D) ∧
      (∀ D : Matrix (Fin r) (Fin m) ℂ, D * C = T →
        hsFrobSq D = hsFrobSq
          (TargetUnisolventCalibration.reducedDecoder C T) →
        D = TargetUnisolventCalibration.reducedDecoder C T) := by
  exact ⟨TargetUnisolventCalibration.reducedDecoder_mul_calibration C T hzero,
    fun D hDC ↦ reducedDecoder_hsFrobSq_le C T D hDC,
    fun D hDC hmin ↦ reducedDecoder_unique_minimum C T D hDC hmin⟩

end TargetUnisolventMinimumNorm
end NCG
