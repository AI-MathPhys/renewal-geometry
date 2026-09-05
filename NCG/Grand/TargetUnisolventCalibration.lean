/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Target-unisolvent finite calibration

The target-calibration theorem is the row-space dual of the exact source Schur
theorem.  This file records the residual, its zero/factorization criterion, the
canonical reduced decoder and the unresolved-rank identity.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace TargetUnisolventCalibration

/-- Positive target-calibration residual `T (I-C†C) T*`. -/
noncomputable def targetCalibrationResidual {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  sourceSchurResidual Cᴴ Tᴴ

/-- Every target row is determined by the acquired calibration rows. -/
def TargetRowsDetermined {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) : Prop :=
  ∃ D : Matrix (Fin r) (Fin m) ℂ, T = D * C

/-- `thm:GT-target-unisolvent-calibration`, equivalence of (i) and (iii). -/
theorem residual_eq_zero_iff_targetRowsDetermined {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    targetCalibrationResidual C T = 0 ↔ TargetRowsDetermined C T := by
  rw [targetCalibrationResidual,
    sourceSchurResidual_eq_zero_iff_rangeIncluded]
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨Dᴴ, ?_⟩
    have := congrArg Matrix.conjTranspose hD
    simpa [Matrix.conjTranspose_mul] using this
  · rintro ⟨D, rfl⟩
    refine ⟨Dᴴ, ?_⟩
    simp [Matrix.conjTranspose_mul]

/-- Row determination is exactly the kernel criterion from clause (ii). -/
theorem targetRowsDetermined_iff_kernel {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    TargetRowsDetermined C T ↔
      ∀ x : Fin d → ℂ, C *ᵥ x = 0 → T *ᵥ x = 0 := by
  constructor
  · rintro ⟨D, rfl⟩ x hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  · intro hker
    have hlinear : LinearMap.ker C.mulVecLin ≤ LinearMap.ker T.mulVecLin := by
      intro x hx
      exact hker x hx
    let Q := LinearMap.ker C.mulVecLin
    let Tq : ((Fin d → ℂ) ⧸ Q) →ₗ[ℂ] (Fin r → ℂ) :=
      Q.liftQ T.mulVecLin hlinear
    let Dlin : LinearMap.range C.mulVecLin →ₗ[ℂ] (Fin r → ℂ) :=
      Tq.comp C.mulVecLin.quotKerEquivRange.symm.toLinearMap
    obtain ⟨Dfull, hDfull⟩ := LinearMap.exists_extend Dlin
    let D : Matrix (Fin r) (Fin m) ℂ := LinearMap.toMatrix' Dfull
    refine ⟨D, ?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul]
    have hD : D.mulVecLin = Dfull := by
      change Matrix.toLin' D = Dfull
      exact Matrix.toLin'_toMatrix' Dfull
    rw [hD]
    apply LinearMap.ext
    intro x
    change T.mulVec x = Dfull (C.mulVec x)
    let cx : LinearMap.range C.mulVecLin := C.mulVecLin.rangeRestrict x
    have hext := DFunLike.congr_fun hDfull cx
    change Dfull (C.mulVec x) = Dlin cx at hext
    have hcx : C.mulVecLin.quotKerEquivRange.symm cx =
        (LinearMap.ker C.mulVecLin).mkQ x := by
      exact C.mulVecLin.quotKerEquivRange_symm_apply_image x cx.property
    have hDlin : Dlin cx = T.mulVec x := by
      change Tq (C.mulVecLin.quotKerEquivRange.symm cx) = T.mulVec x
      rw [hcx]
      exact Submodule.liftQ_apply _ _ x
    exact (hext.trans hDlin).symm

/-- Canonical Moore--Penrose decoder `T C* (C C*)†`. -/
noncomputable def reducedDecoder {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    Matrix (Fin r) (Fin m) ℂ :=
  T * Cᴴ * sourceGramPseudoinverse Cᴴ

/-- On the unisolvent branch the reduced decoder reproduces every target row. -/
theorem reducedDecoder_mul_calibration {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (hzero : targetCalibrationResidual C T = 0) :
    reducedDecoder C T * C = T := by
  have hrange : SourceRangeIncluded Tᴴ Cᴴ :=
    (sourceSchurResidual_eq_zero_iff_rangeIncluded Cᴴ Tᴴ).mp hzero
  rcases hrange with ⟨D, hD⟩
  have hfix := (sourceGramPseudoinverse_projection Cᴴ).2.2.2.2.2
  change sourceRangeProjection Cᴴ * Cᴴ = Cᴴ at hfix
  have hPT : sourceRangeProjection Cᴴ * Tᴴ = Tᴴ := by
    rw [hD, ← Matrix.mul_assoc, hfix]
  have hTP : T * sourceRangeProjection Cᴴ = T := by
    have := congrArg Matrix.conjTranspose hPT
    simpa [(sourceGramPseudoinverse_projection Cᴴ).2.2.2.1,
      Matrix.conjTranspose_mul] using this
  simpa [reducedDecoder, sourceRangeProjection, Matrix.mul_assoc] using hTP

/-- The reduced decoder is the unique extension supported on the acquired-row
range.  This is the finite matrix form of the minimum-Hilbert--Schmidt clause. -/
theorem reducedDecoder_unique_supported {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ)
    (D : Matrix (Fin r) (Fin m) ℂ)
    (hDC : D * C = T)
    (hsupport :
      D * (C * Cᴴ * sourceGramPseudoinverse Cᴴ) = D) :
    D = reducedDecoder C T := by
  calc
    D = D * (C * Cᴴ * sourceGramPseudoinverse Cᴴ) := hsupport.symm
    _ = (D * C) * Cᴴ * sourceGramPseudoinverse Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = reducedDecoder C T := by rw [hDC]; rfl

/-- The residual rank is the rank of the target bank restricted to the
unresolved calibration subspace. -/
theorem targetCalibrationResidual_rank {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    (targetCalibrationResidual C T).rank =
      ((1 - sourceRangeProjection Cᴴ) * Tᴴ).rank := by
  let P := sourceRangeProjection Cᴴ
  let R : Matrix (Fin d) (Fin r) ℂ := (1 - P) * Tᴴ
  obtain ⟨hPH, hP2, _⟩ :=
    (sourceGramPseudoinverse_projection Cᴴ).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hgram : targetCalibrationResidual C T = Rᴴ * R := by
    rw [targetCalibrationResidual,
      sourceSchurResidual_eq_orthogonalResidual]
    change Tᴴᴴ * (1 - P) * Tᴴ = Rᴴ * R
    symm
    calc
      Rᴴ * R = Tᴴᴴ * ((1 - P) * (1 - P)) * Tᴴ := by
        dsimp only [R]
        rw [Matrix.conjTranspose_mul, hQH]
        simp only [Matrix.mul_assoc]
      _ = Tᴴᴴ * (1 - P) * Tᴴ := by rw [hQ2]
  rw [hgram, Matrix.rank_conjTranspose_mul_self]

/-- Consolidated exact target-unisolvence packet. -/
theorem target_unisolvent_calibration {d m r : ℕ}
    (C : Matrix (Fin m) (Fin d) ℂ) (T : Matrix (Fin r) (Fin d) ℂ) :
    (targetCalibrationResidual C T = 0 ↔
      ∀ x : Fin d → ℂ, C *ᵥ x = 0 → T *ᵥ x = 0)
    ∧ (targetCalibrationResidual C T = 0 ↔ TargetRowsDetermined C T)
    ∧ (targetCalibrationResidual C T).rank =
      ((1 - sourceRangeProjection Cᴴ) * Tᴴ).rank := by
  exact ⟨residual_eq_zero_iff_targetRowsDetermined C T |>.trans
      (targetRowsDetermined_iff_kernel C T),
    residual_eq_zero_iff_targetRowsDetermined C T,
    targetCalibrationResidual_rank C T⟩

end TargetUnisolventCalibration
end NCG
