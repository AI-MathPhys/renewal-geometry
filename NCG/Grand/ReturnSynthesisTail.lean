/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceCoercivityInfluenceExact
import NCG.Grand.FiniteProjectionAndReturnIdentities

/-!
# Exact compliance-normalized return synthesis

This file completes `thm:GT-return-synthesis-tail`.  It identifies the Gram
of the compliance-normalized synthesis `M_T^{†/2} Cᴴ` with the singular
Moore--Penrose Schur term `C M_T† Cᴴ`, then assembles equations ER.6--ER.8.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace ReturnSynthesisTail

open NCG.GeometricThresholdBank SourceCoercivityInfluence

variable {h t : Type*} [Fintype h] [Fintype t] [DecidableEq t]

/-- The positive spectral pseudoinverse square root of the tail compliance. -/
noncomputable def pinvSqrt (MT : Matrix t t ℂ) (hMT : MT.PosSemidef) :
    Matrix t t ℂ :=
  spectralFunction hMT.1 fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0

theorem pinvSqrt_posSemidef (MT : Matrix t t ℂ) (hMT : MT.PosSemidef) :
    (pinvSqrt MT hMT).PosSemidef := by
  unfold pinvSqrt
  exact spectralFunction_posSemidef hMT.1 _ fun i => by
    split_ifs <;> positivity

/-- The compliance-normalized mixed return source `M_T^{†/2} Cᴴ`. -/
noncomputable def synthesis (MT : Matrix t t ℂ) (hMT : MT.PosSemidef)
    (C : Matrix h t ℂ) : Matrix t h ℂ :=
  pinvSqrt MT hMT * Cᴴ

/-- The spectral pseudoinverse square root squares to the Moore--Penrose
pseudoinverse on a positive-semidefinite carrier. -/
theorem pinvSqrt_mul_self_eq_pinv (MT : Matrix t t ℂ)
    (hMT : MT.PosSemidef) :
    pinvSqrt MT hMT * pinvSqrt MT hMT = pinv hMT.1 := by
  unfold pinvSqrt pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hMT.1 fun i => ?_
  by_cases hp : 0 < hMT.1.eigenvalues i
  · rw [if_pos hp, if_pos hp]
    have hs : Real.sqrt (hMT.1.eigenvalues i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hp)
    field_simp [hs]
    simpa [pow_two] using (Real.mul_self_sqrt hp.le).symm
  · rw [if_neg hp, if_neg hp, zero_mul]

/-- The normalized synthesis has exactly the Moore--Penrose Schur Gram from
ER.7, with no invertibility assumption on the tail compliance. -/
theorem synthesis_gram (MT : Matrix t t ℂ) (hMT : MT.PosSemidef)
    (C : Matrix h t ℂ) :
    (synthesis MT hMT C)ᴴ * synthesis MT hMT C =
      C * pinv hMT.1 * Cᴴ := by
  rw [synthesis, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    (pinvSqrt_posSemidef MT hMT).1.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (pinvSqrt MT hMT),
    pinvSqrt_mul_self_eq_pinv MT hMT]

/-- `thm:GT-return-synthesis-tail`, equations ER.6--ER.8.  The last norm
identity is supplied by `return_synthesis_tail_norm` after viewing
`(I-Π)S` as the corresponding continuous linear map. -/
theorem return_synthesis_tail_exact
    (MH : Matrix h h ℂ) (MT : Matrix t t ℂ) (hMT : MT.PosSemidef)
    (C : Matrix h t ℂ) (Pi : Matrix t t ℂ) :
    let S := synthesis MT hMT C
    let KR := MH - Sᴴ * Pi * S
    let Kinf := MH - C * pinv hMT.1 * Cᴴ
    KR = MH - Sᴴ * Pi * S
      ∧ Kinf = MH - Sᴴ * S
      ∧ KR - Kinf = Sᴴ * (1 - Pi) * S := by
  dsimp only
  have hgram := synthesis_gram MT hMT C
  refine ⟨rfl, ?_, ?_⟩
  · rw [hgram]
  · rw [← hgram]
    exact FiniteProjectionAndReturnIdentities.return_synthesis_tail_identity
      MH (synthesis MT hMT C) Pi

end ReturnSynthesisTail
end NCG
