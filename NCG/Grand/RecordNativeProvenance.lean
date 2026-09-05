/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProvenancePythagoras
import NCG.Grand.LockedSignReversal

/-!
# record-native provenance closure
-/

open Matrix

namespace NCG

/-- The calibrated same-history reversal source. -/
noncomputable def calibratedReversalSource {Y E : Type*}
    (t : ℝ) (Bp Bm : Matrix Y E ℂ) : Matrix Y E ℂ :=
  ((1 / (2 * t) : ℝ) : ℂ) • (Bp - Bm)

/-- Synthesis of the canonical odd half-step writer through the
two protected source branches. -/
noncomputable def canonicalHodgeSource {Y E : Type*}
    [Fintype E] [DecidableEq E]
    (t : ℝ) (Bp Bm : Matrix Y E ℂ) : Matrix Y E ℂ :=
  Bp * (((1 / (2 * t) : ℝ) : ℂ) • (1 : Matrix E E ℂ))
    + Bm * (-(((1 / (2 * t) : ℝ) : ℂ) • (1 : Matrix E E ℂ)))

theorem canonicalHodgeSource_eq_reversal {Y E : Type*}
    [Fintype E] [DecidableEq E]
    (t : ℝ) (Bp Bm : Matrix Y E ℂ) :
    canonicalHodgeSource t Bp Bm = calibratedReversalSource t Bp Bm := by
  rw [canonicalHodgeSource, calibratedReversalSource,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, smul_sub]
  rw [sub_eq_add_neg]

/-- `cor:SMST-record-native-provenance`: the deterministic,
reversal-odd, calibrated half-step writer gives exactly the reversal
source and hence zero complete residual; for any positive three-panel
decomposition, vanishing of the complete residual is equivalent to
simultaneous vanishing of all panels. -/
theorem smst_record_native_provenance_exact
    {Y E : Type*} [Fintype Y] [Fintype E] [DecidableEq E]
    (t : ℝ) (Bp Bm L Ev N : Matrix Y E ℂ)
    (hsplit :
      (canonicalHodgeSource t Bp Bm - calibratedReversalSource t Bp Bm)ᴴ
          * (canonicalHodgeSource t Bp Bm - calibratedReversalSource t Bp Bm)
        = Lᴴ * L + Evᴴ * Ev + Nᴴ * N) :
    canonicalHodgeSource t Bp Bm = calibratedReversalSource t Bp Bm
    ∧ (canonicalHodgeSource t Bp Bm - calibratedReversalSource t Bp Bm)ᴴ
        * (canonicalHodgeSource t Bp Bm - calibratedReversalSource t Bp Bm) = 0
    ∧ ((canonicalHodgeSource t Bp Bm - calibratedReversalSource t Bp Bm = 0)
      ↔ (Lᴴ * L = 0 ∧ Evᴴ * Ev = 0 ∧ Nᴴ * N = 0)) := by
  have heq := canonicalHodgeSource_eq_reversal t Bp Bm
  have hzero : canonicalHodgeSource t Bp Bm
      - calibratedReversalSource t Bp Bm = 0 := sub_eq_zero.mpr heq
  refine ⟨heq, ?_, ?_⟩
  · rw [hzero, Matrix.mul_zero]
  · exact smst_record_native_provenance _ _ _ _ hsplit

end NCG
