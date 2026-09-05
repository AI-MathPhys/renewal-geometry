/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalPhysicalRate
import NCG.Grand.CommonActionApproximateWardBounds
import NCG.Grand.SampledVersusKilledExact
import NCG.Grand.SourceInfluenceExtremizerAttainmentExact

/-!
# Physical renewal rates from the raw Gram hypotheses

This file closes the normalization step in `thm:renewal-physical-rate`.
Starting from a synthesis Gram identity and the manuscript's weighted action
Gram inequality, it constructs the whitened synthesis and action, proves their
ordinary operator contractions, identifies the normalized Ward-Gram square
root with the residual norm, and invokes the already compiled physical-time
rate theorem.
-/

open Matrix NCG.ThreeCylinderActionResponse
open scoped Norms.L2Operator MatrixOrder ComplexOrder

namespace NCG
namespace PhysicalRateFromGram

variable {h e : ℕ}

/-- Whitening transports the raw weighted action Gram to the ordinary Gram of
the normalized action. -/
theorem normalizedAction_gram
    (G W : Matrix (Fin e) (Fin e) ℂ) (hG : G.PosDef) :
    let A := invSqrt hG.1
    let Q := sqrtM hG.1
    (Q * W * A)ᴴ * (Q * W * A) = A * (Wᴴ * G * W) * A := by
  dsimp
  let Q := sqrtM hG.1
  have hQsq : Q * Q = G :=
    SourceInfluenceAttainment.sqrtM_mul_sqrtM hG.posSemidef
  rw [conjTranspose_mul, conjTranspose_mul]
  rw [(invSqrt_isHermitian hG.1).eq]
  rw [(SourceInfluenceAttainment.sqrtM_posSemidef hG.posSemidef).1.eq]
  change invSqrt hG.1 * (Wᴴ * Q) * (Q * W * invSqrt hG.1) = _
  calc
    _ = invSqrt hG.1 * ((Wᴴ * Q) * Q) * (W * invSqrt hG.1) := by
      simp only [Matrix.mul_assoc]
    _ = invSqrt hG.1 * (Wᴴ * (Q * Q)) * (W * invSqrt hG.1) := by
      rw [Matrix.mul_assoc Wᴴ Q Q]
    _ = invSqrt hG.1 * (Wᴴ * G) * (W * invSqrt hG.1) := by rw [hQsq]
    _ = invSqrt hG.1 * (Wᴴ * G * W) * invSqrt hG.1 := by
      simp only [Matrix.mul_assoc]

/-- The normalized Ward Gram is exactly the ordinary Gram of the whitened
intertwining residual. -/
theorem normalizedResidual_gram
    (R : Matrix (Fin h) (Fin e) ℂ) (G : Matrix (Fin e) (Fin e) ℂ)
    (hG : G.PosDef) :
    let A := invSqrt hG.1
    (R * A)ᴴ * (R * A) = A * (Rᴴ * R) * A := by
  dsimp
  rw [conjTranspose_mul, (invSqrt_isHermitian hG.1).eq]
  simp only [Matrix.mul_assoc]

/-- `thm:renewal-physical-rate` directly from its raw synthesis, weighted
action-Gram, and normalized Ward-Gram data.

The definitions in the conclusion are the manuscript definitions
`V = S G^{-1/2}`, `\widehat W = G^{1/2} W G^{-1/2}`, and
`epsilon = ||G^{-1/2} R^* R G^{-1/2}||^{1/2}`.
-/
theorem renewal_physical_rate_from_gram
    (T : Matrix (Fin h) (Fin h) ℂ)
    (S : Matrix (Fin h) (Fin e) ℂ)
    (G W : Matrix (Fin e) (Fin e) ℂ)
    (lam lam' τ horizon : ℝ)
    (hG : G.PosDef)
    (hGram : Sᴴ * S = G)
    (hT : ‖T‖ ≤ 1)
    (hAction : ((((Real.exp (-(lam * τ))) ^ 2 : ℝ) : ℂ) • G -
      Wᴴ * G * W).PosSemidef)
    (hlam : 0 ≤ lam) (hτ : 0 < τ) (hhorizon : 0 ≤ horizon) :
    let A := invSqrt hG.1
    let Q := sqrtM hG.1
    let V := S * A
    let What := Q * W * A
    let R := T * S - S * W
    let ε := Real.sqrt ‖A * (Rᴴ * R) * A‖
    ‖T * V‖ ≤ Real.exp (-(lam * τ)) + ε
      ∧ ‖Vᴴ * T * V‖ ≤ Real.exp (-(lam * τ)) + ε
      ∧ (ε ≤ Real.exp (-(lam' * τ)) - Real.exp (-(lam * τ)) →
          ‖T * V‖ ≤ Real.exp (-(lam' * τ))
            ∧ ‖Vᴴ * T * V‖ ≤ Real.exp (-(lam' * τ)))
      ∧ (∀ n : ℕ, ‖T ^ n * V - V * What ^ n‖ ≤ n * ε)
      ∧ (∀ n : ℕ, (n : ℝ) * τ ≤ horizon + τ →
          (n : ℝ) * ε ≤ (horizon + τ) * (ε / τ)) := by
  dsimp only
  let A := invSqrt hG.1
  let Q := sqrtM hG.1
  let V := S * A
  let What := Q * W * A
  let R := T * S - S * W
  let ε := Real.sqrt ‖A * (Rᴴ * R) * A‖
  have hAH : Aᴴ = A := (invSqrt_isHermitian hG.1).eq
  have hQA : Q * A = 1 := SampledVersusKilled.sqrtM_mul_invSqrt_of_posDef hG
  have hAQ : A * Q = 1 := SampledVersusKilled.invSqrt_mul_sqrtM_of_posDef hG
  have hAGA : A * G * A = 1 :=
    SampledVersusKilled.invSqrt_mul_self_mul_invSqrt_of_posDef hG
  have hVGram : Vᴴ * V = 1 := by
    dsimp [V]
    rw [conjTranspose_mul, hAH]
    calc
      A * Sᴴ * (S * A) = A * (Sᴴ * S) * A := by
        simp only [Matrix.mul_assoc]
      _ = A * G * A := by rw [hGram]
      _ = 1 := hAGA
  have hV : ‖V‖ ≤ 1 := by
    apply l2_opNorm_le_of_conjTranspose_mul_self_le_scalar V 1 zero_le_one
    rw [hVGram]
    norm_num
    exact PosSemidef.zero
  have hVstar : ‖Vᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hV
  have hWhatGram : Whatᴴ * What = A * (Wᴴ * G * W) * A := by
    simpa [A, Q, What] using normalizedAction_gram G W hG
  have hActionConj := hAction.conjTranspose_mul_mul_same A
  have hWhatBound :
      (((Real.exp (-(lam * τ))) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin e) (Fin e) ℂ) - Whatᴴ * What |>.PosSemidef := by
    rw [hWhatGram]
    rw [hAH] at hActionConj
    have hscaled :
        A * ((((Real.exp (-(lam * τ))) ^ 2 : ℝ) : ℂ) • G) * A =
          (((Real.exp (-(lam * τ))) ^ 2 : ℝ) : ℂ) •
            (1 : Matrix (Fin e) (Fin e) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hAGA]
    simpa only [Matrix.mul_sub, Matrix.sub_mul, hscaled] using hActionConj
  have hrnonneg : 0 ≤ Real.exp (-(lam * τ)) := (Real.exp_pos _).le
  have hWhat : ‖What‖ ≤ Real.exp (-(lam * τ)) :=
    l2_opNorm_le_of_conjTranspose_mul_self_le_scalar What
      (Real.exp (-(lam * τ))) hrnonneg hWhatBound
  have hrle : Real.exp (-(lam * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hWhatOne : ‖What‖ ≤ 1 := hWhat.trans hrle
  have hVWhat : ‖V * What‖ ≤ Real.exp (-(lam * τ)) := by
    calc
      ‖V * What‖ ≤ ‖V‖ * ‖What‖ := Matrix.l2_opNorm_mul V What
      _ ≤ 1 * Real.exp (-(lam * τ)) :=
        mul_le_mul hV hWhat (norm_nonneg _) zero_le_one
      _ = Real.exp (-(lam * τ)) := one_mul _
  have hVWhatEq : V * What = S * W * A := by
    dsimp [V, What]
    calc
      S * A * (Q * W * A) = S * (A * Q) * (W * A) := by
        simp only [Matrix.mul_assoc]
      _ = S * W * A := by
        rw [hAQ, Matrix.mul_one]
        exact (Matrix.mul_assoc S W A).symm
  have hResidual : T * V - V * What = R * A := by
    rw [hVWhatEq]
    dsimp [V, R]
    rw [Matrix.sub_mul, Matrix.mul_assoc T S A, Matrix.mul_assoc S W A]
  have hResidualGram :
      (T * V - V * What)ᴴ * (T * V - V * What) =
        A * (Rᴴ * R) * A := by
    rw [hResidual]
    simpa [A] using normalizedResidual_gram R G hG
  have hεeq : ε = ‖T * V - V * What‖ := by
    dsimp [ε]
    rw [← hResidualGram, Matrix.l2_opNorm_conjTranspose_mul_self]
    exact Real.sqrt_mul_self (norm_nonneg _)
  have hε : 0 ≤ ε := by
    rw [hεeq]
    exact norm_nonneg _
  apply renewal_physical_rate_exact T V What lam lam' τ ε horizon
  · exact hT
  · exact hWhatOne
  · exact hVstar
  · exact hVWhat
  · rw [hεeq]
  · exact hε
  · exact hτ
  · exact hhorizon

end PhysicalRateFromGram
end NCG




