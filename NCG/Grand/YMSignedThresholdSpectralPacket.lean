/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMSignedThreshold
import NCG.Grand.MatrixLoewnerInverseBoundsExact
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.MarginalsOrientation
import NCG.Grand.SignedHaynsworthInertia
import NCG.Grand.SampledVersusKilledExact

/-!
# Spectral block layer of the signed Yang--Mills threshold packet

This file supplies the tail-resolvent threshold transfer, transported third
moment, and exact signed inertia count in YM.3, YM.4, and YM.6.
-/

open Matrix NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace YMSignedThresholdSpectralPacket

/-- The tail block `qI-D` retains the scalar floor `q-d`. -/
theorem tailThreshold_posDef {E : Type*} [Fintype E] [DecidableEq E]
    (D : Matrix E E ℂ) (q d : ℝ)
    (hDupper : (d • (1 : Matrix E E ℂ) - D).PosSemidef)
    (hqd : d < q) :
    (q • (1 : Matrix E E ℂ) - D).PosDef := by
  apply MatrixLoewnerInverseBounds.posDef_of_smul_one_le (sub_pos.mpr hqd)
  rw [Matrix.le_iff]
  have heq :
      q • (1 : Matrix E E ℂ) - D -
          (q - d) • (1 : Matrix E E ℂ) =
        d • (1 : Matrix E E ℂ) - D := by
    module
  rw [heq]
  exact hDupper

/-- The tail resolvent is bounded above by its scalar floor. -/
theorem tailResolvent_upper {E : Type*} [Fintype E] [DecidableEq E]
    (D : Matrix E E ℂ) (q d : ℝ)
    (hDupper : (d • (1 : Matrix E E ℂ) - D).PosSemidef)
    (hqd : d < q) :
    (q • (1 : Matrix E E ℂ) - D)⁻¹ ≤
      (q - d)⁻¹ • (1 : Matrix E E ℂ) := by
  apply MatrixLoewnerInverseBounds.inv_le_smul_one_of_smul_one_le
    (sub_pos.mpr hqd)
  rw [Matrix.le_iff]
  have heq :
      q • (1 : Matrix E E ℂ) - D -
          (q - d) • (1 : Matrix E E ℂ) =
        d • (1 : Matrix E E ℂ) - D := by
    module
  rw [heq]
  exact hDupper

/-- **YM.3.**  The signed head reserve and a scalar tail ceiling imply the
full common-time threshold. -/
theorem signed_threshold_transfer
    {H E : Type} [Fintype H] [Fintype E]
    [DecidableEq H] [DecidableEq E]
    (M1 : Matrix H H ℂ) (B : Matrix H E ℂ) (D : Matrix E E ℂ)
    (q d : ℝ) (hM1 : M1.IsHermitian) (hD : D.PosSemidef)
    (hDupper : (d • (1 : Matrix E E ℂ) - D).PosSemidef)
    (hqd : d < q)
    (hreserve :
      (q • (1 : Matrix H H ℂ) - M1 -
        (q - d)⁻¹ • (B * Bᴴ)).PosSemidef) :
    (q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
      fromBlocks M1 B Bᴴ D).PosSemidef := by
  let Q : Matrix E E ℂ := q • 1 - D
  let A : Matrix H H ℂ := q • 1 - M1
  have hQpd : Q.PosDef := tailThreshold_posDef D q d hDupper hqd
  have hRupper : Q⁻¹ ≤ (q - d)⁻¹ • (1 : Matrix E E ℂ) :=
    tailResolvent_upper D q d hDupper hqd
  have hreturnUpper :
      B * Q⁻¹ * Bᴴ ≤ (q - d)⁻¹ • (B * Bᴴ) := by
    have hconj := MatrixLoewnerInverseBounds.conj_le_conj' hRupper B
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hconj
  have hreturnDeficit :
      ((q - d)⁻¹ • (B * Bᴴ) - B * Q⁻¹ * Bᴴ).PosSemidef :=
    Matrix.le_iff.mp hreturnUpper
  have hSchur : (A - B * Q⁻¹ * Bᴴ).PosSemidef := by
    have heq : A - B * Q⁻¹ * Bᴴ =
        (A - (q - d)⁻¹ • (B * Bᴴ)) +
          ((q - d)⁻¹ • (B * Bᴴ) - B * Q⁻¹ * Bᴴ) := by abel
    rw [heq]
    exact hreserve.add hreturnDeficit
  have hAhead : A.IsHermitian := by
    have hqI : (q • (1 : Matrix H H ℂ)).IsHermitian := by
      change (q • (1 : Matrix H H ℂ))ᴴ = q • (1 : Matrix H H ℂ)
      simp
    exact hqI.sub hM1
  have hrange : Q * SourceCoercivityInfluence.pinv hQpd.1 * (-Bᴴ) = -Bᴴ := by
    rw [GRHRestoringShort.self_mul_pinv hQpd, Matrix.one_mul]
  have hswap : (fromBlocks Q (-Bᴴ) (-B) A).PosSemidef := by
    have hpinv : SourceCoercivityInfluence.pinv hQpd.1 = Q⁻¹ :=
      (Matrix.inv_eq_left_inv (GRHRestoringShort.pinv_mul_self hQpd)).symm
    have hSchur' :
        (A - (-Bᴴ)ᴴ * SourceCoercivityInfluence.pinv hQpd.1 * (-Bᴴ)).PosSemidef := by
      rw [hpinv]
      simpa [Matrix.conjTranspose_neg] using hSchur
    have hs := posSemidef_of_schur hQpd.posSemidef (-Bᴴ) A hAhead hrange hSchur'
    simpa [Matrix.conjTranspose_neg] using hs
  have horig : (fromBlocks A (-B) (-Bᴴ) Q).PosSemidef :=
    (fromBlocks_posSemidef_swap_iff A (-B) (-Bᴴ) Q).2 hswap
  have heq : fromBlocks A (-B) (-Bᴴ) Q =
      q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
        fromBlocks M1 B Bᴴ D := by
    ext (i | i) (j | j) <;> simp [A, Q, Matrix.one_apply]
  rwa [heq] at horig

/-- **YM.4.**  The head block of the transported third moment isolates the
first tail-return moment `B D B*`. -/
theorem thirdMoment_return_identity
    {H E : Type*} [Fintype H] [Fintype E]
    [DecidableEq H] [DecidableEq E]
    (M1 : Matrix H H ℂ) (B : Matrix H E ℂ) (D : Matrix E E ℂ) :
    Matrix.toBlocks₁₁
        (fromBlocks M1 B Bᴴ D * fromBlocks M1 B Bᴴ D *
          fromBlocks M1 B Bᴴ D) -
        M1 ^ 3 - M1 * (B * Bᴴ) - (B * Bᴴ) * M1 =
      B * D * Bᴴ := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁]
  simp only [pow_succ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  noncomm_ring

/-- **YM.5.**  A positive tail bounded by `dI` gives the sharp two-term
Stieltjes sandwich for the return self-energy. -/
theorem stieltjes_return_sandwich
    {H E : Type*} [Fintype H] [Fintype E]
    [DecidableEq H] [DecidableEq E]
    (B : Matrix H E ℂ) (D : Matrix E E ℂ) (q d : ℝ)
    (hD : D.PosSemidef)
    (hDupper : (d • (1 : Matrix E E ℂ) - D).PosSemidef)
    (hd : 0 ≤ d) (hqd : d < q) :
    q⁻¹ • (B * Bᴴ) + (q ^ 2)⁻¹ • (B * D * Bᴴ) ≤
        B * (q • (1 : Matrix E E ℂ) - D)⁻¹ * Bᴴ ∧
      B * (q • (1 : Matrix E E ℂ) - D)⁻¹ * Bᴴ ≤
        q⁻¹ • (B * Bᴴ) + (q * (q - d))⁻¹ • (B * D * Bᴴ) := by
  let Q : Matrix E E ℂ := q • 1 - D
  let R : Matrix E E ℂ := Q⁻¹
  let S : Matrix E E ℂ := CFC.sqrt D
  have hq : 0 < q := lt_of_le_of_lt hd hqd
  have hQpd : Q.PosDef := tailThreshold_posDef D q d hDupper hqd
  have hQle : Q ≤ q • (1 : Matrix E E ℂ) := by
    rw [Matrix.le_iff]
    have heq : q • (1 : Matrix E E ℂ) - Q = D := by
      simp only [Q]
      module
    rwa [heq]
  have hRlower : q⁻¹ • (1 : Matrix E E ℂ) ≤ R := by
    simpa [R] using MatrixLoewnerInverseBounds.smul_one_le_inv_of_le_smul_one
      hq hQpd hQle
  have hRupper : R ≤ (q - d)⁻¹ • (1 : Matrix E E ℂ) := by
    simpa [R, Q] using tailResolvent_upper D q d hDupper hqd
  have hSQ : S * Q = Q * S := by
    have hDQ : D * Q = Q * D := by
      simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    exact (commute_sqrt (show Commute D Q from hDQ)).eq
  have hQunit : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hQpd.isUnit
  letI : Invertible Q := hQpd.isUnit.invertible
  have hSR : S * R = R * S := by
    simpa [R] using MatrixLoewnerInverseBounds.commute_nonsing_inv hSQ
  have hS2 : S * S = D := by
    simpa [S] using sqrt_mul_self_eq D hD
  have hSH : Sᴴ = S := by
    simpa [S] using sqrt_isHermitian D
  have hDRlower : q⁻¹ • D ≤ D * R := by
    have hc := MatrixLoewnerInverseBounds.conj_le_conj hRlower S
    have hleft : Sᴴ * (q⁻¹ • (1 : Matrix E E ℂ)) * S = q⁻¹ • D := by
      rw [hSH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS2]
    have hright : Sᴴ * R * S = D * R := by
      rw [hSH, Matrix.mul_assoc, ← hSR, ← Matrix.mul_assoc, hS2]
    rwa [hleft, hright] at hc
  have hDRupper : D * R ≤ (q - d)⁻¹ • D := by
    have hc := MatrixLoewnerInverseBounds.conj_le_conj hRupper S
    have hleft : Sᴴ * R * S = D * R := by
      rw [hSH, Matrix.mul_assoc, ← hSR, ← Matrix.mul_assoc, hS2]
    have hright :
        Sᴴ * ((q - d)⁻¹ • (1 : Matrix E E ℂ)) * S =
          (q - d)⁻¹ • D := by
      rw [hSH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS2]
    rwa [hleft, hright] at hc
  have hQR : Q * R = 1 := by
    simpa [R] using Matrix.mul_nonsing_inv Q hQunit
  have hlinear : q • R = (1 : Matrix E E ℂ) + D * R := by
    have hQR' := hQR
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hQR'
    exact eq_add_of_sub_eq hQR'
  have hresolvent :
      R = q⁻¹ • (1 : Matrix E E ℂ) + q⁻¹ • (D * R) := by
    calc
      R = (q⁻¹ * q) • R := by rw [inv_mul_cancel₀ hq.ne', one_smul]
      _ = q⁻¹ • (q • R) := by rw [smul_smul]
      _ = q⁻¹ • ((1 : Matrix E E ℂ) + D * R) := by rw [hlinear]
      _ = q⁻¹ • (1 : Matrix E E ℂ) + q⁻¹ • (D * R) := by rw [smul_add]
  have hconj_smul (X : Matrix E E ℂ) :
      B * (q⁻¹ • X) * Bᴴ = q⁻¹ • (B * X * Bᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hreturn :
      B * R * Bᴴ = q⁻¹ • (B * Bᴴ) + q⁻¹ • (B * (D * R) * Bᴴ) := by
    calc
      B * R * Bᴴ =
          B * (q⁻¹ • (1 : Matrix E E ℂ) + q⁻¹ • (D * R)) * Bᴴ := by
            exact congrArg (fun X : Matrix E E ℂ => B * X * Bᴴ) hresolvent
      _ = q⁻¹ • (B * Bᴴ) + q⁻¹ • (B * (D * R) * Bᴴ) := by
            rw [Matrix.mul_add, Matrix.add_mul, hconj_smul, hconj_smul,
              Matrix.mul_one]
  have hlconj := MatrixLoewnerInverseBounds.conj_le_conj' hDRlower B
  have huconj := MatrixLoewnerInverseBounds.conj_le_conj' hDRupper B
  have hqinv : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hlscaled := smul_le_smul_of_nonneg_left hlconj hqinv
  have huscaled := smul_le_smul_of_nonneg_left huconj hqinv
  constructor
  · change q⁻¹ • (B * Bᴴ) + (q ^ 2)⁻¹ • (B * D * Bᴴ) ≤ B * R * Bᴴ
    rw [hreturn]
    have hadd := add_le_add_left hlscaled (q⁻¹ • (B * Bᴴ))
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul,
      pow_two, mul_comm] using hadd
  · change B * R * Bᴴ ≤
      q⁻¹ • (B * Bᴴ) + (q * (q - d))⁻¹ • (B * D * Bᴴ)
    rw [hreturn]
    have hadd := add_le_add_left huscaled (q⁻¹ • (B * Bᴴ))
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul,
      mul_comm]
      using hadd

/-- **YM.6.**  All three signed inertia indices split into the tail threshold
and its exact head Schur complement. -/
theorem signed_threshold_inertia
    {H E : Type} [Fintype H] [Fintype E]
    [DecidableEq H] [DecidableEq E]
    (M1 : Matrix H H ℂ) (B : Matrix H E ℂ) (D : Matrix E E ℂ)
    (q d : ℝ) (hM1 : M1.IsHermitian) (hD : D.PosSemidef)
    (hDupper : (d • (1 : Matrix E E ℂ) - D).PosSemidef)
    (hqd : d < q) :
    let Q : Matrix E E ℂ := q • 1 - D
    let S : Matrix H H ℂ := q • 1 - M1 - B * Q⁻¹ * Bᴴ
    posInertia (q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
        fromBlocks M1 B Bᴴ D) = posInertia Q + posInertia S ∧
    negInertia (q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
        fromBlocks M1 B Bᴴ D) = negInertia Q + negInertia S ∧
    nullInertia (q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
        fromBlocks M1 B Bᴴ D) = nullInertia Q + nullInertia S := by
  dsimp only
  let Q : Matrix E E ℂ := q • 1 - D
  let A : Matrix H H ℂ := q • 1 - M1
  let W : Matrix E H ℂ := -(Q⁻¹ * Bᴴ)
  have hQpd : Q.PosDef := tailThreshold_posDef D q d hDupper hqd
  have hQinv : Q * Q⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQpd.isUnit)
  have hW : Q * W = (-B)ᴴ := by
    simp only [W, Matrix.mul_neg, Matrix.conjTranspose_neg]
    rw [← Matrix.mul_assoc, hQinv, Matrix.one_mul]
  have hfull :
      q • (1 : Matrix (H ⊕ E) (H ⊕ E) ℂ) -
          fromBlocks M1 B Bᴴ D = fromBlocks A (-B) (-B)ᴴ Q := by
    ext (i | i) (j | j) <;> simp [A, Q, Matrix.one_apply]
  have hHerm : (fromBlocks A (-B) (-B)ᴴ Q).IsHermitian := by
    apply Matrix.IsHermitian.fromBlocks
    · have hqI : (q • (1 : Matrix H H ℂ)).IsHermitian := by
        change (q • (1 : Matrix H H ℂ))ᴴ = q • (1 : Matrix H H ℂ)
        simp
      exact hqI.sub hM1
    · rfl
    · exact hQpd.1
  obtain ⟨_, hp, hn, hz⟩ := gt_signed_haynsworth A (-B) Q W hHerm hW
  have hSchur : A - Wᴴ * Q * W = A - B * Q⁻¹ * Bᴴ := by
    have hQH : Qᴴ = Q := hQpd.1.eq
    have hQinvH : (Q⁻¹)ᴴ = Q⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hQH]
    simp only [W, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQinvH, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg]
    congr 1
    calc
      B * Q⁻¹ * Q * (Q⁻¹ * Bᴴ) =
          (B * (Q⁻¹ * Q)) * (Q⁻¹ * Bᴴ) := by
            rw [Matrix.mul_assoc B Q⁻¹ Q]
      _ = B * (Q⁻¹ * Bᴴ) := by
            rw [Matrix.nonsing_inv_mul _
              ((Matrix.isUnit_iff_isUnit_det _).mp hQpd.isUnit),
              Matrix.mul_one]
      _ = B * Q⁻¹ * Bᴴ := by rw [Matrix.mul_assoc]
  rw [hSchur] at hp hn hz
  rw [hfull]
  constructor
  · simpa [Q, A, add_comm] using hp
  constructor
  · simpa [Q, A, add_comm] using hn
  · simpa [Q, A, add_comm] using hz

end YMSignedThresholdSpectralPacket
end NCG
