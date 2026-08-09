/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ProvenancePythagoras

/-!
# Exact EASY 53: concrete same-history provenance Pythagoras

The generic three-projector identity is instantiated here at the manuscript's
pair-span leakage, reversal-even leakage, and odd normalization defect.  The
joint-source Moore--Penrose formula for the pair projector is also verified
directly from the Penrose equations.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option maxHeartbeats 800000

/-- The Moore--Penrose range formula is an orthogonal projector and fixes the
joint synthesis.  Here `J` is the dagger of the Gram, represented by its
Hermiticity, Penrose identities, and the equivalent synthesis-range identity. -/
theorem gram_pinv_range_projection
    {Y K : Type*} [Fintype Y] [Fintype K]
    [DecidableEq Y] [DecidableEq K]
    (B : Matrix Y K ℂ) (J : Matrix K K ℂ)
    (hJH : Jᴴ = J)
    (_hGJG : (Bᴴ * B) * J * (Bᴴ * B) = Bᴴ * B)
    (hJGJ : J * (Bᴴ * B) * J = J)
    (hBJG : B * J * (Bᴴ * B) = B) :
    let P := B * J * Bᴴ
    Pᴴ = P ∧ P * P = P ∧ P * B = B := by
  dsimp only
  have hPH : (B * J * Bᴴ)ᴴ = B * J * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJH]
    simp only [Matrix.mul_assoc]
  have hP2 : (B * J * Bᴴ) * (B * J * Bᴴ) = B * J * Bᴴ := by
    calc
      (B * J * Bᴴ) * (B * J * Bᴴ)
          = B * (J * (Bᴴ * B) * J) * Bᴴ := by
              simp only [Matrix.mul_assoc]
      _ = B * J * Bᴴ := by rw [hJGJ]
  refine ⟨hPH, hP2, ?_⟩
  simpa only [Matrix.mul_assoc] using hBJG

/-- Exact concrete panel decomposition from a retained reversal involution.
The assumptions say that `P` is the pair-range projector and that the retained
reversal source is pair-supported and reversal odd. -/
theorem smst_provenance_pythagoras_exact
    {Y E : Type*} [Fintype Y] [Fintype E] [DecidableEq Y]
    (Θ P : Matrix Y Y ℂ) (BH Brev : Matrix Y E ℂ)
    (hΘH : Θᴴ = Θ) (hΘ2 : Θ * Θ = 1)
    (hPH : Pᴴ = P) (hP2 : P * P = P) (hcomm : Θ * P = P * Θ)
    (hpair : P * Brev = Brev) (hodd : Θ * Brev = -Brev) :
    let Pe := (2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ)
    let Po := (2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) - Θ)
    let L := (1 - P) * BH
    let Ev := Pe * P * BH
    let N := Po * P * BH - Brev
    (BH - Brev)ᴴ * (BH - Brev)
      = Lᴴ * L + Evᴴ * Ev + Nᴴ * N
    ∧ Lᴴ * Ev = 0 ∧ Lᴴ * N = 0 ∧ Evᴴ * N = 0
    ∧ ((BH - Brev = 0) ↔
        (Lᴴ * L = 0 ∧ Evᴴ * Ev = 0 ∧ Nᴴ * N = 0)) := by
  dsimp only
  let Pe : Matrix Y Y ℂ := (2 : ℂ)⁻¹ • (1 + Θ)
  let Po : Matrix Y Y ℂ := (2 : ℂ)⁻¹ • (1 - Θ)
  let Q1 : Matrix Y Y ℂ := 1 - P
  let Q2 : Matrix Y Y ℂ := Pe * P
  let Q3 : Matrix Y Y ℂ := Po * P
  have hpacket := (smst_provenance_pythagoras (Y := Y) (E := E)).2.2
    Θ P hΘH hΘ2 hPH hP2 hcomm
  have hpacketOdd := (smst_provenance_pythagoras (Y := Y) (E := E)).2.2
    (-Θ) P (by rw [Matrix.conjTranspose_neg, hΘH])
      (by rw [neg_mul_neg, hΘ2]) hPH hP2
      (by rw [Matrix.neg_mul, Matrix.mul_neg, hcomm])
  have hQsum : Q1 + Q2 + Q3 = 1 := by
    simpa only [Q1, Q2, Q3, Pe, Po] using hpacket.1
  have hQ1H : Q1ᴴ = Q1 := by
    simp [Q1, Matrix.conjTranspose_sub, hPH]
  have hQ1I : Q1 * Q1 = Q1 := by
    simp only [Q1, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hP2]
    abel
  have hQ2H : Q2ᴴ = Q2 := by
    simpa only [Q2, Pe] using hpacket.2.1
  have hQ2I : Q2 * Q2 = Q2 := by
    simpa only [Q2, Pe] using hpacket.2.2.1
  have hQ3H : Q3ᴴ = Q3 := by
    simpa only [Q3, Po, neg_neg, sub_eq_add_neg] using hpacketOdd.2.1
  have hQ3I : Q3 * Q3 = Q3 := by
    simpa only [Q3, Po, neg_neg, sub_eq_add_neg] using hpacketOdd.2.2.1
  have hQ1Q2 : Q1 * Q2 = 0 := by
    dsimp [Q1, Q2, Pe]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    have hPcommPe : P * ((2 : ℂ)⁻¹ • (1 + Θ))
        = ((2 : ℂ)⁻¹ • (1 + Θ)) * P := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, hcomm]
    rw [← Matrix.mul_assoc, hPcommPe, Matrix.mul_assoc, hP2, sub_self]
  have hQ1Q3 : Q1 * Q3 = 0 := by
    dsimp [Q1, Q3, Po]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    have hPcommPo : P * ((2 : ℂ)⁻¹ • (1 - Θ))
        = ((2 : ℂ)⁻¹ • (1 - Θ)) * P := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, hcomm]
    rw [← Matrix.mul_assoc, hPcommPo, Matrix.mul_assoc, hP2, sub_self]
  have hQ2Q3 : Q2 * Q3 = 0 := by
    simpa only [Q2, Q3, Pe, Po] using hpacket.2.2.2
  have hQ1B : Q1 * Brev = 0 := by
    dsimp [Q1]
    rw [Matrix.sub_mul, Matrix.one_mul, hpair, sub_self]
  have hQ2B : Q2 * Brev = 0 := by
    dsimp [Q2, Pe]
    rw [Matrix.mul_assoc, hpair]
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, hodd]
    module
  have hQ3B : Q3 * Brev = Brev := by
    dsimp [Q3, Po]
    rw [Matrix.mul_assoc, hpair]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, hodd]
    module
  have hQ1X : Q1 * (BH - Brev) = (1 - P) * BH := by
    rw [Matrix.mul_sub, hQ1B, sub_zero]
  have hQ2X : Q2 * (BH - Brev) = Pe * P * BH := by
    rw [Matrix.mul_sub, hQ2B, sub_zero]
  have hQ3X : Q3 * (BH - Brev) = Po * P * BH - Brev := by
    rw [Matrix.mul_sub, hQ3B]
  have hgram := (smst_provenance_pythagoras (Y := Y) (E := E)).1
    Q1 Q2 Q3 hQ1H hQ2H hQ3H hQ1I hQ2I hQ3I hQsum (BH - Brev)
  rw [hQ1X, hQ2X, hQ3X] at hgram
  have h12 := (smst_provenance_pythagoras (Y := Y) (E := E)).2.1
    Q1 Q2 hQ1H hQ1Q2 (BH - Brev)
  have h13 := (smst_provenance_pythagoras (Y := Y) (E := E)).2.1
    Q1 Q3 hQ1H hQ1Q3 (BH - Brev)
  have h23 := (smst_provenance_pythagoras (Y := Y) (E := E)).2.1
    Q2 Q3 hQ2H hQ2Q3 (BH - Brev)
  rw [hQ1X, hQ2X] at h12
  rw [hQ1X, hQ3X] at h13
  rw [hQ2X, hQ3X] at h23
  have hv := smst_record_native_provenance
    (BH - Brev) ((1 - P) * BH) (Pe * P * BH)
      (Po * P * BH - Brev) hgram
  exact ⟨hgram, h12, h13, h23, hv⟩

end NCG
