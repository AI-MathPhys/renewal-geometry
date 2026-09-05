/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Translation–helical common-action handoff
  (`thm:NS-translation-helical-handoff`,
  Gran-Tensor manuscript)

* `ns_translation_helical_handoff`: for the translation
  projection `P_tr = D(D*D)⁻¹D*` and the helical residual
  `R_hel = (1-P_tr)D_hel`,
  (i) `R_hel = 0` is exact routing: the residual vanishes
      exactly when the helical innovation Gram
      `D_hel*(1-P_tr)D_hel` does;
  (ii) the boxed closed helical obstruction
      `𝕆_hel = R*P₀QR ⪰ 0` for commuting hermitian
      idempotents `P₀, Q` (their product is a hermitian
      idempotent);
  (iii) the boxed minimum cost
      `𝕂_hel = R*(Q-P₀)A†(Q-P₀)R ⪰ 0` for PSD `A†`
      (congruence).

The screened action structure `A_Z = L_Z + D_Z*D_Z`, the
identification of `P₀` with the closed-obstruction
projection of the universal open-current packet, and the
canonical minimum decomposition
`(Q-P₀)R c = L^{1/2}a + D*j` with
`‖a‖² + ‖j‖² = ⟨c, 𝕂c⟩` are the manuscript's variational
layer (cf. `NCG.ns_effective_scale_current` for the
Thomson mechanism); the scalar-trace non-determination
remark is its reading.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:NS-translation-helical-handoff`. -/
theorem ns_translation_helical_handoff {n m h : Type}
    [Fintype n] [Fintype m] [Fintype h] [DecidableEq n]
    [DecidableEq m]
    (D : Matrix n m ℂ) (Dh : Matrix n h ℂ)
    [Invertible (Dᴴ * D)]
    (P0 Q Adag : Matrix n n ℂ)
    (hP0H : P0ᴴ = P0) (hP0P : P0 * P0 = P0)
    (hQH : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hcomm : P0 * Q = Q * P0)
    (hAdag : Adag.PosSemidef) :
    -- (i) exact routing ⟺ zero helical innovation
    (Dhᴴ * (1 - D * ((Dᴴ * D)⁻¹ * Dᴴ)) * Dh = 0
      ↔ (1 - D * ((Dᴴ * D)⁻¹ * Dᴴ)) * Dh = 0)
    -- (ii) the boxed closed helical obstruction is PSD
    ∧ (((1 - D * ((Dᴴ * D)⁻¹ * Dᴴ)) * Dh)ᴴ * (P0 * Q)
        * ((1 - D * ((Dᴴ * D)⁻¹ * Dᴴ)) * Dh)
        |>.PosSemidef)
    -- (iii) the boxed minimum surviving cost is PSD
    ∧ ((((Q - P0) * ((1 - D * ((Dᴴ * D)⁻¹ * Dᴴ))
          * Dh))ᴴ * Adag
        * ((Q - P0) * ((1 - D * ((Dᴴ * D)⁻¹ * Dᴴ))
          * Dh))).PosSemidef) := by
  set P := D * ((Dᴴ * D)⁻¹ * Dᴴ) with hP
  have hDDH : (Dᴴ * D)ᴴ = Dᴴ * D := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hDDinvH : ((Dᴴ * D)⁻¹)ᴴ = (Dᴴ * D)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hDDH]
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hDDinvH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hPP : P * P = P := by
    rw [hP]
    calc D * ((Dᴴ * D)⁻¹ * Dᴴ)
          * (D * ((Dᴴ * D)⁻¹ * Dᴴ))
        = D * ((Dᴴ * D)⁻¹ * ((Dᴴ * D)
            * ((Dᴴ * D)⁻¹ * Dᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = D * ((Dᴴ * D)⁻¹ * Dᴴ) := by
          rw [Matrix.mul_inv_cancel_left_of_invertible]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have h1PH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH]
  have hidem : (1 - P) * ((1 - P) * Dh) = (1 - P) * Dh := by
    rw [← Matrix.mul_assoc, h1P]
  have hfact : Dhᴴ * (1 - P) * Dh
      = ((1 - P) * Dh)ᴴ * ((1 - P) * Dh) := by
    rw [Matrix.conjTranspose_mul, h1PH,
      Matrix.mul_assoc Dhᴴ (1 - P) Dh, ← hidem,
      ← Matrix.mul_assoc, hidem]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfact]
    exact Matrix.conjTranspose_mul_self_eq_zero
  · -- P0 * Q is a hermitian idempotent
    have hPQH : (P0 * Q)ᴴ = P0 * Q := by
      rw [Matrix.conjTranspose_mul, hP0H, hQH, hcomm]
    have hPQP : (P0 * Q) * (P0 * Q) = P0 * Q := by
      calc P0 * Q * (P0 * Q)
          = P0 * ((Q * P0) * Q) := by
            simp only [Matrix.mul_assoc]
        _ = P0 * (P0 * (Q * Q)) := by
            rw [← hcomm]
            simp only [Matrix.mul_assoc]
        _ = P0 * Q := by
            rw [hQQ, ← Matrix.mul_assoc, hP0P]
    have hpsd : (P0 * Q).PosSemidef := by
      have hf : P0 * Q = (P0 * Q)ᴴ * (P0 * Q) := by
        rw [hPQH, hPQP]
      rw [hf]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    exact hpsd.conjTranspose_mul_mul_same _
  · exact hAdag.conjTranspose_mul_mul_same _

end NCG
