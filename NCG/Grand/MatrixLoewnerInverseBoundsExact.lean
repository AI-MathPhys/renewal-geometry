/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar
import Mathlib

/-! # Finite matrix Loewner inverse bounds -/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace MatrixLoewnerInverseBounds

theorem star_mulVec_dotProduct {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (Mᴴ *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (M *ᵥ y) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]

theorem conj_le_conj {n m : Type*} [Fintype n] [Fintype m]
    {X Y : Matrix n n ℂ} (h : X ≤ Y) (E : Matrix n m ℂ) :
    Eᴴ * X * E ≤ Eᴴ * Y * E := by
  rw [Matrix.le_iff] at h ⊢
  have hp := h.conjTranspose_mul_mul_same E
  have heq : Eᴴ * (Y - X) * E = Eᴴ * Y * E - Eᴴ * X * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [heq] at hp

theorem conj_le_conj' {n m : Type*} [Fintype n] [Fintype m]
    {X Y : Matrix n n ℂ} (h : X ≤ Y) (B : Matrix m n ℂ) :
    B * X * Bᴴ ≤ B * Y * Bᴴ := by
  rw [Matrix.le_iff] at h ⊢
  have hp := h.mul_mul_conjTranspose_same B
  have heq : B * (Y - X) * Bᴴ = B * Y * Bᴴ - B * X * Bᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [heq] at hp

theorem posDef_of_smul_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} {γ : ℝ} (hγ : 0 < γ)
    (h : γ • (1 : Matrix n n ℂ) ≤ C) : C.PosDef := by
  have hsm : (γ • (1 : Matrix n n ℂ)).PosDef := by
    have hsmC : ((γ : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
      rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.PosDef.diagonal fun _ => by
        exact Complex.zero_lt_real.mpr hγ
    have heq : γ • (1 : Matrix n n ℂ) = (γ : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j
      simp [Complex.real_smul]
    rw [heq]
    exact hsmC
  have hdiff : (C - γ • (1 : Matrix n n ℂ)).PosSemidef := Matrix.le_iff.mp h
  have hp := hsm.add_posSemidef hdiff
  simpa using hp

theorem commute_nonsing_inv {n : Type*} [Fintype n] [DecidableEq n]
    {X M : Matrix n n ℂ} [Invertible M] (h : X * M = M * X) :
    X * M⁻¹ = M⁻¹ * X := by
  calc
    X * M⁻¹ = M⁻¹ * M * (X * M⁻¹) := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]
    _ = M⁻¹ * (M * X) * M⁻¹ := by simp only [Matrix.mul_assoc]
    _ = M⁻¹ * (X * M) * M⁻¹ := by rw [h]
    _ = M⁻¹ * X := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]

theorem inv_le_smul_one_of_smul_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {γ : ℝ} (hγ : 0 < γ)
    (h : γ • (1 : Matrix n n ℂ) ≤ M) :
    M⁻¹ ≤ γ⁻¹ • (1 : Matrix n n ℂ) := by
  have hM : M.PosDef := posDef_of_smul_one_le hγ h
  have hRu : IsUnit (CFC.sqrt M) := sqrt_isUnit hM
  haveI := hRu.invertible
  set R := (CFC.sqrt M)⁻¹ with hR
  have hRH : Rᴴ = R := sqrt_inv_isHermitian M
  have hRR : R * R = M⁻¹ := sqrt_inv_mul_sqrt_inv hM
  have hRMR : R * M * R = 1 := by
    have hMs : M = CFC.sqrt M * CFC.sqrt M :=
      (sqrt_mul_self_eq M hM.posSemidef).symm
    rw [hMs, hR, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (CFC.sqrt M) (CFC.sqrt M),
      ← Matrix.mul_assoc (CFC.sqrt M)⁻¹ (CFC.sqrt M) (CFC.sqrt M),
      Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hconj := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same R
  rw [hRH] at hconj
  have hval : R * (M - γ • (1 : Matrix n n ℂ)) * R = 1 - γ • M⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hRMR, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hRR]
  rw [hval] at hconj
  rw [Matrix.le_iff]
  have hscaled := hconj.smul (a := γ⁻¹) (inv_pos.mpr hγ).le
  have heq : γ⁻¹ • ((1 : Matrix n n ℂ) - γ • M⁻¹) =
      γ⁻¹ • (1 : Matrix n n ℂ) - M⁻¹ := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  rwa [heq] at hscaled

theorem smul_one_le_inv_of_le_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {b : ℝ} (hb : 0 < b) (hM : M.PosDef)
    (h : M ≤ b • (1 : Matrix n n ℂ)) :
    b⁻¹ • (1 : Matrix n n ℂ) ≤ M⁻¹ := by
  have hRu : IsUnit (CFC.sqrt M) := sqrt_isUnit hM
  haveI := hRu.invertible
  set R := (CFC.sqrt M)⁻¹ with hR
  have hRH : Rᴴ = R := sqrt_inv_isHermitian M
  have hRR : R * R = M⁻¹ := sqrt_inv_mul_sqrt_inv hM
  have hRMR : R * M * R = 1 := by
    have hMs : M = CFC.sqrt M * CFC.sqrt M :=
      (sqrt_mul_self_eq M hM.posSemidef).symm
    rw [hMs, hR, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (CFC.sqrt M) (CFC.sqrt M),
      ← Matrix.mul_assoc (CFC.sqrt M)⁻¹ (CFC.sqrt M) (CFC.sqrt M),
      Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hconj := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same R
  rw [hRH] at hconj
  have hval : R * (b • (1 : Matrix n n ℂ) - M) * R = b • M⁻¹ - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hRMR, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hRR]
  rw [hval] at hconj
  rw [Matrix.le_iff]
  have hscaled := hconj.smul (a := b⁻¹) (inv_pos.mpr hb).le
  have heq : b⁻¹ • (b • M⁻¹ - (1 : Matrix n n ℂ)) =
      M⁻¹ - b⁻¹ • (1 : Matrix n n ℂ) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  rwa [heq] at hscaled

theorem mul_conjTranspose_le_smul_one {b T : Type*} [Fintype b] [Fintype T]
    [DecidableEq b] [DecidableEq T] {D : Matrix b T ℂ} {d : ℝ} (hd : ‖D‖ ≤ d) :
    D * Dᴴ ≤ (d ^ 2 : ℝ) • (1 : Matrix b b ℂ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have h1 : (D * Dᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
    have h2 : ((d ^ 2 : ℝ) • (1 : Matrix b b ℂ)).IsHermitian := by
      change (((d ^ 2 : ℝ) • (1 : Matrix b b ℂ))ᴴ) =
        (d ^ 2 : ℝ) • (1 : Matrix b b ℂ)
      simp
    exact h2.sub h1
  · have hexp : star x ⬝ᵥ (((d ^ 2 : ℝ) • (1 : Matrix b b ℂ) - D * Dᴴ) *ᵥ x) =
        (d ^ 2 : ℝ) • (star x ⬝ᵥ x) - star (Dᴴ *ᵥ x) ⬝ᵥ (Dᴴ *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      congr 1
      rw [← Matrix.mulVec_mulVec, ← star_mulVec_dotProduct D x (Dᴴ *ᵥ x)]
    rw [hexp]
    have hxsq : star x ⬝ᵥ x =
        ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 : ℝ) : ℂ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
        inner_self_eq_norm_sq_to_K]
      norm_num
    have hwsq : star (Dᴴ *ᵥ x) ⬝ᵥ (Dᴴ *ᵥ x) =
        ((‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
        inner_self_eq_norm_sq_to_K]
      norm_num
    rw [hxsq, hwsq]
    have hbnd : ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ≤
        d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ := by
      have hDH : ‖Dᴴ‖ = ‖D‖ := Matrix.l2_opNorm_conjTranspose D
      calc
        ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖
            ≤ ‖Dᴴ‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ :=
              Matrix.l2_opNorm_mulVec Dᴴ (WithLp.toLp 2 x : EuclideanSpace ℂ b)
        _ ≤ d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ := by
          rw [hDH]
          gcongr
    have hreal : ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 ≤
        d ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T),
        norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ b)]
    have hcast : ((d ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2
        - ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ) =
        (d ^ 2 : ℝ) • ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 : ℝ) : ℂ) -
          ((‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp [Complex.real_smul]
    rw [← hcast, Complex.zero_le_real]
    linarith

end MatrixLoewnerInverseBounds
end NCG
