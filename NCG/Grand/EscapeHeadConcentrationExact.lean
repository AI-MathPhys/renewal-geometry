/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProjectionAndReturnIdentities
import NCG.Grand.JointSourceUniversality
import NCG.Grand.PositiveOperatorNormBridgeExact

/-!
# Quantitative escape-to-head concentration

This file closes the operator-theoretic gap in
`thm:GT-escape-head-concentration`.  The deficit estimates are derived from an
actual positive block contraction, rather than supplied as scalar hypotheses.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace EscapeHeadConcentration

/-- Euclidean norm of a finite coordinate vector. -/
noncomputable def eNorm {i : Type*} [Fintype i] (x : i → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖

theorem eNorm_nonneg {i : Type*} [Fintype i] (x : i → ℂ) : 0 ≤ eNorm x :=
  norm_nonneg _

/-- Each summand of a Hilbert direct sum has norm at most the full vector. -/
theorem eNorm_left_le_sumElim {h t : Type*} [Fintype h] [Fintype t]
    (x : h → ℂ) (y : t → ℂ) : eNorm x ≤ eNorm (Sum.elim x y) := by
  apply (sq_le_sq₀ (eNorm_nonneg x) (eNorm_nonneg (Sum.elim x y))).mp
  simp only [eNorm, PositiveNormBridge.norm_sq_eq_re_dotProduct,
    WithLp.ofLp_toLp]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.star_apply]
  have hy : 0 ≤ ∑ i, (star (y i) * y i).re := by
    exact Finset.sum_nonneg fun i _ => by
      simp [Complex.star_def, Complex.mul_re]
      nlinarith [sq_nonneg (y i).re, sq_nonneg (y i).im]
  simp only [Complex.add_re, Complex.re_sum]
  linarith

theorem eNorm_right_le_sumElim {h t : Type*} [Fintype h] [Fintype t]
    (x : h → ℂ) (y : t → ℂ) : eNorm y ≤ eNorm (Sum.elim x y) := by
  apply (sq_le_sq₀ (eNorm_nonneg y) (eNorm_nonneg (Sum.elim x y))).mp
  simp only [eNorm, PositiveNormBridge.norm_sq_eq_re_dotProduct,
    WithLp.ofLp_toLp]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.star_apply]
  have hx : 0 ≤ ∑ i, (star (x i) * x i).re := by
    exact Finset.sum_nonneg fun i _ => by
      simp [Complex.star_def, Complex.mul_re]
      nlinarith [sq_nonneg (x i).re, sq_nonneg (x i).im]
  simp only [Complex.add_re, Complex.re_sum]
  linarith

/-- A positive contraction satisfies `P² ≤ P`. -/
theorem positive_contraction_sq_le {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) (hIP : (1 - P).PosSemidef) :
    (P - P * P).PosSemidef := by
  let R := CFC.sqrt P
  have hR : R.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hRR : R * R = P := by rw [← sq, CFC.sq_sqrt P]
  have hcong := hIP.conjTranspose_mul_mul_same R
  have hRH : Rᴴ = R := hR.1.eq
  have hRP : R * P = P * R := by
    rw [← hRR]
    simp only [Matrix.mul_assoc]
  have heq : Rᴴ * (1 - P) * R = P - P * P := by
    rw [hRH, Matrix.mul_sub, Matrix.mul_one, hRP, Matrix.sub_mul,
      hRR, Matrix.mul_assoc, hRR]
  exact heq ▸ hcong

/-- For a positive contraction, the norm of the deficit applied to a vector
is bounded by the square root of its Rayleigh deficit. -/
theorem positive_contraction_apply_le_sqrt {n : Type*}
    [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) (hIP : (1 - P).PosSemidef)
    (u : n → ℂ) :
    eNorm (P *ᵥ u) ≤ Real.sqrt ((star u ⬝ᵥ (P *ᵥ u)).re) := by
  have hsq := positive_contraction_sq_le P hP hIP
  have hform := hsq.dotProduct_mulVec_nonneg u
  have hPH : Pᴴ = P := hP.1.eq
  have hnormsq : eNorm (P *ᵥ u) ^ 2 =
      (star u ⬝ᵥ ((P * P) *ᵥ u)).re := by
    rw [eNorm, PositiveNormBridge.norm_sq_eq_re_dotProduct,
      WithLp.ofLp_toLp,
      gram_realization_inner, hPH]
  have hle : eNorm (P *ᵥ u) ^ 2 ≤ (star u ⬝ᵥ (P *ᵥ u)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.nonneg_iff] at hform
    rw [hnormsq]
    exact sub_nonneg.mp hform.1
  exact Real.le_sqrt_of_sq_le hle

/-- Matrix operator norm controls the Euclidean norm of every multiplied
vector. -/
theorem eNorm_mulVec_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n]
    (A : Matrix m n ℂ) (x : n → ℂ) :
    eNorm (A *ᵥ x) ≤ ‖A‖ * eNorm x := by
  exact Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)

theorem eNorm_add_le {i : Type*} [Fintype i] (x y : i → ℂ) :
    eNorm (x + y) ≤ eNorm x + eNorm y := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ i) (WithLp.toLp 2 y)

/-- Exact operator derivation of both boxed escape estimates (ER.2)--(ER.3). -/
theorem escape_head_concentration
    {h t : Type*} [Fintype h] [Fintype t]
    [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (hT : (Matrix.fromBlocks A B Bᴴ D).PosSemidef)
    (hIT : (1 - Matrix.fromBlocks A B Bᴴ D).PosSemidef)
    (x : h → ℂ) (y : t → ℂ)
    (hunit : eNorm (Sum.elim x y) = 1)
    (hq : ‖D‖ < 1) :
    let δ := (star (Sum.elim x y) ⬝ᵥ
      ((1 - Matrix.fromBlocks A B Bᴴ D) *ᵥ Sum.elim x y)).re
    eNorm y ≤ (‖B‖ + Real.sqrt δ) / (1 - ‖D‖) ∧
      eNorm ((1 - A) *ᵥ x) ≤ Real.sqrt δ + ‖B‖ * eNorm y := by
  let T := Matrix.fromBlocks A B Bᴴ D
  let P := 1 - T
  let u := Sum.elim x y
  let δ := (star u ⬝ᵥ (P *ᵥ u)).re
  have hP : P.PosSemidef := by simpa [P, T] using hIT
  have hIP : (1 - P).PosSemidef := by
    have : (1 - (1 - T) : Matrix (h ⊕ t) (h ⊕ t) ℂ) = T := by module
    simpa [P, this] using hT
  have hdef : eNorm (P *ᵥ u) ≤ Real.sqrt δ :=
    positive_contraction_apply_le_sqrt P hP hIP u
  have hPu : P *ᵥ u = Sum.elim ((1 - A) *ᵥ x - B *ᵥ y)
      ((1 - D) *ᵥ y - Bᴴ *ᵥ x) := by
    simp only [P, T, u]
    rw [show (1 - Matrix.fromBlocks A B Bᴴ D) =
      Matrix.fromBlocks (1 - A) (-B) (-B)ᴴ (1 - D) by
        rw [← Matrix.fromBlocks_one]
        ext i j
        rcases i with i | i <;> rcases j with j | j <;>
          simp [Matrix.one_apply]]
    rw [Matrix.fromBlocks_mulVec]
    ext i
    rcases i with i | i <;> simp [Matrix.neg_mulVec] <;> ring
  have hheadDef : eNorm ((1 - A) *ᵥ x - B *ᵥ y) ≤ Real.sqrt δ := by
    calc
      eNorm ((1 - A) *ᵥ x - B *ᵥ y)
          ≤ eNorm (P *ᵥ u) := by rw [hPu]; exact eNorm_left_le_sumElim _ _
      _ ≤ Real.sqrt δ := hdef
  have htailDef : eNorm ((1 - D) *ᵥ y - Bᴴ *ᵥ x) ≤ Real.sqrt δ := by
    calc
      eNorm ((1 - D) *ᵥ y - Bᴴ *ᵥ x)
          ≤ eNorm (P *ᵥ u) := by rw [hPu]; exact eNorm_right_le_sumElim _ _
      _ ≤ Real.sqrt δ := hdef
  have hx1 : eNorm x ≤ 1 := by
    rw [← hunit]
    exact eNorm_left_le_sumElim x y
  have hDy : eNorm (D *ᵥ y) ≤ ‖D‖ * eNorm y := eNorm_mulVec_le D y
  have hBx : eNorm (Bᴴ *ᵥ x) ≤ ‖B‖ := by
    calc
      eNorm (Bᴴ *ᵥ x) ≤ ‖Bᴴ‖ * eNorm x := eNorm_mulVec_le Bᴴ x
      _ = ‖B‖ * eNorm x := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left hx1 (norm_nonneg B)
      _ = ‖B‖ := mul_one _
  have hBD : eNorm ((1 - D) *ᵥ y) ≤ Real.sqrt δ + ‖B‖ := by
    calc
      eNorm ((1 - D) *ᵥ y)
          = eNorm (((1 - D) *ᵥ y - Bᴴ *ᵥ x) + Bᴴ *ᵥ x) := by
              apply congrArg eNorm
              funext i
              simp
      _ ≤ eNorm ((1 - D) *ᵥ y - Bᴴ *ᵥ x) + eNorm (Bᴴ *ᵥ x) :=
        eNorm_add_le _ _
      _ ≤ Real.sqrt δ + ‖B‖ := add_le_add htailDef hBx
  have hlower : (1 - ‖D‖) * eNorm y ≤ eNorm ((1 - D) *ᵥ y) := by
    have htri : eNorm y ≤ eNorm ((1 - D) *ᵥ y) + eNorm (D *ᵥ y) := by
      calc
        eNorm y = eNorm ((1 - D) *ᵥ y + D *ᵥ y) := by
          apply congrArg eNorm
          funext i
          simp [Matrix.sub_mulVec]
        _ ≤ _ := eNorm_add_le _ _
    nlinarith
  have htailScalar : (1 - ‖D‖) * eNorm y ≤ ‖B‖ + Real.sqrt δ := by
    linarith
  have htail : eNorm y ≤ (‖B‖ + Real.sqrt δ) / (1 - ‖D‖) :=
    FiniteProjectionAndReturnIdentities.escape_tail_bound
      ‖D‖ ‖B‖ δ (eNorm y) hq htailScalar
  have hBy : eNorm (B *ᵥ y) ≤ ‖B‖ * eNorm y := eNorm_mulVec_le B y
  have hhead : eNorm ((1 - A) *ᵥ x) ≤ Real.sqrt δ + ‖B‖ * eNorm y := by
    calc
      eNorm ((1 - A) *ᵥ x)
          = eNorm (((1 - A) *ᵥ x - B *ᵥ y) + B *ᵥ y) := by
              apply congrArg eNorm
              funext i
              simp
      _ ≤ eNorm ((1 - A) *ᵥ x - B *ᵥ y) + eNorm (B *ᵥ y) := eNorm_add_le _ _
      _ ≤ Real.sqrt δ + ‖B‖ * eNorm y := add_le_add hheadDef hBy
  exact ⟨htail, hhead⟩

end EscapeHeadConcentration
end NCG
