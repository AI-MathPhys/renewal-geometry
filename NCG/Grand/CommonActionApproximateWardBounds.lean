/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CommonActionRouter
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.SchurRedheffer
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib

/-!
# Approximate Ward bounds for a common action

This file proves the quantitative clauses of the common-action router theorem.
The Ward graph residual splits into its source-range component and the Schur
innovation, so a small Ward quadratic form bounds the Schur residual.  A
closed-range Moore--Penrose margin then gives the stated operator-norm router
estimate.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG

/-- The action source along the graph direction `(-W y, y)`. -/
def commonActionWardResidual {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ) : Matrix (Fin h) (Fin e) ℂ :=
  BE - BΓ * W

/-- Exact orthogonal splitting of the Ward quadratic form into the Schur
innovation and the component retained by the first source range. -/
theorem commonActionWardResidual_gram_decomposition {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ) :
    (commonActionWardResidual BΓ BE W)ᴴ *
        commonActionWardResidual BΓ BE W =
      sourceSchurResidual BΓ BE +
        (sourceRangeProjection BΓ * commonActionWardResidual BΓ BE W)ᴴ *
          (sourceRangeProjection BΓ * commonActionWardResidual BΓ BE W) := by
  let P := sourceRangeProjection BΓ
  let R := commonActionWardResidual BΓ BE W
  obtain ⟨hPH, hP2, hPB⟩ :=
    (sourceGramPseudoinverse_projection BΓ).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  change P * BΓ = BΓ at hPB
  have hQB : (1 - P) * R = (1 - P) * BE := by
    dsimp only [R, commonActionWardResidual]
    rw [Matrix.mul_sub]
    have hz : (1 - P) * BΓ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_self]
    rw [← Matrix.mul_assoc, hz, Matrix.zero_mul, sub_zero]
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hSE : sourceSchurResidual BΓ BE =
      ((1 - P) * R)ᴴ * ((1 - P) * R) := by
    rw [hQB, sourceSchurResidual_eq_orthogonalResidual]
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - P), hQ2]
  have hdec : R = P * R + (1 - P) * R := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have hcross : (P * R)ᴴ * ((1 - P) * R) = 0 := by
    rw [Matrix.conjTranspose_mul, hPH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, Matrix.mul_sub, Matrix.mul_one,
      hP2, sub_self, Matrix.zero_mul, Matrix.mul_zero]
  have hcross' : ((1 - P) * R)ᴴ * (P * R) = 0 := by
    have ht := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using ht
  change Rᴴ * R = _
  conv_lhs => rw [hdec]
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, hcross, hcross']
  rw [← hSE]
  abel

/-- The Schur innovation is below every Ward graph quadratic form. -/
theorem commonAction_schur_le_wardResidual {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ) :
    ((commonActionWardResidual BΓ BE W)ᴴ *
        commonActionWardResidual BΓ BE W -
      sourceSchurResidual BΓ BE).PosSemidef := by
  rw [commonActionWardResidual_gram_decomposition, add_sub_cancel_left]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Approximate Ward symmetry bounds the Schur innovation by the same scalar
quadratic error. -/
theorem commonAction_approximateWard_schur_bound {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ)
    (ε : ℝ)
    (hWard : (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) -
      (commonActionWardResidual BΓ BE W)ᴴ *
        commonActionWardResidual BΓ BE W).PosSemidef) :
    (sourceSchurResidual BΓ BE).PosSemidef ∧
      ((((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) -
        sourceSchurResidual BΓ BE).PosSemidef) := by
  refine ⟨sourceSchurResidual_posSemidef BΓ BE, ?_⟩
  have hdiff := commonAction_schur_le_wardResidual BΓ BE W
  have hadd := hWard.add hdiff
  convert hadd using 1 <;> module

/-- A scalar upper Loewner bound on `RᴴR` gives the corresponding spectral
operator-norm bound on `R`. -/
theorem l2_opNorm_le_of_conjTranspose_mul_self_le_scalar
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (R : Matrix m n ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - Rᴴ * R).PosSemidef) :
    ‖R‖ ≤ ε := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hε ?_
  intro x
  have hq := hbound.re_dotProduct_nonneg (WithLp.ofLp x)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hq
  simp only [dotProduct_sub, dotProduct_smul] at hq
  rw [← gram_realization_inner R] at hq
  rw [star_dot_self, star_dot_self] at hq
  let y : EuclideanSpace ℂ m :=
    (EuclideanSpace.equiv m ℂ).symm (R *ᵥ WithLp.ofLp x)
  change ‖y‖ ≤ ε * ‖x‖
  have hy : ‖y‖ ^ 2 = ∑ i, Complex.normSq ((R *ᵥ WithLp.ofLp x) i) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.normSq_eq_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hx : ‖x‖ ^ 2 = ∑ i, Complex.normSq ((WithLp.ofLp x) i) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.normSq_eq_norm_sq]
  rw [← hy, ← hx] at hq
  change 0 ≤ ((↑(ε ^ 2) : ℂ) * ↑(‖x‖ ^ 2) - ↑(‖y‖ ^ 2)).re at hq
  norm_num at hq
  simp only [← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hq
  nlinarith [norm_nonneg y, norm_nonneg x,
    mul_nonneg hε (norm_nonneg x)]

/-- The Moore--Penrose lower-margin formulation used for a closed source
range: it is the sharp finite-dimensional form of `GΓ ⪰ m² I` on its support. -/
def SourceSupportLowerMargin {h g : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ) (m : ℝ) : Prop :=
  ‖sourceGramPseudoinverse BΓ‖ ≤ (m ^ 2)⁻¹

/-- Exact router-difference formula on the supported source coefficients. -/
theorem commonAction_routerDifference {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ)
    (hW : sourceGramPseudoinverse BΓ * (BΓᴴ * BΓ) * W = W) :
    sourceGramPseudoinverse BΓ * (BΓᴴ * BE) - W =
      sourceGramPseudoinverse BΓ * BΓᴴ *
        commonActionWardResidual BΓ BE W := by
  have hterm : sourceGramPseudoinverse BΓ * BΓᴴ * (BΓ * W) = W := by
    simpa only [Matrix.mul_assoc] using hW
  rw [commonActionWardResidual, Matrix.mul_sub, hterm]
  simp only [Matrix.mul_assoc]

/-- Exact Ward symmetry gives the Moore--Penrose router and zero Schur
innovation on the supported source coefficients, without assuming an
invertible source Gram. -/
theorem commonAction_exactWard_router {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ)
    (hC : BΓᴴ * BE = (BΓᴴ * BΓ) * W)
    (hGE : BEᴴ * BE = (BΓᴴ * BE)ᴴ * W)
    (hW : sourceGramPseudoinverse BΓ * (BΓᴴ * BΓ) * W = W) :
    sourceGramPseudoinverse BΓ * (BΓᴴ * BE) = W ∧
      BEᴴ * BE = Wᴴ * (BΓᴴ * BΓ) * W ∧
      sourceSchurResidual BΓ BE = 0 := by
  let G := BΓᴴ * BΓ
  let J := sourceGramPseudoinverse BΓ
  have hGH : Gᴴ = G := by
    dsimp only [G]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hK : J * (BΓᴴ * BE) = W := by
    rw [hC]
    simpa only [G, J, Matrix.mul_assoc] using hW
  have hGEW : BEᴴ * BE = Wᴴ * G * W := by
    rw [hGE, hC, Matrix.conjTranspose_mul, hGH]
  refine ⟨hK, hGEW, ?_⟩
  have hGJG : G * J * G = G := by
    simpa only [G, J] using (sourceGramPseudoinverse_projection BΓ).2.1
  have hterm : (BΓᴴ * BE)ᴴ * J * (BΓᴴ * BE) = Wᴴ * G * W := by
    rw [hC, Matrix.conjTranspose_mul, hGH]
    calc
      Wᴴ * G * J * (G * W) = Wᴴ * (G * J * G) * W := by
        simp only [Matrix.mul_assoc]
      _ = Wᴴ * G * W := by rw [hGJG]
  unfold sourceSchurResidual
  rw [show sourceGramPseudoinverse BΓ = J from rfl, hGEW, hterm, sub_self]

set_option maxHeartbeats 800000 in
-- Expanding the Moore--Penrose router Gram requires heavier matrix normalization.
/-- The canonical Moore--Penrose router reproduces the explained Gram part;
the unexplained remainder is exactly the source Schur residual. -/
theorem commonAction_routerGram_pythagoras {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ) :
    let G := BΓᴴ * BΓ
    let C := BΓᴴ * BE
    let K := sourceGramPseudoinverse BΓ * C
    BEᴴ * BE = Kᴴ * G * K + sourceSchurResidual BΓ BE ∧
      (sourceSchurResidual BΓ BE = 0 ↔ BEᴴ * BE = Kᴴ * G * K) := by
  dsimp only
  let G := BΓᴴ * BΓ
  let C := BΓᴴ * BE
  let J := sourceGramPseudoinverse BΓ
  change BEᴴ * BE = (J * C)ᴴ * G * (J * C) + sourceSchurResidual BΓ BE ∧
    (sourceSchurResidual BΓ BE = 0 ↔ BEᴴ * BE = (J * C)ᴴ * G * (J * C))
  obtain ⟨hJH, _, hJGJ, _, _, _⟩ := sourceGramPseudoinverse_projection BΓ
  change Jᴴ = J at hJH
  change J * G * J = J at hJGJ
  have hrouter : (J * C)ᴴ * G * (J * C) = Cᴴ * J * C := by
    rw [Matrix.conjTranspose_mul, hJH]
    calc
      Cᴴ * J * G * (J * C) = Cᴴ * (J * G * J) * C := by
        simp only [Matrix.mul_assoc]
      _ = Cᴴ * J * C := by rw [hJGJ]
  have hsum : BEᴴ * BE = (J * C)ᴴ * G * (J * C) +
      sourceSchurResidual BΓ BE := by
    rw [hrouter]
    unfold sourceSchurResidual
    change BEᴴ * BE = Cᴴ * J * C + (BEᴴ * BE - Cᴴ * J * C)
    abel
  refine ⟨hsum, ?_⟩
  constructor
  · intro hz
    calc
      BEᴴ * BE = (J * C)ᴴ * G * (J * C) + sourceSchurResidual BΓ BE := hsum
      _ = (J * C)ᴴ * G * (J * C) := by rw [hz, add_zero]
  · intro heq
    have hadd : (J * C)ᴴ * G * (J * C) + sourceSchurResidual BΓ BE =
        (J * C)ᴴ * G * (J * C) := hsum.symm.trans heq
    have hsub := congrArg
      (fun M => M - (J * C)ᴴ * G * (J * C)) hadd
    simpa only [add_sub_cancel_left, sub_self] using hsub

/-- The coefficient inclusion of the first source into a two-source sum. -/
def firstSourceCoefficientInclusion (g e : ℕ) :
    Matrix (Fin g ⊕ Fin e) (Fin g) ℂ :=
  Matrix.fromRows (1 : Matrix (Fin g) (Fin g) ℂ) 0

/-- The first-source coefficient inclusion is an isometry and hence has
operator norm at most one. -/
theorem firstSourceCoefficientInclusion_norm_le_one (g e : ℕ) :
    ‖firstSourceCoefficientInclusion g e‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖(EuclideanSpace.equiv (Fin g ⊕ Fin e) ℂ).symm
      (firstSourceCoefficientInclusion g e *ᵥ WithLp.ofLp x)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [firstSourceCoefficientInclusion, Matrix.fromRows_mulVec,
    Fintype.sum_sum_type]

/-- A source factor is bounded by the square root of the complete joint-Hessian
norm. -/
theorem firstSource_norm_le_sqrt_jointGram {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ) :
    ‖BΓ‖ ≤ Real.sqrt
      ‖(Matrix.fromCols BΓ BE)ᴴ * Matrix.fromCols BΓ BE‖ := by
  let T := Matrix.fromCols BΓ BE
  let J := firstSourceCoefficientInclusion g e
  have hTJ : T * J = BΓ := by
    dsimp only [T, J, firstSourceCoefficientInclusion]
    rw [Matrix.fromCols_mul_fromRows]
    simp
  have hnorm : ‖BΓ‖ ≤ ‖T‖ := by
    rw [← hTJ]
    exact le_trans (Matrix.l2_opNorm_mul T J)
      (mul_le_of_le_one_right (norm_nonneg T)
        (firstSourceCoefficientInclusion_norm_le_one g e))
  have hgram : ‖Tᴴ * T‖ = ‖T‖ ^ 2 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]
  rw [hgram, Real.sqrt_sq (norm_nonneg T)]
  exact hnorm

/-- Quantitative approximate-Ward router estimate.  The Hessian radius
hypothesis is the standard principal-source bound `‖BΓ‖ ≤ sqrt ‖H‖`; the
support margin is the equivalent Moore--Penrose form of `GΓ ⪰ m²I`. -/
theorem commonAction_approximateWard_router_bound {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ)
    (ε m Hnorm : ℝ)
    (hε : 0 ≤ ε) (hm : 0 < m)
    (hWard : (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) -
      (commonActionWardResidual BΓ BE W)ᴴ *
        commonActionWardResidual BΓ BE W).PosSemidef)
    (hW : sourceGramPseudoinverse BΓ * (BΓᴴ * BΓ) * W = W)
    (hmargin : SourceSupportLowerMargin BΓ m)
    (hprincipal : ‖BΓ‖ ≤ Real.sqrt Hnorm) :
    ‖sourceGramPseudoinverse BΓ * (BΓᴴ * BE) - W‖ ≤
      Real.sqrt Hnorm / m ^ 2 * ε := by
  change ‖sourceGramPseudoinverse BΓ‖ ≤ (m ^ 2)⁻¹ at hmargin
  rw [commonAction_routerDifference BΓ BE W hW]
  calc
    ‖sourceGramPseudoinverse BΓ * BΓᴴ *
        commonActionWardResidual BΓ BE W‖
        ≤ ‖sourceGramPseudoinverse BΓ‖ * ‖BΓᴴ‖ *
            ‖commonActionWardResidual BΓ BE W‖ := by
          exact le_trans (Matrix.l2_opNorm_mul _ _)
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
              (norm_nonneg _))
    _ ≤ (m ^ 2)⁻¹ * Real.sqrt Hnorm * ε := by
      rw [Matrix.l2_opNorm_conjTranspose]
      have hRnorm := l2_opNorm_le_of_conjTranspose_mul_self_le_scalar
        (commonActionWardResidual BΓ BE W) ε hε hWard
      have hinv : 0 ≤ (m ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg m)
      have hsqrt : 0 ≤ Real.sqrt Hnorm := Real.sqrt_nonneg _
      calc
        ‖sourceGramPseudoinverse BΓ‖ * ‖BΓ‖ *
            ‖commonActionWardResidual BΓ BE W‖
            ≤ ((m ^ 2)⁻¹ * Real.sqrt Hnorm) *
                ‖commonActionWardResidual BΓ BE W‖ := by
              gcongr
        _ ≤ ((m ^ 2)⁻¹ * Real.sqrt Hnorm) * ε := by
              exact mul_le_mul_of_nonneg_left hRnorm (mul_nonneg hinv hsqrt)
    _ = Real.sqrt Hnorm / m ^ 2 * ε := by
      field_simp

/-- The router estimate with `Hnorm` specialized to the literal complete
joint-Hessian norm from the manuscript. -/
theorem commonAction_approximateWard_router_bound_jointHessian {h g e : ℕ}
    (BΓ : Matrix (Fin h) (Fin g) ℂ)
    (BE : Matrix (Fin h) (Fin e) ℂ)
    (W : Matrix (Fin g) (Fin e) ℂ)
    (ε m : ℝ)
    (hε : 0 ≤ ε) (hm : 0 < m)
    (hWard : (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) -
      (commonActionWardResidual BΓ BE W)ᴴ *
        commonActionWardResidual BΓ BE W).PosSemidef)
    (hW : sourceGramPseudoinverse BΓ * (BΓᴴ * BΓ) * W = W)
    (hmargin : SourceSupportLowerMargin BΓ m) :
    ‖sourceGramPseudoinverse BΓ * (BΓᴴ * BE) - W‖ ≤
      Real.sqrt ‖(Matrix.fromCols BΓ BE)ᴴ * Matrix.fromCols BΓ BE‖ /
        m ^ 2 * ε :=
  commonAction_approximateWard_router_bound BΓ BE W ε m
    ‖(Matrix.fromCols BΓ BE)ᴴ * Matrix.fromCols BΓ BE‖
    hε hm hWard hW hmargin (firstSource_norm_le_sqrt_jointGram BΓ BE)

end NCG
