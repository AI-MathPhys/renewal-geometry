/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Locked record count, Choi rank, and minimal Naimark record
  (`thm:locked-opportunity-instrument`, Gran-Tensor manuscript)

* `locked_opportunity_instrument`: the record count
  `6·2·2 = 24` accepted plus one no-response record; the
  locked coefficient `ϑ = 576851/417942208512` is admissible
  (`0 < ϑ < 1`); the boxed mixing matrix
  `M_ϑ = ϑI + (1−ϑ)cc*` is positive definite; each displayed
  environment effect `F_∅ = (1−ϑ)M^{-1/2}cc*M^{-1/2}`,
  `F_j = ϑM^{-1/2}e_je_j*M^{-1/2}` is positive semidefinite;
  and the outcome family is a resolution of the identity
  (`F_∅ + Σ_j F_j = I`).

Rendering disclosed: the synthesis `B` of the 24 accepted Choi
vectors and the identity `J_opp = BM_ϑB*` are the declared
concrete-instrument inputs (linear independence gives rank 24);
the non-projectivity of the 25-effect POVM on the
24-dimensional environment and the explicit 25-cell Naimark
null vector `n₂₅` are the manuscript's dimension-count and
frame computation on that concrete instrument.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:locked-opportunity-instrument`. -/
theorem locked_opportunity_instrument {n : Type*} [Fintype n]
    [DecidableEq n] (c : n → ℂ) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    -- record count bookkeeping
    (6 * 2 * 2 = 24 ∧ 24 + 1 = 25)
    -- the locked coefficient is admissible
    ∧ (0 < (576851 : ℝ) / 417942208512
        ∧ (576851 : ℝ) / 417942208512 < 1)
    -- the boxed mixing matrix is positive definite
    ∧ (((θ : ℂ) • (1 : Matrix n n ℂ)
        + ((1 - θ : ℝ) : ℂ)
            • Matrix.vecMulVec c (star c)).PosDef)
    -- effects are positive semidefinite
    ∧ (∀ S : Matrix n n ℂ, Sᴴ = S →
        (((1 - θ : ℝ) : ℂ)
          • (S * Matrix.vecMulVec c (star c) * S)).PosSemidef)
    ∧ (∀ (S : Matrix n n ℂ) (j : n), Sᴴ = S →
        ((θ : ℂ)
          • (S * Matrix.single j j (1 : ℂ) * S)).PosSemidef)
    -- resolution of the identity on the environment
    ∧ (∀ M : Matrix n n ℂ, M.PosDef →
        M = (θ : ℂ) • (1 : Matrix n n ℂ)
          + ((1 - θ : ℝ) : ℂ)
              • Matrix.vecMulVec c (star c) →
        ((1 - θ : ℝ) : ℂ)
            • ((CFC.sqrt M)⁻¹ * Matrix.vecMulVec c (star c)
              * (CFC.sqrt M)⁻¹)
          + ∑ j, (θ : ℂ)
              • ((CFC.sqrt M)⁻¹ * Matrix.single j j (1 : ℂ)
                * (CFC.sqrt M)⁻¹) = 1) := by
  have hθC : (0 : ℂ) < (θ : ℂ) :=
    Complex.zero_lt_real.mpr hθ0
  have h1θ : (0 : ℂ) ≤ ((1 - θ : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by linarith)
  have hccH : (Matrix.vecMulVec c (star c)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star c
  have hsingle : ∑ j : n, Matrix.single j j (1 : ℂ) = 1 := by
    ext i k
    rw [Matrix.sum_apply]
    by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
      · intro b _ hb
        rw [Matrix.single_apply,
          if_neg (fun hand => hb hand.1)]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    · rw [Matrix.one_apply_ne hik]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hik rfl
  refine ⟨⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · have h1 : ((θ : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
      rw [Matrix.smul_one_eq_diagonal]
      rw [Matrix.posDef_diagonal_iff]
      intro i
      exact hθC
    exact h1.add_posSemidef (hccH.smul h1θ)
  · intro S hS
    refine Matrix.PosSemidef.smul ?_ h1θ
    have := hccH.mul_mul_conjTranspose_same S
    rwa [hS] at this
  · intro S j hS
    refine Matrix.PosSemidef.smul ?_ hθC.le
    have hsp : (Matrix.single j j (1 : ℂ)).PosSemidef := by
      have h : Matrix.single j j (1 : ℂ)
          = Matrix.vecMulVec (Pi.single j 1)
              (star (Pi.single j 1)) := by
        ext i k
        rw [Matrix.single_apply, Matrix.vecMulVec_apply,
          Pi.star_apply, Pi.single_apply, Pi.single_apply]
        by_cases hi : j = i <;> by_cases hk : j = k <;>
          simp [hi, hk, eq_comm]
      rw [h]
      exact Matrix.posSemidef_vecMulVec_self_star _
    have := hsp.mul_mul_conjTranspose_same S
    rwa [hS] at this
  · intro M hM hMdef
    haveI := (sqrt_isUnit hM).invertible
    have hSMS : (CFC.sqrt M)⁻¹ * M * (CFC.sqrt M)⁻¹ = 1 := by
      rw [show (CFC.sqrt M)⁻¹ * M * (CFC.sqrt M)⁻¹
          = (CFC.sqrt M)⁻¹ * (CFC.sqrt M * CFC.sqrt M)
            * (CFC.sqrt M)⁻¹ from by
        rw [sqrt_mul_self_eq M hM.posSemidef],
        ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
        Matrix.one_mul, Matrix.mul_inv_of_invertible]
    have hpull : ∑ j, (θ : ℂ)
          • ((CFC.sqrt M)⁻¹ * Matrix.single j j (1 : ℂ)
            * (CFC.sqrt M)⁻¹)
        = (θ : ℂ) • ((CFC.sqrt M)⁻¹ * (1 : Matrix n n ℂ)
            * (CFC.sqrt M)⁻¹) := by
      rw [← Finset.smul_sum]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsingle]
    rw [hpull,
      show ((1 - θ : ℝ) : ℂ)
          • ((CFC.sqrt M)⁻¹ * Matrix.vecMulVec c (star c)
            * (CFC.sqrt M)⁻¹)
        = (CFC.sqrt M)⁻¹
            * (((1 - θ : ℝ) : ℂ)
              • Matrix.vecMulVec c (star c))
            * (CFC.sqrt M)⁻¹ from by
        rw [Matrix.mul_smul, Matrix.smul_mul],
      show (θ : ℂ) • ((CFC.sqrt M)⁻¹ * (1 : Matrix n n ℂ)
            * (CFC.sqrt M)⁻¹)
        = (CFC.sqrt M)⁻¹ * ((θ : ℂ) • (1 : Matrix n n ℂ))
            * (CFC.sqrt M)⁻¹ from by
        rw [Matrix.mul_smul, Matrix.smul_mul],
      show (CFC.sqrt M)⁻¹
            * (((1 - θ : ℝ) : ℂ)
              • Matrix.vecMulVec c (star c))
            * (CFC.sqrt M)⁻¹
          + (CFC.sqrt M)⁻¹ * ((θ : ℂ) • (1 : Matrix n n ℂ))
            * (CFC.sqrt M)⁻¹
        = (CFC.sqrt M)⁻¹
            * (((1 - θ : ℝ) : ℂ)
                • Matrix.vecMulVec c (star c)
              + (θ : ℂ) • (1 : Matrix n n ℂ))
            * (CFC.sqrt M)⁻¹ from by
        rw [Matrix.mul_add, Matrix.add_mul],
      show ((1 - θ : ℝ) : ℂ) • Matrix.vecMulVec c (star c)
          + (θ : ℂ) • (1 : Matrix n n ℂ) = M from by
        rw [hMdef]; abel]
    exact hSMS

end NCG
