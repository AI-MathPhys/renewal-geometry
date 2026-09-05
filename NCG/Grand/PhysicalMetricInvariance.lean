/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandAudit
import NCG.Grand.SqrtPolar

/-!
# Positive-congruence invariance of word-Gram hierarchies

This module completes `thm:metric-independence` beyond its operator sandwich:
the physical and regular Grams have identical kernels and ranks at every word
depth, hence identical flat-depth and relation reconstructions.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- A finite metric operator is uniquely determined by all of its
sesquilinear matrix coefficients. -/
theorem metricOperator_unique {n : Type*} [Fintype n] [DecidableEq n]
    (G H : Matrix n n ℂ)
    (hcoeff : ∀ a b : n → ℂ,
      star a ⬝ᵥ (G *ᵥ b) = star a ⬝ᵥ (H *ᵥ b)) : G = H := by
  ext i j
  have h := hcoeff (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

/-- A positive-definite congruence Gram has exactly the synthesis kernel. -/
theorem metricGram_kernel_eq {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (G : Matrix n n ℂ) (hG : G.PosDef) (W : Matrix n r ℂ) :
    LinearMap.ker (Wᴴ * G * W).mulVecLin = LinearMap.ker W.mulVecLin := by
  have hSsq : (CFC.sqrt G)ᴴ * CFC.sqrt G = G := by
    rw [sqrt_isHermitian G,
      sqrt_mul_self_eq G hG.posSemidef]
  have hgram : Wᴴ * G * W =
      (CFC.sqrt G * W)ᴴ * (CFC.sqrt G * W) := by
    calc
      Wᴴ * G * W = Wᴴ * ((CFC.sqrt G)ᴴ * CFC.sqrt G) * W := by rw [hSsq]
      _ = (CFC.sqrt G * W)ᴴ * (CFC.sqrt G * W) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  rw [hgram, Matrix.ker_mulVecLin_conjTranspose_mul_self]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hSdet : IsUnit (CFC.sqrt G).det :=
    (CFC.sqrt G).isUnit_iff_isUnit_det.mp (sqrt_isUnit hG)
  constructor
  · intro h
    have hleft := congrArg (fun x => (CFC.sqrt G)⁻¹ *ᵥ x) h
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul (CFC.sqrt G) hSdet,
      Matrix.one_mul] at hleft
    exact hleft
  · intro h
    calc
      (CFC.sqrt G * W) *ᵥ v = CFC.sqrt G *ᵥ (W *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h, Matrix.mulVec_zero]

/-- Therefore physical and regular word Grams have the same kernel. -/
theorem physical_regular_gram_kernel_eq
    {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (G : Matrix n n ℂ) (hG : G.PosDef) (W : Matrix n r ℂ) :
    LinearMap.ker (Wᴴ * G * W).mulVecLin =
      LinearMap.ker (Wᴴ * W).mulVecLin := by
  rw [metricGram_kernel_eq G hG W,
    Matrix.ker_mulVecLin_conjTranspose_mul_self]

/-- Positive congruence also preserves the Gram rank. -/
theorem physical_regular_gram_rank_eq
    {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (G : Matrix n n ℂ) (hG : G.PosDef) (W : Matrix n r ℂ) :
    (Wᴴ * G * W).rank = (Wᴴ * W).rank := by
  have hSsq : (CFC.sqrt G)ᴴ * CFC.sqrt G = G := by
    rw [sqrt_isHermitian G,
      sqrt_mul_self_eq G hG.posSemidef]
  have hgram : Wᴴ * G * W =
      (CFC.sqrt G * W)ᴴ * (CFC.sqrt G * W) := by
    calc
      Wᴴ * G * W = Wᴴ * ((CFC.sqrt G)ᴴ * CFC.sqrt G) * W := by rw [hSsq]
      _ = (CFC.sqrt G * W)ᴴ * (CFC.sqrt G * W) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  have hSdet : IsUnit (CFC.sqrt G).det :=
    (CFC.sqrt G).isUnit_iff_isUnit_det.mp (sqrt_isUnit hG)
  calc
    (Wᴴ * G * W).rank = (CFC.sqrt G * W).rank := by
      rw [hgram, Matrix.rank_conjTranspose_mul_self]
    _ = W.rank := Matrix.rank_mul_eq_right_of_isUnit_det _ _ hSdet
    _ = (Wᴴ * W).rank := (Matrix.rank_conjTranspose_mul_self W).symm

/-- Exact hierarchy package: relations, ranks, and every adjacent flat-depth
test are metric independent. -/
theorem metricWordHierarchy_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (hG : G.PosDef)
    (R : ℕ → Type*) [∀ d, Fintype (R d)] [∀ d, DecidableEq (R d)]
    (W : ∀ d, Matrix n (R d) ℂ) :
    (∀ d, LinearMap.ker ((W d)ᴴ * G * W d).mulVecLin =
      LinearMap.ker ((W d)ᴴ * W d).mulVecLin)
    ∧ (∀ d, ((W d)ᴴ * G * W d).rank = ((W d)ᴴ * W d).rank)
    ∧ (∀ d, (((W (d + 1))ᴴ * G * W (d + 1)).rank =
          ((W d)ᴴ * G * W d).rank) ↔
        (((W (d + 1))ᴴ * W (d + 1)).rank =
          ((W d)ᴴ * W d).rank)) := by
  refine ⟨fun d => physical_regular_gram_kernel_eq G hG (W d),
    fun d => physical_regular_gram_rank_eq G hG (W d), ?_⟩
  intro d
  rw [physical_regular_gram_rank_eq G hG (W (d + 1)),
    physical_regular_gram_rank_eq G hG (W d)]

end NCG
