/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact norm of a finite Dirac off-diagonal block

The norm throughout is the Euclidean (L2) operator norm on matrices.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG.FiniteSpectralizationBlockNormExact

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

abbrev euclideanCLM {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (A : Matrix M N ℂ) :
    EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ M :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

def leftPart (z : EuclideanSpace ℂ (I ⊕ J)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => z (Sum.inl i))

def rightPart (z : EuclideanSpace ℂ (I ⊕ J)) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => z (Sum.inr j))

def leftEmbed (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ (I ⊕ J) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun _ => 0))

theorem norm_sq_split (z : EuclideanSpace ℂ (I ⊕ J)) :
    ‖z‖ ^ 2 = ‖leftPart z‖ ^ 2 + ‖rightPart z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, leftPart, rightPart]
  rw [Fintype.sum_sum_type]

@[simp] theorem leftPart_leftEmbed (x : EuclideanSpace ℂ I) :
    leftPart (leftEmbed x : EuclideanSpace ℂ (I ⊕ J)) = x := by
  apply WithLp.ofLp_injective
  rfl

@[simp] theorem rightPart_leftEmbed (x : EuclideanSpace ℂ I) :
    rightPart (leftEmbed x : EuclideanSpace ℂ (I ⊕ J)) = 0 := by
  apply WithLp.ofLp_injective
  funext j
  rfl

@[simp] theorem norm_leftEmbed (x : EuclideanSpace ℂ I) :
    ‖(leftEmbed x : EuclideanSpace ℂ (I ⊕ J))‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_split, leftPart_leftEmbed, rightPart_leftEmbed, norm_zero,
    zero_pow, add_zero]
  omega

def offDiagonal (B : Matrix J I ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 0 (-Bᴴ) B 0

theorem offDiagonal_apply_leftPart (B : Matrix J I ℂ)
    (z : EuclideanSpace ℂ (I ⊕ J)) :
    leftPart (euclideanCLM (offDiagonal B) z) =
      euclideanCLM (-Bᴴ) (rightPart z) := by
  apply WithLp.ofLp_injective
  funext i
  change (Matrix.toEuclideanLin (offDiagonal B) z).ofLp (Sum.inl i) =
    (Matrix.toEuclideanLin (-Bᴴ) (rightPart z)).ofLp i
  rw [Matrix.ofLp_toEuclideanLin_apply,
    Matrix.ofLp_toEuclideanLin_apply]
  change (∑ k : I ⊕ J, offDiagonal B (Sum.inl i) k * z k) =
    ∑ j : J, (-Bᴴ) i j * z (Sum.inr j)
  rw [Fintype.sum_sum_type]
  simp [offDiagonal]

theorem offDiagonal_apply_rightPart (B : Matrix J I ℂ)
    (z : EuclideanSpace ℂ (I ⊕ J)) :
    rightPart (euclideanCLM (offDiagonal B) z) =
      euclideanCLM B (leftPart z) := by
  apply WithLp.ofLp_injective
  funext j
  change (Matrix.toEuclideanLin (offDiagonal B) z).ofLp (Sum.inr j) =
    (Matrix.toEuclideanLin B (leftPart z)).ofLp j
  rw [Matrix.ofLp_toEuclideanLin_apply,
    Matrix.ofLp_toEuclideanLin_apply]
  change (∑ k : I ⊕ J, offDiagonal B (Sum.inr j) k * z k) =
    ∑ i : I, B j i * z (Sum.inl i)
  rw [Fintype.sum_sum_type]
  simp [offDiagonal]

theorem offDiagonal_apply_leftEmbed (B : Matrix J I ℂ)
    (x : EuclideanSpace ℂ I) :
    rightPart (euclideanCLM (offDiagonal B) (leftEmbed x)) =
      euclideanCLM B x := by
  rw [offDiagonal_apply_rightPart, leftPart_leftEmbed]

/-- The Euclidean operator norm of the Dirac off-diagonal block is exactly
the norm of its differential block. -/
theorem norm_offDiagonal (B : Matrix J I ℂ) :
    ‖offDiagonal B‖ = ‖B‖ := by
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  let S := euclideanCLM (offDiagonal B)
  let T := euclideanCLM B
  change ‖S‖ = ‖T‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound S (norm_nonneg T)
    intro z
    have hleft :
        ‖euclideanCLM (-Bᴴ) (rightPart z)‖
          ≤ ‖T‖ * ‖rightPart z‖ := by
      calc
        _ ≤ ‖-Bᴴ‖ * ‖rightPart z‖ :=
          (euclideanCLM (-Bᴴ)).le_opNorm _
        _ = ‖T‖ * ‖rightPart z‖ := by
          change ‖-Bᴴ‖ * ‖rightPart z‖ = ‖B‖ * ‖rightPart z‖
          rw [norm_neg, Matrix.l2_opNorm_conjTranspose]
    have hright :
        ‖euclideanCLM B (leftPart z)‖
          ≤ ‖T‖ * ‖leftPart z‖ := by
      exact (euclideanCLM B).le_opNorm _
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
      (norm_nonneg z))).mp
    rw [norm_sq_split]
    rw [offDiagonal_apply_leftPart, offDiagonal_apply_rightPart]
    rw [mul_pow, norm_sq_split, mul_add]
    nlinarith [sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
      (norm_nonneg (rightPart z))) |>.2 hleft,
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
      (norm_nonneg (leftPart z))) |>.2 hright]
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg S)
    intro x
    have hs := S.le_opNorm (leftEmbed x)
    have hpart :
        ‖euclideanCLM B x‖ ≤
          ‖euclideanCLM (offDiagonal B) (leftEmbed x)‖ := by
      rw [← offDiagonal_apply_leftEmbed]
      have hsquare := norm_sq_split
        (euclideanCLM (offDiagonal B) (leftEmbed x))
      have hnonneg : 0 ≤
          ‖leftPart (euclideanCLM (offDiagonal B)
            (leftEmbed x))‖ ^ 2 := sq_nonneg _
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      nlinarith
    calc
      ‖T x‖ = ‖euclideanCLM B x‖ := rfl
      _ ≤ ‖euclideanCLM (offDiagonal B) (leftEmbed x)‖ := hpart
      _ ≤ ‖S‖ * ‖leftEmbed x‖ := hs
      _ = ‖S‖ * ‖x‖ := by rw [norm_leftEmbed]

end

end NCG.FiniteSpectralizationBlockNormExact
