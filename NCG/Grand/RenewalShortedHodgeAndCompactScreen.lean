/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ShortedHodge
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.StateTightness

/-!
# Singular protected-soft Hodge short and compact spectral screen

This module replaces the faithful soft-coordinate inverse by the exact
Moore--Penrose range projection, identifies the normalized shorted action with
the Gram of the physical differential, and proves the uniform diagonal
spectral-screen estimate used in the manuscript.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG
namespace RenewalShortedHodgeAndCompactScreen

/-- Orthogonal projection onto the protected-soft range. -/
noncomputable def softProjection {y f : ℕ}
    (Z : Matrix (Fin y) (Fin f) ℂ) : Matrix (Fin y) (Fin y) ℂ :=
  sourceRangeProjection Z

/-- The Moore--Penrose formula gives a Hermitian idempotent fixing the entire
protected synthesis, even when its columns are linearly dependent. -/
theorem softProjection_properties {y f : ℕ}
    (Z : Matrix (Fin y) (Fin f) ℂ) :
    let P := softProjection Z
    Pᴴ = P ∧ P * P = P ∧ P * Z = Z := by
  simpa only [softProjection] using
    (sourceGramPseudoinverse_projection Z).2.2.2

/-- The protected-soft shorted action. -/
def shortedAction {e y : ℕ} (D : Matrix (Fin y) (Fin e) ℂ)
    (P : Matrix (Fin y) (Fin y) ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  Dᴴ * ((1 - P) * D)

/-- A Hermitian projection makes the shorted action the exact Gram of the
unprotected differential. -/
theorem shortedAction_eq_gram {e y : ℕ}
    (D : Matrix (Fin y) (Fin e) ℂ) (P : Matrix (Fin y) (Fin y) ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) :
    shortedAction D P = ((1 - P) * D)ᴴ * ((1 - P) * D) := by
  simp only [shortedAction, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, hPstar, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P D, hPid]
  abel

/-- Exact Pythagoras for arbitrary soft compensation. -/
theorem singular_shorted_pythagoras {e y f m : ℕ}
    (D : Matrix (Fin y) (Fin e) ℂ) (Z : Matrix (Fin y) (Fin f) ℂ)
    (X : Matrix (Fin e) (Fin m) ℂ) (W : Matrix (Fin f) (Fin m) ℂ) :
    let P := softProjection Z
    (D * X + Z * W)ᴴ * (D * X + Z * W) =
      ((1 - P) * (D * X))ᴴ * ((1 - P) * (D * X))
        + (P * (D * X) + Z * W)ᴴ * (P * (D * X) + Z * W) := by
  dsimp only
  obtain ⟨hPstar, hPid, hPZ⟩ := softProjection_properties Z
  have hZP : Zᴴ * softProjection Z = Zᴴ := by
    have h := congrArg Matrix.conjTranspose hPZ
    simpa only [Matrix.conjTranspose_mul, hPstar,
      Matrix.conjTranspose_conjTranspose] using h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, hPstar,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (softProjection Z) (softProjection Z) (D * X), hPid,
    ← Matrix.mul_assoc Zᴴ (softProjection Z) (D * X), hZP,
    ← Matrix.mul_assoc (softProjection Z) Z W, hPZ]
  abel

/-- The Pythagorean lower bound is attained by the Moore--Penrose
least-squares compensation. -/
theorem singular_shorted_attainment {e y f m : ℕ}
    (D : Matrix (Fin y) (Fin e) ℂ) (Z : Matrix (Fin y) (Fin f) ℂ)
    (X : Matrix (Fin e) (Fin m) ℂ) :
    let J := sourceGramPseudoinverse Z
    let P := softProjection Z
    D * X + Z * (-(J * (Zᴴ * (D * X)))) = (1 - P) * (D * X) := by
  dsimp only
  rw [Matrix.sub_mul, Matrix.one_mul]
  have hZW : Z * (-(sourceGramPseudoinverse Z * (Zᴴ * (D * X)))) =
      -(softProjection Z * (D * X)) := by
    simp only [Matrix.mul_neg, Matrix.mul_assoc, softProjection,
      sourceRangeProjection]
  rw [hZW]
  abel

/-- A scalar is the squared minimum singular value of `B` when it is the
largest uniform lower bound for the Gram quadratic form. -/
def IsSquaredMinimumSingularValue {e y : ℕ}
    (B : Matrix (Fin y) (Fin e) ℂ) (sigmaSq : ℝ) : Prop :=
  (∀ x : Fin e → ℂ,
      sigmaSq * ∑ i, Complex.normSq (x i) ≤
        (star x ⬝ᵥ ((Bᴴ * B) *ᵥ x)).re)
    ∧ ∀ mu : ℝ,
      (∀ x : Fin e → ℂ,
        mu * ∑ i, Complex.normSq (x i) ≤
          (star x ⬝ᵥ ((Bᴴ * B) *ᵥ x)).re) →
      mu ≤ sigmaSq

/-- The optimal physical Poincare constant for a normalized action Gram. -/
def IsOptimalPoincareConstant {e : ℕ}
    (A : Matrix (Fin e) (Fin e) ℂ) (lambda : ℝ) : Prop :=
  (∀ x : Fin e → ℂ,
      lambda * ∑ i, Complex.normSq (x i) ≤ (star x ⬝ᵥ (A *ᵥ x)).re)
    ∧ ∀ mu : ℝ,
      (∀ x : Fin e → ℂ,
        mu * ∑ i, Complex.normSq (x i) ≤ (star x ⬝ᵥ (A *ᵥ x)).re) →
      mu ≤ lambda

/-- The normalized shorted action is exactly the Gram of
`(I-P) D G^{-1/2}`. -/
theorem normalized_shortedAction_eq_physicalGram {e y : ℕ}
    (D : Matrix (Fin y) (Fin e) ℂ) (P : Matrix (Fin y) (Fin y) ℂ)
    (GinvHalf : Matrix (Fin e) (Fin e) ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) :
    GinvHalfᴴ * shortedAction D P * GinvHalf =
      ((1 - P) * D * GinvHalf)ᴴ * ((1 - P) * D * GinvHalf) := by
  rw [shortedAction_eq_gram D P hPstar hPid]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Hence the optimal physical Poincare constant is precisely the squared
minimum singular value of the normalized unprotected differential. -/
theorem optimalPoincareConstant_iff_squaredMinimumSingularValue {e y : ℕ}
    (D : Matrix (Fin y) (Fin e) ℂ) (P : Matrix (Fin y) (Fin y) ℂ)
    (GinvHalf : Matrix (Fin e) (Fin e) ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) (lambda : ℝ) :
    IsOptimalPoincareConstant
        (GinvHalfᴴ * shortedAction D P * GinvHalf) lambda ↔
      IsSquaredMinimumSingularValue ((1 - P) * D * GinvHalf) lambda := by
  rw [normalized_shortedAction_eq_physicalGram D P GinvHalf hPstar hPid]
  rfl

/-- Squared norm on the spectral complement of the cutoff `R`. -/
noncomputable def spectralTailNormSq {i : Type*} [Fintype i]
    (ell : i → ℝ) (R : ℝ) (x : i → ℂ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => R < ell j), Complex.normSq (x j)

/-- Diagonal spectral form of `(I+L)^s`. -/
noncomputable def spectralSobolevEnergy {i : Type*} [Fintype i]
    (ell : i → ℝ) (s : ℝ) (x : i → ℂ) : ℝ :=
  ∑ j, (1 + ell j) ^ s * Complex.normSq (x j)

/-- The spectral complement has the exact `(1+R)^s` coercive weight. -/
theorem spectralTail_weighted_by_sobolevEnergy {i : Type*} [Fintype i]
    (ell : i → ℝ) (x : i → ℂ) (R s : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hR : 0 ≤ R) (hs : 0 < s) :
    (1 + R) ^ s * spectralTailNormSq ell R x ≤
      spectralSobolevEnergy ell s x := by
  have hbase : 0 ≤ 1 + R := by linarith
  rw [spectralTailNormSq, spectralSobolevEnergy, Finset.mul_sum]
  calc
    (∑ j ∈ Finset.univ.filter (fun j => R < ell j),
        (1 + R) ^ s * Complex.normSq (x j)) ≤
        ∑ j ∈ Finset.univ.filter (fun j => R < ell j),
          (1 + ell j) ^ s * Complex.normSq (x j) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_filter] at hj
      have hle : 1 + R ≤ 1 + ell j := by linarith [hj.2]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hbase hle hs.le) (Complex.normSq_nonneg _)
    _ ≤ ∑ j, (1 + ell j) ^ s * Complex.normSq (x j) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) ?_
      intro j _hj _hnot
      exact mul_nonneg (Real.rpow_nonneg (by linarith [hell j]) s)
        (Complex.normSq_nonneg _)

/-- The manuscript's common compact-screen estimate after applying the form
domination and the diagonal spectral complement bound. -/
theorem common_compact_screen_bound {i : Type*} [Fintype i]
    (ell : i → ℝ) (x : i → ℂ) (R s c C0 E action : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hR : 0 ≤ R) (hs : 0 < s) (hc : 0 < c)
    (haction : action ≤ E)
    (hcoercive : c * spectralSobolevEnergy ell s x -
        C0 * (∑ j, Complex.normSq (x j)) ≤ action) :
    spectralTailNormSq ell R x ≤
      (E + C0 * (∑ j, Complex.normSq (x j))) /
        (c * (1 + R) ^ s) := by
  have hweight := spectralTail_weighted_by_sobolevEnergy ell x R s hell hR hs
  have hden : 0 < c * (1 + R) ^ s :=
    mul_pos hc (Real.rpow_pos_of_pos (by linarith) s)
  rw [le_div_iff₀ hden]
  calc
    spectralTailNormSq ell R x * (c * (1 + R) ^ s) =
        c * ((1 + R) ^ s * spectralTailNormSq ell R x) := by ring
    _ ≤ c * spectralSobolevEnergy ell s x := mul_le_mul_of_nonneg_left hweight hc.le
    _ ≤ action + C0 * (∑ j, Complex.normSq (x j)) := by linarith
    _ ≤ E + C0 * (∑ j, Complex.normSq (x j)) := by linarith

end RenewalShortedHodgeAndCompactScreen
end NCG
