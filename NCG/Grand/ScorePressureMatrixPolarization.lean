/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScorePressureExact

/-!
# Multiparameter score-pressure polarization

The directional score-pressure identities determine the full symmetric
Hessian.  This file records that polarization step and identifies the score
matrix as a positive covariance Gram.
-/

open Matrix Finset

namespace NCG
namespace ScorePressure

/-- The quadratic form of a real matrix. -/
def matrixQuadratic {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  dotProduct x (A *ᵥ x)

/-- A symmetric finite real matrix is determined by its directional quadratic
form. -/
theorem symmetric_matrix_eq_of_quadratic_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hquad : ∀ x : I → ℝ, matrixQuadratic A x = matrixQuadratic B x) :
    A = B := by
  ext i j
  let ei : I → ℝ := Pi.single i 1
  let ej : I → ℝ := Pi.single j 1
  have hii := hquad ei
  have hjj := hquad ej
  have hij := hquad (ei + ej)
  have hAji : A j i = A i j := by
    have h := congrFun (congrFun hA i) j
    simpa only [Matrix.transpose_apply] using h
  have hBji : B j i = B i j := by
    have h := congrFun (congrFun hB i) j
    simpa only [Matrix.transpose_apply] using h
  simp [matrixQuadratic, dotProduct, Matrix.mulVec, ei, ej, Pi.single_apply,
    Finset.sum_ite_eq'] at hii hjj hij
  simp only [mul_add, add_mul, Finset.sum_add_distrib] at hij
  simp [Finset.sum_ite_eq'] at hij
  rw [hAji, hBji] at hij
  linarith

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

/-- Center a finite family of score coordinates. -/
def centeredCoordinate (p : Ω → ℝ) (a : I → Ω → ℝ)
    (i : I) (ω : Ω) : ℝ :=
  a i ω - ∑ ξ, p ξ * a i ξ

/-- The full multiparameter score covariance matrix. -/
def scoreCovarianceMatrix (p : Ω → ℝ) (a : I → Ω → ℝ) :
    Matrix I I ℝ :=
  fun i j => ∑ ω, p ω * centeredCoordinate p a i ω *
    centeredCoordinate p a j ω

theorem scoreCovarianceMatrix_symmetric (p : Ω → ℝ)
    (a : I → Ω → ℝ) :
    (scoreCovarianceMatrix p a)ᵀ = scoreCovarianceMatrix p a := by
  ext i j
  simp only [Matrix.transpose_apply, scoreCovarianceMatrix]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The square-root weighted centered-score synthesis. -/
noncomputable def scoreSynthesis (p : Ω → ℝ) (a : I → Ω → ℝ) :
    Matrix Ω I ℝ :=
  fun ω i => Real.sqrt (p ω) * centeredCoordinate p a i ω

/-- The covariance matrix is literally the Gram of the score synthesis. -/
theorem scoreCovarianceMatrix_eq_gram
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (a : I → Ω → ℝ) :
    scoreCovarianceMatrix p a = (scoreSynthesis p a)ᴴ * scoreSynthesis p a := by
  classical
  ext i j
  simp only [scoreCovarianceMatrix, scoreSynthesis, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    (p ω * centeredCoordinate p a i ω) * centeredCoordinate p a j ω
        = (Real.sqrt (p ω)) ^ 2 *
            (centeredCoordinate p a i ω * centeredCoordinate p a j ω) := by
              rw [Real.sq_sqrt (hp ω)]
              ring
    _ = Real.sqrt (p ω) * centeredCoordinate p a i ω *
          (Real.sqrt (p ω) * centeredCoordinate p a j ω) := by ring

/-- **(NL.5), matrix form**: the score covariance is positive semidefinite. -/
theorem scoreCovarianceMatrix_posSemidef
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (a : I → Ω → ℝ) :
    (scoreCovarianceMatrix p a).PosSemidef := by
  rw [scoreCovarianceMatrix_eq_gram p hp a]
  exact Matrix.posSemidef_conjTranspose_mul_self _
/-- **(NL.6), full matrix form**: once the already-proved directional
log-partition identity is known in every direction, polarization identifies
the entire pressure Hessian with direct second action plus score covariance. -/
theorem pressure_hessian_matrix_from_directional
    [DecidableEq I] (p : Ω → ℝ) (a : I → Ω → ℝ)
    (b : I → I → Ω → ℝ) (H : Matrix I I ℝ)
    (hH : Hᵀ = H) (hb : ∀ i j ω, b j i ω = b i j ω)
    (hdir : ∀ x : I → ℝ,
      matrixQuadratic H x =
        matrixQuadratic
          (fun i j => (∑ ω, p ω * b i j ω) + scoreCovarianceMatrix p a i j) x) :
    H = fun i j => (∑ ω, p ω * b i j ω) +
      scoreCovarianceMatrix p a i j := by
  let K : Matrix I I ℝ := fun i j =>
    (∑ ω, p ω * b i j ω) + scoreCovarianceMatrix p a i j
  apply symmetric_matrix_eq_of_quadratic_eq H K hH
  · ext i j
    change K j i = K i j
    dsimp only [K]
    congr 1
    · apply Finset.sum_congr rfl
      intro ω _
      rw [hb i j ω]
    · have hcov := congrFun (congrFun (scoreCovarianceMatrix_symmetric p a) i) j
      simpa only [Matrix.transpose_apply] using hcov
  · exact hdir

/-- **(NL.7), action form**: replacing the log-weight second derivative by
`-Aᵢⱼ` changes only the direct expectation term. -/
theorem action_pressure_hessian_matrix_from_directional
    [DecidableEq I] (p : Ω → ℝ) (A1 : I → Ω → ℝ)
    (A2 : I → I → Ω → ℝ) (H : Matrix I I ℝ)
    (hH : Hᵀ = H) (hA2 : ∀ i j ω, A2 j i ω = A2 i j ω)
    (hdir : ∀ x : I → ℝ,
      matrixQuadratic H x =
        matrixQuadratic
          (fun i j => -(∑ ω, p ω * A2 i j ω) +
            scoreCovarianceMatrix p A1 i j) x) :
    H = fun i j => -(∑ ω, p ω * A2 i j ω) +
      scoreCovarianceMatrix p A1 i j := by
  let b : I → I → Ω → ℝ := fun i j ω => -A2 i j ω
  have hb : ∀ i j ω, b j i ω = b i j ω := by
    intro i j ω
    simp only [b]
    rw [hA2 i j ω]
  have h := pressure_hessian_matrix_from_directional p A1 b H hH hb
    (fun x => by simpa only [b, mul_neg, Finset.sum_neg_distrib] using hdir x)
  simpa only [b, mul_neg, Finset.sum_neg_distrib] using h

end ScorePressure
end NCG
