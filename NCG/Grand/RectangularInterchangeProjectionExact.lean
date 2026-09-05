/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AssemblyRectangularStoppingFrontExact

/-!
# Rectangular interchange for nested projection systems

This closes the projection-instantiation layer of
`thm:GT-rectangular-interchange`.  The earlier algebraic identities are here
applied to an actual rectangle of finite-dimensional orthogonal projections.
In particular, both reveal orders consist of pairwise orthogonal projection
increments, the genuinely mixed corner is positive, the rectangular
curvature is a positive commutator Gram and its zero branch has the standard
four-range split.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace RectangularInterchangeProjection

open AssemblyRectangularStoppingFront
open FiniteRecurrenceAndPredictiveCarriers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Five projections forming the base, two marginal cells, their join, and
the completed rectangular cell.  Each multiplication identity is the matrix
form of inclusion of the corresponding nested subspaces. -/
structure System (n : Type*) [Fintype n] [DecidableEq n] where
  base : Matrix n n ℂ
  future : Matrix n n ℂ
  context : Matrix n n ℂ
  join : Matrix n n ℂ
  square : Matrix n n ℂ
  base_proj : IsOrthProj base
  future_proj : IsOrthProj future
  context_proj : IsOrthProj context
  join_proj : IsOrthProj join
  square_proj : IsOrthProj square
  base_future : base * future = base
  base_context : base * context = base
  future_join : future * join = future
  context_join : context * join = context
  join_square : join * square = join

/-- Matrix nesting is transitive. -/
theorem projection_mul_trans {P Q R : Matrix n n ℂ}
    (hPQ : P * Q = P) (hQR : Q * R = Q) : P * R = P := by
  calc
    P * R = (P * Q) * R := by rw [hPQ]
    _ = P * (Q * R) := Matrix.mul_assoc _ _ _
    _ = P * Q := by rw [hQR]
    _ = P := hPQ

/-- For orthogonal projections, one-sided nesting also gives the reverse
multiplication identity. -/
theorem reverse_projection_mul {P Q : Matrix n n ℂ}
    (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hPQ : P * Q = P) :
    Q * P = P := by
  have h := congrArg Matrix.conjTranspose hPQ
  simpa [Matrix.conjTranspose_mul, hP.1, hQ.1] using h

/-- The difference of two nested orthogonal projections is an orthogonal
projection. -/
theorem projection_increment_isOrthProj {P Q : Matrix n n ℂ}
    (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hPQ : P * Q = P) :
    IsOrthProj (Q - P) := by
  have hQP := reverse_projection_mul hP hQ hPQ
  constructor
  · rw [Matrix.conjTranspose_sub, hQ.1, hP.1]
  · simp only [Matrix.sub_mul, Matrix.mul_sub]
    rw [hQ.2, hQP, hPQ, hP.2]
    abel

/-- Every orthogonal projection is positive semidefinite. -/
theorem isOrthProj_posSemidef {P : Matrix n n ℂ} (hP : IsOrthProj P) :
    P.PosSemidef := by
  have hgram : Pᴴ * P = P := by rw [hP.1, hP.2]
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self P

/-- Consecutive increments in a nested projection chain are orthogonal. -/
theorem successive_projection_increments_mul_eq_zero
    {P Q R : Matrix n n ℂ} (hQ : IsOrthProj Q)
    (hPQ : P * Q = P) (hQR : Q * R = Q) :
    (Q - P) * (R - Q) = 0 := by
  have hPR := projection_mul_trans hPQ hQR
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  rw [hQR, hQ.2, hPR, hPQ]
  abel

/-- Nonconsecutive increments in a nested projection chain are orthogonal. -/
theorem separated_projection_increments_mul_eq_zero
    {P Q R S : Matrix n n ℂ}
    (hPR : P * R = P) (hPS : P * S = P)
    (hQR : Q * R = Q) (hQS : Q * S = Q) :
    (Q - P) * (S - R) = 0 := by
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  rw [hQS, hQR, hPS, hPR]
  abel

/-- Three pairwise orthogonal projection increments. -/
structure OrthogonalIncrementTriple
    (A B C : Matrix n n ℂ) : Prop where
  first_proj : IsOrthProj A
  second_proj : IsOrthProj B
  third_proj : IsOrthProj C
  first_second : A * B = 0
  first_third : A * C = 0
  second_third : B * C = 0

/-- Every four-term nested projection chain has an orthogonal three-increment
decomposition. -/
theorem orthogonal_increment_triple
    (P Q R S : Matrix n n ℂ)
    (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hR : IsOrthProj R) (hS : IsOrthProj S)
    (hPQ : P * Q = P) (hQR : Q * R = Q) (hRS : R * S = R) :
    OrthogonalIncrementTriple (Q - P) (R - Q) (S - R) := by
  have hPR := projection_mul_trans hPQ hQR
  have hQS := projection_mul_trans hQR hRS
  have hPS := projection_mul_trans hPR hRS
  exact
    { first_proj := projection_increment_isOrthProj hP hQ hPQ
      second_proj := projection_increment_isOrthProj hQ hR hQR
      third_proj := projection_increment_isOrthProj hR hS hRS
      first_second := successive_projection_increments_mul_eq_zero hQ hPQ hQR
      first_third := separated_projection_increments_mul_eq_zero hPR hPS hQR hQS
      second_third := successive_projection_increments_mul_eq_zero hR hQR hRS }

/-- Exact projection-level conclusion of `thm:GT-rectangular-interchange`.

The first two conjuncts certify that (PA.7) and (PA.8) are orthogonal
decompositions rather than merely additive identities.  The following terms
give the displayed identities, positivity of the mixed corner, the secant,
and (PA.11), including its exact zero criterion and four-range split. -/
theorem rectangular_interchange_projection_exact (D : System n) :
    OrthogonalIncrementTriple
        (D.future - D.base) (D.join - D.future) (D.square - D.join) ∧
      OrthogonalIncrementTriple
        (D.context - D.base) (D.join - D.context) (D.square - D.join) ∧
      D.square - D.base =
        (D.future - D.base) + (D.join - D.future) + (D.square - D.join) ∧
      D.square - D.base =
        (D.context - D.base) + (D.join - D.context) + (D.square - D.join) ∧
      (D.square - D.join).PosSemidef ∧
      AssemblyRectangularStoppingFront.interchangeSecant
          D.base D.future D.context D.join =
        (D.future - D.base) - (D.join - D.context) ∧
      let P := D.future - D.base
      let Q := D.context - D.base
      let K := P * Q - Q * P
      (Kᴴ * K).PosSemidef ∧
        (Kᴴ * K = 0 ↔ P * Q = Q * P) ∧
        (P * Q = Q * P →
          let R : Fin 4 → Matrix n n ℂ :=
            ![P * Q, P * (1 - Q), (1 - P) * Q, (1 - P) * (1 - Q)]
          (∀ i, IsOrthProj (R i)) ∧
            (∀ i j, i ≠ j → R i * R j = 0) ∧ ∑ i, R i = 1) := by
  have hFuture := orthogonal_increment_triple
    D.base D.future D.join D.square D.base_proj D.future_proj
      D.join_proj D.square_proj D.base_future D.future_join D.join_square
  have hContext := orthogonal_increment_triple
    D.base D.context D.join D.square D.base_proj D.context_proj
      D.join_proj D.square_proj D.base_context D.context_join D.join_square
  have hMixed := projection_increment_isOrthProj
    D.join_proj D.square_proj D.join_square
  have hPA7 := AssemblyRectangularStoppingFront.future_first_decomposition
    D.base D.future D.join D.square
  have hPA8 := AssemblyRectangularStoppingFront.context_first_decomposition
    D.base D.context D.join D.square
  have hSecant := (AssemblyRectangularStoppingFront.interchange_secant
    D.base D.future D.context D.join).1
  refine ⟨hFuture, hContext, ?_, ?_, isOrthProj_posSemidef hMixed,
    hSecant, ?_⟩
  · simpa [AssemblyRectangularStoppingFront.mixedCorner] using hPA7
  · simpa [AssemblyRectangularStoppingFront.mixedCorner] using hPA8
  · dsimp only
    have hCurvature := rectangular_curvature
      (D.future - D.base) (D.context - D.base)
    refine ⟨hCurvature.1, hCurvature.2, ?_⟩
    intro hcomm
    exact commuting_projections_four_range
      (D.future - D.base) (D.context - D.base)
      (projection_increment_isOrthProj D.base_proj D.future_proj D.base_future)
      (projection_increment_isOrthProj D.base_proj D.context_proj D.base_context)
      hcomm

end RectangularInterchangeProjection
end NCG
