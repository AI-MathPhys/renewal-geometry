/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeightedGraphOrthonormalCoordinatesExact

/-!
# The actual Dirac square is the weighted graph Hodge Laplacian

The matrix transpose represents the weighted codifferential under the same
coordinate maps as the incidence matrix. This identifies the actual zero-form
block of the Dirac square with `-2 L_s`, including nonconstant vertex masses.
-/

open Matrix
open scoped BigOperators

namespace NCG.WeightedGraphHodgeLaplacianCoordinates

open FiniteWeightedGraphHodgeDirac StationaryWeightedGraphGenerator
open WeightedGraphOrthonormalCoordinates

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sqrt_mass_mul_edgeWeight_mul_sqrt
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) (x y : V) :
    Real.sqrt (mass x) * edgeWeight mass conductance x y * Real.sqrt (conductance x y) =
      conductance x y := by
  rw [mul_comm (Real.sqrt (mass x)), edgeWeight_mul_sqrt_mass mass conductance hmass hc,
    Real.mul_self_sqrt (hc x y)]

theorem weighted_differential_entry
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) (x y z : V) :
    Real.sqrt (mass z) * differential mass conductance (x, y) z *
        Real.sqrt (conductance x y) =
      (if z = y then conductance x y else 0) - (if z = x then conductance x y else 0) := by
  by_cases hzy : z = y
  · subst z
    by_cases hyx : y = x
    · subst y
      simp [differential, edgeWeight]
    · simp only [differential, if_pos, if_neg hyx, sub_zero]
      exact sqrt_mass_mul_edgeWeight_mul_sqrt mass (fun i j => conductance j i)
        hmass (fun x y => hc y x) y x
  · by_cases hzx : z = x
    · subst z
      simp only [differential, if_neg hzy, if_pos, zero_sub]
      have h := sqrt_mass_mul_edgeWeight_mul_sqrt mass conductance hmass hc x y
      nlinarith
    · simp [differential, hzy, hzx]

theorem sqrt_mass_mul_transpose_mulVec_edgeCoordinates
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (omega : V → V → ℝ) (x : V) :
    Real.sqrt (mass x) * ((differential mass conductance)ᵀ.mulVec
      (edgeCoordinates conductance omega)) x =
      ∑ y, (conductance y x * omega y x - conductance x y * omega x y) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, edgeCoordinates, Finset.mul_sum]
  have hterm : ∀ xy : V × V,
      Real.sqrt (mass x) * (differential mass conductance xy x *
        (Real.sqrt (conductance xy.1 xy.2) * omega xy.1 xy.2)) =
      (if x = xy.2 then conductance xy.1 xy.2 * omega xy.1 xy.2 else 0) -
        (if x = xy.1 then conductance xy.1 xy.2 * omega xy.1 xy.2 else 0) := by
    intro xy
    rw [show Real.sqrt (mass x) * (differential mass conductance xy x *
        (Real.sqrt (conductance xy.1 xy.2) * omega xy.1 xy.2)) =
      (Real.sqrt (mass x) * differential mass conductance xy x *
        Real.sqrt (conductance xy.1 xy.2)) * omega xy.1 xy.2 by ring]
    rw [weighted_differential_entry mass conductance hmass hc]
    simp only [sub_mul, ite_mul, zero_mul]
  simp only [hterm, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp

/-- The transpose is the actual weighted adjoint under the same coordinate maps. -/
theorem transpose_mulVec_edgeCoordinates
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (omega : V → V → ℝ) :
    (differential mass conductance)ᵀ.mulVec (edgeCoordinates conductance omega) =
      vertexCoordinates mass (weightedCodifferential mass conductance omega) := by
  funext x
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr (hmass x)).ne'
  rw [sqrt_mass_mul_transpose_mulVec_edgeCoordinates mass conductance hmass hc]
  simp only [vertexCoordinates, weightedCodifferential]
  rw [← mul_assoc, Real.mul_self_sqrt (hmass x).le]
  field_simp [(hmass x).ne']

/-- Full coordinate-faithful **SP.17** for the actual matrix Dirac square. -/
theorem hodgeLaplacian_mulVec_vertexCoordinates
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (hsymm : ∀ x y, conductance x y = conductance y x) (f : V → ℝ) :
    ((differential mass conductance)ᵀ * differential mass conductance).mulVec
        (vertexCoordinates mass f) =
      vertexCoordinates mass (fun x => -2 * symmetricRateGenerator mass conductance f x) := by
  rw [← Matrix.mulVec_mulVec, differential_mulVec_vertexCoordinates mass conductance hmass hc,
    transpose_mulVec_edgeCoordinates mass conductance hmass hc,
    codifferential_differential_eq_neg_two_generator mass conductance hmass hsymm]

end

end NCG.WeightedGraphHodgeLaplacianCoordinates
