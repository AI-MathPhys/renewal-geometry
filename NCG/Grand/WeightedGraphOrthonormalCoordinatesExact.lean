/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StationaryWeightedGraphGeneratorExact

/-!
# Exact weighted-to-orthonormal graph coordinates

Vertex functions are multiplied by the square root of the vertex mass, and
one-forms by the square root of conductance. The corrected incidence matrix
intertwines these maps with the actual endpoint-difference differential.
The target coefficient uses the target mass, including for unequal masses.
-/

open Matrix
open scoped BigOperators

namespace NCG.WeightedGraphOrthonormalCoordinates

open FiniteWeightedGraphHodgeDirac StationaryWeightedGraphGenerator

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def vertexCoordinates (mass : V → ℝ) (f : V → ℝ) : V → ℝ :=
  fun x => Real.sqrt (mass x) * f x

def edgeCoordinates (conductance : V → V → ℝ) (omega : V → V → ℝ) : V × V → ℝ :=
  fun xy => Real.sqrt (conductance xy.1 xy.2) * omega xy.1 xy.2

theorem edgeWeight_mul_sqrt_mass
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) (x y : V) :
    edgeWeight mass conductance x y * Real.sqrt (mass x) = Real.sqrt (conductance x y) := by
  rw [edgeWeight, Real.sqrt_div (hc x y)]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (hmass x)).ne'

/-- Exact coordinate intertwining for the manuscript differential `f(y)-f(x)`. -/
theorem differential_mulVec_vertexCoordinates
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) (f : V → ℝ) :
    (differential mass conductance).mulVec (vertexCoordinates mass f) =
      edgeCoordinates conductance (functionDifferential f) := by
  funext xy
  simp only [Matrix.mulVec, dotProduct, differential, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, vertexCoordinates, edgeCoordinates, functionDifferential]
  rw [← mul_assoc, edgeWeight_mul_sqrt_mass mass (fun i j => conductance j i) hmass
      (fun x y => hc y x),
    ← mul_assoc, edgeWeight_mul_sqrt_mass mass conductance hmass hc]
  ring

/-- The constant weighted function lies in the kernel in the correct coordinates. -/
theorem differential_mulVec_sqrt_mass_eq_zero
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y) :
    (differential mass conductance).mulVec (fun x => Real.sqrt (mass x)) = 0 := by
  have h := differential_mulVec_vertexCoordinates mass conductance hmass hc (fun _ => 1)
  have hvertex : vertexCoordinates mass (fun _ => 1) = fun x => Real.sqrt (mass x) := by
    funext x
    simp [vertexCoordinates]
  have hedge : edgeCoordinates conductance (functionDifferential (fun _ => 1)) = 0 := by
    funext xy
    simp [edgeCoordinates, functionDifferential]
  rw [hvertex, hedge] at h
  exact h

/-- Retaining a diagonal pair cannot create a spurious one-form differential. -/
theorem differential_self_loop (mass : V → ℝ) (conductance : V → V → ℝ) (x z : V) :
    differential mass conductance (x, x) z = 0 := by
  simp [differential, edgeWeight]

/-- Regression check: the physical constant for masses one and four has
orthonormal coordinates `(1,2)`, not `(1,1)`. -/
theorem unequal_mass_constant_regression :
    (differential (fun b : Bool => if b then 4 else 1)
      (fun x y : Bool => if x = y then 0 else 1)).mulVec
        (fun b : Bool => if b then 2 else 1) = 0 := by
  have h := differential_mulVec_sqrt_mass_eq_zero
    (fun b : Bool => if b then 4 else 1) (fun x y : Bool => if x = y then 0 else 1)
    (by intro b; cases b <;> norm_num) (by intro x y; split_ifs <;> norm_num)
  have hsqrt : (fun b : Bool => Real.sqrt (if b then 4 else 1)) =
      (fun b : Bool => if b then 2 else 1) := by
    funext b
    cases b <;> norm_num
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hsqrt] at h
  exact h

end

end NCG.WeightedGraphOrthonormalCoordinates
