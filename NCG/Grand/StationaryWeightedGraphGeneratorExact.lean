/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedGraphHodgeDiracExact

/-!
# Stationary weighted graph generator and Hodge Laplacian

This file proves the rate-coordinate identity in (SP.17) of
`thm:GT-NCG-graph-spectralization`.  It works in the manuscript's weighted
function coordinates: the differential is the endpoint difference and the
codifferential is its weighted adjoint.  Symmetry of the conductance then
identifies the zero-form Hodge Laplacian with minus twice the reversible
renewal generator.
-/

open scoped BigOperators

noncomputable section

namespace NCG.StationaryWeightedGraphGenerator

variable {V : Type*} [Fintype V]

/-- The endpoint-difference differential on all oriented pairs. -/
def functionDifferential (f : V → ℝ) : V → V → ℝ :=
  fun x y => f y - f x

/-- The adjoint of `functionDifferential` for vertex weight `mass` and
oriented-edge weight `conductance`. -/
def weightedCodifferential (mass : V → ℝ) (conductance : V → V → ℝ)
    (omega : V → V → ℝ) : V → ℝ :=
  fun x => (1 / mass x) *
    ∑ y, (conductance y x * omega y x - conductance x y * omega x y)

/-- The reversible rate generator with rates `conductance x y / mass x`. -/
def symmetricRateGenerator (mass : V → ℝ) (conductance : V → V → ℝ)
    (f : V → ℝ) : V → ℝ :=
  fun x => ∑ y, (conductance x y / mass x) * (f y - f x)

/-- **(SP.17)** in the manuscript's weighted function coordinates:
`partial* partial = -2 L_s`. -/
theorem codifferential_differential_eq_neg_two_generator
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x)
    (hsymm : ∀ x y, conductance x y = conductance y x)
    (f : V → ℝ) :
    weightedCodifferential mass conductance (functionDifferential f) =
      fun x => -2 * symmetricRateGenerator mass conductance f x := by
  funext x
  unfold weightedCodifferential functionDifferential symmetricRateGenerator
  apply congrArg (fun z : ℝ => z)
  calc
    (1 / mass x) *
        ∑ y, (conductance y x * (f x - f y) -
          conductance x y * (f y - f x)) =
      (1 / mass x) *
        ∑ y, (-2 * conductance x y * (f y - f x)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro y hy
          rw [← hsymm x y]
          ring
    _ = -2 * ∑ y, (conductance x y / mass x) * (f y - f x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [div_eq_mul_inv]
      ring

/-- Pointwise form of (SP.17), convenient when rewriting a zero-form Dirac
square at a specified vertex. -/
theorem codifferential_differential_apply
    (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x)
    (hsymm : ∀ x y, conductance x y = conductance y x)
    (f : V → ℝ) (x : V) :
    weightedCodifferential mass conductance (functionDifferential f) x =
      -2 * ∑ y, (conductance x y / mass x) * (f y - f x) := by
  simpa [symmetricRateGenerator] using
    congrFun (codifferential_differential_eq_neg_two_generator
      mass conductance hmass hsymm f) x

end NCG.StationaryWeightedGraphGenerator
