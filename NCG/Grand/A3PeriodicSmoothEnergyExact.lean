/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3UniformEnergyConsistencyExact
import NCG.Grand.LatticePeriodicDifferentiationExact

/-!
# Smooth sampling consistency on the actual A3 period lattice

The period basis is `(1,1,0), (1,0,1), (0,1,1)`, not the cubic coordinate
lattice. Every one of the twelve roots has explicit integral coordinates in
this basis. Continuous differentiability and lattice periodicity imply the
global uniform square-root energy limit, with uniform derivative continuity
derived internally from the bounded fundamental domain.
-/

open Module
open scoped BigOperators Topology

namespace NCG.A3PeriodicSmoothEnergy

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency LatticePeriodicDifferentiation

noncomputable section

/-- Coordinates in the three independent A3 roots. -/
def coordinates : Space ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![(x 0 + x 1 - x 2) / 2, (x 0 - x 1 + x 2) / 2,
    (-x 0 + x 1 + x 2) / 2]
  invFun z := WithLp.toLp 2 ![z 0 + z 1, z 0 + z 2, z 1 + z 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i
    fin_cases i <;> simp <;> ring
  right_inv z := by
    ext i
    fin_cases i <;> simp <;> ring

def basis : Basis (Fin 3) ℝ Space := Basis.ofEquivFun coordinates

/-- The full-rank root period lattice in the manuscript's Euclidean realization. -/
def lattice : AddSubgroup Space := periodLattice basis

def rootCoordinates : Fin 12 → (Fin 3 → ℤ) :=
  ![![1, 0, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 0],
    ![0, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 0],
    ![0, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, -1]]

theorem coordinates_integerCombination (z : Fin 3 → ℤ) :
    coordinates (integerCombination basis z) = fun i => (z i : ℝ) := by
  funext i
  change basis.repr (∑ j, (z j : ℝ) • basis j) i = (z i : ℝ)
  rw [basis.repr_sum_self]

theorem root_eq_integerCombination (r : Fin 12) :
    root r = integerCombination basis (rootCoordinates r) := by
  apply coordinates.injective
  rw [coordinates_integerCombination]
  ext i
  fin_cases r <;> fin_cases i <;>
    norm_num [coordinates, root, a3Roots, rootCoordinates, Matrix.cons_val_two]

theorem root_mem_lattice (r : Fin 12) : root r ∈ lattice := by
  exact ⟨rootCoordinates r, (root_eq_integerCombination r).symm⟩

/-- The basis vectors themselves are three of the twelve roots. -/
theorem basis_eq_selected_root (i : Fin 3) :
    basis i = root (![0, 4, 8] i) := by
  have hcoords : rootCoordinates (![0, 4, 8] i) = Pi.single i 1 := by
    fin_cases i <;> decide
  rw [root_eq_integerCombination, hcoords]
  simp [integerCombination, Pi.single_apply]

/-- Genuine uniform smooth-test consistency for the A3 torus, with no supplied
uniform continuity or remainder estimate. -/
theorem tendstoUniformly_periodic_sqrt_sampledEnergy
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : Continuous (fun x => innerSL ℝ (v x)))
    (hperiod : ∀ p : lattice, ∀ x : Space, f (x + p) = f x) :
    TendstoUniformly (fun h x => Real.sqrt (sampledEnergy f x h))
      (fun x => ‖v x‖) (𝓝[>] (0 : ℝ)) := by
  exact tendstoUniformly_sqrt_sampledEnergy f v hf
    (uniformContinuous_derivative_of_lattice_periodic basis f _ hf hdf hperiod)

end

end NCG.A3PeriodicSmoothEnergy
