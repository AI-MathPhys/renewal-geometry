/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3ConnesDistanceUniformBoundsExact

/-!
# Measurable periodic lifts of arbitrary finite A3 observables

Flooring the true root-basis coordinates gives a measurable step-function
lift on Euclidean space. It is exactly periodic, samples back to the
original observable, intertwines every mesh root translation, and retains
the actual local-energy bound pointwise, including across period seams.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.A3PeriodicStepFunctionLift

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open LatticePeriodicDifferentiation A3DiscreteUnitBallEquicontinuity
open FiniteRootGraphEnergy FiniteWeightedGraphHodgeDirac FiniteRootGraphUnitBallBounds

noncomputable section

def integerIndex (d : ℕ) (p : Space) : Fin 3 → ℤ :=
  fun i => ⌊(d : ℝ) * coordinates p i⌋

def index (d : ℕ) (p : Space) : Vertex d := fun i => (integerIndex d p i : ZMod d)

def lift (d : ℕ) (f : Vertex d → ℝ) (p : Space) : ℝ := f (index d p)

theorem index_point (d : ℕ) [NeZero d] (x : Vertex d) : index d (point d x) = x := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  funext i
  change ((⌊(d : ℝ) * coordinates (point d x) i⌋ : ℤ) : ZMod d) = x i
  rw [coordinates_point, mul_div_cancel₀ _ hd, Int.floor_natCast,
    Int.cast_natCast, ZMod.natCast_zmod_val]

theorem lift_point (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (x : Vertex d) :
    lift d f (point d x) = f x := by rw [lift, index_point]

theorem integerIndex_lattice_translate (d : ℕ) (p : Space) (z : Fin 3 → ℤ) (i : Fin 3) :
    integerIndex d (p + integerCombination basis z) i =
      integerIndex d p i + (d : ℤ) * z i := by
  unfold integerIndex
  rw [map_add, Pi.add_apply, coordinates_integerCombination, mul_add]
  rw [show (d : ℝ) * (z i : ℝ) = (((d : ℤ) * z i : ℤ) : ℝ) by simp]
  exact Int.floor_add_intCast _ _

theorem lift_periodic (d : ℕ) (f : Vertex d → ℝ) (q : lattice) (p : Space) :
    lift d f (p + q) = lift d f p := by
  obtain ⟨z, hz⟩ := q.property
  unfold lift
  congr 1
  funext i
  change (integerIndex d (p + q.val) i : ZMod d) = (integerIndex d p i : ZMod d)
  rw [← hz, integerIndex_lattice_translate]
  simp

theorem integerIndex_root_translate
    (d : ℕ) [NeZero d] (p : Space) (r : Fin 12) (i : Fin 3) :
    integerIndex d (p + mesh d • root r) i = integerIndex d p i + rootCoordinates r i := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hcoord : coordinates (p + mesh d • root r) i =
      coordinates p i + mesh d * (rootCoordinates r i : ℝ) := by
    rw [map_add, Pi.add_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      root_eq_integerCombination, coordinates_integerCombination]
  unfold integerIndex
  rw [hcoord]
  rw [show (d : ℝ) * (coordinates p i + mesh d * (rootCoordinates r i : ℝ)) =
      (d : ℝ) * coordinates p i + (rootCoordinates r i : ℝ) by
    unfold mesh
    field_simp
    <;> ring]
  exact Int.floor_add_intCast _ _

theorem index_root_translate
    (d : ℕ) [NeZero d] (p : Space) (r : Fin 12) :
    index d (p + mesh d • root r) = rootStep d (index d p) r := by
  funext i
  change (integerIndex d (p + mesh d • root r) i : ZMod d) =
    (integerIndex d p i : ZMod d) + (rootCoordinates r i : ZMod d)
  rw [integerIndex_root_translate, Int.cast_add]

theorem measurable_integerIndex (d : ℕ) : Measurable (integerIndex d) := by
  apply measurable_pi_lambda
  intro i
  have hc : Continuous (fun p : Space => coordinates p i) :=
    (continuous_apply i).comp coordinates.toLinearMap.continuous_of_finiteDimensional
  exact Int.measurable_floor.comp (measurable_const.mul hc.measurable)

theorem measurable_lift (d : ℕ) (f : Vertex d → ℝ) : Measurable (lift d f) := by
  have h : Measurable (fun z : Fin 3 → ℤ => f (fun i => (z i : ZMod d))) :=
    measurable_of_countable _
  exact h.comp (measurable_integerIndex d)

theorem sampledEnergy_lift_eq_localEnergy
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (p : Space) :
    sampledEnergy (lift d f) p (mesh d) =
      localEnergy (mass d) (conductance d) f (index d p) := by
  unfold mass conductance
  rw [localEnergy_eq_root_difference_sum (rootStep d) (1 / 8) (mesh d)
    (by norm_num) (mesh_pos d)]
  simp only [sampledEnergy, rootDifference, lift, index_root_translate]
  ring

/-- The full twelve-direction energy constraint holds at every Euclidean point. -/
theorem sampledEnergy_lift_le_one
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (p : Space) :
    sampledEnergy (lift d f) p (mesh d) ≤ 1 := by
  rw [sampledEnergy_lift_eq_localEnergy]
  have h := localEnergy_le_graphLipschitz_sq (mass d) (conductance d) f (index d p)
  have hn : 0 ≤ graphLipschitz (mass d) (conductance d) f := norm_nonneg _
  nlinarith

end

end NCG.A3PeriodicStepFunctionLift
