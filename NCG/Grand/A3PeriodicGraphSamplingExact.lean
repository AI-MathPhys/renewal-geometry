/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3PeriodicSmoothEnergyExact
import NCG.Grand.LatticeGridSamplingExact
import NCG.Grand.FiniteRootGraphEnergyExact

/-!
# Smooth energy consistency on the actual finite periodic A3 graph

Vertices are basis coordinates modulo the scalar period, and every root step
is reduced modulo that same period. The weighted graph energy equals the
Euclidean root-difference energy exactly, including across the period seam.
For a continuously differentiable periodic field, the local square-root
energies converge uniformly over all vertices on the cofinal period sequence.
-/

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace NCG.A3PeriodicGraphSampling

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicSmoothEnergy
open LatticePeriodicDifferentiation FiniteRootGraphEnergy FiniteWeightedGraphHodgeDirac

noncomputable section

abbrev Vertex (d : ℕ) := Fin 3 → ZMod d

def mesh (d : ℕ) : ℝ := 1 / (d : ℝ)

def point (d : ℕ) (x : Vertex d) : Space := LatticeGridSampling.embed basis d x

def rootStep (d : ℕ) (x : Vertex d) (r : Fin 12) : Vertex d :=
  LatticeGridSampling.step d x (rootCoordinates r)

def mass (d : ℕ) : Vertex d → ℝ := fun _ => mesh d ^ 3

def conductance (d : ℕ) [NeZero d] : Vertex d → Vertex d → ℝ :=
  rootConductance (rootStep d) (1 / 8) (mesh d)

theorem mesh_pos (d : ℕ) [NeZero d] : 0 < mesh d := by
  unfold mesh
  exact one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))

theorem sample_rootStep_eq_translate
    (d : ℕ) [NeZero d] (x : Vertex d) (r : Fin 12)
    (f : Space → ℝ) (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) :
    f (point d (rootStep d x r)) = f (point d x + mesh d • root r) := by
  simpa only [point, rootStep, mesh, ← root_eq_integerCombination] using
    LatticeGridSampling.sample_step_eq_translate basis d x (rootCoordinates r) f hperiod

theorem localEnergy_sample_eq
    (d : ℕ) [NeZero d] (f : Space → ℝ)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) (x : Vertex d) :
    localEnergy (mass d) (conductance d) (fun y => f (point d y)) x =
      sampledEnergy f (point d x) (mesh d) := by
  unfold mass conductance
  rw [localEnergy_eq_root_difference_sum (rootStep d) (1 / 8)
    (mesh d) (by norm_num) (mesh_pos d)]
  simp only [sample_rootStep_eq_translate d _ _ f hperiod, sampledEnergy, rootDifference]
  ring

theorem graphLipschitz_sample_sq_eq
    (d : ℕ) [NeZero d] (f : Space → ℝ)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) :
    graphLipschitz (mass d) (conductance d) (fun y => f (point d y)) ^ 2 =
      ‖fun x : Vertex d => sampledEnergy f (point d x) (mesh d)‖ := by
  rw [graphLipschitz, norm_sq_dirac_commutator]
  congr 1
  funext x
  exact localEnergy_sample_eq d f hperiod x

/-- The actual finite periodic graph has uniform smooth-test local-energy consistency. -/
theorem eventually_uniform_localEnergy_sample
    (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hdf : Continuous (fun x => innerSL ℝ (v x)))
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vertex (n + 1),
      |Real.sqrt (localEnergy (mass (n + 1)) (conductance (n + 1))
        (fun y => f (point (n + 1) y)) x) - ‖v (point (n + 1) x)‖| < ε := by
  have huc := uniformContinuous_derivative_of_lattice_periodic basis f _ hf hdf hperiod
  obtain ⟨δ, hδ, hbound⟩ := uniform_sqrt_energy_consistency f v hf huc ε hε
  have hmesh : Tendsto (fun n : ℕ => mesh (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mesh, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  filter_upwards [hmesh.eventually (eventually_lt_nhds hδ)] with n hn
  intro x
  rw [localEnergy_sample_eq (n + 1) f hperiod x]
  exact hbound (mesh (n + 1)) (mesh_pos (n + 1)) hn (point (n + 1) x)

end

end NCG.A3PeriodicGraphSampling
