/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeakClosureAndAncientConstantCounterexamples

/-!
# Nonzero constant ancient Navier--Stokes solutions

This file gives the full constant-field counterexample used in
`cth:NS-ancient-nontrivial`.  Unlike the earlier algebraic core, the
definitions below expose the viscosity-one Navier--Stokes residual,
incompressibility, the classical local-energy equality, local cubic mass,
and the viscous dissipation measure.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG
namespace AncientConstantNavierStokesExact

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Spatial Fréchet derivative of a time-dependent velocity field. -/
noncomputable def spatialDerivative (u : ℝ → Space → Space) (t : ℝ) (x : Space) :
    Space →L[ℝ] Space :=
  fderiv ℝ (u t) x

/-- Time derivative of a time-dependent velocity field. -/
noncomputable def timeDerivative (u : ℝ → Space → Space) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s => u s x) t 1

/-- Componentwise spatial Laplacian, written with the canonical orthonormal basis. -/
noncomputable def laplacianComponent (u : ℝ → Space → Space)
    (t : ℝ) (x : Space) (j : Fin 3) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y => (spatialDerivative u t y (EuclideanSpace.single i 1)) j)
      x (EuclideanSpace.single i 1)

/-- The viscosity-one incompressible Navier--Stokes residual in component `j`. -/
noncomputable def navierStokesResidual (u : ℝ → Space → Space)
    (p : ℝ → Space → ℝ) (t : ℝ) (x : Space) (j : Fin 3) : ℝ :=
  timeDerivative u t x j +
    spatialDerivative u t x (u t x) j +
    fderiv ℝ (p t) x (EuclideanSpace.single j 1) -
    laplacianComponent u t x j

/-- The divergence of a velocity field. -/
noncomputable def velocityDivergence (u : ℝ → Space → Space) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialDerivative u t x (EuclideanSpace.single i 1) i

/-- Pointwise classical local-energy residual.

Its vanishing is the local-energy equality
`∂ₜ |u|²/2 + div ((|u|²/2+p)u) - Δ(|u|²/2) + |∇u|² = 0`.
-/
noncomputable def localEnergyResidual (u : ℝ → Space → Space)
    (p : ℝ → Space → ℝ) (t : ℝ) (x : Space) : ℝ :=
  fderiv ℝ (fun s => ‖u s x‖ ^ 2 / 2) t 1 +
    (∑ i : Fin 3,
      fderiv ℝ
        (fun y => (‖u t y‖ ^ 2 / 2 + p t y) * (u t y i))
        x (EuclideanSpace.single i 1)) -
    (∑ i : Fin 3,
      fderiv ℝ
        (fun y =>
          fderiv ℝ (fun z => ‖u t z‖ ^ 2 / 2) y
            (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)) +
    ‖spatialDerivative u t x‖ ^ 2

/-- A smooth ancient classical solution satisfying local-energy equality.
This is the smooth (hence suitable) formulation needed by the counterexample. -/
def IsSmoothAncientSuitable (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop :=
  ContDiff ℝ ⊤ (Function.uncurry u) ∧
  ContDiff ℝ ⊤ (Function.uncurry p) ∧
  (∀ t ≤ 0, ∀ x j, navierStokesResidual u p t x j = 0) ∧
  (∀ t ≤ 0, ∀ x, velocityDivergence u t x = 0) ∧
  (∀ t ≤ 0, ∀ x, localEnergyResidual u p t x = 0)

/-- The constant ancient velocity field. -/
def constantVelocity (c : Space) : ℝ → Space → Space := fun _ _ => c

/-- The accompanying constant zero pressure. -/
def zeroPressure : ℝ → Space → ℝ := fun _ _ => 0

/-- The nonnegative local cubic mass on the backward unit spatial cylinder
`[-a,0] × B(0,1)`. -/
noncomputable def localCubicMass (u : ℝ → Space → Space) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (-a) 0,
    ∫⁻ x in Metric.ball (0 : Space) 1, ENNReal.ofReal (‖u t x‖ ^ 3)

/-- Viscous dissipation measure `|∇u|² dt dx` on spacetime. -/
noncomputable def viscousDissipationMeasure (u : ℝ → Space → Space) :
    Measure (ℝ × Space) :=
  volume.withDensity fun z =>
    ENNReal.ofReal (‖spatialDerivative u z.1 z.2‖ ^ 2)

@[simp] theorem constantVelocity_spatialDerivative (c : Space) (t : ℝ) (x : Space) :
    spatialDerivative (constantVelocity c) t x = 0 := by
  change fderiv ℝ (fun _ : Space => c) x = 0
  exact fderiv_const_apply c

@[simp] theorem zeroPressure_spatialDerivative (t : ℝ) (x : Space) :
    fderiv ℝ (zeroPressure t) x = 0 := by
  change fderiv ℝ (fun _ : Space => (0 : ℝ)) x = 0
  exact fderiv_const_apply 0

theorem constantVelocity_isSmoothAncientSuitable (c : Space) :
  IsSmoothAncientSuitable (constantVelocity c) zeroPressure := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ⊤ (fun _ : ℝ × Space => c)
    exact contDiff_const
  · change ContDiff ℝ ⊤ (fun _ : ℝ × Space => (0 : ℝ))
    exact contDiff_const
  · intro t ht x j
    simp [navierStokesResidual, timeDerivative, laplacianComponent,
      constantVelocity, zeroPressure, fderiv_const_apply]
  · intro t ht x
    simp [velocityDivergence]
  · intro t ht x
    simp [localEnergyResidual, constantVelocity, zeroPressure,
      fderiv_const_apply]

theorem constantVelocity_localCubicMass (c : Space) (a : ℝ) :
    localCubicMass (constantVelocity c) a =
      volume (Set.Icc (-a) 0) * volume (Metric.ball (0 : Space) 1) *
        ENNReal.ofReal (‖c‖ ^ 3) := by
  simp [localCubicMass, constantVelocity, mul_comm, mul_left_comm, mul_assoc]

theorem constantVelocity_localCubicMass_pos (c : Space) (hc : c ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    0 < localCubicMass (constantVelocity c) a := by
  rw [constantVelocity_localCubicMass]
  have htime : 0 < volume (Set.Icc (-a) 0) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hspace : 0 < volume (Metric.ball (0 : Space) 1) :=
    Metric.measure_ball_pos volume (0 : Space) (by norm_num)
  have hmass : 0 < ENNReal.ofReal (‖c‖ ^ 3) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  positivity

theorem constantVelocity_viscousDissipationMeasure (c : Space) :
    viscousDissipationMeasure (constantVelocity c) = 0 := by
  simp [viscousDissipationMeasure, constantVelocity_spatialDerivative]

/-- Exact counterexample package: every nonzero constant vector field is a
smooth ancient suitable Navier--Stokes solution, has positive local cubic
mass on every nondegenerate backward cylinder, and has zero dissipation
measure.  Thus nonzero ancient mass alone is not a singularity certificate. -/
theorem nonzero_constant_ancient_not_singularity_certificate
    (c : Space) (hc : c ≠ 0) (a : ℝ) (ha : 0 < a) :
    IsSmoothAncientSuitable (constantVelocity c) zeroPressure ∧
      0 < localCubicMass (constantVelocity c) a ∧
      viscousDissipationMeasure (constantVelocity c) = 0 := by
  exact ⟨constantVelocity_isSmoothAncientSuitable c,
    constantVelocity_localCubicMass_pos c hc a ha,
    constantVelocity_viscousDissipationMeasure c⟩

end AncientConstantNavierStokesExact
end NCG
