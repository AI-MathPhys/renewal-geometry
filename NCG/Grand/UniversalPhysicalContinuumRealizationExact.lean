/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalPhysicalContinuumExact
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# The assembled physical Grand-Tensor continuum realization

This file supplies the object that was missing from the earlier formalization
of `thm:universal-physical-continuum`.  It records the limiting C-star state and
GNS carrier, declared bounded observables, positive Gram profile, a coercive
selected source sector, an explicit non-scalar centered vector, operational
locality, and the classified feedback branch.  The assembly theorem derives
positivity, dense-sector coercivity, and nontriviality from the corresponding
convergence certificates.
-/

open Filter Topology Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace UniversalContinuum

/-- The three controlled feedback outcomes retained by the positive continuum
branch. -/
inductive ControlledFeedbackBranch where
  | memoryless
  | finiteRational
  | shortMemory
  deriving DecidableEq

/-- A typed nontrivial physical continuum realization.  No target-domain
semantic is included: only the operational and analytic data asserted by the
manuscript theorem are fields. -/
structure PhysicalContinuumRealization
    (A H ι : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Finite ι] where
  state : A →ₚ[ℂ] ℂ
  state_normalized : state 1 = 1
  representation : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  cyclicVector : H
  state_vector : ∀ a, state a =
    inner ℂ cyclicVector (representation a cyclicVector)
  cyclic : DenseRange fun a : A => representation a cyclicVector
  boundedObservable : ℕ → H →L[ℂ] H
  gram : Matrix ι ι ℂ
  gram_posSemidef : gram.PosSemidef
  sourceSector : Set H
  sourceSector_dense : Dense sourceSector
  sourceEnergy : H → ℝ
  sourceEnergy_continuous : Continuous sourceEnergy
  coercivityFloor : ℝ
  source_coercive : ∀ x, coercivityFloor * ‖x‖ ^ 2 ≤ sourceEnergy x
  centeredWitness : H
  centeredWitness_ne_zero : centeredWitness ≠ 0
  centeredWitness_orthogonal : inner ℂ cyclicVector centeredWitness = 0
  centeredWitness_nonscalar : ∀ c : ℂ, centeredWitness ≠ c • cyclicVector
  localRelation : H → H → Prop
  feedback : ControlledFeedbackBranch
  exactCompatibility : Bool

/-- Positive physical-continuum assembly from the six reconstructed profile
certificates.  Entrywise Gram convergence, dense source saturation, and the
positive centered witness are discharged rather than copied into the output. -/
theorem physical_continuum_realization_of_profiles
    {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Finite ι]
    (state : A →ₚ[ℂ] ℂ) (hstateOne : state 1 = 1)
    (representation : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Omega : H)
    (hstate : ∀ a, state a = inner ℂ Omega (representation a Omega))
    (hcyclic : DenseRange fun a : A => representation a Omega)
    (boundedObservable : ℕ → H →L[ℂ] H)
    (stageGram : ℕ → Matrix ι ι ℂ) (gram : Matrix ι ι ℂ)
    (hstageGram : ∀ n, (stageGram n).PosSemidef)
    (hgramLimit : ∀ i j,
      Tendsto (fun n => stageGram n i j) atTop (nhds (gram i j)))
    (sourceSector : Set H) (hsourceDense : Dense sourceSector)
    (sourceEnergy : H → ℝ) (henergyContinuous : Continuous sourceEnergy)
    (c : ℝ)
    (hcoerciveDense : ∀ x ∈ sourceSector, c * ‖x‖ ^ 2 ≤ sourceEnergy x)
    (centered : H) (hcentered : centered ≠ 0)
    (horthogonal : inner ℂ Omega centered = 0)
    (localRelation : H → H → Prop)
    (feedback : ControlledFeedbackBranch) (exactCompatibility : Bool) :
    Nonempty (PhysicalContinuumRealization A H ι) := by
  have hgram : gram.PosSemidef :=
    posSemidef_of_entrywise_tendsto hstageGram hgramLimit
  have hcoercive : ∀ x : H, c * ‖x‖ ^ 2 ≤ sourceEnergy x := by
    intro x
    exact dense_coercivity_extension sourceEnergy henergyContinuous c
      sourceSector hsourceDense hcoerciveDense x
  have hnonscalar : ∀ z : ℂ, centered ≠ z • Omega :=
    fun z => not_scalar_of_centered_positive hcentered horthogonal z
  exact ⟨{
    state := state
    state_normalized := hstateOne
    representation := representation
    cyclicVector := Omega
    state_vector := hstate
    cyclic := hcyclic
    boundedObservable := boundedObservable
    gram := gram
    gram_posSemidef := hgram
    sourceSector := sourceSector
    sourceSector_dense := hsourceDense
    sourceEnergy := sourceEnergy
    sourceEnergy_continuous := henergyContinuous
    coercivityFloor := c
    source_coercive := hcoercive
    centeredWitness := centered
    centeredWitness_ne_zero := hcentered
    centeredWitness_orthogonal := horthogonal
    centeredWitness_nonscalar := hnonscalar
    localRelation := localRelation
    feedback := feedback
    exactCompatibility := exactCompatibility }⟩

/-- The assembled realization is genuinely nontrivial: its centered witness
cannot lie in the scalar cyclic line. -/
theorem PhysicalContinuumRealization.nontrivial
    {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Finite ι] (R : PhysicalContinuumRealization A H ι) :
    ∀ c : ℂ, R.centeredWitness ≠ c • R.cyclicVector :=
  R.centeredWitness_nonscalar

end UniversalContinuum
end NCG
