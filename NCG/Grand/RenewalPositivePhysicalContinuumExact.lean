/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalRegenerativeContinuumAssemblyExact
import NCG.Grand.UniversalPhysicalContinuumRealizationExact
import NCG.Grand.OperationalTrivialityGNSDensityExact

/-!
# Regenerative discharge of the positive physical continuum

The regenerative packet supplies the state/tightness/coercive estimates.  Once
the separately declared observable and common-domain profile limits are given,
the completed compatible state is put in its canonical Mathlib GNS
representation and assembled into the physical continuum realization.
-/

open Filter Topology Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG.RenewalRegenerativeContinuum

universe u v

variable {V n i Hn eS eF Hp Ep : Type*}
variable [NormedAddCommGroup V]
variable [Fintype n] [DecidableEq n]
variable [Fintype i]
variable [Fintype Hn] [Fintype eS]
variable [Fintype Hp] [Fintype Ep] [DecidableEq Hp] [DecidableEq Ep]

variable {ι₀ : Type u} [Preorder ι₀] [IsDirectedOrder ι₀] [Nonempty ι₀]
variable {A : ι₀ → Type v}
variable [∀ j, NormedRing (A j)] [∀ j, StarRing (A j)]
variable [∀ j, CStarRing (A j)] [∀ j, NormedAlgebra ℂ (A j)]
variable [∀ j, StarModule ℂ (A j)]
variable {f : ∀ j k, j ≤ k → A j →⋆ₐ[ℂ] A k}
variable [DirectedSystem A (fun j k hjk => f j k hjk)]
variable [NCG.PreCStarDirectLimit.IsometricSystem f]

/-- **Regenerative discharge of the positive physical-continuum branch.**
The output uses the canonical completed state and its canonical cyclic GNS
representation; only the observable/domain convergence data deliberately left
separate by the manuscript are additional arguments. -/
theorem renewal_positive_physical_continuum
    {j : Type*} [Finite j]
    (omega : NCG.PreCStarDirectLimit.CompatibleState f)
    (P : FinitePacket
      (V := V) (n := n) (i := i) (Hn := Hn) (eS := eS) (eF := eF)
      (Hp := Hp) (Ep := Ep))
    (boundedObservable : ℕ →
      omega.completionPositiveLinearMap.GNS →L[ℂ]
        omega.completionPositiveLinearMap.GNS)
    (stageGram : ℕ → Matrix j j ℂ) (gram : Matrix j j ℂ)
    (hstageGram : ∀ m, (stageGram m).PosSemidef)
    (hgramLimit : ∀ a b,
      Tendsto (fun m => stageGram m a b) atTop (nhds (gram a b)))
    (sourceSector : Set omega.completionPositiveLinearMap.GNS)
    (hsourceDense : Dense sourceSector)
    (sourceEnergy : omega.completionPositiveLinearMap.GNS → ℝ)
    (henergyContinuous : Continuous sourceEnergy)
    (c : ℝ)
    (hcoerciveDense : ∀ x ∈ sourceSector,
      c * ‖x‖ ^ 2 ≤ sourceEnergy x)
    (centered : omega.completionPositiveLinearMap.GNS)
    (hcentered : centered ≠ 0)
    (horthogonal : inner ℂ
      (NCG.OperationalTrivialityGNS.gnsCyclicVector
        omega.completionPositiveLinearMap) centered = 0)
    (localRelation : omega.completionPositiveLinearMap.GNS →
      omega.completionPositiveLinearMap.GNS → Prop)
    (feedback : NCG.UniversalContinuum.ControlledFeedbackBranch)
    (exactCompatibility : Bool) :
    AnalyticConclusions P ∧
    Nonempty (NCG.UniversalContinuum.PhysicalContinuumRealization
      (NCG.PreCStarDirectLimit.Completion f)
      omega.completionPositiveLinearMap.GNS j) := by
  refine ⟨finitePacket_analytic_conclusions P, ?_⟩
  exact NCG.UniversalContinuum.physical_continuum_realization_of_profiles
    omega.completionPositiveLinearMap
    omega.toPreCStarState.completionPositiveLinearMap_one
    omega.completionPositiveLinearMap.gnsStarAlgHom
    (NCG.OperationalTrivialityGNS.gnsCyclicVector
      omega.completionPositiveLinearMap)
    (NCG.OperationalTrivialityGNS.gnsCyclicVector_state
      omega.completionPositiveLinearMap)
    (NCG.OperationalTrivialityGNS.gnsCyclicVector_denseRange
      omega.completionPositiveLinearMap)
    boundedObservable stageGram gram hstageGram hgramLimit
    sourceSector hsourceDense sourceEnergy henergyContinuous c
    hcoerciveDense centered hcentered horthogonal localRelation feedback
    exactCompatibility

end NCG.RenewalRegenerativeContinuum
