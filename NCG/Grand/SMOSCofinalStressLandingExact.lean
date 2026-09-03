/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EnergyHamiltonianIncidenceExact
import NCG.Grand.StressCompositeWickExcess
import NCG.Grand.BrandNewEasy03

/-!
# Operator landing for the cofinal stress/current sector

This file isolates the functional-analytic conclusion of
`thm:SMOS-cofinal-stress` from its genuinely analytic OS compactness input.
A cutoff insertion lying below a closed limiting insertion is closable;
closed Ward defects which vanish on one graph core vanish on their whole
domains; equality of the energy and Hamiltonian closures follows from their
common core; and a transported quotient-visible Wick excess simultaneously
proves non-Gaussianity and scheme-invariant nonvanishing.

The trace-anomaly conclusion is stated with the actual finite source matrices:
an admissible scheme change preserves both the identity projector and the
ambient represented anomaly source.  Thus the absolute identity/pressure
direction is not silently quotiented into the anomaly class.
-/

open Matrix

namespace NCG
namespace SMOSCofinalStressLanding

open EnergyHamiltonianIncidenceExact
open SourceCompleteWardAtlasExact
open StressCompositeWickExcess

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A represented insertion inherited as a restriction of a closed limiting
operator is closable.  This is the graph-compactness-to-closability step used
for both current and stress insertions. -/
theorem isClosable_of_le_closed
    (insertion limit : E →ₗ.[ℂ] G)
    (hlimit : limit.IsClosed) (hle : insertion ≤ limit) :
    insertion.IsClosable :=
  hlimit.isClosable.leIsClosable hle

/-- Every selected Ward relation extends from the common graph core to the
whole domain of its closed limiting defect. -/
theorem ward_relations_vanish_of_common_core
    {ι : Type*} (defect : ι → E →ₗ.[ℂ] G) (S : Submodule ℂ E)
    (hclosed : ∀ i, (defect i).IsClosed)
    (hcore : ∀ i, (defect i).HasCore S)
    (hzero : ∀ i (x : E) (hx : x ∈ S),
      defect i ⟨x, (hcore i).le_domain hx⟩ = 0) :
    ∀ i (x : (defect i).domain), defect i x = 0 := by
  intro i
  exact closed_defect_vanishes_on_core
    (defect i) (hclosed i) S (hcore i) (hzero i)

/-- The operator-algebraic landing conclusion of the conditional OS
stress/current continuum theorem.

The closed extensions are the outputs of the inherited compactness/domain
packet.  The theorem derives, rather than assumes, closability of the landed
insertions, extension of every selected Ward identity, equality of the energy
and OS-Hamiltonian closures, non-Gaussianity, and preservation of the nonzero
excess under an admissible scheme change. -/
theorem cofinal_stress_operator_landing
    {ι k : ℕ}
    {Stress Composite StressQ CompositeQ Value : Type*}
    {Stress' Composite' Value' : Type*}
    [AddCommGroup Stress] [Module ℂ Stress]
    [AddCommGroup Composite] [Module ℂ Composite]
    [AddCommGroup StressQ] [Module ℂ StressQ]
    [AddCommGroup CompositeQ] [Module ℂ CompositeQ]
    [AddCommGroup Value] [Module ℂ Value]
    [AddCommGroup Stress'] [Module ℂ Stress']
    [AddCommGroup Composite'] [Module ℂ Composite']
    [AddCommGroup Value'] [Module ℂ Value']
    (current stress currentLimit stressLimit : E →ₗ.[ℂ] G)
    (hcurrentLimit : currentLimit.IsClosed)
    (hstressLimit : stressLimit.IsClosed)
    (hcurrentLe : current ≤ currentLimit)
    (hstressLe : stress ≤ stressLimit)
    (defect : Fin ι → E →ₗ.[ℂ] G) (core : Submodule ℂ E)
    (hdefectClosed : ∀ i, (defect i).IsClosed)
    (hdefectCore : ∀ i, (defect i).HasCore core)
    (hdefectZero : ∀ i (x : E) (hx : x ∈ core),
      defect i ⟨x, (hdefectCore i).le_domain hx⟩ = 0)
    (energy hamiltonian : E →ₗ.[ℂ] G)
    (henergy : energy.IsClosable) (hhamiltonian : hamiltonian.IsClosable)
    (henergyCore : energy.closure.HasCore core)
    (hhamiltonianCore : hamiltonian.closure.HasCore core)
    (henergyEq : ∀ (x : E) (hx : x ∈ core),
      energy.closure ⟨x, henergyCore.le_domain hx⟩ =
        hamiltonian.closure ⟨x, hhamiltonianCore.le_domain hx⟩)
    (positiveHamiltonian : Prop) (hpositive : positiveHamiltonian)
    (packet : QuotientPacket (𝕜 := ℂ) k Stress Composite
      StressQ CompositeQ Value)
    (hrelation : packet.stressCurrentRelation)
    (hincidence : packet.energyHamiltonianIncidence)
    (hvisible : excess packet.visibleDirect packet.visibleWick ≠ 0)
    (scheme : SchemeChange (𝕜 := ℂ) (Stress := StressQ)
      (Composite := CompositeQ) (Value := Value) (Stress' := Stress')
      (Composite' := Composite') (Value' := Value'))
    (direct' wick' : Tensor (𝕜 := ℂ) k Stress' Composite' Value')
    (hdirect : Covariant scheme packet.visibleDirect direct')
    (hwick : Covariant scheme packet.visibleWick wick') :
    current.IsClosable ∧
      stress.IsClosable ∧
      (∀ i (x : (defect i).domain), defect i x = 0) ∧
      energy.closure = hamiltonian.closure ∧
      positiveHamiltonian ∧
      (¬ IsGaussianOnPacket packet.direct packet.wick) ∧
      (excess direct' wick' = 0 ↔
        excess packet.visibleDirect packet.visibleWick = 0) ∧
      excess direct' wick' ≠ 0 := by
  have hcurrent : current.IsClosable :=
    isClosable_of_le_closed current currentLimit hcurrentLimit hcurrentLe
  have hstress : stress.IsClosable :=
    isClosable_of_le_closed stress stressLimit hstressLimit hstressLe
  have hward : ∀ i (x : (defect i).domain), defect i x = 0 :=
    ward_relations_vanish_of_common_core defect core hdefectClosed
      hdefectCore hdefectZero
  have henergyHamiltonian : energy.closure = hamiltonian.closure :=
    operator_closures_eq_of_common_core energy hamiltonian henergy hhamiltonian
      core henergyCore hhamiltonianCore henergyEq
  have hstressPacket :=
    stress_linked_primitive_non_gaussianity_and_scheme_invariance
      packet hrelation hincidence hvisible scheme direct' wick' hdirect hwick
  have hvisible' : excess direct' wick' ≠ 0 := by
    intro hzero
    exact hvisible (hstressPacket.2.mp hzero)
  exact ⟨hcurrent, hstress, hward, henergyHamiltonian, hpositive,
    hstressPacket.1, hstressPacket.2, hvisible'⟩

section TraceScheme

variable {m p q r s p' : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype p] [DecidableEq p]
variable [Fintype q] [DecidableEq q]
variable [Fintype r] [DecidableEq r]
variable [Fintype s] [DecidableEq s]
variable [Fintype p'] [DecidableEq p']

/-- The trace part of the landing theorem: an admissible change of represented
operator and nuisance coordinates preserves the identity range separately and
preserves the represented anomaly source as an ambient physical vector. -/
theorem trace_anomaly_lands_scheme_covariantly
    (I₀ : Matrix m p ℂ) (N₀ : Matrix m q ℂ) (O : Matrix m r ℂ)
    (Ssc : Matrix m s ℂ) (I₀' : Matrix m p' ℂ)
    (hPI : smosTraceRangeProj I₀' = smosTraceRangeProj I₀)
    (U : Matrix q q ℂ) [Invertible U]
    (M : Matrix r r ℂ) [Invertible M]
    (R : Matrix q r ℂ) (R₀ : Matrix p r ℂ) :
    smosTraceRangeProj I₀' = smosTraceRangeProj I₀ ∧
      smosTraceRangeProj
          (smosTraceComposite I₀' (N₀ * U)
            (O * M + N₀ * R + I₀ * R₀)) * Ssc =
        smosTraceRangeProj (smosTraceComposite I₀ N₀ O) * Ssc := by
  exact ⟨hPI,
    smos_trace_scheme_anomaly_source_invariance
      I₀ N₀ O Ssc I₀' hPI U M R R₀⟩

end TraceScheme

end SMOSCofinalStressLanding
end NCG
