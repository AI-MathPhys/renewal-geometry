/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.GeneratedChartIdentification
import MathPhys.Continuum.GeneratedCoupledIdentificationFinal
import MathPhys.Continuum.GeneratedCoupledIdentification

/-!
# `lem:generated-physical-identification` under chart-local smoothness

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`, for
back-reacting Dirac data whose sources are smooth only near Lorentzian charts
(`GenChL.SMSmoothL`; gauge-charged spinors, `GenChNoGo.not_smSmooth_of_charged`):
`GenCplId.generated_physical_identification_coupled` and
`GenCplIdF.generated_physical_identification_coupledDirac` re-proved under `SMSmoothL`
(suffix `L`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! #### `generated_physical_identification_coupled` (from `Continuum/GeneratedCoupledIdentification.lean`) -/
namespace MathPhys.GenCplId.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
/-- **`lem:generated-physical-identification` for back-reacting spinors (`Σ = 𝕋³`).**  For theory
data with smooth sources, the **symmetric Dirac stress** of a Dirac pairing with the Dirac current
and the Yukawa source (`GenDStress.CoupledDirac`: the spinors back-react on the metric, the gauge
field and the Higgs field), the current Noether identity and on-shell stress conservation
(`GenCplMat.StressConservation`), and forms with the
Clifford unitarity relations, there are Euclidean coordinates `κ` of the state space such that
for every compact chart margin `K ⊇ cthickening δ K₀` the realized coefficient maps `A^j, F` of the
independent symmetric system satisfy: for every `H^q` radius `R₀` there is a Kato time `T > 0`
such that every constrained smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` and initial values
in `K₀` has a two-sided Kato solution `U` on `(-T, T) × 𝕋³`, and there are a smooth field tuple
`z` and `t₁ > 0` such that on `[0, t₁] × 𝕋³` the Kato solution is the actual-jet state of `z` and
`z` satisfies the complete Einstein, Yang–Mills, Higgs, Dirac and dual Dirac equations and the
harmonic and temporal-gauge constraints.  The defining-jet identities of the spinor jets and the
harmonic constraint propagate through the coupled constraint system
(`GenCplCon.coupled_constraints_vanish`: wave block for the harmonic defect, symmetric hyperbolic
block for the tangential and normal-prolongation spinor defects, zero-order couplings). -/
theorem generated_physical_identification_coupledL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hN : GenNoether.CurrentNoether SM)
    (hT : GenCplMat.StressConservation SM) {mm q : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm + 1 ≤ q)
    (hq2 : mm + 2 ≤ q) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δ : ℝ, 0 < δ → Metric.cthickening δ K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ) (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
            TwoSidedSol A F U₀ T U P ∧
            ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ ∀ x ∈ slab 0 t₁,
              (∀ b, U b x = κ (stateF SM z x) b) ∧
                bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  obtain ⟨κ, hκ, hreal⟩ := MathPhys.ActualJetKato.ChL.actual_jet_kato_realizationL hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δ hδ hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    MathPhys.GenCplKato.ChL.modified_kato_realization_cplL hS hU hC κ hκ K hK hKc
  refine ⟨A, F, hA, hsym, hF, hAK, hFK, fun R₀ hR₀ => ?_⟩
  obtain ⟨T, hT0, hkato⟩ := KatoGalerkin.kato_two_sided (d := 3) hm (by omega) hq2 hA hsym hF hR₀
  obtain ⟨TM, hTM0, hkatoM⟩ := KatoSmooth.kato_two_sided_smooth hm hq hAM hsymM hFM hR₀
  refine ⟨T, hT0, fun U₀ hCD hU₀ hUp hE hK₀ => ?_⟩
  obtain ⟨U, P, hUP⟩ := hkato U₀ hU₀ hUp hE
  obtain ⟨UM, PM, hMP, hMs⟩ := hkatoM U₀ hU₀ hUp hE
  refine ⟨U, P, hUP, ?_⟩
  obtain ⟨z₀, hdat₀, hC₀⟩ := hCD
  -- symmetry of the shift-transported solution
  have hU0 : ∀ y, (fun c => U₀ c (Fin.cons 0 y)) = κ (stateF SM z₀ (Fin.cons 0 y)) := fun y =>
    funext fun c => (hdat₀ c y).symm
  have hinv := GenBackward.twoSided_invariant hAM hsymM hFM (GenPhysIdFinal.tauKL κ) (fun j a v w => hτA j a v w)
    (fun a v => hτF a v) hMP (fun y => by
      rw [GenPhysIdFinal.tauKL_apply, hU0 y, GenPhysIdFinal.tauK_of_isSymmP (GenPhysIdFinal.isSymmP_stateF z₀ _)])
  -- the margin
  obtain ⟨τ, hτ, hKW⟩ := GenPhysIdFinal.exists_twoSided_mem hMP hδ hKδ hK₀
  set ε := min τ TM with hεdef
  have hε : 0 < ε := lt_min hτ hTM0
  have hKWε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → (fun c => UM c x) ∈ K := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact hKW x ⟨show -τ < x 0 by linarith [min_le_left τ TM],
      show x 0 < τ by linarith [min_le_left τ TM]⟩
  have hsymε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → AJKatoMod.IsSymmP (GenPhysIdFinal.Wof κ UM x) := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact GenPhysIdFinal.isSymmP_of_tauK (hinv x ⟨by linarith [min_le_right τ TM],
      by linarith [min_le_right τ TM]⟩)
  exact MathPhys.GenCplId.ChL.core_identification_cplL hS hU hC hN hT hκ hKc hA hsym hF hAK hFK hAM hFM hAMK hFMK hdat₀ hC₀
    hMP hMs hε (min_le_right τ TM) hKWε hsymε hT0 hUP
end MathPhys.GenCplId.ChL

/-! #### `generated_physical_identification_coupledDirac` (from `Continuum/GeneratedCoupledIdentificationFinal.lean`) -/
namespace MathPhys.GenCplIdF.ChL
open Filter Topology Set
open scoped BigOperators ContDiff NNReal
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk QLEnergy KatoGalerkin FrameCurvature HarmonicDefect
  ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge
  ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss
  GenDiracCur
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}
/-- **`lem:generated-physical-identification` for back-reacting spinors (`Σ = 𝕋³`), closed**:
the hypotheses on the theory data are smooth sources, back-reacting Dirac data
(`GenDStress.CoupledDirac`: the symmetric Dirac stress, the Dirac current and the Yukawa source
of a Dirac pairing) and unitary forms; the current and stress Noether identities are proved
(`GenDiracCur.currentNoether_of_variationalDirac`, `GenDSN.stressConservation_of_coupledDirac`). -/
theorem generated_physical_identification_coupledDiracL (hS : GenChL.SMSmoothL SM)
    (hU : UnitaryForms SM bG bV bS bS') (hC : GenDStress.CoupledDirac SM) {mm q : ℕ}
    (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm + 1 ≤ q) (hq2 : mm + 2 ≤ q) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K₀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∀ δ : ℝ, 0 < δ → Metric.cthickening δ K₀ ⊆ K →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → ∃ T > 0, ∀ U₀ : Fin (dimS m V S S') → ST 3 → ℝ,
          GenPhysIdClosed.ConstrainedData SM κ U₀ → (∀ b, ContDiff ℝ ∞ (U₀ b)) →
          (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
          (∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) →
          ∃ (U : Fin (dimS m V S S') → ST 3 → ℝ) (P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ),
            TwoSidedSol A F U₀ T U P ∧
            ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ ∀ x ∈ slab 0 t₁,
              (∀ b, U b x = κ (stateF SM z x) b) ∧
                bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 :=
  MathPhys.GenCplId.ChL.generated_physical_identification_coupledL hS hU hC
    (currentNoether_of_variationalDirac hC.toVariationalDirac)
    (GenDSN.stressConservation_of_coupledDirac hC) hm hq hq2
end MathPhys.GenCplIdF.ChL
