/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetSliceExistence
import RenewalGeometry.Continuum.GeneratedCoupledKato
import RenewalGeometry.Continuum.GeneratedChartSmooth

/-!
# Constrained Cauchy slice data are constrained actual-jet data

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`,
`lem:generated-physical-identification`: the bridge from Cauchy slice data satisfying the
Hamiltonian, momentum and Gauss constraints (in the unit-lapse zero-shift temporal gauge with the
harmonic completion of the lapse and shift time derivatives) to the constrained actual-jet data
class `GenPhysIdClosed.ConstrainedData` of the generated-dynamics chain.

* **`SliceCauchy.exists_sliceConstrained`** — a `Constrained` slice datum is the Cauchy datum of a
  slice-constrained smooth field tuple (all residuals, `C` and `∂_tC` vanish on `t = 0`), with
  the prescribed slice values and normal derivatives;
* **`SliceCauchy.constrainedData`** — its actual-jet state is a `ConstrainedData` datum;
* `stressSymm_of_coupledDirac` — back-reacting Dirac data have a symmetric stress;
* `exists_sliceConstrained_of_smooth` / `_of_smoothL` — the versions for theory data with
  `SMSmooth` or chart-local `GenChL.SMSmoothL` sources and `GenDStress.CoupledDirac`;
* **`SliceCauchy.constrained_of_sliceConstrained`** (necessity) — conversely, a completion
  `D.mkTuple P ε _` which is slice-constrained has `Constrained` slice data: the rows are exactly
  the constraints of the class.
-/

open Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation SliceExt GenHarmonic GenStress GenConstraint GenPhysIdClosed
  ActualJetRecon GenPhysId ActualJetKato

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'}

/-- **Back-reacting Dirac data have a symmetric stress.** -/
theorem stressSymm_of_coupledDirac (hC : GenDStress.CoupledDirac SM) : StressSymm SM := by
  intro fj hg hgi μ ν
  unfold stressF
  rw [GenCplKato.coord_symm_cpl hC, AJKatoMod.ymStressB_symm hC.ipG_symm hg hgi,
    AJKatoMod.higgsStressB_symm hC.ipV_symm _ _ hg]

namespace SliceCauchy

variable (D : SliceCauchy m V S S')

/-- **Completion of constrained Cauchy data** (`prop:generated-initial`, Cauchy-data completion):
for theory data with smooth bosonic residual fields and symmetric stress, a slice datum satisfying
the Hamiltonian, momentum and Gauss constraints is the Cauchy datum of a smooth periodic field
tuple which is slice-constrained, with metric `diag(-1, γ)`, `∂_tg = (2tr_γK, harmonic shift
rate, -2K)`, gauge potential `(0, A)`, `∂_tA = (0, Ȧ)`, Higgs field `H`, `∂_tH = Ḣ` and spinors
`Ψ, Ψ̄` on the slice. -/
theorem exists_sliceConstrained (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z))
    (hT : StressSymm SM) (hc : D.Constrained SM) :
    ∃ z : Tuple m V S S', SliceConstrained SM z ∧ ∀ y : Fin 3 → ℝ,
      z.g (Fin.cons 0 y) = met4 (-1) 0 (D.γ y) ∧ pd z.g 0 (Fin.cons 0 y) = D.vt y ∧
      z.A (Fin.cons 0 y) = padL (D.A y) ∧ pd z.A 0 (Fin.cons 0 y) = padL (D.Ad y) ∧
      z.H (Fin.cons 0 y) = D.H y ∧ pd z.H 0 (Fin.cons 0 y) = D.Hd y ∧
      z.ψ (Fin.cons 0 y) = D.ψ y ∧ z.ψb (Fin.cons 0 y) = D.ψb y := by
  refine ⟨D.z2 hB hT, D.z2_sliceConstrained hB hT hc, fun y => ?_⟩
  have hε := D.tup_ne (D.P2 hB hT)
  have hch := (D.exists_epsP (D.P2 hB hT)).choose_spec.2
  refine ⟨D.mk_g (hch := hch) y, D.mk_dg (hch := hch) y hε 0, D.mk_A (hch := hch) y,
    D.mk_dA (hch := hch) y hε 0, D.mk_H (hch := hch) y, D.mk_dH (hch := hch) y hε 0,
    D.mk_ψ (hch := hch) y, D.mk_ψb (hch := hch) y⟩

/-- **Constrained Cauchy data give constrained actual-jet data**: the actual-jet state of the
completion is a datum of the class `GenPhysIdClosed.ConstrainedData` of
`lem:generated-physical-identification`. -/
theorem constrainedData (hB : ∀ z : Tuple m V S S', ContDiff ℝ ∞ (bosF SM z))
    (hT : StressSymm SM) (hc : D.Constrained SM)
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) :
    ∃ z : Tuple m V S S', SliceConstrained SM z ∧ ConstrainedData SM κ (stU κ SM z) ∧
      ∀ y : Fin 3 → ℝ, z.g (Fin.cons 0 y) = met4 (-1) 0 (D.γ y) ∧
        pd z.g 0 (Fin.cons 0 y) = D.vt y ∧ z.A (Fin.cons 0 y) = padL (D.A y) ∧
        pd z.A 0 (Fin.cons 0 y) = padL (D.Ad y) ∧ z.H (Fin.cons 0 y) = D.H y ∧
        pd z.H 0 (Fin.cons 0 y) = D.Hd y ∧ z.ψ (Fin.cons 0 y) = D.ψ y ∧
        z.ψb (Fin.cons 0 y) = D.ψb y := by
  obtain ⟨z, hz, hd⟩ := D.exists_sliceConstrained hB hT hc
  exact ⟨z, hz, ⟨z, fun _ _ => rfl, hz⟩, hd⟩

/-- `exists_sliceConstrained` for smooth back-reacting Dirac data. -/
theorem exists_sliceConstrained_of_smooth (hS : SMSmooth SM) (hC : GenDStress.CoupledDirac SM)
    (hc : D.Constrained SM) : ∃ z : Tuple m V S S', SliceConstrained SM z :=
  let ⟨z, hz, _⟩ := D.exists_sliceConstrained (fun z => contDiff_bosF SM z hS)
    (stressSymm_of_coupledDirac hC) hc
  ⟨z, hz⟩

/-- `exists_sliceConstrained` for chart-locally smooth back-reacting (charged) Dirac data. -/
theorem exists_sliceConstrained_of_smoothL (hS : GenChL.SMSmoothL SM)
    (hC : GenDStress.CoupledDirac SM) (hc : D.Constrained SM) :
    ∃ z : Tuple m V S S', SliceConstrained SM z :=
  let ⟨z, hz, _⟩ := D.exists_sliceConstrained (fun z => ActualJetState.ChL.contDiff_bosFL SM z hS)
    (stressSymm_of_coupledDirac hC) hc
  ⟨z, hz⟩

/-- **Necessity of the constraint rows**: if a completion of `D` is slice-constrained, then `D`
satisfies the Hamiltonian, momentum and Gauss constraints. -/
theorem constrained_of_sliceConstrained {P : Params m V S S'} {ε : ℝ}
    {hch : ∀ x, GChart (D.gF P ε x)} (hε : ε ≠ 0)
    (hz : SliceConstrained SM (D.mkTuple P ε hch)) : D.Constrained SM := by
  intro y
  obtain ⟨hB, hD, -, -⟩ := hz y
  have hrD : (((D.mkTuple P ε hch).jet (Fin.cons 0 y)).res SM).rD = 0 := congrArg Prod.fst hD
  have hrDb : (((D.mkTuple P ε hch).jet (Fin.cons 0 y)).res SM).rDb = 0 := congrArg Prod.snd hD
  obtain ⟨h0, hs⟩ := D.einsteinConstraint_mk SM hε y hrD hrDb
  have hE : ∀ ν, einsteinConstraint SM (D.mkTuple P ε hch) (Fin.cons 0 y) ν = 0 :=
    fun ν => einsteinConstraint_of_bosF SM _ (congrArg Prod.fst hB) ν
  refine ⟨h0.symm.trans (hE 0), fun i => (hs i).symm.trans (hE i.succ), ?_⟩
  have hA : (((D.mkTuple P ε hch).jet (Fin.cons 0 y)).res SM).rA = 0 :=
    congrArg (fun b => b.2.1) hB
  have hdd := D.ddA_mk (P := Params.zero) (P' := P) (hch := D.exists_eps0.choose_spec.2)
    (hch' := hch) D.ε0_ne hε y
  have hsh := (D.agree_mk (hch := D.exists_eps0.choose_spec.2) (hch' := hch) D.ε0_ne hε y).rA_shift
    _ hdd SM 0
  have hgi : ((D.mkTuple Params.zero D.exists_eps0.choose D.exists_eps0.choose_spec.2).jet
      (Fin.cons 0 y)).FJ.gi = met4 (-1) 0 (D.γi y) :=
    D.mk_gi (hch := D.exists_eps0.choose_spec.2) y
  rw [hgi, sum_shift_A, padL_zero, neg_zero, add_zero, hA] at hsh
  exact hsh.symm

end SliceCauchy

end RenewalGeometry.GenSlice
