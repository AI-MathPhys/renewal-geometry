/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientDefectUI

/-!
# Non-vacuity of `critical_quotient_defect_SM`

The flat vacuum (identity coframe, `A = H = Ψ = Ψ̄ = 0`) with the physical bank `physicalBank`
(`κ = 1`, `Λ = 0`, unit couplings, `λ = 1`, `v = 0`) and a vanishing Yukawa mass satisfies every
hypothesis of `critical_quotient_defect_SM` (with zero budgets `c_h = ε_h = 0`): the complete
first-variation covector vanishes at the flat jet, so the box first variations vanish.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet FirstVariationCalculus
  QuadraticPacketDefect BosonicStressDefectBox CurvatureCovariance CriticalQuotientDensity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- The flat vacuum field tuple. -/
def flatZ : FieldTuple (Fin 5) := FieldTuple.mk (fun _ => flatCoframe) 0 0 0 0

@[simp] theorem flatZ_e : flatZ.e = fun _ => flatCoframe := rfl
@[simp] theorem flatZ_A : flatZ.A = 0 := rfl
@[simp] theorem flatZ_H : flatZ.H = 0 := rfl
@[simp] theorem flatZ_Ψ : flatZ.Ψ = 0 := rfl
@[simp] theorem flatZ_Ψb : flatZ.Ψb = 0 := rfl

theorem redJet_flatZ (x : E4) :
    redJet flatZ x = (RJet.mk flatCoframe 0 0 0 0 0 0 0 0 0 : RJet (Fin 5)) := by
  have hA : curvatureF (0 : E4 → ConnFibre) x = 0 := by rw [curvatureF_zero]; rfl
  have hK : covDerivHiggs (0 : E4 → ConnFibre) (0 : E4 → HiggsFibre) x = 0 := by
    rw [covDerivHiggs_zero]; rfl
  have he : (fun i => pd (fun _ : E4 => flatCoframe) i x) = 0 := funext fun i => pd_const' _ i x
  have hΨ : (fun i => pd (0 : E4 → SpinorFibre (Fin 5)) i x) = 0 :=
    funext fun i => pd_const' (0 : SpinorFibre (Fin 5)) i x
  simp only [redJet, flatZ_e, flatZ_A, flatZ_H, flatZ_Ψ, flatZ_Ψb, hA, hK, he, hΨ, Pi.zero_apply]

theorem gravCov_flatZ (R : RJet (Fin 5)) (he : R.de = 0) :
    gravCov (C := Fin 5) physicalBank R = 0 := by
  simp only [gravCov, gravCovF, he, map_zero, zero_apply, zero_add, physicalBank]
  simp

theorem smCov_flatZ (mY : CoefficientBank Unit → ℂ) (R : RJet (Fin 5)) (hA : R.A = 0)
    (hF : R.F = 0) (hH : R.H = 0) (hK : R.K = 0) (hΨ : R.Ψ = 0) (hΨb : R.Ψb = 0)
    (hdΨ : R.dΨ = 0) (hdΨb : R.dΨb = 0) :
    bosonCov physicalBank R + diracCov (defCarrier Unit mY) physicalBank R = 0 := by
  have hq : higgsQuad (0 : HiggsFibre) = 0 := by simp [higgsQuad]
  have hpU : pU (defCarrier Unit mY) R = 0 := by
    simp only [pU, ContinuousLinearMap.prod_apply]
    rw [show πΨb R = R.Ψb from rfl, show πΨ R = R.Ψ from rfl, hΨ, hΨb]; rfl
  have hpW : pW (defCarrier Unit mY) R = 0 := by
    simp only [pW, ContinuousLinearMap.prod_apply]
    rw [show πdΨ R = R.dΨ from rfl, show πdΨb R = R.dΨb from rfl, hdΨ, hdΨb]; rfl
  simp only [bosonCov, diracCov, hA, hF, hH, hK, hΨb, hΨ, hpU, hpW, hq, map_zero,
    zero_apply, smul_zero, Finset.sum_const_zero, add_zero, physicalBank,
    sub_zero, ContinuousLinearMap.zero_comp]
  simp

theorem fullCov_flatZ (mY : CoefficientBank Unit → ℂ) (x : E4) :
    fullCov mY physicalBank (redJet flatZ x) = 0 := by
  rw [redJet_flatZ, fullCov, add_assoc, gravCov_flatZ _ rfl, zero_add]
  exact smCov_flatZ mY _ rfl rfl rfl rfl rfl rfl rfl rfl


/-! ### The flat hypotheses -/

section FlatHyps

theorem contDiff_flatZ : ContDiff ℝ ∞ flatZ.e ∧ ContDiff ℝ ∞ flatZ.A ∧ ContDiff ℝ ∞ flatZ.H ∧
    ContDiff ℝ ∞ flatZ.Ψ ∧ ContDiff ℝ ∞ flatZ.Ψb :=
  ⟨contDiff_const, contDiff_const, contDiff_const, contDiff_const, contDiff_const⟩

theorem flatZ_lie (y : E4) (μ : Fin 4) : flatZ.A y μ ∈ smLie := smLie.zero_mem

theorem flat_coframeLimit (a b : E4) (φ : ℕ → ℕ) (_hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CoframeLimitH1 (box a b) (fun _ => flatZ.e) (φ ∘ ψ) := by
  have : IsFiniteMeasure (volume.restrict (box a b)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  refine ⟨id, strictMono_id, fun _ => flatCoframe, 0, fun i ν => memLp_const _,
    fun i ν μ => MemLp.zero, fun i ν => ⟨?_, ?_, fun μ => ?_⟩⟩
  · simp only [flatZ_e, sub_self]
    exact tendsto_const_nhds.congr fun _ => eLpNorm_zero.symm
  · simp only [flatZ_e, sub_self]
    exact tendsto_const_nhds.congr fun _ => eLpNorm_zero.symm
  · simp only [flatZ_e, pd_const', Pi.zero_apply, sub_self]
    exact tendsto_const_nhds.congr fun _ => eLpNorm_zero.symm

theorem curvVec_flatZ (x : E4) : curvVec (connM (0 : E4 → ConnFibre)) x = 0 := by
  have h1 : entries (connM (0 : E4 → ConnFibre)) = 0 := by
    funext ν c e y; simp [entries, connM]
  have h2 : entryGrad (connM (0 : E4 → ConnFibre)) = 0 := by
    funext ν c e μ y; simp [entryGrad, connM, pd_const']
  ext p
  simp [curvVec, h1, h2, curvatureW]

theorem curvEnergy_flatZ (S : Set E4) : curvEnergy (connM flatZ.A) S = 0 := by
  simp [curvEnergy, curvVec_flatZ]

theorem curvUI_flatZ (a b : E4) :
    CriticalCurvatureUI volume (box a b) (fun (_ : ℕ) x => curvVec (connM flatZ.A) x) :=
  (criticalCurvatureUI_iff _ _ _).2 fun ε _ => ⟨1, one_pos, fun h E _ _ _ => by
    simp [curvVec_flatZ]⟩

theorem embH_zero : embH 0 = 0 := by
  funext c
  refine Fin.addCases (m := 3) (n := 2) (motive := fun c => embH 0 c = (0 : Fin 5 → ℂ) c)
    (fun i => ?_) (fun i => ?_) c <;> simp [embH]

theorem matterSec_flatZ (s : MIdx) : matterSec flatZ s = 0 := by
  funext y c
  rcases s with _ | s | s
  · simp [matterSec, embH_zero]
  · simp [matterSec]
  · simp [matterSec]

theorem covDerV_flatZ (μ : Fin 4) (y : E4) :
    covDerV (connM (0 : E4 → ConnFibre)) (0 : E4 → Fin 5 → ℂ) μ y = 0 := by
  funext c
  simp [covDerV, pdV, pd_const', Matrix.mulVec]

theorem Q3_flatZ (a b : E4) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (_ : ℕ) s,
    ∑ e, eLpNorm (fun y => matterSec flatZ s y e) 2 (volume.restrict (box a b)) +
      ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM flatZ.A) (matterSec flatZ s) μ y e) 2
        (volume.restrict (box a b)) ≤ B := by
  refine ⟨0, by simp, fun _ s => ?_⟩
  simp [covDerV_flatZ, matterSec_flatZ]

theorem boxVariation_flatZ (S : Set E4) (v : FieldTuple (Fin 5)) :
    boxVariation (fun _ => (0 : ℂ)) physicalBank S flatZ v = 0 := by
  simp [boxVariation, fullCov_flatZ]

end FlatHyps

/-! ### The theorem applies to the flat vacuum -/

theorem zero_mem_box_unit : (0 : E4) ∈ box (fun _ => (-1 : ℝ)) (fun _ => 1) := by
  simp only [box, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies, Pi.zero_apply]
  intro i; norm_num

/-- **Non-vacuity of `critical_quotient_defect_SM`**: the flat vacuum sequence with the physical
bank (`Λ = 0`, `v = 0`), vanishing Yukawa mass, zero budgets `c_h = ε_h = 0`, the chart `(-1, 1)⁴`
and `K' = {0}` satisfies every hypothesis, so the theorem applies (and produces its Coulomb cover of `K'`). -/
theorem critical_quotient_defect_SM_applies_flat :
    ∃ (N : ℕ) (ctr : Fin N → E4) (r : ℝ), 0 < r ∧ ({0} : Set E4) ⊆ ⋃ j, innerCube (ctr j) r := by
  obtain ⟨N, ctr, r, hr, -, -, hcov, -⟩ := critical_quotient_defect_SM (Ysec := Unit) (fun _ => (0 : ℂ))
    ⟨fun _ => 0, continuous_const, fun _ => rfl⟩ (a := fun _ => -1) (b := fun _ => 1)
    (fun _ => flatZ) (fun _ => contDiff_flatZ.1) (fun _ => contDiff_flatZ.2.1)
    (fun _ => contDiff_flatZ.2.2.1) (fun _ => contDiff_flatZ.2.2.2.1)
    (fun _ => contDiff_flatZ.2.2.2.2) (fun _ y μ => flatZ_lie y μ) (fun _ => physicalBank)
    ⟨{physicalBank}, isCompactBankSet_physical, fun _ => rfl⟩ (Ke := {flatCoframe})
    isCompact_singleton (singleton_subset_iff.mpr (coframeChart_subset_GL flatCoframe_mem_chart))
    (fun _ _ _ => rfl) (flat_coframeLimit _ _)
    ⟨0, fun _ => (curvEnergy_flatZ _).trans_le (by simp)⟩ (curvUI_flatZ _ _) (Q3_flatZ _ _)
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ v _ => by simp [boxVariation_flatZ]) (fun _ _ _ => by simp)
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    (K' := {0}) isCompact_singleton (singleton_subset_iff.mpr zero_mem_box_unit) (η := 1) one_pos
  exact ⟨N, ctr, r, hr, hcov⟩

end RenewalGeometry.CriticalQuotientRows
