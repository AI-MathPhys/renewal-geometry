/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedChartDynamics
import RenewalGeometry.Continuum.GeneratedChartPhysId
import RenewalGeometry.Continuum.GeneratedChargedNoGo

/-!
# A gauge-charged back-reacting instance of the coupled theorems

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`,
`cor:generated-nonempty`, `lem:generated-physical-identification` (back-reacting **charged**
spinors).

The charged quaternionic data `GenDStress.quatSMT` (gauge algebra `u(1)` acting on the spinors by
right multiplication by `i`, real Higgs with scalar Yukawa coupling, the Dirac current
`μ_S ≠ 0` in the Yang–Mills equation and the symmetric Dirac stress in the Einstein equation,
`GenDStress.quatCoupled`) do **not** satisfy `SMSmooth` (`GenChNoGo.not_smSmooth_quatSMT`), but
they satisfy the chart-local smoothness `GenChL.SMSmoothL`:

* **`quatSMT_smoothL`** — `SMSmoothL quatSMT` (the adapted frame `frU(g⁻¹)` in the Dirac current
  is smooth on Lorentzian charts, `contDiffAt_frU`);
* `quatSMT_unitary` — Clifford-unitary forms;
* **`quatSMT_charged_hyps`** — all hypotheses of the chart-local top theorems hold, with nonzero
  gauge coupling on the spinors, a nonzero spinor moment map (nonvanishing Dirac current) and a
  nonzero Dirac stress; the theorems `generated_dynamics_cpl_statL`,
  `generated_nonempty_norms_cpl_statL` apply to them (example).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenChargedInst

open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve GenNoether
  GenDiracCur GenDStress GenCplIdF ActualJetKato

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

set_option maxHeartbeats 4000000 in
/-- **The charged quaternionic data have chart-locally smooth sources.** -/
theorem quatSMT_smoothL : GenChL.SMSmoothL quatSMT where
  J ν p hc := by
    have hfr : ∀ A μ, ContDiffAt ℝ ∞
        (fun q : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × SQ × SQ => frU q.2.1 A μ) p :=
      fun A μ => by
        have h := (contDiffAt_frU hc A μ).of_le (m := ∞) le_top
        exact h.comp (f := fun q : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × SQ × SQ => q.2.1) p
          (by fun_prop)
    have e : (fun q : Met × Met × MatLie 1 × (Fin 4 → MatLie 1) × SQ × SQ =>
        quatSMT.Jcur q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 ν) =
        fun q => diracCur μSQ (diracQ 1 (by norm_num)).Fr q.1 q.2.1 q.2.2.2.2.1 q.2.2.2.2.2 ν := by
      funext q
      show (2 : ℝ) • (0 : MatLie 1 →ₗ[ℝ] MatLie 1 →ₗ[ℝ] MatLie 1) _ _ +
        diracCur μSQ _ _ _ _ _ ν = _
      simp
    rw [e]
    unfold diracCur
    fun_prop
  SH := by
    have : (fun p : Met × Met × MatLie 1 × SQ × SQ =>
        quatSMT.SH p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) =
        fun p => yukQ p.2.2.2.2 p.2.2.2.1 := by
      funext p
      show (2 * 0 * (traceForm 1 _ _ - 0 ^ 2)) • _ + yukQ _ _ = _
      simp
    rw [this]
    exact contDiff_bilin yukQ (by fun_prop) (by fun_prop)
  P2 A B := by
    have : (fun p : MatLie 1 × SQ × SQ => quatSMT.TD.P'' A B p.1 p.2.1 p.2.2) =
        fun p => -etaL A B * (p.1 0 0 * PQ p.2.1 p.2.2) := by
      funext p
      show yukP (diracQ 1 _) PQ A B p.1 p.2.1 p.2.2 = _
      unfold yukP
      simp only [LinearMap.smul_apply, LinearMap.compl₂_apply, smul_eq_mul, SpinorProlongation.mass]
      show -etaL A B * PQ p.2.1 ((0 + (1 * p.1 0 0) • (1 : Module.End ℝ SQ)) p.2.2) = _
      simp
    rw [this]
    have h1 : ContDiff ℝ ∞ (fun p : MatLie 1 × SQ × SQ => p.1 0 0) := by
      have : ContDiff ℝ ∞ (fun M : MatLie 1 => M 0 0) :=
        (contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_apply ℝ (Fin 1 → ℝ) (0 : Fin 1))
      exact this.comp contDiff_fst
    exact contDiff_const.mul (h1.mul (contDiff_bilin PQ (by fun_prop) (by fun_prop)))

/-- **The charged quaternionic data carry unitary forms.** -/
theorem quatSMT_unitary : UnitaryForms quatSMT (frob 1) (frob 1) PQ PQ where
  symG x y := by simp only [frob_apply, mul_comm]
  symV x y := by simp only [frob_apply, mul_comm]
  symS := PQ_symm
  symS' := PQ_symm
  posG := frob_pos
  posV := frob_pos
  posS := PQ_pos
  posS' := PQ_pos
  c0 := quatN_unitary.c0
  ci := quatN_unitary.ci
  c0b := quatN_unitary.c0b
  cib := quatN_unitary.cib

/-- The spinor moment map of the charged data is nonzero: the Dirac current does not vanish. -/
theorem quatSMT_muS_ne :
    quatVarT.μS ((0 : Quaternion ℝ), qU 0) (quatSM.D.Fr.c 0 ((1 : Quaternion ℝ), 0)) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 0) 0
  change PQ ((0 : Quaternion ℝ), qU 0) (rightI (swapQ ((1 : Quaternion ℝ), 0))) = 0 at h1
  simp [PQ_apply, dotQ] at h1
  change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + 0 * 0 + 1 = 0 at h1
  norm_num at h1

/-- **The charged quaternionic data satisfy all hypotheses of the chart-local coupled theorems
with nonzero gauge coupling, nonvanishing Dirac current and nonzero Dirac stress**, while the
global smoothness `SMSmooth` fails for them. -/
theorem quatSMT_charged_hyps : GenChL.SMSmoothL quatSMT ∧
    UnitaryForms quatSMT (frob 1) (frob 1) PQ PQ ∧ Nonempty (CoupledDirac quatSMT) ∧
    quatSMT.κ ≠ 0 ∧ quatSMT.D.ρ ≠ 0 ∧
    (∃ (X : MatLie 1) (φ x : SQ), quatVarT.P φ (quatSMT.D.ρ X x) ≠ 0) ∧
    quatSMT.TD.frame 0 ((1 : Quaternion ℝ), 0)
      (fun A => if A = 0 then ((1 : Quaternion ℝ), 0) else 0) (qU 0, 0) 0 0 1 ≠ 0 ∧
    ¬ SMSmooth quatSMT := by
  have hch : ∃ (X : MatLie 1) (φ x : SQ), quatVarT.P φ (quatSMT.D.ρ X x) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact quatSMT_muS_ne (quatVarT.ipG_nondeg _ fun X => by
      rw [quatVarT.μS_dual]; exact hall X _ _)
  refine ⟨quatSMT_smoothL, quatSMT_unitary, ⟨quatCoupled⟩, by norm_num [quatSMT, quatSM], ?_, hch,
    by rw [quatSMT_stress_ne]; norm_num, GenChNoGo.not_smSmooth_quatSMT⟩
  intro h0
  obtain ⟨X, φ, x, hne⟩ := hch
  rw [h0] at hne
  simp at hne

/-- `generated_nonempty_norms_cpl_statL` applies to the charged data and yields Euclidean
coordinates of the state space orthonormal for the block form. -/
example : ∃ κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ),
    ∀ v w, ipP (frob 1) (frob 1) PQ PQ (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  obtain ⟨κ, hκ, -⟩ := GenCplDynS.ChL.generated_nonempty_norms_cpl_statL quatSMT_smoothL
    quatSMT_unitary quatCoupled quatSMT_charged_hyps.2.2.2.1 (s := 3) (p := 1) le_rfl le_rfl
  exact ⟨κ, hκ⟩

/-- `generated_physical_identification_coupledDiracL` (`lem:generated-physical-identification`)
applies to the charged data. -/
example : ∃ κ : StateP 1 (MatLie 1) SQ SQ ≃ₗ[ℝ] (Fin (dimS 1 (MatLie 1) SQ SQ) → ℝ),
    ∀ v w, ipP (frob 1) (frob 1) PQ PQ (κ.symm v) (κ.symm w) = ∑ i, v i * w i := by
  obtain ⟨κ, hκ, -⟩ := GenCplIdF.ChL.generated_physical_identification_coupledDiracL
    quatSMT_smoothL quatSMT_unitary quatCoupled (mm := 2) (q := 5) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨κ, hκ⟩

end RenewalGeometry.GenChargedInst
