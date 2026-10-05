/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel
import RenewalGeometry.Continuum.ActualJetKatoRealization

/-!
# Non-vacuity of `prop:coupled-bootstrap`: the flat vacuum

For the vanishing-coupling theory data `trivSMM` (gauge algebra `gl(1)`, adjoint Higgs, zero spinor
spaces; smooth sources `trivSMM_smooth`) with the Frobenius forms (`unitaryForms_triv`):

* `flat` — the flat vacuum tuple (Minkowski metric, vanishing gauge, Higgs and spinor fields);
* `flat_exact` — it is an exact solution on every slab (`ExactOn`: all Einstein, Yang–Mills, Higgs
  and Dirac residuals and the harmonic defect vanish);
* `stateF_flat` — its actual-jet state is the constant Minkowski state;
* **`coupled_bootstrap_flat`** — Euclidean coordinates `eX` for the block inner product exist
  (`ActualJetKato.exists_state_coords`), the hypotheses of `coupled_bootstrap_orth` hold, the flat
  vacuum lies in the reference class `refSet` (compact chart margin `K = {Minkowski state}`,
  `C_tH^{k+1}` bound `R₁ = |state|`), its mismatch with itself vanishes, and
  `CoupledBootstrapConclusion` holds for the concrete slab model.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap.FlatVacuum

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci SlabSemi AposterioriShadow

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

theorem pd_const' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (μ : Fin 4)
    (x : ST 3) : pd (fun _ : ST 3 => c) μ x = 0 := by
  simp [SobolevOpen.pd]

theorem pd_const_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (μ : Fin 4) :
    pd (fun _ : ST 3 => c) μ = fun _ => 0 := funext fun x => pd_const' c μ x

theorem minkInv_symm (μ ν : Fin 4) : minkInv μ ν = minkInv ν μ := by
  unfold minkInv; split_ifs <;> simp_all

/-- **The flat vacuum**: Minkowski metric, vanishing gauge, Higgs and spinor fields. -/
def flat : Tuple 1 (MatLie 1) PUnit.{1} PUnit.{1} where
  g := fun _ => minkInv
  A := fun _ => 0
  H := fun _ => 0
  ψ := fun _ => PUnit.unit
  ψb := fun _ => PUnit.unit
  g_smooth := contDiff_const
  A_smooth := contDiff_const
  H_smooth := contDiff_const
  ψ_smooth := contDiff_const
  ψb_smooth := contDiff_const
  g_per := fun _ _ => rfl
  A_per := fun _ _ => rfl
  H_per := fun _ _ => rfl
  ψ_per := fun _ _ => rfl
  ψb_per := fun _ _ => rfl
  g_symm := fun _ => minkInv_symm
  temporal := fun _ => rfl
  det_ne := fun _ => minkInv_det
  lor := fun _ => by rw [ginvOf_minkInv]; exact minkInv_isLorChart

theorem flat_dg (x : ST 3) : flat.dg x = 0 := by
  funext α; exact pd_const' _ α x

theorem flat_ddg (x : ST 3) : flat.ddg x = 0 := by
  funext β α; simp [Tuple.ddg, flat, pd_const_fun]

theorem flat_jet_dA (x : ST 3) : (flat.jet x).dA = 0 := by
  funext γ μ; simp [Tuple.jet, flat, pd_const_fun]

theorem flat_jet_ddA (x : ST 3) : (flat.jet x).ddA = 0 := by
  funext δ γ μ; simp [Tuple.jet, flat, pd_const_fun]

theorem flat_jet_dH (x : ST 3) : (flat.jet x).dH = 0 := by
  funext γ; simp [Tuple.jet, flat, pd_const_fun]

theorem flat_jet_ddH (x : ST 3) : (flat.jet x).ddH = 0 := by
  funext δ γ; simp [Tuple.jet, flat, pd_const_fun]

theorem flat_bosF (x : ST 3) : bosF trivSMM flat x = 0 := by
  have h1 : (flat.jet x).FJ.dg = 0 := flat_dg x
  have h2 : (flat.jet x).FJ.ddg = 0 := flat_ddg x
  have h3 : (flat.jet x).A = 0 := rfl
  have h6 : (flat.jet x).H = 0 := rfl
  simp only [bosF, ActualJet.res, ActualJet.Tact, h1, h2, h3, flat_jet_dA, flat_jet_ddA, h6,
    flat_jet_dH, flat_jet_ddH]
  simp [einstein, ricci, ricciJ, chr, dchr, dchr1, dchr2, dginv, trG,
    ActualJetGauge.higgsRes, ActualJetGauge.waveH, ActualJetGauge.dDH,
    ActualJetGauge.DH, ymStressB, higgsStressB, trivSMM, DiracStressForm.coord,
    DiracStressForm.frame]
  constructor
  · funext μ ν; simp [traceRev, trG]
  · funext ν; simp [ActualJetGauge.ymRes, ActualJetGauge.ymDiv, ActualJetGauge.dFm,
      ActualJetGauge.Fm, fieldStrength]

theorem flat_CF (x : ST 3) : CF flat x = 0 := by
  funext l
  simp [CF, ActualJetWriter.C, cUp, chr, flat_dg]

/-- **The flat vacuum is an exact solution** on every slab. -/
theorem flat_exact (T : ℝ) : ExactOn trivSMM T flat := fun x _ =>
  ⟨flat_bosF x, Subsingleton.elim _ _, flat_CF x⟩

/-- The constant Minkowski state `((η, 0, 0), 0)`. -/
def minkState : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} := ((minkInv, 0, 0), 0)

/-- **The actual-jet state of the flat vacuum is the constant Minkowski state.** -/
theorem stateF_flat (x : ST 3) : stateF trivSMM flat x = minkState := by
  have h1 : (flat.jet x).FJ.dg = 0 := flat_dg x
  have h3 : (flat.jet x).A = 0 := rfl
  have h6 : (flat.jet x).H = 0 := rfl
  simp only [stateF, toP, ActualJet.state, h1, h3, h6, flat_jet_dA, flat_jet_dH, minkState]
  refine Prod.ext (Prod.ext rfl (Prod.ext ?_ ?_)) ?_
  · funext μ ν; simp [AdaptedFrame.pJ]
  · funext a μ ν; simp [AdaptedFrame.qJ]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_
      (Subsingleton.elim _ _))))))
    · funext i; rfl
    · funext a; simp [ActualJetGauge.elec, ActualJetGauge.frT, ActualJetGauge.Fm, fieldStrength]
    · funext a; simp [ActualJetGauge.magn, ActualJetGauge.dualVec, ActualJetGauge.Fsp,
        ActualJetGauge.frT, ActualJetGauge.Fm, fieldStrength]
    · simp [ActualJetGauge.frV, ActualJetGauge.DH]
    · funext a; simp [ActualJetGauge.frV, ActualJetGauge.DH]

/-- Coordinates of the bosonic residual space (any linear isomorphism). -/
def eYflat : (Fin (Module.finrank ℝ (BosP 1 (MatLie 1))) → ℝ) ≃L[ℝ] BosP 1 (MatLie 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- Coordinates of the Dirac residual space (any linear isomorphism). -/
def eYDflat : (Fin (Module.finrank ℝ (PUnit.{1} × PUnit.{1})) → ℝ) ≃L[ℝ] PUnit.{1} × PUnit.{1} :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- **Non-vacuity of `prop:coupled-bootstrap`** (flat vacuum; reference = actual = flat vacuum):
for every `k ≥ 4` and `T > 0` there are Euclidean coordinates `eX` of the block inner product
(with the Clifford unitarity relations, so `coupled_bootstrap_orth` applies), a compact chart
margin `K` and a bound `R₁` such that the flat vacuum lies in the reference class, its mismatch
with itself vanishes, and `CoupledBootstrapConclusion` holds for the concrete slab model. -/
theorem coupled_bootstrap_flat {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) :
    ∃ (n : ℕ) (eX : (Fin n → ℝ) ≃L[ℝ] StateP 1 (MatLie 1) PUnit.{1} PUnit.{1})
      (K : Set (Fin n → ℝ)) (R₁ : ℝ),
      (∀ v w, ipState (ActualJetKato.frob 1) (ActualJetKato.frob 1)
        (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ) (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ)
          (ofP (eX v)) (ofP (eX w)) = ∑ i, v i * w i) ∧
      IsCompact K ∧ K ⊆ chartC eX ∧ 0 ≤ R₁ ∧ flat ∈ refSet trivSMM eX k T K R₁ ∧
      (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT).mismatch flat flat = 0 ∧
      ∃ dstar Cstar : ℝ, 0 < dstar ∧ 0 ≤ Cstar ∧
        CoupledBootstrapConclusion (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT)
          (refSet trivSMM eX k T K R₁) dstar Cstar := by
  obtain ⟨κ, hκ⟩ := ActualJetKato.exists_state_coords ActualJetKato.unitaryForms_triv
  set eX : (Fin _ → ℝ) ≃L[ℝ] StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} :=
    κ.symm.toContinuousLinearEquiv with heX
  have hX : ∀ v w, ipState (ActualJetKato.frob 1) (ActualJetKato.frob 1)
      (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ) (0 : PUnit.{1} →ₗ[ℝ] PUnit.{1} →ₗ[ℝ] ℝ)
        (ofP (eX v)) (ofP (eX w)) = ∑ i, v i * w i := hκ
  set c := eX.symm minkState with hc
  have huC : ∀ b, uC trivSMM eX flat b = fun _ => c b := fun b => funext fun x => by
    simp only [uC, stateF_flat, hc]
  have hK : IsCompact ({c} : Set _) := isCompact_singleton
  have hKO : ({c} : Set _) ⊆ chartC eX := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    show MetChart (eX (eX.symm minkState)).1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact metChart_mink
  set R₁ := Real.sqrt (∑ b, c b ^ 2)
  have hE : ∀ t, energyQ (k + 1) (uC trivSMM eX flat) t = ∑ b, c b ^ 2 := fun t => by
    unfold energyQ
    exact Finset.sum_congr rfl fun b _ => by rw [huC b, Q_const]
  have hmem : flat ∈ refSet trivSMM eX k T {c} R₁ := by
    refine ⟨flat_exact T, fun x _ => ?_, fun t _ => ?_⟩
    · show (fun b => uC trivSMM eX flat b x) ∈ ({c} : Set _)
      simp only [huC]; rfl
    · rw [hE, Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)]
  have hmis : (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT).mismatch flat flat
      = 0 := by
    have hex := flat_exact T
    unfold SlabModel.mismatch
    rw [sub_self, norm_zero,
      (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT).exact_resB flat hex,
      (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT).exact_resD flat hex,
      (slabModel trivSMM eX eYflat eYDflat trivSMM_smooth k T hT).exact_harm flat hex]
    norm_num
  refine ⟨_, eX, {c}, R₁, hX, hK, hKO, Real.sqrt_nonneg _, hmem, hmis, ?_⟩
  exact coupled_bootstrap_orth trivSMM eX eYflat eYDflat trivSMM_smooth _ _ _ _
    ActualJetKato.unitaryForms_triv.c0 ActualJetKato.unitaryForms_triv.ci
    ActualJetKato.unitaryForms_triv.c0b ActualJetKato.unitaryForms_triv.cib hX hk hT hK hKO
    (Real.sqrt_nonneg _)

end RenewalGeometry.CoupledBootstrap.FlatVacuum
