/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSlabSymmetric
import RenewalGeometry.Continuum.CoupledBootstrapFlatVacuum

/-!
# Regular reference solutions for the native closure: constant backgrounds

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` ("Let `z_*` be a regular
torsion-free Einstein–Standard-Model solution on `Q = [0,T] × 𝕋³`, written in harmonic coordinates
and temporal internal gauge"): the reference class `refSet` of `prop:coupled-bootstrap` used by
`thm:native-closure` is non-empty for the slab data of a slab model whenever the model admits a
constant background.

* **`vacTuple`** (generic) — the constant background: Minkowski metric, vanishing gauge potential
  and spinors, constant Higgs value `H₀`.
* **`vacTuple_exact`** (generic) — it is an exact solution on every slab (all Einstein,
  Yang–Mills, Higgs and Dirac residuals and the harmonic defect vanish) whenever the
  cosmological balance `Λ + κλ(⟨H₀,H₀⟩ - v²)² = 0` holds and the Yang–Mills current and Higgs
  source of the theory data vanish at the background.
* **`vacTuple_mem_refSet`** (generic) — for any state coordinates the constant background lies in
  the reference class with the compact chart margin `{state}` and `C_tH^{k+1}` bound `|state|`.
* **`refSet_nonempty_slab`** — for a slab model with `Λ + κλ_Hv_H⁴ = 0` (the symmetric vacuum
  `H₀ = 0`), in the orthonormal coordinates `SlabSymmetric.slabX`, the reference class is
  non-empty; **`refSet_nonempty_slab_higgs`** — the same for a Higgs vacuum
  `λ_H(⟨H₀,H₀⟩ - v_H²) = 0` when `Λ = 0`.
* `refSet_nonempty_diracSlab` — non-vacuity for the concrete slab model `diracSlab`.

A general slab model (`Λ` unconstrained) need not admit a constant background (the flat metric is
a solution only for vanishing effective cosmological constant); the manuscript supplies the
reference solution as data (`thm:native-closure`) and a backreacting homogeneous example in
`prop:homogeneous`.
-/

open Finset Set

noncomputable section

namespace RenewalGeometry.RefSetNonempty

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci SlabSemi AposterioriShadow CoupledBootstrap

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

section Generic

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **The constant background**: Minkowski metric, vanishing gauge potential and spinors,
constant Higgs value `H₀`. -/
def vacTuple (H₀ : V) : Tuple m V S S' where
  g := fun _ => minkInv
  A := fun _ => 0
  H := fun _ => H₀
  ψ := fun _ => 0
  ψb := fun _ => 0
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
  g_symm := fun _ => FlatVacuum.minkInv_symm
  temporal := fun _ => rfl
  det_ne := fun _ => minkInv_det
  lor := fun _ => by rw [ginvOf_minkInv]; exact minkInv_isLorChart

variable (H₀ : V)

theorem vac_dg (x : ST 3) : (vacTuple (m := m) (S := S) (S' := S') H₀).dg x = 0 := by
  funext α; exact FlatVacuum.pd_const' _ α x

theorem vac_ddg (x : ST 3) : (vacTuple (m := m) (S := S) (S' := S') H₀).ddg x = 0 := by
  funext β α; simp [Tuple.ddg, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_dA (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).dA = 0 := by
  funext γ μ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_ddA (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ddA = 0 := by
  funext δ γ μ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_dH (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).dH = 0 := by
  funext γ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_ddH (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ddH = 0 := by
  funext δ γ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_cψ (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).cψ = 0 := by
  funext γ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

theorem vac_jet_cψb (x : ST 3) : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).cψb = 0 := by
  funext γ; simp [Tuple.jet, vacTuple, FlatVacuum.pd_const_fun]

variable (SM : SMData (MatLie m) V S S')

/-- **The constant background solves the bosonic rows** under the cosmological balance and
vanishing current and Higgs source at the background. -/
theorem vac_bosF (hE : SM.Λ + SM.κ * (SM.lamH * (SM.ipV H₀ H₀ - SM.vH ^ 2) ^ 2) = 0)
    (hJ : ∀ ν, SM.Jcur minkInv minkInv H₀ 0 0 0 ν = 0) (hSH : SM.SH minkInv minkInv H₀ 0 0 = 0)
    (x : ST 3) : bosF SM (vacTuple (m := m) (S := S) (S' := S') H₀) x = 0 := by
  have h1' : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).FJ.dg = 0 := vac_dg H₀ x
  have h2' : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).FJ.ddg = 0 := vac_ddg H₀ x
  have h3 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).A = 0 := rfl
  have h6 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).H = H₀ := rfl
  have h7 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψ = 0 := rfl
  have h8 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψb = 0 := rfl
  have h9 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).FJ.g = minkInv := rfl
  simp only [bosF, ActualJet.res, ActualJet.Tact, h1', h2', h3, vac_jet_dA, vac_jet_ddA, h6,
    vac_jet_dH, vac_jet_ddH, h7, h8, vac_jet_cψ, vac_jet_cψb, h9]
  simp [einstein, ricci, ricciJ, chr, dchr, dchr1, dchr2, dginv, trG,
    ActualJetGauge.higgsRes, ActualJetGauge.waveH, ActualJetGauge.dDH,
    ActualJetGauge.DH, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, ActualJet.Xs, cov]
  have hgi : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).FJ.gi = minkInv := ginvOf_minkInv
  have hFm : ActualJetGauge.Fm (0 : Fin 4 → MatLie m) 0 = 0 := by
    funext μ ν; simp [ActualJetGauge.Fm, fieldStrength]
  have hDH : ActualJetGauge.DH (0 : Fin 4 → MatLie m) H₀ 0 = 0 := by
    funext μ; simp [ActualJetGauge.DH]
  rw [hgi, hFm, hDH]
  refine ⟨?_, ?_, hSH⟩
  · have e : (fun a b => SM.Λ * minkInv a b - SM.κ * (∑ α, ∑ β, minkInv α β *
        (SM.ipG ((0 : Fin 4 → Fin 4 → MatLie m) a α)) ((0 : Fin 4 → Fin 4 → MatLie m) b β) -
        4⁻¹ * minkInv a b * ∑ α, ∑ β, ∑ γ, ∑ δ, minkInv α γ * minkInv β δ *
          (SM.ipG ((0 : Fin 4 → Fin 4 → MatLie m) α β)) ((0 : Fin 4 → Fin 4 → MatLie m) γ δ) +
        -(minkInv a b * (SM.lamH * ((SM.ipV H₀) H₀ - SM.vH ^ 2) ^ 2)))) = fun _ _ => 0 := by
      funext a b
      simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, sub_zero, zero_add]
      linear_combination (minkInv a b) * hE
    rw [e]
    funext μ ν; simp [traceRev, trG]
  · funext ν
    simp [ActualJetGauge.ymRes, ActualJetGauge.ymDiv, ActualJetGauge.dFm, ActualJetGauge.Fm,
      fieldStrength, hJ]

/-- The constant background solves both Dirac rows (vanishing spinors). -/
theorem vac_dirF (x : ST 3) : dirF SM (vacTuple (m := m) (S := S) (S' := S') H₀) x = 0 := by
  have h3 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).A = 0 := rfl
  have h7 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψ = 0 := rfl
  have h8 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψb = 0 := rfl
  simp only [dirF, ActualJet.res, h3, h7, h8, vac_jet_cψ, vac_jet_cψb, vac_jet_dA]
  simp [ActualJet.rD, resD, dirac, mass, cov, ActualJetSpinor.dψf]

/-- The constant background is in harmonic gauge. -/
theorem vac_CF (x : ST 3) : CF (vacTuple (m := m) (S := S) (S' := S') H₀) x = 0 := by
  funext l
  simp [CF, ActualJetWriter.C, cUp, chr, vac_dg]

/-- **The constant background is an exact solution on every slab.** -/
theorem vacTuple_exact (hE : SM.Λ + SM.κ * (SM.lamH * (SM.ipV H₀ H₀ - SM.vH ^ 2) ^ 2) = 0)
    (hJ : ∀ ν, SM.Jcur minkInv minkInv H₀ 0 0 0 ν = 0) (hSH : SM.SH minkInv minkInv H₀ 0 0 = 0)
    (T : ℝ) : ExactOn SM T (vacTuple (m := m) (S := S) (S' := S') H₀) := fun x _ =>
  ⟨vac_bosF H₀ SM hE hJ hSH x, vac_dirF H₀ SM x, vac_CF H₀ x⟩

/-- The constant state of the background. -/
def vacState : StateP m V S S' := ((minkInv, 0, 0), (0, 0, 0, H₀, 0, 0, 0, 0, 0, 0))

/-- **The actual-jet state of the constant background is constant.** -/
theorem stateF_vac (x : ST 3) :
    stateF SM (vacTuple (m := m) (S := S) (S' := S') H₀) x = vacState H₀ := by
  have h1 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).FJ.dg = 0 := vac_dg H₀ x
  have h3 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).A = 0 := rfl
  have h6 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).H = H₀ := rfl
  have h7 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψ = 0 := rfl
  have h8 : ((vacTuple (m := m) (S := S) (S' := S') H₀).jet x).ψb = 0 := rfl
  simp only [stateF, toP, ActualJet.state, h1, h3, h6, h7, h8, vac_jet_dA, vac_jet_dH,
    vac_jet_cψ, vac_jet_cψb, vacState]
  refine Prod.ext (Prod.ext rfl (Prod.ext ?_ ?_)) ?_
  · funext μ ν; simp [AdaptedFrame.pJ]
  · funext a μ ν; simp [AdaptedFrame.qJ]
  · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_
      (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))))))))
    · funext i; rfl
    · funext a; simp [ActualJetGauge.elec, ActualJetGauge.frT, ActualJetGauge.Fm, fieldStrength]
    · funext a; simp [ActualJetGauge.magn, ActualJetGauge.dualVec, ActualJetGauge.Fsp,
        ActualJetGauge.frT, ActualJetGauge.Fm, fieldStrength]
    · simp [ActualJetGauge.frV, ActualJetGauge.DH]
    · funext a; simp [ActualJetGauge.frV, ActualJetGauge.DH]
    · funext a; simp [ActualJet.Xs, cov, ActualJetSpinor.dψf]
    · funext a; simp [ActualJet.Xs, cov, ActualJetSpinor.dψf]

/-- **The constant background lies in the reference class** of `prop:coupled-bootstrap` for any
state coordinates: compact chart margin `{eX⁻¹ state}`, `C_tH^{k+1}` bound `|eX⁻¹ state|`. -/
theorem vacTuple_mem_refSet {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
    (hE : SM.Λ + SM.κ * (SM.lamH * (SM.ipV H₀ H₀ - SM.vH ^ 2) ^ 2) = 0)
    (hJ : ∀ ν, SM.Jcur minkInv minkInv H₀ 0 0 0 ν = 0) (hSH : SM.SH minkInv minkInv H₀ 0 0 = 0)
    (k : ℕ) (T : ℝ) :
    IsCompact ({eX.symm (vacState H₀)} : Set (Fin n → ℝ)) ∧
      ({eX.symm (vacState H₀)} : Set (Fin n → ℝ)) ⊆ chartC eX ∧
      0 ≤ Real.sqrt (∑ b, (eX.symm (vacState H₀)) b ^ 2) ∧
      vacTuple (m := m) (S := S) (S' := S') H₀ ∈ refSet SM eX k T {eX.symm (vacState H₀)}
        (Real.sqrt (∑ b, (eX.symm (vacState H₀)) b ^ 2)) := by
  set c := eX.symm (vacState H₀) with hc
  have huC : ∀ b, uC SM eX (vacTuple (m := m) (S := S) (S' := S') H₀) b = fun _ => c b :=
    fun b => funext fun x => by simp only [uC, stateF_vac, hc]
  refine ⟨isCompact_singleton, ?_, Real.sqrt_nonneg _, vacTuple_exact H₀ SM hE hJ hSH T,
    fun x _ => ?_, fun t _ => ?_⟩
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have := uC_mem_chart SM eX (vacTuple (m := m) (S := S) (S' := S') H₀) 0
    simp only [huC] at this
    exact this
  · show (fun b => uC SM eX (vacTuple (m := m) (S := S) (S' := S') H₀) b x) ∈ ({c} : Set _)
    simp only [huC]; rfl
  · have hE' : energyQ (k + 1) (uC SM eX (vacTuple (m := m) (S := S) (S' := S') H₀)) t =
        ∑ b, c b ^ 2 := by
      unfold energyQ
      exact Finset.sum_congr rfl fun b _ => by rw [huC b, Q_const]
    rw [hE', Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)]

end Generic

/-! ### The slab data of a slab model -/

section Slab

open SlabData NativeDensity NativeModel SlabSymmetric

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The Riesz vector of the zero function vanishes. -/
theorem rieszVec_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) :
    rieszVec hB (fun _ => 0) = 0 := by
  simp [rieszVec]

/-- The slab Yang–Mills current vanishes at a constant Higgs background with vanishing gauge
field and spinors. -/
theorem slab_Jcur_vac (δ : ℝ) (H₀ : 𝓗) (ν : Fin 4) :
    (toSMData M δ).Jcur minkInv minkInv H₀ 0 0 0 ν = 0 := by
  change Jcur M δ minkInv minkInv H₀ (0 : Fin 4 → 𝓗) (0 : 𝓢) (0 : CoSpinor 𝓢) ν = 0
  unfold Jcur
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hr : ∀ c : 𝔄 → ℝ, c = (fun _ => 0) → rieszVec M.ipA_nondeg c = 0 := by
    rintro c rfl; exact rieszVec_zero M.ipA_nondeg
  rw [hr _ ?_, map_zero, map_zero, smul_zero]
  funext x
  simp [curVal]

/-- The slab Higgs source vanishes at a critical point of the Higgs potential with vanishing
spinors. -/
theorem slab_SH_vac (δ : ℝ) (H₀ : 𝓗)
    (hH : M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) = 0 ∨ H₀ = 0) :
    (toSMData M δ).SH minkInv minkInv H₀ 0 0 = 0 := by
  change SH M H₀ (0 : 𝓢) (0 : CoSpinor 𝓢) = 0
  have h : srcVal M H₀ 0 0 = fun _ => 0 := by
    funext η
    rcases hH with hH | rfl
    · simp only [srcVal, map_zero, Complex.zero_re, add_zero, ContinuousLinearMap.zero_apply]
      linear_combination (2 * (M.hermH η H₀ + M.hermH H₀ η)) * hH
    · simp [srcVal]
  simp only [SH, h, rieszVec_zero, smul_zero]
  rfl

/-- **`refSet` is non-empty for slab models with `Λ + κλ_Hv_H⁴ = 0`** (symmetric vacuum `H₀ = 0`,
flat metric): in the orthonormal coordinates `slabX` there are a compact chart margin `K` and a
bound `R₁ ≥ 0` for which the reference class of `thm:native-closure` contains the flat vacuum. -/
theorem refSet_nonempty_slab (hc : M.Λ + M.κ * (M.lamH * M.vH ^ 4) = 0) (δ : ℝ) (k : ℕ)
    (T : ℝ) : ∃ (K : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)) (R₁ : ℝ),
      IsCompact K ∧ K ⊆ chartC (slabX M) ∧ 0 ≤ R₁ ∧
      vacTuple (m := m) (S := 𝓢) (S' := CoSpinor 𝓢) (0 : HSp M) ∈
        refSet (toSMData M δ) (slabX M) k T K R₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := vacTuple_mem_refSet (S := 𝓢) (S' := CoSpinor 𝓢) (0 : HSp M)
    (toSMData M δ) (slabX M) (by
      show M.Λ + M.κ * (M.lamH * (M.hermH 0 0 - M.vH ^ 2) ^ 2) = 0
      simp only [map_zero, zero_apply, zero_sub]
      linear_combination hc)
    (slab_Jcur_vac M δ (0 : 𝓗)) (slab_SH_vac M δ (0 : 𝓗) (Or.inr rfl)) k T
  exact ⟨_, _, h1, h2, h3, h4⟩

/-- **`refSet` is non-empty for slab models with `Λ = 0`** at a Higgs vacuum
`λ_H(⟨H₀, H₀⟩ - v_H²) = 0` (flat metric, constant Higgs field `H₀`). -/
theorem refSet_nonempty_slab_higgs (hΛ : M.Λ = 0) (H₀ : HSp M)
    (hH : M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) = 0) (δ : ℝ) (k : ℕ) (T : ℝ) :
    ∃ (K : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)) (R₁ : ℝ),
      IsCompact K ∧ K ⊆ chartC (slabX M) ∧ 0 ≤ R₁ ∧
      vacTuple (m := m) (S := 𝓢) (S' := CoSpinor 𝓢) H₀ ∈
        refSet (toSMData M δ) (slabX M) k T K R₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := vacTuple_mem_refSet (S := 𝓢) (S' := CoSpinor 𝓢) H₀
    (toSMData M δ) (slabX M) (by
      show M.Λ + M.κ * (M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) ^ 2) = 0
      rw [hΛ]
      linear_combination (M.κ * (M.hermH H₀ H₀ - M.vH ^ 2)) * hH)
    (slab_Jcur_vac M δ H₀) (slab_SH_vac M δ H₀ (Or.inl hH)) k T
  exact ⟨_, _, h1, h2, h3, h4⟩

/-- **Non-vacuity**: the concrete slab model `diracSlab` (`Λ = λ_H = v_H = 0`) has a non-empty
reference class for every margin, order and slab length. -/
theorem refSet_nonempty_diracSlab (δ : ℝ) (k : ℕ) (T : ℝ) :
    ∃ (K : Set (Fin (ActualJetKato.dimS 1 (HSp diracSlab) NativeModelExample.Sp
        (CoSpinor NativeModelExample.Sp)) → ℝ)) (R₁ : ℝ),
      IsCompact K ∧ K ⊆ chartC (slabX diracSlab) ∧ 0 ≤ R₁ ∧
      (refSet (toSMData diracSlab δ) (slabX diracSlab) k T K R₁).Nonempty := by
  obtain ⟨K, R₁, h1, h2, h3, h4⟩ := refSet_nonempty_slab diracSlab (by
    simp [diracSlab, NativeModelExample.diracModel]) δ k T
  exact ⟨K, R₁, h1, h2, h3, ⟨_, h4⟩⟩

end Slab

end RenewalGeometry.RefSetNonempty

end
