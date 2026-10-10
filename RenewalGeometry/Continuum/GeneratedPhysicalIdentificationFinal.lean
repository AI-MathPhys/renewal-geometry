/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedStateUniqueness
import RenewalGeometry.Continuum.GeneratedPhysicalIdentificationClosed

/-!
# `lem:generated-physical-identification`: closure of the defining-jet identities

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), with `Σ = 𝕋³`.

Assembly of the propagation of the defining-jet identities:

* the shift-transported system (`AJKatoMod.modified_kato_realization`) has a smooth two-sided Kato
  solution `W` (`KatoSmooth.kato_two_sided_smooth`), symmetric in the metric blocks
  (`GenBackward.twoSided_invariant`) and in the chart margin near `t = 0`;
* its head fields form a smooth tuple `z` (`SlabLocal.exists_ext`);
* the first jets of `z` and of the constrained datum `z₀` agree on the initial slice
  (`stateF_eq_of_jets`), so the defining-jet identities hold initially;
* metric, gauge, Higgs and Dirac sectors propagate two-sidedly (`GenHiggsDefect`,
  `GenGaugeRows`, `GenSpinorDefect`); the spinor-free tuple solves the symmetric system and is
  physical by constraint propagation (`GenPhysIdClosed.physical_of_smooth_state`); hence `z` is
  physical and `W` is its actual-jet state (`GenStateUnique.state_eq_of_rows`);
* `W` solves the original realized system, so the Kato solution of the original system is the
  actual-jet state of the physical solution `z` (`KatoStab.twoSided_unique`).

Disclosed hypotheses: `Σ = 𝕋³`; smooth periodic data with an `H^q` bound (`q ≥ 2m + 1`,
`m > 3/2`) and initial values in a compact chart margin; theory data with the current and stress
Noether identities and decoupled spinors (`AJKatoMod.Decoupled`: vanishing Dirac stress form and
spinor-independent Yang–Mills/Higgs sources), all implied by `GenStress.VariationalStress`
(`generated_physical_identification_variational`).  The shift-transported head rows are an
auxiliary device of the proof: the defining-jet defects of the original metric and Higgs head rows
are only weakly hyperbolic for nonzero shift, while the conclusion concerns the original system.
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenPhysIdFinal

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

/-! ### The actual-jet state is a function of the first jets -/

section FirstJets

/-- **Tuples with the same first jets at a point have the same actual-jet state there.** -/
theorem stateF_eq_of_jets {z z' : Tuple m V S S'} {x : ST 3} (hg : z.g x = z'.g x)
    (hdg : z.dg x = z'.dg x) (hA : z.A x = z'.A x) (hdA : ∀ γ, pd z.A γ x = pd z'.A γ x)
    (hH : z.H x = z'.H x) (hdH : ∀ γ, pd z.H γ x = pd z'.H γ x)
    (hψ : z.ψ x = z'.ψ x) (hdψ : ∀ γ, pd z.ψ γ x = pd z'.ψ γ x)
    (hψb : z.ψb x = z'.ψb x) (hdψb : ∀ γ, pd z.ψb γ x = pd z'.ψb γ x) :
    stateF SM z x = stateF SM z' x := by
  have hgi : z.gi x = z'.gi x := by unfold Tuple.gi; rw [hg]
  have he : z.e x = z'.e x := by unfold Tuple.e; rw [hgi]
  have hde : z.de x = z'.de x := by unfold Tuple.de; rw [hgi, hdg]
  have hAF : (z.jet x).AF = (z'.jet x).AF := by
    rw [← ActualJet.frameU_eq', ← ActualJet.frameU_eq']
    exact congrArg frameU hgi
  have hNe : ∀ B γ, (z.jet x).FJ.Ne B γ = (z'.jet x).FJ.Ne B γ := by
    intro B γ; funext μ
    simp only [FrameJet.Ne, FrameJet.Γ, Tuple.jet, Tuple.FJ]
    simp only [hgi, hdg, he, hde]
  have hG : (z.jet x).FJ.G = (z'.jet x).FJ.G := by
    funext A B C
    simp only [FrameJet.G, FrameJet.P, hNe]
    simp only [Tuple.jet, Tuple.FJ]
    simp only [hg, he]
  have hXs : ∀ (ψ : S) (cψ : Fin 4 → S) (a : Fin 4),
      (z.jet x).Xs SM.D ψ cψ a = (z'.jet x).Xs SM.D ψ cψ a := by
    intro ψ cψ a
    rw [ActualJetBridge.Xs_eq, ActualJetBridge.Xs_eq, hG]
    simp only [Tuple.jet, Tuple.FJ]
    simp only [he, hA]
  have hXsb : ∀ (ψ : S') (cψ : Fin 4 → S') (a : Fin 4),
      (z.jet x).Xs SM.Db ψ cψ a = (z'.jet x).Xs SM.Db ψ cψ a := by
    intro ψ cψ a
    rw [ActualJetBridge.Xs_eq, ActualJetBridge.Xs_eq, hG]
    simp only [Tuple.jet, Tuple.FJ]
    simp only [he, hA]
  show toP ((z.jet x).state SM) = toP ((z'.jet x).state SM)
  unfold ActualJet.state
  rw [hAF]
  simp only [hXs, hXsb]
  simp only [Tuple.jet, Tuple.FJ, hg, hdg, hA, hdA, hH, hdH, hψ, hdψ, hψb, hdψb]

/-- The actual-jet state has symmetric metric blocks. -/
theorem isSymmP_stateF (z : Tuple m V S S') (x : ST 3) : AJKatoMod.IsSymmP (stateF SM z x) := by
  rw [AJKatoMod.isSymmP_iff]
  refine ⟨fun μ ν => ?_, fun μ ν => ?_, fun a μ ν => ?_⟩
  · rw [GenDefJet.stateF_fst_fst]; exact z.g_symm x μ ν
  · show (z.jet x).AF.pJ (fun α => (z.jet x).FJ.dg α μ ν) =
      (z.jet x).AF.pJ (fun α => (z.jet x).FJ.dg α ν μ)
    simp only [(z.jet x).FJ.dg_symm]
  · show (z.jet x).AF.qJ (fun α => (z.jet x).FJ.dg α μ ν) a =
      (z.jet x).AF.qJ (fun α => (z.jet x).FJ.dg α ν μ) a
    simp only [(z.jet x).FJ.dg_symm]

end FirstJets

/-! ### Realized solutions as state fields -/

section Realized

/-- The state field of a coordinate solution. -/
def Wof (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (UM : Fin (dimS m V S S') → ST 3 → ℝ) (y : ST 3) : StateP m V S S' :=
  κ.symm (fun c => UM c y)

theorem pd_pi_apply {n : ℕ} {U : Fin n → ST 3 → ℝ} {x : ST 3}
    (hU : ∀ b, DifferentiableAt ℝ (U b) x) (μ : Fin 4) :
    pd (fun y => fun c => U c y) μ x = fun b => pd (U b) μ x := by
  have hf : HasFDerivAt (fun y => fun c => U c y)
      (ContinuousLinearMap.pi fun b => fderiv ℝ (U b) x) x :=
    hasFDerivAt_pi.2 fun b => (hU b).hasFDerivAt
  unfold SobolevOpen.pd
  rw [hf.fderiv]
  rfl

theorem pd_Wof (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {UM : Fin (dimS m V S S') → ST 3 → ℝ} {x : ST 3} (hU : ∀ b, DifferentiableAt ℝ (UM b) x)
    (μ : Fin 4) : pd (Wof κ UM) μ x = κ.symm (fun b => pd (UM b) μ x) := by
  set κs : (Fin (dimS m V S S') → ℝ) →L[ℝ] StateP m V S S' :=
    LinearMap.toContinuousLinearMap κ.symm.toLinearMap with hκs
  have hV : DifferentiableAt ℝ (fun y => fun c => UM c y) x := differentiableAt_pi.2 hU
  rw [show Wof κ UM = fun y => κs (fun c => UM c y) from rfl, GenHarmonic.pd_clm κs hV μ,
    pd_pi_apply hU μ]
  rfl

theorem contDiffOn_Wof (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {UM : Fin (dimS m V S S') → ST 3 → ℝ} {O : Set (ST 3)} (hU : ∀ b, ContDiffOn ℝ ∞ (UM b) O) :
    ContDiffOn ℝ ∞ (Wof κ UM) O := by
  set κs : (Fin (dimS m V S S') → ℝ) →L[ℝ] StateP m V S S' :=
    LinearMap.toContinuousLinearMap κ.symm.toLinearMap with hκs
  exact κs.contDiff.comp_contDiffOn (contDiffOn_pi.2 hU)

theorem isSPeriodic_Wof (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {UM : Fin (dimS m V S S') → ST 3 → ℝ} (hU : ∀ b, IsSPeriodic (UM b)) :
    IsSPeriodic (Wof κ UM) := fun k x => by
  simp only [Wof, hU _ k x]

variable {n : ℕ} {AM : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
    (Fin (dimS m V S S') → ℝ) → ℝ} {FM : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}

variable (SM) in
/-- **A realized solution of the shift-transported system solves it pointwise** at symmetric
states of the margin. -/
theorem rows_of_twoSidedM (hAM : ∀ i a b, ContDiff ℝ ∞ (AM i a b))
    (hFM : ∀ a, ContDiff ℝ ∞ (FM a)) {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {K : Set (Fin (dimS m V S S') → ℝ)}
    (hAMK : ∀ v ∈ K, AJKatoMod.IsSymmP (κ.symm v) → ∀ j a (w : Fin (dimS m V S S') → ℝ),
      ∑ b, AM j a b v * w b = κ (AJKatoMod.princPM SM (κ.symm v) j (κ.symm w)) a)
    (hFMK : ∀ v ∈ K, AJKatoMod.IsSymmP (κ.symm v) → ∀ a,
      FM a v = κ (toP (AJKatoMod.FsysM SM (ofP (κ.symm v)))) a)
    {U₀ UM : Fin (dimS m V S S') → ST 3 → ℝ} {PM : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ}
    {T : ℝ} (h : TwoSidedSol AM FM U₀ T UM PM) {x : ST 3} (hx : x ∈ openSlab (-T) T)
    (hxK : (fun c => UM c x) ∈ K) (hxS : AJKatoMod.IsSymmP (κ.symm fun c => UM c x)) :
    pd (Wof κ UM) 0 x + ∑ j : Fin 3, AJKatoMod.princPM SM (Wof κ UM x) j (pd (Wof κ UM) j.succ x) =
      toP (AJKatoMod.FsysM SM (ofP (Wof κ UM x))) := by
  have hdiff : ∀ b, DifferentiableAt ℝ (UM b) x := fun b =>
    ((h.contDiffOn hAM hFM b).differentiableOn one_ne_zero x hx).differentiableAt
      ((isOpen_openSlab _ _).mem_nhds hx)
  have hpd : ∀ b μ, pd (UM b) μ x = solPartial AM FM UM PM b μ x := fun b μ =>
    h.pd_eq hAM hFM b hx μ
  have hP : ∀ i : Fin 3, κ.symm (fun b => PM b i x) = pd (Wof κ UM) i.succ x := by
    intro i
    rw [pd_Wof κ hdiff]
    congr 1
    funext b
    rw [hpd b i.succ]
    rfl
  apply κ.injective
  funext a
  rw [map_add, map_sum]
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [pd_Wof κ hdiff 0, LinearEquiv.apply_symm_apply, hpd a 0]
  show KatoGalerkin.genP AM FM UM PM a x + _ = _
  unfold KatoGalerkin.genP
  rw [hFMK _ hxK hxS a]
  have hS1 : ∀ i : Fin 3, ∑ b', AM i a b' (fun c => UM c x) * PM b' i x =
      κ (AJKatoMod.princPM SM (Wof κ UM x) i (pd (Wof κ UM) i.succ x)) a := by
    intro i
    rw [hAMK _ hxK hxS i a (fun b' => PM b' i x), hP i]
    rfl
  simp only [hS1]
  show κ (toP (AJKatoMod.FsysM SM (ofP (Wof κ UM x)))) a - _ + _ = _
  abel

/-- Two-sided solutions with the same generator on a smaller slab. -/
theorem twoSided_of_gen {A' F' : _} {A F : _} {U₀ UM : Fin n → ST 3 → ℝ}
    {PM : Fin n → Fin 3 → ST 3 → ℝ} {T T' : ℝ} (h : TwoSidedSol A' F' U₀ T UM PM) (hT : T' ≤ T)
    (hgen : ∀ t ∈ Ioo (-T') T', ∀ y b, genP A F UM PM b (Fin.cons t y) =
      genP A' F' UM PM b (Fin.cons t y)) :
    TwoSidedSol A F U₀ T' UM PM where
  contU := h.contU
  contP := h.contP
  perU := h.perU
  perP := h.perP
  init := h.init
  space := h.space
  time b t ht y := by
    rw [hgen t ht y b]
    exact h.time b t ⟨by linarith [ht.1], by linarith [ht.2]⟩ y

/-- The coordinate transposition as a continuous linear map. -/
def tauKL (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) :
    (Fin (dimS m V S S') → ℝ) →L[ℝ] (Fin (dimS m V S S') → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := AJKatoMod.tauK κ, map_add' := AJKatoMod.tauK_add κ,
      map_smul' := AJKatoMod.tauK_smul κ }

theorem tauKL_apply (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v : Fin (dimS m V S S') → ℝ) : tauKL κ v = AJKatoMod.tauK κ v := rfl

theorem isSymmP_of_tauK {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {v : Fin (dimS m V S S') → ℝ} (h : AJKatoMod.tauK κ v = v) : AJKatoMod.IsSymmP (κ.symm v) := by
  unfold AJKatoMod.IsSymmP
  have := congrArg κ.symm h
  unfold AJKatoMod.tauK at this
  rwa [LinearEquiv.symm_apply_apply] at this

theorem tauK_of_isSymmP {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    {w : StateP m V S S'} (h : AJKatoMod.IsSymmP w) : AJKatoMod.tauK κ (κ w) = κ w := by
  unfold AJKatoMod.tauK
  rw [LinearEquiv.symm_apply_apply, h]

end Realized


/-! ### The initial slice and the head tuple -/

section Slice

variable (SM) in
/-- **All first derivatives of a solution of the shift-transported system agree on the initial
slice with those of a slice-constrained tuple with the same data** (spatial derivatives from the
data, the time derivative from the rows: the constrained tuple satisfies the system on the
slice). -/
theorem slice_pd_eq (hS : SMSmooth SM) {W : ST 3 → StateP m V S S'} {z₀ : Tuple m V S S'}
    {O : Set (ST 3)} (hO : IsOpen O) (hW : ContDiffOn ℝ 1 W O)
    (hC₀ : GenPhysIdClosed.SliceConstrained SM z₀)
    (hdat : ∀ y, W (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y)) {y : Fin 3 → ℝ}
    (hy : (Fin.cons 0 y : ST 3) ∈ O)
    (hrow : pd W 0 (Fin.cons 0 y) + ∑ j : Fin 3, AJKatoMod.princPM SM (W (Fin.cons 0 y)) j
      (pd W j.succ (Fin.cons 0 y)) = toP (AJKatoMod.FsysM SM (ofP (W (Fin.cons 0 y))))) :
    ∀ μ, pd W μ (Fin.cons 0 y) = pd (stateF SM z₀) μ (Fin.cons 0 y) := by
  have hdW : DifferentiableAt ℝ W (Fin.cons 0 y) :=
    GenHarmonic.diffAt_of_contDiffOn hO hW one_ne_zero hy
  have hdU : DifferentiableAt ℝ (stateF SM z₀) (Fin.cons 0 y) :=
    (contDiff_stateF SM z₀).differentiable (by simp) _
  have hsp : ∀ j : Fin 3, pd W j.succ (Fin.cons 0 y) = pd (stateF SM z₀) j.succ (Fin.cons 0 y) :=
    fun j => GenPhysIdClosed.pd_eq_of_slice hdat rfl hdW hdU j
  have hsym0 := GenPhysIdClosed.symEqAt_of_sliceConstrained SM hS hC₀ y
  have herr : errF SM z₀ (Fin.cons 0 y) = 0 := (symEqAt_iff SM z₀ _).1 hsym0
  have h0 := AJKatoMod.writer_pde_errM (SM := SM) z₀ (Fin.cons 0 y)
  rw [herr, add_zero] at h0
  rw [hdat y] at hrow
  simp only [hsp] at hrow
  intro μ
  induction μ using Fin.cases with
  | zero => exact add_right_cancel (hrow.trans h0.symm)
  | succ j => exact hsp j

/-- Matching of a head field and its first derivatives through a linear block. -/
theorem jet_match {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : StateP m V S S' →L[ℝ] E) {f f₀ : ST 3 → E} {W U : ST 3 → StateP m V S S'} {x : ST 3}
    (hf : f =ᶠ[𝓝 x] fun y => L (W y)) (hf₀ : f₀ = fun y => L (U y))
    (hdW : DifferentiableAt ℝ W x) (hdU : DifferentiableAt ℝ U x)
    (hval : W x = U x) (hpd : ∀ μ, pd W μ x = pd U μ x) :
    f x = f₀ x ∧ ∀ γ, pd f γ x = pd f₀ γ x := by
  refine ⟨by rw [hf.eq_of_nhds, hf₀, hval], fun γ => ?_⟩
  rw [(SlabLocal.pd_eventuallyEq hf γ).eq_of_nhds, hf₀, GenHarmonic.pd_clm L hdW γ,
    GenHarmonic.pd_clm L hdU γ, hpd γ]

variable (m V S S') in
/-- The metric block of a state. -/
def prG' : StateP m V S S' →L[ℝ] Met :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.1.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (m V S S') in
/-- The potential `(0, A_i)` of a state. -/
def prA' : StateP m V S S' →L[ℝ] (Fin 4 → MatLie m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Fin.cases (motive := fun _ => MatLie m) 0 (fun i => v.2.1 i)
      map_add' := fun v w => by
        funext μ
        induction μ using Fin.cases with
        | zero => simp
        | succ i => rfl
      map_smul' := fun c v => by
        funext μ
        induction μ using Fin.cases with
        | zero => simp
        | succ i => rfl }

theorem prA'_apply (v : StateP m V S S') :
    prA' m V S S' v = Fin.cases (motive := fun _ => MatLie m) 0 (fun i => v.2.1 i) := rfl

theorem A_eq_prA' (z : Tuple m V S S') :
    z.A = fun y => prA' m V S S' (stateF SM z y) := by
  funext y μ
  induction μ using Fin.cases with
  | zero => rw [prA'_apply, Fin.cases_zero]; exact z.temporal y
  | succ i => rfl

/-- **The head fields of a symmetric chart-valued state field form a slab-local tuple.** -/
def headTuple (W : ST 3 → StateP m V S S') {a b : ℝ} (hW : ContDiffOn ℝ ∞ W (openSlab a b))
    (hWp : IsSPeriodic W) (hsym : ∀ y ∈ openSlab a b, AJKatoMod.IsSymmP (W y))
    (hc : ∀ y ∈ openSlab a b, MetChart (W y).1) : SlabLocal.LocalTuple m V S S' a b where
  g y := (W y).1.1
  A y := prA' m V S S' (W y)
  H y := (W y).2.2.2.2.1
  ψ y := (W y).2.2.2.2.2.2.2.1
  ψb y := (W y).2.2.2.2.2.2.2.2.2.1
  g_smooth := (prG' m V S S').contDiff.comp_contDiffOn hW
  A_smooth := (prA' m V S S').contDiff.comp_contDiffOn hW
  H_smooth := (GenHiggsDefect.prH m V S S').contDiff.comp_contDiffOn hW
  ψ_smooth := (GenSpinorDefect.prψ m V S S').contDiff.comp_contDiffOn hW
  ψb_smooth := (GenSpinorDefect.prψb m V S S').contDiff.comp_contDiffOn hW
  g_per := fun k x => by simp only [hWp k x]
  A_per := fun k x => by simp only [hWp k x]
  H_per := fun k x => by simp only [hWp k x]
  ψ_per := fun k x => by simp only [hWp k x]
  ψb_per := fun k x => by simp only [hWp k x]
  g_symm := fun y hy => ((AJKatoMod.isSymmP_iff _).1 (hsym y hy)).1
  temporal := fun _ _ => rfl
  det_ne := fun y hy => (hc y hy).1
  lor := fun y hy => (hc y hy).2

end Slice


/-! ### The core identification -/

section Core

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

set_option maxHeartbeats 4000000 in -- long assembly proof
/-- **The core identification**: a smooth two-sided solution `W` of the realized
shift-transported system with constrained data, symmetric and in the chart margin on
`(-ε, ε) × 𝕋³`, has a physical head tuple `z` whose actual-jet state is `W` near `t = 0`, and the
Kato solution of the original realized system is the actual-jet state of `z` on `[0, t₁] × 𝕋³`. -/
theorem core_identification (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hD : AJKatoMod.Decoupled SM) (hN : GenNoether.CurrentNoether SM)
    (hT : GenStress.StressNoether SM)
    {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i)
    {K : Set (Fin (dimS m V S S') → ℝ)} (hKc : ∀ v ∈ K, MetChart (κ.symm v).1)
    {A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    {F : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (hAK : ∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
      κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a)
    (hFK : ∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a)
    {AM : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    {FM : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ}
    (hAM : ∀ i a b, ContDiff ℝ ∞ (AM i a b)) (hFM : ∀ a, ContDiff ℝ ∞ (FM a))
    (hAMK : ∀ v ∈ K, AJKatoMod.IsSymmP (κ.symm v) → ∀ j a (w : Fin (dimS m V S S') → ℝ),
      ∑ b, AM j a b v * w b = κ (AJKatoMod.princPM SM (κ.symm v) j (κ.symm w)) a)
    (hFMK : ∀ v ∈ K, AJKatoMod.IsSymmP (κ.symm v) → ∀ a,
      FM a v = κ (toP (AJKatoMod.FsysM SM (ofP (κ.symm v)))) a)
    {U₀ : Fin (dimS m V S S') → ST 3 → ℝ} {z₀ : Tuple m V S S'}
    (hdat₀ : ∀ b y, GenPhysId.stU κ SM z₀ b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y))
    (hC₀ : GenPhysIdClosed.SliceConstrained SM z₀)
    {TM : ℝ} {UM : Fin (dimS m V S S') → ST 3 → ℝ} {PM : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ}
    (hMP : TwoSidedSol AM FM U₀ TM UM PM)
    (hMs : ∀ b, ContDiffOn ℝ ∞ (UM b) (openSlab (-TM) TM)) {ε : ℝ} (hε : 0 < ε) (hεT : ε ≤ TM)
    (hKW : ∀ x ∈ openSlab (-ε) ε, (fun c => UM c x) ∈ K)
    (hsymε : ∀ x ∈ openSlab (-ε) ε, AJKatoMod.IsSymmP (Wof κ UM x))
    {T : ℝ} (hT0 : 0 < T) {U : Fin (dimS m V S S') → ST 3 → ℝ}
    {P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ} (hUP : TwoSidedSol A F U₀ T U P) :
    ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ ∀ x ∈ slab 0 t₁,
      (∀ b, U b x = κ (stateF SM z x) b) ∧ bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  have hsubT : ∀ x : ST 3, x ∈ openSlab (-ε) ε → x ∈ openSlab (-TM) TM := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact ⟨show -TM < x 0 by linarith, show x 0 < TM by linarith⟩
  set W := Wof κ UM with hWdef
  have hWs : ContDiffOn ℝ ∞ W (openSlab (-ε) ε) := (contDiffOn_Wof κ hMs).mono hsubT
  have hWp : IsSPeriodic W := isSPeriodic_Wof κ hMP.perU
  have hchart : ∀ x ∈ openSlab (-ε) ε, MetChart (W x).1 := fun x hx => hKc _ (hKW x hx)
  have hrowM : ∀ x ∈ openSlab (-ε) ε, pd W 0 x +
      ∑ j : Fin 3, AJKatoMod.princPM SM (W x) j (pd W j.succ x) =
        toP (AJKatoMod.FsysM SM (ofP (W x))) := fun x hx =>
    rows_of_twoSidedM SM hAM hFM hAMK hFMK hMP (hsubT x hx) (hKW x hx) (hsymε x hx)
  -- the head tuple
  set ε' := ε / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨z, hz⟩ := SlabLocal.exists_ext (headTuple W hWs hWp hsymε hchart) (c := -ε') (d := ε')
    (by linarith) (by linarith) (by linarith)
  have hsub' : ∀ x : ST 3, x ∈ openSlab (-ε') ε' → x ∈ openSlab (-ε) ε := fun x hx => by
    have h1 : -ε' < x 0 := hx.1
    have h2 : x 0 < ε' := hx.2
    exact ⟨show -ε < x 0 by linarith, show x 0 < ε by linarith⟩
  have hMS : GenHiggsDefect.MSol SM W z (-ε') ε' :=
    { smooth := hWs.mono hsub'
      per := hWp
      chart := fun y hy => hchart y (hsub' y hy)
      g := fun y hy => ((hz y hy).1.eq_of_nhds).symm
      A := fun y hy i => by rw [(hz y hy).2.1.eq_of_nhds]; rfl
      H := fun y hy => ((hz y hy).2.2.1.eq_of_nhds).symm
      ψ := fun y hy => ((hz y hy).2.2.2.1.eq_of_nhds).symm
      ψb := fun y hy => ((hz y hy).2.2.2.2.eq_of_nhds).symm
      row := fun y hy => hrowM y (hsub' y hy) }
  have hW1 : ContDiffOn ℝ 1 W (openSlab (-ε') ε') := hMS.smooth.of_le (by norm_cast)
  -- the initial slice
  have hy0 : ∀ y : Fin 3 → ℝ, (Fin.cons 0 y : ST 3) ∈ openSlab (-ε') ε' := fun y =>
    ⟨by show -ε' < 0; linarith, by show (0 : ℝ) < ε'; exact hε'0⟩
  have hslice0 : ∀ y, W (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y) := fun y => by
    show κ.symm (fun c => UM c (Fin.cons 0 y)) = _
    have : (fun c => UM c (Fin.cons 0 y)) = κ (stateF SM z₀ (Fin.cons 0 y)) :=
      funext fun c => (hMP.init c y).trans (hdat₀ c y).symm
    rw [this, LinearEquiv.symm_apply_apply]
  have hpd0 : ∀ y μ, pd W μ (Fin.cons 0 y) = pd (stateF SM z₀) μ (Fin.cons 0 y) := fun y =>
    slice_pd_eq SM hS (isOpen_openSlab _ _) hW1 hC₀ hslice0 (hy0 y) (hMS.row _ (hy0 y))
  have hslice : ∀ y, W (Fin.cons 0 y) = stateF SM z (Fin.cons 0 y) := by
    intro y
    have hx := hy0 y
    have hdW : DifferentiableAt ℝ W (Fin.cons 0 y) :=
      GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab _ _) hW1 one_ne_zero hx
    have hdU : DifferentiableAt ℝ (stateF SM z₀) (Fin.cons 0 y) :=
      (contDiff_stateF SM z₀).differentiable (by simp) _
    obtain ⟨hzA, hzdA⟩ := jet_match (prA' m V S S') (hz _ hx).2.1 (A_eq_prA' (SM := SM) z₀) hdW hdU
      (hslice0 y) (hpd0 y)
    obtain ⟨hzg, hzdg⟩ := jet_match (prG' m V S S') (hz _ hx).1
      (show z₀.g = fun y => prG' m V S S' (stateF SM z₀ y) from
        funext fun y => (GenDefJet.stateF_fst_fst SM z₀ y).symm) hdW hdU (hslice0 y) (hpd0 y)
    obtain ⟨hzH, hzdH⟩ := jet_match (GenHiggsDefect.prH m V S S') (hz _ hx).2.2.1
      (show z₀.H = fun y => GenHiggsDefect.prH m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    obtain ⟨hzψ, hzdψ⟩ := jet_match (GenSpinorDefect.prψ m V S S') (hz _ hx).2.2.2.1
      (show z₀.ψ = fun y => GenSpinorDefect.prψ m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    obtain ⟨hzψb, hzdψb⟩ := jet_match (GenSpinorDefect.prψb m V S S') (hz _ hx).2.2.2.2
      (show z₀.ψb = fun y => GenSpinorDefect.prψb m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    rw [hslice0 y]
    exact (stateF_eq_of_jets hzg (funext fun α => hzdg α) hzA hzdA hzH hzdH hzψ hzdψ hzψb
      hzdψb).symm
  -- the sectors
  have ha' : -ε' < 0 := by linarith
  have hmet := GenHiggsDefect.metric_sector hS ha' hε'0 hMS (fun y => by rw [hslice y])
  have hEB : ∀ x ∈ openSlab (-ε') ε', (W x).2.2.1 = (stateF SM z x).2.2.1 ∧
      (W x).2.2.2.1 = (stateF SM z x).2.2.2.1 := by
    have hinit : ∀ y : Fin 3 → ℝ, (W (Fin.cons 0 y)).2.2.1 = (stateF SM z (Fin.cons 0 y)).2.2.1 ∧
        (W (Fin.cons 0 y)).2.2.2.1 = (stateF SM z (Fin.cons 0 y)).2.2.2.1 := fun y => by
      rw [hslice y]; exact ⟨rfl, rfl⟩
    exact GenHiggsDefect.of_forward_backward ha' hε'0
      (fun t₁ h01 h1b => GenGaugeRows.gauge_sector_forward z ha' h01 h1b hMS.smooth hMS.per
        hMS.chart hmet hMS.A hMS.row hinit)
      (fun t₁ ha1 h10 => GenGaugeRows.gauge_sector_backward z ha1 h10 hε'0 hMS.smooth hMS.per
        hMS.chart hmet hMS.A hMS.row hinit)
  have hQ := GenHiggsDefect.higgs_sector hS ha' hε'0 hMS hmet hEB (fun y => by rw [hslice y])
  have hPi := GenHiggsDefect.higgs_Pi hMS
  have hB : ∀ y ∈ openSlab (-ε') ε', GenSpinorDefect.prB m V S S' (W y) =
      GenSpinorDefect.prB m V S S' (stateF SM z y) := by
    intro y hy
    rw [GenSpinorDefect.prB_eq_iff]
    exact ⟨hmet y hy, funext (hMS.A y hy), (hEB y hy).1, (hEB y hy).2, hMS.H y hy, hPi y hy,
      hQ y hy⟩
  -- the spinor-free tuple is physical
  have hsymZ := GenSpinorDefect.symEqAt_zeroSp SM hD hMS hB
  have hS0' : ∀ y : Fin 3 → ℝ, stateF SM (GenSpinorDefect.zeroSp z) (Fin.cons 0 y) =
      stateF SM (GenSpinorDefect.zeroSp z₀) (Fin.cons 0 y) := by
    intro y
    apply GenSpinorDefect.eq_of_prB_prS
    · rw [GenSpinorDefect.prB_stateF_zeroSp, GenSpinorDefect.prB_stateF_zeroSp, ← hslice y,
        hslice0 y]
    · rw [GenSpinorDefect.prS_stateF_zeroSp, GenSpinorDefect.prS_stateF_zeroSp]
  have hC0' : GenPhysIdClosed.SliceConstrained SM (GenSpinorDefect.zeroSp z₀) := fun y => by
    obtain ⟨h1, -, h3, h4⟩ := hC₀ y
    exact ⟨by rw [GenSpinorDefect.bosF_zeroSp SM hD]; exact h1,
      GenSpinorDefect.dirF_zeroSp _ _, h3, h4⟩
  have hphys' := GenPhysIdClosed.physical_of_smooth_state hN hT hS hε'0 hsymZ hS0' hC0'
  have hdir := GenSpinorDefect.dirac_of_rows hMS hmet
  have hphys : ∀ x : ST 3, 0 ≤ x 0 → x 0 < ε' →
      bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := fun x h0 h1 =>
    ⟨by rw [← GenSpinorDefect.bosF_zeroSp SM hD]; exact (hphys' x h0 h1).1,
      hdir x ⟨by linarith, h1⟩, (hphys' x h0 h1).2.2⟩
  -- `W` is the actual-jet state of `z`
  have horig := GenSpinorDefect.orig_row_of_MSol SM hD hMS hB
  have herr : ∀ x ∈ slab 0 (ε' / 2), errF SM z x = 0 := fun x hx =>
    GenStateUnique.errF_zero_of_phys hphys hx.1 (by have := hx.2; linarith)
  have hWz := GenStateUnique.state_eq_of_rows hS hU hκ ha' (by positivity : (0 : ℝ) < ε' / 2)
    (by linarith) hW1 hWp hmet horig herr hslice
  -- `W` solves the original realized system
  have hgen : ∀ t ∈ Ioo (-ε') ε', ∀ y b, genP A F UM PM b (Fin.cons t y) =
      genP AM FM UM PM b (Fin.cons t y) := by
    intro t ht y b
    have hx : (Fin.cons t y : ST 3) ∈ openSlab (-ε') ε' := ht
    have hxε := hsub' _ hx
    have hdiff : ∀ b, DifferentiableAt ℝ (UM b) (Fin.cons t y) := fun b =>
      ((hMP.contDiffOn hAM hFM b).differentiableOn one_ne_zero _ (hsubT _ hxε)).differentiableAt
        ((isOpen_openSlab _ _).mem_nhds (hsubT _ hxε))
    have hP : ∀ j : Fin 3, κ.symm (fun c => PM c j (Fin.cons t y)) =
        pd W j.succ (Fin.cons t y) := by
      intro j
      rw [pd_Wof κ hdiff]
      congr 1
      funext c
      rw [hMP.pd_eq hAM hFM c (hsubT _ hxε) j.succ]
      rfl
    rw [genP_eq_actual_jet hAK hFK UM PM _ (hKW _ hxε) b]
    have h0 : genP AM FM UM PM b (Fin.cons t y) = pd (UM b) 0 (Fin.cons t y) :=
      (hMP.pd_eq hAM hFM b (hsubT _ hxε) 0).symm
    rw [h0]
    have h1 : pd (UM b) 0 (Fin.cons t y) = κ (pd W 0 (Fin.cons t y)) b := by
      rw [pd_Wof κ hdiff, LinearEquiv.apply_symm_apply]
    rw [h1]
    simp only [hP]
    have hrow := horig _ hx
    have e1 : κ (toS (Fsys SM (ofP (κ.symm fun c => UM c (Fin.cons t y))))) b =
        κ (toP (Fsys SM (ofP (W (Fin.cons t y))))) b := rfl
    have e2 : ∀ j : Fin 3, κ (toS (princ (frameU (ginvOf (κ.symm fun c => UM c (Fin.cons t y)).1.1))
        SM.D.Fr SM.Db.Fr j (ofP (pd W j.succ (Fin.cons t y))))) b =
        κ (princL SM (W (Fin.cons t y)) j (pd W j.succ (Fin.cons t y))) b := fun j => rfl
    rw [e1]
    simp only [e2]
    rw [← hrow, map_add, map_sum, Pi.add_apply, Finset.sum_apply]
    abel
  have hOrig := twoSided_of_gen (A := A) (F := F) hMP (by linarith : ε' ≤ TM) hgen
  set t₁ := min T (ε' / 2) / 2 with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁T : t₁ < T := by
    have := min_le_left T (ε' / 2); rw [ht₁]; linarith
  have ht₁ε : t₁ < ε' / 2 := by
    have := min_le_right T (ε' / 2); rw [ht₁]; linarith
  have huniq := KatoStab.twoSided_unique hA hsym hF hUP hOrig ht₁0 ht₁T (by linarith)
  refine ⟨z, t₁, ht₁0, fun x hx => ?_⟩
  have hx' : x ∈ slab 0 (ε' / 2) := ⟨hx.1, by have := hx.2; linarith⟩
  have hxp := hphys x hx.1 (by have := hx.2; linarith)
  refine ⟨fun b => ?_, hxp.1, hxp.2.1, hxp.2.2⟩
  rw [huniq x hx b, ← hWz x hx']
  show UM b x = κ (κ.symm fun c => UM c x) b
  rw [LinearEquiv.apply_symm_apply]

end Core


/-! ### The lemma -/

section Main

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- A two-sided coordinate solution stays in `K` near `t = 0` when its data lie in `K₀` with
`cthickening δ K₀ ⊆ K`. -/
theorem exists_twoSided_mem {n : ℕ} {A : Fin 3 → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} {U₀ UM : Fin n → ST 3 → ℝ} {PM : Fin n → Fin 3 → ST 3 → ℝ}
    {TM : ℝ} (hMP : TwoSidedSol A F U₀ TM UM PM) {K₀ K : Set (Fin n → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hKδ : Metric.cthickening δ K₀ ⊆ K) (hK₀ : ∀ y, (fun c => U₀ c (Fin.cons 0 y)) ∈ K₀) :
    ∃ τ > 0, ∀ x : ST 3, x ∈ openSlab (-τ) τ → (fun c => UM c x) ∈ K := by
  have hK0M : ∀ y, (fun c => UM c (Fin.cons 0 y)) ∈ K₀ := fun y => by
    have : (fun c => UM c (Fin.cons 0 y)) = fun c => U₀ c (Fin.cons 0 y) :=
      funext fun c => hMP.init c y
    rw [this]; exact hK₀ y
  obtain ⟨t₀, ht₀, hmem⟩ := exists_time_mem hMP.contU hMP.perU hδ hKδ hK0M
  have hMR := GenBackward.TwoSidedSol.reflect hMP
  have hK0R : ∀ y, (fun c => UM c (KatoGalerkin.refl (Fin.cons 0 y))) ∈ K₀ := fun y => by
    rw [KatoGalerkin.refl_cons, neg_zero]; exact hK0M y
  obtain ⟨t₀', ht₀', hmem'⟩ := exists_time_mem hMR.contU hMR.perU hδ hKδ hK0R
  refine ⟨min t₀ t₀', lt_min ht₀ ht₀', fun x hx => ?_⟩
  have h1 : -min t₀ t₀' < x 0 := hx.1
  have h2 : x 0 < min t₀ t₀' := hx.2
  have hx' : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
  rcases le_or_gt 0 (x 0) with h0 | h0
  · rw [hx']
    exact hmem (x 0) ⟨h0, by linarith [min_le_left t₀ t₀']⟩ _
  · have := hmem' (-(x 0)) ⟨by linarith, by linarith [min_le_right t₀ t₀']⟩ (Fin.tail x)
    rw [KatoGalerkin.refl_cons, neg_neg, ← hx'] at this
    exact this

/-- **`lem:generated-physical-identification` for the actual-jet system (`Σ = 𝕋³`), closed.**
For theory data with smooth sources, decoupled spinors (`AJKatoMod.Decoupled`: symmetric
gauge/Higgs stress forms, vanishing Dirac stress form, spinor-independent Yang–Mills and Higgs
sources) and the current and stress Noether identities, and forms with the Clifford unitarity
relations, there are Euclidean coordinates `κ` of the state space such that for every compact
chart margin `K ⊇ cthickening δ K₀` the realized coefficient maps `A^j, F` of the independent
symmetric system satisfy: for every `H^q` radius `R₀` there is a Kato time `T > 0` such that every
constrained smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` and initial values in `K₀` has a
two-sided Kato solution `U` on `(-T, T) × 𝕋³`, and there are a smooth field tuple `z` and
`t₁ > 0` such that on `[0, t₁] × 𝕋³` the Kato solution is the actual-jet state of `z` and `z`
satisfies the complete Einstein, Yang–Mills, Higgs, Dirac and dual Dirac equations and the
harmonic and temporal-gauge constraints.  No smooth solution is assumed: it is constructed from the
shift-transported system (`AJKatoMod`), whose head fields are shown to have the defining-jet
identities. -/
theorem generated_physical_identification (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hD : AJKatoMod.Decoupled SM) (hN : GenNoether.CurrentNoether SM)
    (hT : GenStress.StressNoether SM) {mm q : ℕ} (hm : (3 : ℝ) / 2 < mm) (hq : 2 * mm + 1 ≤ q)
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
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δ hδ hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    AJKatoMod.modified_kato_realization hS hU hD κ hκ K hK hKc
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
  have hinv := GenBackward.twoSided_invariant hAM hsymM hFM (tauKL κ) (fun j a v w => hτA j a v w)
    (fun a v => hτF a v) hMP (fun y => by
      rw [tauKL_apply, hU0 y, tauK_of_isSymmP (isSymmP_stateF z₀ _)])
  -- the margin
  obtain ⟨τ, hτ, hKW⟩ := exists_twoSided_mem hMP hδ hKδ hK₀
  set ε := min τ TM with hεdef
  have hε : 0 < ε := lt_min hτ hTM0
  have hKWε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → (fun c => UM c x) ∈ K := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact hKW x ⟨show -τ < x 0 by linarith [min_le_left τ TM],
      show x 0 < τ by linarith [min_le_left τ TM]⟩
  have hsymε : ∀ x : ST 3, x ∈ openSlab (-ε) ε → AJKatoMod.IsSymmP (Wof κ UM x) := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact isSymmP_of_tauK (hinv x ⟨by linarith [min_le_right τ TM],
      by linarith [min_le_right τ TM]⟩)
  exact core_identification hS hU hD hN hT hκ hKc hA hsym hF hAK hFK hAM hFM hAMK hFMK hdat₀ hC₀
    hMP hMs hε (min_le_right τ TM) hKWε hsymε hT0 hUP

end Main


/-! ### Non-vacuity -/

section NonVacuity

/-- **Variational data have decoupled spinors**: the class `GenStress.VariationalStress` (for
which the current and stress Noether identities are proved) has symmetric gauge/Higgs forms,
vanishing Dirac stress form and spinor-independent Yang–Mills and Higgs sources (e.g. the
vanishing-coupling data `trivSMM` and the Yang–Mills–adjoint-Higgs data `GenNoether.adjSM`). -/
theorem decoupled_of_variationalStress (hV : GenStress.VariationalStress SM) :
    AJKatoMod.Decoupled SM where
  ipG_symm := hV.ipG_symm
  ipV_symm := hV.ipV_symm
  TD_P := hV.P_zero
  TD_P' := hV.P'_zero
  TD_P'' := hV.P''_zero
  J_spin := fun _ _ _ _ _ _ _ _ => funext fun _ => by rw [hV.J_eq, hV.J_eq]
  SH_spin := fun _ _ _ _ _ _ _ => by rw [hV.SH_eq, hV.SH_eq]

/-- **`lem:generated-physical-identification` for variational theory data**: the hypotheses on the
theory data reduce to the variational structure (`GenStress.VariationalStress`), which gives the
current and stress Noether identities and decoupled spinors. -/
theorem generated_physical_identification_variational (hS : SMSmooth SM)
    {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ} (hU : UnitaryForms SM bG bV bS bS')
    (hV : GenStress.VariationalStress SM) {mm q : ℕ} (hm : (3 : ℝ) / 2 < mm)
    (hq : 2 * mm + 1 ≤ q) (hq2 : mm + 2 ≤ q) :
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
  generated_physical_identification hS hU (decoupled_of_variationalStress hV)
    (GenNoether.currentNoether_of_variational hV.toVariationalBosonic)
    (GenStress.stressNoether_of_variational hV) hm hq hq2

open CoupledBootstrap.FlatVacuum in
/-- **Non-vacuity**: for the vanishing-coupling data `trivSMM` all hypotheses on the theory data
hold, the flat-vacuum datum is constrained, smooth, periodic and in a chart margin, and the lemma
produces the Kato solution together with a physical tuple whose actual-jet state it is. -/
example : ∃ (κ : StateP 1 (MatLie 1) PUnit.{1} PUnit.{1} ≃ₗ[ℝ]
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ))
    (A : Fin 3 → Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
        (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ)
    (F : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) →
      (Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ℝ) → ℝ) (T : ℝ)
    (U : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → ST 3 → ℝ)
    (P : Fin (dimS 1 (MatLie 1) PUnit.{1} PUnit.{1}) → Fin 3 → ST 3 → ℝ)
    (z : Tuple 1 (MatLie 1) PUnit.{1} PUnit.{1}) (t₁ : ℝ),
    0 < T ∧ TwoSidedSol A F (GenPhysId.stU κ trivSMM flat) T U P ∧ 0 < t₁ ∧
      ∀ x ∈ slab 0 t₁, (∀ b, U b x = κ (stateF trivSMM z x) b) ∧
        bosF trivSMM z x = 0 ∧ dirF trivSMM z x = 0 ∧ CF z x = 0 := by
  obtain ⟨κ, -, h⟩ := generated_physical_identification_variational trivSMM_smooth
    unitaryForms_triv GenStress.trivSMM_variationalStress (mm := 2) (q := 5) (by norm_num)
    (by norm_num) (by norm_num)
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen (κ.symm ⁻¹' chartSet (m := 1) (V := MatLie 1) (S := PUnit.{1})
      (S' := PUnit.{1})) := isOpen_chartSet.preimage hκc
  have hmem : κ minkState ∈ κ.symm ⁻¹' chartSet (m := 1) (V := MatLie 1) (S := PUnit.{1})
      (S' := PUnit.{1}) := by
    show MetChart (κ.symm (κ minkState)).1
    rw [LinearEquiv.symm_apply_apply]
    exact metChart_mink
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  have hK : IsCompact (Metric.closedBall (κ minkState) (r / 2)) := isCompact_closedBall _ _
  have hKc : ∀ v ∈ Metric.closedBall (κ minkState) (r / 2), MetChart (κ.symm v).1 := fun v hv =>
    hball (Metric.closedBall_subset_ball (half_lt_self hr) hv)
  have hKδ : Metric.cthickening (r / 2) ({κ minkState} : Set _) ⊆
      Metric.closedBall (κ minkState) (r / 2) :=
    (Metric.cthickening_singleton _ (by positivity)).le
  obtain ⟨A, F, -, -, -, -, -, h2⟩ := h {κ minkState} _ hK hKc (r / 2) (by positivity) hKδ
  obtain ⟨T, hT, h3⟩ := h2 (Real.sqrt |energyQ 5 (GenPhysId.stU κ trivSMM flat) 0|)
    (Real.sqrt_nonneg _)
  obtain ⟨U, P, hsol, z, t₁, ht₁, hid⟩ := h3 (GenPhysId.stU κ trivSMM flat)
    ⟨flat, fun _ _ => rfl, GenPhysIdClosed.flat_sliceConstrained⟩
    (GenPhysId.contDiff_stU κ trivSMM flat) (GenPhysId.isSPeriodic_stU κ trivSMM flat)
    (by rw [Real.sq_sqrt (abs_nonneg _)]; exact le_abs_self _)
    (fun y => by
      show κ (stateF trivSMM flat (Fin.cons 0 y)) ∈ ({κ minkState} : Set _)
      rw [stateF_flat]; exact Set.mem_singleton _)
  exact ⟨κ, A, F, T, U, P, z, t₁, hT, hsol, ht₁, hid⟩

end NonVacuity


end RenewalGeometry.GenPhysIdFinal
