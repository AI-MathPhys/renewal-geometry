/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.GeneratedChartPropagation
import MathPhys.FieldTheory.Continuum.GeneratedCoupledIdentification
import MathPhys.FieldTheory.Continuum.GeneratedReadoutResiduals

/-!
# Chart-local smoothness of the sources: coupled identification and readouts

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
`thm:generated-dynamics` (back-reacting charged spinors): `GenCplId.core_identification_cpl` and
`GenReadout.readouts_of_identified` re-proved under `GenChL.SMSmoothL` (suffix `L`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! #### `core_identification_cpl` (from `Continuum/GeneratedCoupledIdentification.lean`) -/
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
/-- **The core identification for back-reacting spinors**: a smooth two-sided solution `W` of the
realized shift-transported system with constrained data, symmetric and in the chart margin on
`(-ε, ε) × 𝕋³`, has a physical head tuple `z` whose actual-jet state is `W` near `t = 0`, and the
Kato solution of the original realized system is the actual-jet state of `z` on `[0, t₁] × 𝕋³`. -/
theorem core_identification_cplL (hS : GenChL.SMSmoothL SM) (hU : UnitaryForms SM bG bV bS bS')
    (hC : GenDStress.CoupledDirac SM) (hN : GenNoether.CurrentNoether SM)
    (hT : GenCplMat.StressConservation SM)
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
    (hsymε : ∀ x ∈ openSlab (-ε) ε, AJKatoMod.IsSymmP (GenPhysIdFinal.Wof κ UM x))
    {T : ℝ} (hT0 : 0 < T) {U : Fin (dimS m V S S') → ST 3 → ℝ}
    {P : Fin (dimS m V S S') → Fin 3 → ST 3 → ℝ} (hUP : TwoSidedSol A F U₀ T U P) :
    ∃ (z : Tuple m V S S') (t₁ : ℝ), 0 < t₁ ∧ ∀ x ∈ slab 0 t₁,
      (∀ b, U b x = κ (stateF SM z x) b) ∧ bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  have hsubT : ∀ x : ST 3, x ∈ openSlab (-ε) ε → x ∈ openSlab (-TM) TM := fun x hx => by
    have h1 : -ε < x 0 := hx.1
    have h2 : x 0 < ε := hx.2
    exact ⟨show -TM < x 0 by linarith, show x 0 < TM by linarith⟩
  set W := GenPhysIdFinal.Wof κ UM with hWdef
  have hWs : ContDiffOn ℝ ∞ W (openSlab (-ε) ε) :=
    (GenPhysIdFinal.contDiffOn_Wof κ hMs).mono hsubT
  have hWp : IsSPeriodic W := GenPhysIdFinal.isSPeriodic_Wof κ hMP.perU
  have hchart : ∀ x ∈ openSlab (-ε) ε, MetChart (W x).1 := fun x hx => hKc _ (hKW x hx)
  have hrowM : ∀ x ∈ openSlab (-ε) ε, pd W 0 x +
      ∑ j : Fin 3, AJKatoMod.princPM SM (W x) j (pd W j.succ x) =
        toP (AJKatoMod.FsysM SM (ofP (W x))) := fun x hx =>
    GenPhysIdFinal.rows_of_twoSidedM SM hAM hFM hAMK hFMK hMP (hsubT x hx) (hKW x hx) (hsymε x hx)
  -- the head tuple
  set ε' := ε / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨z, hz⟩ := SlabLocal.exists_ext (GenPhysIdFinal.headTuple W hWs hWp hsymε hchart)
    (c := -ε') (d := ε') (by linarith) (by linarith) (by linarith)
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
    MathPhys.GenPhysIdFinal.ChL.slice_pd_eqL SM hS (isOpen_openSlab _ _) hW1 hC₀ hslice0 (hy0 y)
      (hMS.row _ (hy0 y))
  have hslice : ∀ y, W (Fin.cons 0 y) = stateF SM z (Fin.cons 0 y) := by
    intro y
    have hx := hy0 y
    have hdW : DifferentiableAt ℝ W (Fin.cons 0 y) :=
      GenHarmonic.diffAt_of_contDiffOn (isOpen_openSlab _ _) hW1 one_ne_zero hx
    have hdU : DifferentiableAt ℝ (stateF SM z₀) (Fin.cons 0 y) :=
      (contDiff_stateF SM z₀).differentiable (by simp) _
    obtain ⟨hzA, hzdA⟩ := GenPhysIdFinal.jet_match (GenPhysIdFinal.prA' m V S S') (hz _ hx).2.1
      (GenPhysIdFinal.A_eq_prA' (SM := SM) z₀) hdW hdU (hslice0 y) (hpd0 y)
    obtain ⟨hzg, hzdg⟩ := GenPhysIdFinal.jet_match (GenPhysIdFinal.prG' m V S S') (hz _ hx).1
      (show z₀.g = fun y => GenPhysIdFinal.prG' m V S S' (stateF SM z₀ y) from
        funext fun y => (GenDefJet.stateF_fst_fst SM z₀ y).symm) hdW hdU (hslice0 y) (hpd0 y)
    obtain ⟨hzH, hzdH⟩ := GenPhysIdFinal.jet_match (GenHiggsDefect.prH m V S S') (hz _ hx).2.2.1
      (show z₀.H = fun y => GenHiggsDefect.prH m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    obtain ⟨hzψ, hzdψ⟩ := GenPhysIdFinal.jet_match (GenSpinorDefect.prψ m V S S')
      (hz _ hx).2.2.2.1
      (show z₀.ψ = fun y => GenSpinorDefect.prψ m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    obtain ⟨hzψb, hzdψb⟩ := GenPhysIdFinal.jet_match (GenSpinorDefect.prψb m V S S')
      (hz _ hx).2.2.2.2
      (show z₀.ψb = fun y => GenSpinorDefect.prψb m V S S' (stateF SM z₀ y) from rfl) hdW hdU
      (hslice0 y) (hpd0 y)
    rw [hslice0 y]
    exact (GenPhysIdFinal.stateF_eq_of_jets hzg (funext fun α => hzdg α) hzA hzdA hzH hzdH hzψ
      hzdψ hzψb hzdψb).symm
  -- the bosonic sectors and the Dirac equations
  have ha' : -ε' < 0 := by linarith
  have hmet := MathPhys.GenHiggsDefect.ChL.metric_sectorL hS ha' hε'0 hMS (fun y => by rw [hslice y])
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
  have hQ := MathPhys.GenHiggsDefect.ChL.higgs_sectorL hS ha' hε'0 hMS hmet hEB (fun y => by rw [hslice y])
  have hPi := GenHiggsDefect.higgs_Pi hMS
  have hB : ∀ y ∈ openSlab (-ε') ε', GenSpinorDefect.prB m V S S' (W y) =
      GenSpinorDefect.prB m V S S' (stateF SM z y) := by
    intro y hy
    rw [GenSpinorDefect.prB_eq_iff]
    exact ⟨hmet y hy, funext (hMS.A y hy), (hEB y hy).1, (hEB y hy).2, hMS.H y hy, hPi y hy,
      hQ y hy⟩
  have hdir := GenSpinorDefect.dirac_of_rows hMS hmet
  have hCpl : GenCplRows.CplSol SM W z (-ε') ε' := ⟨hMS, hB, hdir⟩
  -- a global smooth extension and the coupled constraint system
  set ε'' := ε' / 2 with hε''
  have hε''0 : 0 < ε'' := by positivity
  obtain ⟨W', hW's, hW'p, hW'e⟩ := exists_global_ext hMS.smooth hMS.per
    (show -ε' < -ε'' by linarith) (show -ε'' < ε'' by linarith) (show ε'' < ε' by linarith)
  have hCpl' : GenCplRows.CplSol SM W' z (-ε'') ε'' :=
    cplSol_congr hCpl (by linarith) (by linarith) hW's.contDiffOn hW'p hW'e
  have hy0'' : ∀ y : Fin 3 → ℝ, (Fin.cons 0 y : ST 3) ∈ openSlab (-ε'') ε'' := fun y =>
    ⟨by show -ε'' < 0; linarith, by show (0 : ℝ) < ε''; exact hε''0⟩
  have hslice' : ∀ y, W' (Fin.cons 0 y) = stateF SM z (Fin.cons 0 y) := fun y => by
    rw [hW'e _ (hy0'' y)]; exact hslice y
  have hpd0' : ∀ (y : Fin 3 → ℝ) μ, pd W' μ (Fin.cons 0 y) =
      pd (stateF SM z₀) μ (Fin.cons 0 y) := fun y μ => by
    have hev : W' =ᶠ[𝓝 (Fin.cons 0 y : ST 3)] W :=
      Filter.eventually_of_mem ((isOpen_openSlab _ _).mem_nhds (hy0'' y)) hW'e
    rw [(SlabLocal.pd_eventuallyEq hev μ).eq_of_nhds]
    exact hpd0 y μ
  have hS0 : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y) :=
    fun y => (hslice y).symm.trans (hslice0 y)
  obtain ⟨hc0, hct⟩ := cF_slice hCpl' (by linarith) hε''0 hS0 hpd0' hC₀
  have hw0 := wF_slice hW's hCpl' (by linarith) hε''0 hslice' hc0 hct
  have hG0 : ∀ y : Fin 3 → ℝ, gaussF SM z (Fin.cons 0 y) = 0 := by
    intro y
    rw [GenPhysIdClosed.gauss_eq_of_slice SM hS0 rfl]
    unfold gaussF
    rw [(hC₀ y).1]
    simp
  set t₂ := ε'' / 2 with ht₂
  have ht₂0 : 0 < t₂ := by positivity
  have hdiv := MathPhys.GenCplMat.ChL.divT_zero_cplL hN hT hS hCpl' (show -ε'' < 0 by linarith) ht₂0
    (show t₂ < ε'' by linarith) hG0
  have hvan := GenCplCon.coupled_constraints_vanish hC hU hW's hW'p hCpl'
    (show -ε'' < 0 by linarith) ht₂0 (show t₂ < ε'' by linarith) (fun x hx => (hdiv x hx).1)
    hc0 hct hw0
  -- the head tuple is physical and `W` is its actual-jet state on `[0, t₂)`
  have hphys : ∀ x : ST 3, 0 ≤ x 0 → x 0 < t₂ →
      W x = stateF SM z x ∧ bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
    intro x h0 h1
    have hxs : x ∈ slab 0 t₂ := ⟨h0, h1.le⟩
    have hxo : x ∈ openSlab (-ε'') ε'' := ⟨by linarith, by linarith⟩
    obtain ⟨hcx, hwx⟩ := hvan x hxs
    have hY : GenCplX.Yt SM W' z x = 0 := congrArg Prod.fst hwx
    have hYb : GenCplX.Ybt SM W' z x = 0 := congrArg (fun v => v.2.2.1) hwx
    have hdc : ∀ μ, pd (GenHarmonic.cF z) μ x = 0 := by
      rcases h0.lt_or_eq with hpos | hzero
      · intro μ
        refine GenConstraint.pd_eq_zero_of_eventually ?_ μ
        have hO : IsOpen (openSlab (d := 3) 0 t₂) := isOpen_openSlab 0 t₂
        exact Filter.eventually_of_mem (hO.mem_nhds ⟨hpos, h1⟩) fun y hy =>
          (hvan y ⟨hy.1.le, hy.2.le⟩).1
      · have hx : x = Fin.cons 0 (Fin.tail x) :=
          (GenPhysIdClosed.cons_tail_eq hzero.symm).symm
        intro μ
        induction μ using Fin.cases with
        | zero => rw [hx]; exact hct _
        | succ j =>
          exact GenPhysIdClosed.zero_on_slice_pd (GenHarmonic.contDiff_cF z) hc0 hzero.symm j
    have hWx : W' x = stateF SM z x := by
      apply GenSpinorDefect.eq_of_prB_prS (hCpl'.bos x hxo)
      rw [GenSpinorDefect.prS_apply, GenSpinorDefect.prS_apply]
      have hX : (W' x).2.2.2.2.2.2.2.2.1 = (stateF SM z x).2.2.2.2.2.2.2.2.1 :=
        sub_eq_zero.1 hY
      have hXb : (W' x).2.2.2.2.2.2.2.2.2.2 = (stateF SM z x).2.2.2.2.2.2.2.2.2.2 :=
        sub_eq_zero.1 hYb
      exact Prod.ext (hCpl'.ψ_eq hxo) (Prod.ext hX (Prod.ext (hCpl'.ψb_eq hxo) hXb))
    have hp := physical_of_defects hC hCpl' hxo (hdiv x hxs).2 hcx hdc hY hYb
    refine ⟨?_, hp⟩
    rw [← hW'e x hxo]
    exact hWx
  -- `W` solves the original realized system
  have horig := GenCplRows.orig_row_cpl hCpl
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
      rw [GenPhysIdFinal.pd_Wof κ hdiff]
      congr 1
      funext c
      rw [hMP.pd_eq hAM hFM c (hsubT _ hxε) j.succ]
      rfl
    rw [genP_eq_actual_jet hAK hFK UM PM _ (hKW _ hxε) b]
    have h0 : genP AM FM UM PM b (Fin.cons t y) = pd (UM b) 0 (Fin.cons t y) :=
      (hMP.pd_eq hAM hFM b (hsubT _ hxε) 0).symm
    rw [h0]
    have h1 : pd (UM b) 0 (Fin.cons t y) = κ (pd W 0 (Fin.cons t y)) b := by
      rw [GenPhysIdFinal.pd_Wof κ hdiff, LinearEquiv.apply_symm_apply]
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
  have hOrig := GenPhysIdFinal.twoSided_of_gen (A := A) (F := F) hMP (by linarith : ε' ≤ TM) hgen
  set t₁ := min T t₂ / 2 with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁T : t₁ < T := by
    have := min_le_left T t₂; rw [ht₁]; linarith
  have ht₁ε : t₁ < t₂ := by
    have := min_le_right T t₂; rw [ht₁]; linarith
  have huniq := KatoStab.twoSided_unique hA hsym hF hUP hOrig ht₁0 ht₁T (by linarith)
  refine ⟨z, t₁, ht₁0, fun x hx => ?_⟩
  have hxp := hphys x hx.1 (by have := hx.2; linarith)
  refine ⟨fun b => ?_, hxp.2⟩
  rw [huniq x hx b, ← hxp.1]
  show UM b x = κ (κ.symm fun c => UM c x) b
  rw [LinearEquiv.apply_symm_apply]
end MathPhys.GenCplId.ChL

/-! #### `readouts_of_identified` (from `Continuum/GeneratedReadoutResiduals.lean`) -/
namespace MathPhys.GenReadout.ChL
open Set Filter Topology
open scoped ContDiff
open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite
  GenResMaps GenPhysIdFinal
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'}
set_option maxHeartbeats 4000000 in
/-- **The residual readouts for an identified exact solution.**  Let `z` be a physical smooth
tuple on `[0, t₁] × 𝕋³` (`R_B(z) = R_D(z) = 0`), `V = κ(𝒰(z))` its coordinate actual-jet state,
and let a one-sided classical solution `U` coincide with `V` there, with the time derivatives
`∂_tV = U_t` and `c_k(∂_t²V) = D₂`.  Then for all coordinates `e_B`, `e_D` there are `C`, `η > 0`
such that every Hermite cell `[jτ, (j+1)τ] ⊆ [0, t₁]` whose Fourier-form rates against `U` are
`C_r(τ² + δ + ν)` (values, slopes) and `C_r(τ + δ + ν)` (second derivatives), with
`τ + δ + ν ≤ η`, has its head metric in the Lorentzian chart and the residual bounds of
`eq:generated-bosonic` / `eq:generated-Dirac` on every slice of the open cell. -/
theorem readouts_of_identifiedL (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (hS : GenChL.SMSmoothL SM) {s : ℕ} (hs : 3 ≤ s) {z : Tuple m V S S'} {t₁ : ℝ}
    (hphys : ∀ x ∈ slab (d := 3) 0 t₁, bosF SM z x = 0 ∧ dirF SM z x = 0)
    {U Ut : Fin (dimS m V S S') → ST 3 → ℝ} {D₂ : Fin (dimS m V S S') → (Fin 3 → ℤ) → ℝ → ℝ}
    (hUV : ∀ x ∈ slab (d := 3) 0 t₁, ∀ b, U b x = stC κ SM z b x)
    (hVt : ∀ b, ∀ t ∈ Icc 0 t₁, ∀ y,
      pd (stC κ SM z b) 0 (Fin.cons t y) = Ut b (Fin.cons t y))
    (hVtt : ∀ b k, ∀ t ∈ Icc 0 t₁, coef (pd (pd (stC κ SM z b) 0) 0) t k = D₂ b k t)
    {Cr τs : ℝ} (hCr : 0 ≤ Cr) (hτs : 0 < τs) {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ))
    {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ)) :
    ∃ C ≥ 0, ∃ η > 0, ∃ K2 : Set (J2I 3 × Fin (dimS m V S S') → ℝ), IsCompact K2 ∧
      (∀ w ∈ K2, headJ (m := m) (V := V) (S := S) (S' := S') κ w ∈ chartJ2 m V S S') ∧
      ∀ {q N : ℕ} (τ : ℝ), 0 < τ → τ ≤ τs → ∀ δ ν : ℝ, 0 ≤ δ → 0 ≤ ν →
      τ + δ + ν ≤ η → ∀ (j : ℕ) (Uj Uj1 Gj Gj1 : GS 3 (dimS m V S S') N),
      ((j : ℝ) + 1) * τ ≤ t₁ →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
        (cf q (SpectralGalerkin.hermite τ Uj Uj1 Gj Gj1 θ) b k -
          coef (U b) (j * τ + θ * τ) k) ^ 2 ≤ (Cr * (τ ^ 2 + δ + ν)) ^ 2) →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq (s + 2) k *
        (cf q (SpectralGalerkin.hermiteD τ Uj Uj1 Gj Gj1 θ) b k -
          coef (Ut b) (j * τ + θ * τ) k) ^ 2 ≤ (Cr * (τ ^ 2 + δ + ν)) ^ 2) →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ S₀ : Finset (Fin 3 → ℤ), ∑ b, ∑ k ∈ S₀, wq s k *
        (cf q (SpectralGalerkin.hermiteDD τ Uj Uj1 Gj Gj1 θ) b k -
          D₂ b k (j * τ + θ * τ)) ^ 2 ≤ (Cr * (τ + δ + ν)) ^ 2) →
      (∀ y : ST 3, y 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
        (fun p => j2c (recW τ (j * τ) Uj Uj1 Gj Gj1 q) p y) ∈ K2) ∧
      (∀ y ∈ openSlab (j * τ) ((j + 1) * τ),
        HeadChart κ (fun c => recW τ (j * τ) Uj Uj1 Gj Gj1 q c y)) ∧
      ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
        ∑ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
          riemR (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x) c - riemR (hj2 z x) c) t ≤
            (C * (τ + δ + ν)) ^ 2 ∧
        ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x)) k) t ≤
          (C * (τ + δ + ν)) ^ 2 ∧
        ∑ k, Q (s + 1) (fun x =>
          eD (GenResMaps.dirR SM (hjF κ (recW τ (j * τ) Uj Uj1 Gj Gj1 q) x)) k) t ≤
            (C * (τ ^ 2 + δ + ν)) ^ 2 := by
  set Vf := stC κ SM z with hVfdef
  have hV : ∀ b, ContDiff ℝ ∞ (Vf b) := contDiff_stC κ SM z
  have hVp : ∀ b, IsSPeriodic (Vf b) := isSPeriodic_stC κ SM z
  have hj2V : ∀ p, ContDiff ℝ ∞ (j2c Vf p) := fun p => contDiff_jop2 p.1 (hV p.2)
  have hj2Vp : ∀ p, IsSPeriodic (j2c Vf p) := fun p => isSPeriodic_jop2 p.1 (hVp p.2)
  have hj1V : ∀ p, ContDiff ℝ ∞ (j1c Vf p) := fun p => contDiff_jop1 p.1 (hV p.2)
  have hj1Vp : ∀ p, IsSPeriodic (j1c Vf p) := fun p => isSPeriodic_jop1 p.1 (hVp p.2)
  -- the compact jet sets of the exact solution
  obtain ⟨K1, hK1, hK1r, hK1m⟩ := exists_compact_slices (fun p => (hj2V p).continuous) hj2Vp t₁
  obtain ⟨K1', hK1', hK1r', hK1m'⟩ :=
    exists_compact_slices (fun p => (hj1V p).continuous) hj1Vp t₁
  -- the charts
  set O := headJ (m := m) (V := V) (S := S) (S' := S') κ ⁻¹' chartJ2 m V S S' with hOdef
  have hO : IsOpen O := isOpen_chartJ2.preimage (contDiff_headJ κ).continuous
  set O1 := head1J (m := m) (V := V) (S := S) (S' := S') κ ⁻¹' chartJ2 m V S S' with hO1def
  have hO1 : IsOpen O1 := isOpen_chartJ2.preimage (contDiff_head1J κ).continuous
  have hK1O : K1 ⊆ O := by
    intro w hw
    obtain ⟨x, rfl⟩ := hK1r hw
    show headJ κ (fun p => j2c Vf p x) ∈ chartJ2 m V S S'
    rw [← hj2_eq_headJ κ SM z x]
    exact ⟨z.det_ne x, z.lor x⟩
  have hK1O' : K1' ⊆ O1 := by
    intro w hw
    obtain ⟨x, rfl⟩ := hK1r' hw
    show head1J κ (fun p => j1c Vf p x) ∈ chartJ2 m V S S'
    have hg : (head1J (m := m) (V := V) (S := S) (S' := S') κ (fun p => j1c Vf p x)).1.1 =
        z.g x := Lg_stC κ z x
    show (Matrix.of (head1J κ (fun p => j1c Vf p x)).1.1).det ≠ 0 ∧
      IsLorChart (ginvOf (head1J κ (fun p => j1c Vf p x)).1.1)
    rw [hg]
    exact ⟨z.det_ne x, z.lor x⟩
  -- the readout families
  have hΨR : ∀ c : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      ContDiffOn ℝ ∞ (fun w => riemR (headJ (m := m) (V := V) (S := S) (S' := S') κ w) c) O :=
    fun c => contDiffOn_comp_preimage (contDiff_headJ κ) fun w hw => riemR_smooth hw c
  have hΨB : ∀ k : Fin nB,
      ContDiffOn ℝ ∞ (fun w => eB (bosR SM (headJ κ w)) k) O := fun k =>
    contDiffOn_comp_preimage (Φ := fun j => eB (bosR SM j) k) (contDiff_headJ κ) fun w hw =>
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nB => ℝ) k).comp eB).contDiff
        |>.contDiffAt).comp w (MathPhys.GenResMaps.ChL.bosR_smoothL SM hS hw)
  have hΨD : ∀ k : Fin nD,
      ContDiffOn ℝ ∞ (fun w => eD (GenResMaps.dirR SM (head1J κ w)) k) O1 := fun k =>
    contDiffOn_comp_preimage (Φ := fun j => eD (GenResMaps.dirR SM j) k) (contDiff_head1J κ)
      fun w hw => (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nD => ℝ) k).comp
        eD).contDiff |>.contDiffAt).comp w (dirR_smooth SM hw)
  -- energy bounds of the exact jets
  have hMb : ∀ {ι : Type} [Fintype ι] (r : ℕ) (f : ι → ST 3 → ℝ), (∀ i, ContDiff ℝ ∞ (f i)) →
      ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc 0 t₁, ∑ i, Q r (f i) t ≤ M := by
    intro ι _ r f hf
    have hc : ContinuousOn (fun t => ∑ i, Q r (f i) t) (Icc 0 t₁) :=
      (continuous_finsetSum _ fun i _ => continuous_Q r (hf i)).continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨|M|, abs_nonneg _, fun t ht => ?_⟩
    have := hM t ht
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  obtain ⟨M2, hM2, hM2b⟩ := hMb s (j2c Vf) hj2V
  obtain ⟨M1, hM1, hM1b⟩ := hMb (s + 1) (j1c Vf) hj1V
  -- the readout cores
  obtain ⟨εR, hεR, hsubR, ΨR, hΨRs, hΨRK, KR, hKR, CSR, hCSR, coreR⟩ :=
    readout_core (r := s) hs hO hK1 hK1O hΨR hM2
  obtain ⟨εB, hεB, hsubB, ΨB, hΨBs, hΨBK, KB, hKB, CSB, hCSB, coreB⟩ :=
    readout_core (r := s) hs hO hK1 hK1O hΨB hM2
  obtain ⟨εD, hεD, hsubD, ΨD, hΨDs, hΨDK, KD, hKD, CSD, hCSD, coreD⟩ :=
    readout_core (r := s + 1) (by omega) hO1 hK1' hK1O' hΨD hM1
  -- the constants
  set Mst : ℝ := max 1 τs with hMst
  have hMst1 : 1 ≤ Mst := le_max_left _ _
  have hMstτ : τs ≤ Mst := le_max_right _ _
  set CE : ℝ := 21 * (Cr ^ 2 + 2 * (Cr ^ 2 * Mst ^ 2)) with hCE
  set CE1 : ℝ := 5 * (2 * (Cr ^ 2 * Mst ^ 2)) with hCE1
  have hCE0 : 0 ≤ CE := by positivity
  have hCE10 : 0 ≤ CE1 := by positivity
  set εm : ℝ := min εR (min εB εD) with hεm
  have hεm0 : 0 < εm := lt_min hεR (lt_min hεB hεD)
  set Λ : ℝ := (CE + CE1 + 1) * (CSR + CSB + CSD + 1) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have h1 : 1 ≤ CE + CE1 + 1 := by linarith
    have h2 : 1 ≤ CSR + CSB + CSD + 1 := by linarith
    nlinarith
  have hΛ0 : 0 < Λ := by linarith
  set η : ℝ := min 1 εm / Real.sqrt Λ with hη
  have hη0 : 0 < η := div_pos (lt_min one_pos hεm0) (Real.sqrt_pos.2 hΛ0)
  set C : ℝ := Real.sqrt (256 * (KR * CE)) + Real.sqrt (nB * (KB * CE)) +
    Real.sqrt (nD * (KD * (10 * Cr ^ 2))) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, η, hη0, Metric.cthickening εR K1, hK1.cthickening, fun w hw => hsubR hw,
    fun {q N} τ hτ hττ δ ν hδ hν hεη j Uj Uj1 Gj Gj1 hj h0 h1 h2 => ?_⟩
  set W := recW τ (j * τ) Uj Uj1 Gj Gj1 q with hWdef
  have hW : ∀ b, ContDiff ℝ ∞ (W b) := fun b => contDiff_recW τ _ Uj Uj1 Gj Gj1 b
  have hWp : ∀ b, IsSPeriodic (W b) := fun b => isSPeriodic_recW τ _ Uj Uj1 Gj Gj1 b
  have hj2W : ∀ p, ContDiff ℝ ∞ (j2c W p) := fun p => contDiff_jop2 p.1 (hW p.2)
  have hj2Wp : ∀ p, IsSPeriodic (j2c W p) := fun p => isSPeriodic_jop2 p.1 (hWp p.2)
  have hj1W : ∀ p, ContDiff ℝ ∞ (j1c W p) := fun p => contDiff_jop1 p.1 (hW p.2)
  have hj1Wp : ∀ p, IsSPeriodic (j1c W p) := fun p => isSPeriodic_jop1 p.1 (hWp p.2)
  set ε : ℝ := τ + δ + ν with hεdef
  set ε₂ : ℝ := τ ^ 2 + δ + ν with hε₂def
  have hε0 : 0 ≤ ε := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hε₂ε : ε₂ ≤ Mst * ε := by
    have h1 : τ ^ 2 ≤ Mst * τ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hττ.trans hMstτ) hτ.le
    have h2 : δ + ν ≤ Mst * (δ + ν) := le_mul_of_one_le_left (by positivity) hMst1
    rw [hε₂def, hεdef]; nlinarith
  -- `ε` is small
  have hεsq : ε ^ 2 * Λ ≤ (min 1 εm) ^ 2 := by
    have h1 : ε ≤ min 1 εm / Real.sqrt Λ := hεη
    have h2 : ε * Real.sqrt Λ ≤ min 1 εm := by
      rwa [le_div_iff₀ (Real.sqrt_pos.2 hΛ0)] at h1
    have h3 : (ε * Real.sqrt Λ) ^ 2 ≤ (min 1 εm) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rwa [mul_pow, Real.sq_sqrt hΛ0.le] at h3
  have hmin1 : (min 1 εm) ^ 2 ≤ 1 := by
    have := min_le_left 1 εm
    have h0 : 0 ≤ min 1 εm := le_min zero_le_one hεm0.le
    nlinarith
  have hmin2 : ∀ e, e ≥ εm → (min 1 εm) ^ 2 ≤ e ^ 2 := fun e he => by
    have h0 : 0 ≤ min 1 εm := le_min zero_le_one hεm0.le
    exact pow_le_pow_left₀ h0 ((min_le_right 1 εm).trans he) 2
  have hsmall : ∀ A B : ℝ, A * B ≤ Λ → A * (B * ε ^ 2) ≤ (min 1 εm) ^ 2 := fun A B h => by
    have := mul_le_mul_of_nonneg_right h (sq_nonneg ε)
    nlinarith [hεsq]
  have hp1 : 0 ≤ CSB + CSD + 1 := by positivity
  have hp2 : 0 ≤ CSR + CSD + 1 := by positivity
  have hp3 : 0 ≤ CSR + CSB + 1 := by positivity
  have hCSRΛ : CSR * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE0 hp1, mul_nonneg (add_nonneg hCE10 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCSBΛ : CSB * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE0 hp2, mul_nonneg (add_nonneg hCE10 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCSDΛ : CSD * CE1 ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg hCE10 hp3, mul_nonneg (add_nonneg hCE0 zero_le_one)
      (add_nonneg (add_nonneg (add_nonneg hCSR hCSB) hCSD) zero_le_one)]
  have hCEΛ : 1 * CE ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg (add_nonneg (add_nonneg hCE0 hCE10) zero_le_one)
      (add_nonneg (add_nonneg hCSR hCSB) hCSD)]
  have hCE1Λ : 1 * CE1 ≤ Λ := by
    rw [hΛ]; nlinarith [mul_nonneg (add_nonneg (add_nonneg hCE0 hCE10) zero_le_one)
      (add_nonneg (add_nonneg hCSR hCSB) hCSD)]
  have hE1 : CE * ε ^ 2 ≤ 1 := by
    have := hsmall 1 CE hCEΛ; linarith
  have hE1' : CE1 * ε ^ 2 ≤ 1 := by
    have := hsmall 1 CE1 hCE1Λ; linarith
  have hεmR : (min 1 εm) ^ 2 ≤ εR ^ 2 := hmin2 εR (min_le_left _ _)
  have hεmB : (min 1 εm) ^ 2 ≤ εB ^ 2 := hmin2 εB ((min_le_right _ _).trans (min_le_left _ _))
  have hεmD : (min 1 εm) ^ 2 ≤ εD ^ 2 := hmin2 εD ((min_le_right _ _).trans (min_le_right _ _))
  -- the Dirac energy
  set ED : ℝ := 10 * Cr ^ 2 * ε₂ ^ 2 with hED
  have hED0 : 0 ≤ ED := by positivity
  have hEDle : ED ≤ CE1 * ε ^ 2 := by
    have h1 : ε₂ ^ 2 ≤ Mst ^ 2 * ε ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hε₂0 hε₂ε 2
    have h2 : 0 ≤ Cr ^ 2 := sq_nonneg _
    rw [hED, hCE1]; nlinarith
  -- energies on the cell
  have hen : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ p : J2I 3 × Fin (dimS m V S S'), Q s (fun x => j2c W p x - j2c Vf p x) t ≤ CE * ε ^ 2 ∧
      ∑ p : J1I 3 × Fin (dimS m V S S'), Q (s + 1) (fun x => j1c W p x - j1c Vf p x) t ≤ ED := by
    intro t ht
    obtain ⟨e0, e1, e2⟩ := cell_energies (q := q) (s := s) hτ hV hVp hUV hVt hVtt h0 h1 h2 ht hj
    have E2 := jet2_energy_le (r := s) hW hV e0 e1 e2
    have E1 := jet1_energy_le (r := s) hW hV e0 e1
    rw [card_J2I] at E2
    rw [card_J1I] at E1
    constructor
    · refine E2.trans ?_
      have h1 : (Cr * ε₂) ^ 2 ≤ Cr ^ 2 * Mst ^ 2 * ε ^ 2 := by
        rw [mul_pow, mul_assoc, ← mul_pow Mst]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε₂0 hε₂ε 2) (sq_nonneg _)
      have h2 : (Cr * ε) ^ 2 = Cr ^ 2 * ε ^ 2 := by ring
      rw [hCE]
      push_cast
      nlinarith
    · refine E1.trans (le_of_eq ?_)
      push_cast
      rw [hED]; ring
  -- the readout cores on the cell
  have hcR : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j2c W p (Fin.cons t y)) ∈ Metric.cthickening εR K1) ∧
      ∀ c, Q s (fun x => ΨR c (fun p => j2c W p x) - ΨR c (fun p => j2c Vf p x)) t ≤
        KR * (CE * ε ^ 2) := fun t ht =>
    coreR (j2c W) (j2c Vf) hj2W hj2V hj2Wp hj2Vp t (CE * ε ^ 2) (by positivity) hE1
      ((hsmall CSR CE hCSRΛ).trans hεmR) (hK1m t (slab_of_cell hτ hj ht))
      (hM2b t (slab_of_cell hτ hj ht)) (hen t ht).1
  have hcB : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j2c W p (Fin.cons t y)) ∈ Metric.cthickening εB K1) ∧
      ∀ k, Q s (fun x => ΨB k (fun p => j2c W p x) - ΨB k (fun p => j2c Vf p x)) t ≤
        KB * (CE * ε ^ 2) := fun t ht =>
    coreB (j2c W) (j2c Vf) hj2W hj2V hj2Wp hj2Vp t (CE * ε ^ 2) (by positivity) hE1
      ((hsmall CSB CE hCSBΛ).trans hεmB) (hK1m t (slab_of_cell hτ hj ht))
      (hM2b t (slab_of_cell hτ hj ht)) (hen t ht).1
  have hcD : ∀ t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (∀ y, (fun p => j1c W p (Fin.cons t y)) ∈ Metric.cthickening εD K1') ∧
      ∀ k, Q (s + 1) (fun x => ΨD k (fun p => j1c W p x) - ΨD k (fun p => j1c Vf p x)) t ≤
        KD * ED := fun t ht =>
    coreD (j1c W) (j1c Vf) hj1W hj1V hj1Wp hj1Vp t ED hED0 (hEDle.trans hE1')
      (le_trans (mul_le_mul_of_nonneg_left hEDle hCSD) ((hsmall CSD CE1 hCSDΛ).trans hεmD))
      (hK1m' t (slab_of_cell hτ hj ht)) (hM1b t (slab_of_cell hτ hj ht)) (hen t ht).2
  -- points of the open cell
  have hcell : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hx_cons : ∀ x : ST 3, (Fin.cons (x 0) (Fin.tail x) : ST 3) = x := Fin.cons_self_tail
  have hmR : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c W p x) ∈ Metric.cthickening εR K1 := fun x hx => by
    have := (hcR (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hmB : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c W p x) ∈ Metric.cthickening εB K1 := fun x hx => by
    have := (hcB (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hmD : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j1c W p x) ∈ Metric.cthickening εD K1' := fun x hx => by
    have := (hcD (x 0) (hcell x hx)).1 (Fin.tail x)
    rwa [hx_cons] at this
  have hexK : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j2c Vf p x) ∈ K1 := fun x hx => by
    have := hK1m (x 0) (slab_of_cell hτ hj (hcell x hx)) (Fin.tail x)
    rwa [hx_cons] at this
  have hexK' : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      (fun p => j1c Vf p x) ∈ K1' := fun x hx => by
    have := hK1m' (x 0) (slab_of_cell hτ hj (hcell x hx)) (Fin.tail x)
    rwa [hx_cons] at this
  have hphysx : ∀ x ∈ openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      bosF SM z x = 0 ∧ dirF SM z x = 0 := fun x hx =>
    hphys x (slab_of_cell hτ hj (hcell x hx))
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun t ht => ?_⟩
  · have := (hcR (y 0) hy).1 (Fin.tail y)
    rwa [hx_cons] at this
  · -- the chart
    exact headChart_of_mem κ (hsubR (hmR y hy))
  · have hO' : IsOpen (openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :=
      isOpen_openSlab _ _
    have hsl : ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) ∈
        openSlab (d := 3) ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := fun y => by
      show (j : ℝ) * τ < (Fin.cons t y : ST 3) 0 ∧ (Fin.cons t y : ST 3) 0 < ((j : ℝ) + 1) * τ
      simpa using ht
    have htI : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) := ⟨ht.1.le, ht.2.le⟩
    have hCsq : ∀ a b : ℝ, 0 ≤ a → Real.sqrt a ≤ C → a * b ^ 2 ≤ (C * b) ^ 2 :=
      fun a b ha hac => by
        have := pow_le_pow_left₀ (Real.sqrt_nonneg a) hac 2
        rw [Real.sq_sqrt ha] at this
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg b)
    have hs1 : Real.sqrt (256 * (KR * CE)) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg ((nB : ℝ) * (KB * CE)),
        Real.sqrt_nonneg ((nD : ℝ) * (KD * (10 * Cr ^ 2)))]
    have hs2 : Real.sqrt ((nB : ℝ) * (KB * CE)) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg (256 * (KR * CE)),
        Real.sqrt_nonneg ((nD : ℝ) * (KD * (10 * Cr ^ 2)))]
    have hs3 : Real.sqrt ((nD : ℝ) * (KD * (10 * Cr ^ 2))) ≤ C := by
      rw [hC]; linarith [Real.sqrt_nonneg (256 * (KR * CE)),
        Real.sqrt_nonneg ((nB : ℝ) * (KB * CE))]
    refine ⟨?_, ?_, ?_⟩
    · -- the Riemann tensor
      have hc : ∀ c : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q s (fun x =>
          riemR (hjF κ W x) c - riemR (hj2 z x) c) t ≤ KR * (CE * ε ^ 2) := by
        intro c
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcR t htI).2 c)
        show riemR (hjF κ W x) c - riemR (hj2 z x) c =
          ΨR c (fun p => j2c W p x) - ΨR c (fun p => j2c Vf p x)
        rw [hΨRK c _ (hmR x hx), hΨRK c _ (Metric.self_subset_cthickening _ (hexK x hx)),
          hjF_eq κ hW x, hj2_eq_headJ κ SM z x]
      refine (Finset.sum_le_sum fun c _ => hc c).trans ?_
      rw [Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq (256 * (KR * CE)) ε (by positivity) hs1
      push_cast
      exact le_trans (le_of_eq (by ring)) this
    · -- the bosonic residual
      have hk : ∀ k, Q s (fun x => eB (bosR SM (hjF κ W x)) k) t ≤ KB * (CE * ε ^ 2) := by
        intro k
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcB t htI).2 k)
        show eB (bosR SM (hjF κ W x)) k =
          ΨB k (fun p => j2c W p x) - ΨB k (fun p => j2c Vf p x)
        rw [hΨBK k _ (hmB x hx), hΨBK k _ (Metric.self_subset_cthickening _ (hexK x hx)),
          ← hj2_eq_headJ κ SM z x, bosR_hj2, (hphysx x hx).1, map_zero, Pi.zero_apply,
          sub_zero, hjF_eq κ hW x]
      refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq ((nB : ℝ) * (KB * CE)) ε (by positivity) hs2
      exact le_trans (le_of_eq (by ring)) this
    · -- the Dirac residual
      have hk : ∀ k, Q (s + 1) (fun x => eD (GenResMaps.dirR SM (hjF κ W x)) k) t ≤
          KD * ED := by
        intro k
        refine le_of_eq_of_le (Q_congr_open hO' (fun x hx => ?_) hsl) ((hcD t htI).2 k)
        show eD (GenResMaps.dirR SM (hjF κ W x)) k =
          ΨD k (fun p => j1c W p x) - ΨD k (fun p => j1c Vf p x)
        have hex : GenResMaps.dirR SM (head1J κ (fun p => j1c Vf p x)) = 0 := by
          rw [← dirR_hjF κ SM hV x, hjF_eq κ hV x, ← hj2_eq_headJ κ SM z x, dirR_hj2,
            (hphysx x hx).2]
        rw [hΨDK k _ (hmD x hx), hΨDK k _ (Metric.self_subset_cthickening _ (hexK' x hx)),
          hex, map_zero, Pi.zero_apply, sub_zero, dirR_hjF κ SM hW x]
      refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have := hCsq ((nD : ℝ) * (KD * (10 * Cr ^ 2))) ε₂ (by positivity) hs3
      rw [hED]
      exact le_trans (le_of_eq (by ring)) this
end MathPhys.GenReadout.ChL
