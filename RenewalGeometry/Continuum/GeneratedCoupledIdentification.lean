/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledMatter
import RenewalGeometry.Continuum.GeneratedCoupledKato
import RenewalGeometry.Continuum.GeneratedPhysicalIdentificationFinal

/-!
# `lem:generated-physical-identification` for back-reacting spinors

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`), with `Σ = 𝕋³`, for theory data with the **symmetric Dirac stress**
(`GenDStress.CoupledDirac`: the spinors back-react on the metric).

The proof follows `GenPhysIdFinal.core_identification`, with the decoupled-spinor step (the
spinor-free tuple solves the symmetric system) replaced by the **coupled constraint system**
(`GenCplCon.coupled_constraints_vanish`): the harmonic defect, the tangential spinor defects and
the normal prolongation defects of the head tuple vanish, by uniqueness for a wave block coupled
at order zero to a symmetric hyperbolic first-order block.

* `cplSol_congr`, `exists_global_ext` — locality of coupled solutions, global smooth extensions;
* `ddg_eq_of_metric` — the metric 2-jet on a slice is fixed by the metric blocks of the
  derivatives of the state;
* initial values of the defects on the data slice;
* **`core_identification_cpl`**, **`generated_physical_identification_coupled`**.
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenCplId

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

/-! ### Locality -/

section Locality

/-- **Coupled solutions are local**: a smooth periodic field agreeing with a coupled solution on
a sub-slab is a coupled solution there. -/
theorem cplSol_congr {W W' : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b c d : ℝ}
    (h : GenCplRows.CplSol SM W z a b) (hac : a ≤ c) (hdb : d ≤ b)
    (hs : ContDiffOn ℝ ∞ W' (openSlab c d)) (hp : IsSPeriodic W')
    (he : ∀ y ∈ openSlab c d, W' y = W y) : GenCplRows.CplSol SM W' z c d := by
  have hsub : ∀ y : ST 3, y ∈ openSlab c d → y ∈ openSlab a b := fun y hy =>
    ⟨lt_of_le_of_lt hac hy.1, lt_of_lt_of_le hy.2 hdb⟩
  have hev : ∀ y ∈ openSlab c d, W' =ᶠ[𝓝 y] W := fun y hy =>
    Filter.eventually_of_mem ((isOpen_openSlab c d).mem_nhds hy) he
  have hpd : ∀ y ∈ openSlab c d, ∀ μ, pd W' μ y = pd W μ y := fun y hy μ =>
    (SlabLocal.pd_eventuallyEq (hev y hy) μ).eq_of_nhds
  refine ⟨⟨hs, hp, fun y hy => ?_, fun y hy => ?_, fun y hy i => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_,
    fun y hy => h.dir y (hsub y hy)⟩
  · rw [he y hy]; exact h.ms.chart y (hsub y hy)
  · rw [he y hy]; exact h.ms.g y (hsub y hy)
  · rw [he y hy]; exact h.ms.A y (hsub y hy) i
  · rw [he y hy]; exact h.ms.H y (hsub y hy)
  · rw [he y hy]; exact h.ms.ψ y (hsub y hy)
  · rw [he y hy]; exact h.ms.ψb y (hsub y hy)
  · simp only [hpd y hy, he y hy]
    exact h.ms.row y (hsub y hy)
  · rw [he y hy]; exact h.bos y (hsub y hy)

/-- **Global smooth extensions** of slab-local periodic fields. -/
theorem exists_global_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : ST 3 → E}
    {a b c d : ℝ} (hW : ContDiffOn ℝ ∞ W (openSlab a b)) (hp : IsSPeriodic W) (hac : a < c)
    (hcd : c < d) (hdb : d < b) :
    ∃ W' : ST 3 → E, ContDiff ℝ ∞ W' ∧ IsSPeriodic W' ∧ ∀ y ∈ openSlab c d, W' y = W y := by
  obtain ⟨φ, hφ, hφr, hφid⟩ := SlabLocal.exists_time_reparam hac hcd hdb
  refine ⟨fun x => W (SlabLocal.reparam φ x), hW.comp_contDiff (SlabLocal.contDiff_reparam hφ)
    (SlabLocal.reparam_mem hφr), fun k x => by simp only [SlabLocal.reparam_shift, hp k],
    fun y hy => ?_⟩
  have : SlabLocal.reparam φ y = y := by
    unfold SlabLocal.reparam
    rw [hφid _ hy, Fin.cons_self_tail]
  simp only [this]

end Locality

/-! ### The metric 2-jet on a slice -/

section Slice

variable (SM) in
/-- **The metric 2-jet on a slice is fixed by the metric blocks of the state and of its
derivatives** (the `p`- and `q`-blocks of `∂_γ𝒰` are the frame components `e_A{}^β∂_γ∂_βg`). -/
theorem ddg_eq_of_metric {z z0 : Tuple m V S S'} {x : ST 3}
    (hSx : stateF SM z x = stateF SM z0 x)
    (hm : ∀ γ, (pd (stateF SM z) γ x).1 = (pd (stateF SM z0) γ x).1) : z.ddg x = z0.ddg x := by
  have hd1 : ∀ γ, (toP ((z.jet x).dstate SM γ)).1 = (toP ((z0.jet x).dstate SM γ)).1 := by
    intro γ
    rw [← pd_stateF SM z x γ, ← pd_stateF SM z0 x γ]
    exact hm γ
  have hfj := GenPhysIdClosed.firstJet_eq SM hSx
  have hdg : z.dg x = z0.dg x := congrArg FirstJet.dg hfj
  have hde : z.de x = z0.de x := congrArg FirstJet.de hfj
  have hAF : (z.jet x).AF = (z0.jet x).AF := congrArg FirstJet.AF hfj
  have he : z.e x = z0.e x := by
    funext A μ
    rw [← Tuple.jet_AF_fr, ← Tuple.jet_AF_fr, hAF]
  funext γ β μ ν
  set w : Fin 4 → ℝ := fun β => z.ddg x γ β μ ν - z0.ddg x γ β μ ν with hw
  have hcomp : ∀ A, ∑ β, z.e x A β * w β = 0 := by
    intro A
    have key : ∀ (B : Fin 4), (∑ β, ((z.jet x).FJ.de γ B β * (z.jet x).FJ.dg β μ ν +
        (z.jet x).AF.fr B β * (z.jet x).FJ.ddg γ β μ ν)) =
        ∑ β, ((z0.jet x).FJ.de γ B β * (z0.jet x).FJ.dg β μ ν +
        (z0.jet x).AF.fr B β * (z0.jet x).FJ.ddg γ β μ ν) → ∑ β, z.e x B β * w β = 0 := by
      intro B hB
      simp only [show (z.jet x).FJ.de = z.de x from rfl, show (z0.jet x).FJ.de = z0.de x from rfl,
        show (z.jet x).FJ.dg = z.dg x from rfl, show (z0.jet x).FJ.dg = z0.dg x from rfl,
        show (z.jet x).FJ.ddg = z.ddg x from rfl, show (z0.jet x).FJ.ddg = z0.ddg x from rfl,
        Tuple.jet_AF_fr, hde, hdg, ← he] at hB
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hB
      rw [← hB]
      exact Finset.sum_congr rfl fun β _ => by rw [hw]; ring
    induction A using Fin.cases with
    | zero =>
      refine key 0 ?_
      have := congrArg (fun U => U.2.1 μ ν) (hd1 γ)
      simpa [ActualJet.dstate, AdaptedFrame.dpJ, toP] using this
    | succ a =>
      refine key a.succ ?_
      have := congrArg (fun U => U.2.2 a μ ν) (hd1 γ)
      simpa [ActualJet.dstate, AdaptedFrame.dqJ, toP] using this
  have hinv := ActualJetRecon.inv_vec (z.jet x).FJ w β
  have h0 : w β = 0 := by
    rw [hinv]
    refine Finset.sum_eq_zero fun A _ => ?_
    have : ∑ β', (z.jet x).FJ.e A β' • w β' = 0 := by
      simp only [smul_eq_mul]
      exact hcomp A
    rw [this, smul_zero]
  rw [hw] at h0
  linarith

end Slice

/-! ### Initial values of the coupled defects on the data slice -/

section Initial

variable {W : ST 3 → StateP m V S S'} {z z₀ : Tuple m V S S'} {a b : ℝ}

/-- The harmonic defect and its time derivative vanish on the data slice. -/
theorem cF_slice (h : GenCplRows.CplSol SM W z a b) (ha : a < 0) (hb : 0 < b)
    (hS0 : ∀ y : Fin 3 → ℝ, stateF SM z (Fin.cons 0 y) = stateF SM z₀ (Fin.cons 0 y))
    (hpd0 : ∀ (y : Fin 3 → ℝ) μ, pd W μ (Fin.cons 0 y) = pd (stateF SM z₀) μ (Fin.cons 0 y))
    (hC₀ : GenPhysIdClosed.SliceConstrained SM z₀) :
    (∀ y : Fin 3 → ℝ, GenHarmonic.cF z (Fin.cons 0 y) = 0) ∧
      ∀ y : Fin 3 → ℝ, pd (GenHarmonic.cF z) 0 (Fin.cons 0 y) = 0 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hC : ∀ y : Fin 3 → ℝ, CF z (Fin.cons 0 y) = 0 := fun y => by
    rw [GenPhysIdClosed.CF_eq_of_state SM (hS0 y)]; exact (hC₀ y).2.2.1
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpdB := GenHiggsDefect.pd_block_eq' hO hW1 hUd (GenSpinorDefect.prB m V S S') h.bos
  have hdC : ∀ y : Fin 3 → ℝ, pd (CF z) 0 (Fin.cons 0 y) = 0 := by
    intro y
    have hy : (Fin.cons 0 y : ST 3) ∈ openSlab a b := ⟨ha, hb⟩
    have hm : ∀ γ, (pd (stateF SM z) γ (Fin.cons 0 y)).1 =
        (pd (stateF SM z₀) γ (Fin.cons 0 y)).1 := fun γ => by
      rw [← hpd0 y γ]
      exact ((GenSpinorDefect.prB_eq_iff.1 (hpdB _ hy γ)).1).symm
    have hfj := GenPhysIdClosed.firstJet_eq SM (hS0 y)
    have hgi : z.gi (Fin.cons 0 y) = z₀.gi (Fin.cons 0 y) := congrArg FirstJet.gi hfj
    have hdg : z.dg (Fin.cons 0 y) = z₀.dg (Fin.cons 0 y) := congrArg FirstJet.dg hfj
    rw [pd_CF z _ 0, hgi, hdg, ddg_eq_of_metric SM (hS0 y) hm, ← pd_CF z₀ _ 0]
    exact (hC₀ y).2.2.2
  refine ⟨fun y => GenHarmonic.cF_eq_zero_of_CF z (hC y), fun y => ?_⟩
  have hCy := hC y
  have hdCy := hdC y
  refine pd_eq_of_line ((GenHarmonic.contDiff_cF z).differentiable (by simp) (Fin.cons 0 y)) ?_
  refine hasDerivAt_pi.2 fun c => ?_
  have hCl := hasDerivAt_line0 ((contDiff_CF z).differentiable (by simp) (Fin.cons 0 y)) 0
  have h' := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) =>
    (z.line_g (Fin.cons 0 y) 0 c k).fun_mul (hasDerivAt_pi.1 hCl k)
  simp only [zero_smul, add_zero, hCy, hdCy, Pi.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero] at h'
  rw [Pi.zero_apply]
  exact h'

theorem sD_slice (hc0 : ∀ y : Fin 3 → ℝ, GenHarmonic.cF z (Fin.cons 0 y) = 0)
    (hct : ∀ y : Fin 3 → ℝ, pd (GenHarmonic.cF z) 0 (Fin.cons 0 y) = 0) (y : Fin 3 → ℝ) :
    GenCplCov.sD z (Fin.cons 0 y) = 0 := by
  have hpd : ∀ μ, pd (GenHarmonic.cF z) μ (Fin.cons 0 y) = 0 := by
    intro μ
    induction μ using Fin.cases with
    | zero => exact hct y
    | succ j => exact GenPhysIdClosed.zero_on_slice_pd (GenHarmonic.contDiff_cF z) hc0 rfl j
  funext μ ν
  rw [GenCplBox.sD_eq, hpd μ, hpd ν, hc0 y]
  simp

theorem kinT_zero (D : DiracData (MatLie m) V S) (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (ψ : S) (ψb : S')
    (A B : Fin 4) : GenDStress.kinT D P ψ 0 ψb 0 A B = 0 := by
  unfold GenDStress.kinT
  simp

theorem ricTerm_zero {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (g gi : Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame) (ψ : S₀) (a : Fin 4) :
    GenCplRows.ricTerm D g gi AF (fun _ _ => 0) ψ a = 0 := by
  unfold GenCplRows.ricTerm frT2
  simp

theorem XrowFX_zero {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → MatLie m) (H : V) (a : Fin 4) :
    GenCplRows.XrowFX D g gi dg AF de A H 0 a = 0 := by
  unfold GenCplRows.XrowFX
  simp

/-- The tangential and normal-prolongation spinor defects vanish on the data slice. -/
theorem wF_slice (hW : ContDiff ℝ ∞ W) (h : GenCplRows.CplSol SM W z a b) (ha : a < 0)
    (hb : 0 < b) (hslice : ∀ y : Fin 3 → ℝ, W (Fin.cons 0 y) = stateF SM z (Fin.cons 0 y))
    (hc0 : ∀ y : Fin 3 → ℝ, GenHarmonic.cF z (Fin.cons 0 y) = 0)
    (hct : ∀ y : Fin 3 → ℝ, pd (GenHarmonic.cF z) 0 (Fin.cons 0 y) = 0) (y : Fin 3 → ℝ) :
    GenCplBd.wF SM W z (Fin.cons 0 y) = 0 := by
  have hy : (Fin.cons 0 y : ST 3) ∈ openSlab a b := ⟨ha, hb⟩
  have hYt0 : ∀ y' : Fin 3 → ℝ, GenCplX.Yt SM W z (Fin.cons 0 y') = 0 := fun y' => by
    simp only [GenCplX.Yt, hslice y', sub_self]
  have hYbt0 : ∀ y' : Fin 3 → ℝ, GenCplX.Ybt SM W z (Fin.cons 0 y') = 0 := fun y' => by
    simp only [GenCplX.Ybt, hslice y', sub_self]
  have hsD := sD_slice hc0 hct y
  have hsD' : (fun μ ν => symDefect (z.g (Fin.cons 0 y)) (z.gi (Fin.cons 0 y))
      (z.dg (Fin.cons 0 y)) (z.ddg (Fin.cons 0 y)) μ ν) = fun _ _ => 0 := hsD
  -- all first derivatives of the tangential defects vanish on the slice
  have hpdY : ∀ μ, pd (GenCplX.Yt SM W z) μ (Fin.cons 0 y) = 0 := by
    have hsp : ∀ j : Fin 3, pd (GenCplX.Yt SM W z) j.succ (Fin.cons 0 y) = 0 := fun j =>
      GenPhysIdClosed.zero_on_slice_pd (GenCplP.contDiff_Yt SM W z hW) hYt0 rfl j
    intro μ
    induction μ using Fin.cases with
    | zero =>
      funext a'
      have hr := GenCplX.x_row_cpl h hy a'
      have hYf : GenCplX.Yf SM W z (Fin.cons 0 y) = 0 := by
        simp only [GenCplX.Yf, hYt0 y]
        exact (GenCplP.oneFormL SM.D).map_zero
      rw [hYf, hsD', XrowFX_zero, ricTerm_zero] at hr
      simp only [hsp, Pi.zero_apply] at hr
      simpa [diracP] using hr
    | succ j => exact hsp j
  have hpdYb : ∀ μ, pd (GenCplX.Ybt SM W z) μ (Fin.cons 0 y) = 0 := by
    have hsp : ∀ j : Fin 3, pd (GenCplX.Ybt SM W z) j.succ (Fin.cons 0 y) = 0 := fun j =>
      GenPhysIdClosed.zero_on_slice_pd (GenCplP.contDiff_Ybt SM W z hW) hYbt0 rfl j
    intro μ
    induction μ using Fin.cases with
    | zero =>
      funext a'
      have hr := GenCplX.x_row_cpl_b h hy a'
      have hYf : GenCplX.Ybf SM W z (Fin.cons 0 y) = 0 := by
        simp only [GenCplX.Ybf, hYbt0 y]
        exact (GenCplP.oneFormL SM.Db).map_zero
      rw [hYf, hsD', XrowFX_zero, ricTerm_zero] at hr
      simp only [hsp, Pi.zero_apply] at hr
      simpa [diracP] using hr
    | succ j => exact hsp j
  -- the one-form fields and their frame derivatives vanish on the slice
  have hYfz : GenCplX.Yf SM W z (Fin.cons 0 y) = 0 := by
    simp only [GenCplX.Yf, hYt0 y]
    exact (GenCplP.oneFormL SM.D).map_zero
  have hYbfz : GenCplX.Ybf SM W z (Fin.cons 0 y) = 0 := by
    simp only [GenCplX.Ybf, hYbt0 y]
    exact (GenCplP.oneFormL SM.Db).map_zero
  have hfdY : ∀ B, GenCplCov.fd z (GenCplX.Yf SM W z) B (Fin.cons 0 y) = 0 := by
    intro B
    have e : GenCplX.Yf SM W z = fun y' => GenCplP.oneFormL SM.D (GenCplX.Yt SM W z y') := rfl
    have hd := (GenCplP.contDiff_Yt SM W z hW).differentiable (by simp) (Fin.cons 0 y)
    rw [e, GenCplN.fd_lin z (GenCplP.oneFormL SM.D) hd B, GenCplN.fd_eq_sum]
    simp [hpdY]
  have hfdYb : ∀ B, GenCplCov.fd z (GenCplX.Ybf SM W z) B (Fin.cons 0 y) = 0 := by
    intro B
    have e : GenCplX.Ybf SM W z = fun y' => GenCplP.oneFormL SM.Db (GenCplX.Ybt SM W z y') := rfl
    have hd := (GenCplP.contDiff_Ybt SM W z hW).differentiable (by simp) (Fin.cons 0 y)
    rw [e, GenCplN.fd_lin z (GenCplP.oneFormL SM.Db) hd B, GenCplN.fd_eq_sum]
    simp [hpdYb]
  have hP : GenCplP.Pf SM W z (Fin.cons 0 y) = 0 := by
    show GenCplCov.QF z SM.D (GenCplX.Yf SM W z) (Fin.cons 0 y) 0 -
      GenCplCov.RF z SM.D z.ψ (GenCplX.Yf SM W z) (Fin.cons 0 y) 0 = 0
    rw [GenCplCov.QF_apply]
    simp only [GenCplCov.covF_apply, hfdY, hYfz, GenCplCov.RF, hsD, Pi.zero_apply, map_zero,
      zero_add, Finset.smul_sum, smul_zero, Finset.sum_const_zero, sub_zero]
    have := ricTerm_zero SM.D (z.g (Fin.cons 0 y)) (z.gi (Fin.cons 0 y))
      (frameU (z.gi (Fin.cons 0 y))) (z.ψ (Fin.cons 0 y)) 0
    rw [show (0 : Fin 4 → Fin 4 → ℝ) = fun _ _ => 0 from rfl, this]
    simp
  have hPb : GenCplP.Pbf SM W z (Fin.cons 0 y) = 0 := by
    show GenCplCov.QF z SM.Db (GenCplX.Ybf SM W z) (Fin.cons 0 y) 0 -
      GenCplCov.RF z SM.Db z.ψb (GenCplX.Ybf SM W z) (Fin.cons 0 y) 0 = 0
    rw [GenCplCov.QF_apply]
    simp only [GenCplCov.covF_apply, hfdYb, hYbfz, GenCplCov.RF, hsD, Pi.zero_apply, map_zero,
      zero_add, Finset.smul_sum, smul_zero, Finset.sum_const_zero, sub_zero]
    have := ricTerm_zero SM.Db (z.g (Fin.cons 0 y)) (z.gi (Fin.cons 0 y))
      (frameU (z.gi (Fin.cons 0 y))) (z.ψb (Fin.cons 0 y)) 0
    rw [show (0 : Fin 4 → Fin 4 → ℝ) = fun _ _ => 0 from rfl, this]
    simp
  simp only [GenCplBd.wF, hYt0 y, hYbt0 y, hP, hPb]
  rfl

end Initial

/-! ### The core identification -/

section Core

variable {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **Physical consequences of the vanishing of the coupled defects**: at a point of a coupled
solution where the harmonic defect and its derivatives and the spinor defects vanish, all
residuals and the harmonic defect of `z` vanish. -/
theorem physical_of_defects (hC : GenDStress.CoupledDirac SM) {W : ST 3 → StateP m V S S'}
    {z : Tuple m V S S'} {a b : ℝ} (h : GenCplRows.CplSol SM W z a b) {x : ST 3}
    (hx : x ∈ openSlab a b) (hA : (bosF SM z x).2.1 = 0) (hc : GenHarmonic.cF z x = 0)
    (hdc : ∀ μ, pd (GenHarmonic.cF z) μ x = 0) (hY : GenCplX.Yt SM W z x = 0)
    (hYb : GenCplX.Ybt SM W z x = 0) :
    bosF SM z x = 0 ∧ dirF SM z x = 0 ∧ CF z x = 0 := by
  have hYf : GenCplX.Yf SM W z x = 0 := by
    simp only [GenCplX.Yf, hY]; exact (GenCplP.oneFormL SM.D).map_zero
  have hYbf : GenCplX.Ybf SM W z x = 0 := by
    simp only [GenCplX.Ybf, hYb]; exact (GenCplP.oneFormL SM.Db).map_zero
  have hsD : GenCplCov.sD z x = 0 := by
    funext μ ν
    rw [GenCplBox.sD_eq, hdc μ, hdc ν, hc]
    simp
  have hSD : GenCplEin.stressDiff SM W z x = fun _ _ => 0 := by
    funext μ ν
    rw [GenCplSD.stressDiff_eq hC h hx]
    unfold GenCplSD.ΔSf
    simp [hYf, hYbf, kinT_zero]
  have hEin : (bosF SM z x).1 = 0 := by
    funext μ ν
    rw [GenCplEin.etr_eq h hx, hSD]
    have : symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν = GenCplCov.sD z x μ ν := rfl
    rw [this, hsD]
    simp [traceRev, trG]
  have hmat := GenCplMat.matterAt_cpl h hx
  refine ⟨Prod.ext hEin (Prod.ext hA hmat.2.1), hmat.1, ?_⟩
  funext k
  rw [GenHarmonic.CF_eq_of_cF z x k, hc]
  simp

set_option maxHeartbeats 4000000 in -- long assembly proof
/-- **The core identification for back-reacting spinors**: a smooth two-sided solution `W` of the
realized shift-transported system with constrained data, symmetric and in the chart margin on
`(-ε, ε) × 𝕋³`, has a physical head tuple `z` whose actual-jet state is `W` near `t = 0`, and the
Kato solution of the original realized system is the actual-jet state of `z` on `[0, t₁] × 𝕋³`. -/
theorem core_identification_cpl (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
    GenPhysIdFinal.slice_pd_eq SM hS (isOpen_openSlab _ _) hW1 hC₀ hslice0 (hy0 y)
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
  have hdiv := GenCplMat.divT_zero_cpl hN hT hS hCpl' (show -ε'' < 0 by linarith) ht₂0
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

end Core


/-! ### The lemma -/

section Main

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
theorem generated_physical_identification_coupled (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
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
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K₀ K hK hKc δ hδ hKδ => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  obtain ⟨AM, FM, hAM, hsymM, hFM, hAMK, hFMK, hτA, hτF⟩ :=
    GenCplKato.modified_kato_realization_cpl hS hU hC κ hκ K hK hKc
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
  exact core_identification_cpl hS hU hC hN hT hκ hKc hA hsym hF hAK hFK hAM hFM hAMK hFMK hdat₀ hC₀
    hMP hMs hε (min_le_right τ TM) hKWε hsymε hT0 hUP

end Main

end RenewalGeometry.GenCplId
