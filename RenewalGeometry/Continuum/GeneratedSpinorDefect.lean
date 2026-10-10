/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHiggsDefect

/-!
# The spinor sector of the defining-jet identities

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`).  Let `W` solve the shift-transported system with the head fields of a
smooth tuple `z`, and suppose its bosonic auxiliary variables are already the actual ones.

* **`dirac_of_rows`** — the Dirac head rows of `W` force the Dirac equations of `z`:
  `r_D(z) = r̄_D(z) = 0` (the `Ψ`-row of the actual-jet state carries the forcing `-Nc₀r_D`,
  `c₀² = 1`);
* `zeroSp` — the tuple with vanishing spinors; for theory data with decoupled spinors
  (`AJKatoMod.Decoupled`) its actual-jet state solves the symmetric system wherever `W` does
  (**`symEqAt_zeroSp`**): the bosonic rows coincide with those of `W` and the spinor rows vanish.
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenSpinorDefect

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint GenGauss GenHiggsDefect

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'}

/-! ### Block projections of the spinor variables -/

section Blocks

variable (m V S S') in
def prψ : StateP m V S S' →L[ℝ] S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.2.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (m V S S') in
def prψb : StateP m V S S' →L[ℝ] S' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.2.2.2.1, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }

theorem prψ_apply (v : StateP m V S S') : prψ m V S S' v = v.2.2.2.2.2.2.2.1 := rfl
theorem prψb_apply (v : StateP m V S S') : prψb m V S S' v = v.2.2.2.2.2.2.2.2.2.1 := rfl

end Blocks

/-! ### The Dirac equations from the Dirac head rows -/

section Dirac

/-- The explicit Dirac head-row forcing as a function of the metric block, the potential, the Higgs
field and the spinor. -/
def Gψ {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) (v1 : MetP)
    (A : Fin 3 → MatLie m) (H : V) (ψ : S₀) : S₀ :=
  (frameU (ginvOf v1.1)).N • psiF D v1.1 (ginvOf v1.1)
    (fun γ μ ν => ∑ X, cof v1.1 lorentzSign (frameU (ginvOf v1.1)).fr X γ *
      gradOfpq (v1.2.1 μ ν) (fun a => v1.2.2 a μ ν) X)
    (frameU (ginvOf v1.1))
    (frameJet (ginvOf v1.1) (fun γ l σ => dginv (ginvOf v1.1) (fun γ μ ν => ∑ X,
      cof v1.1 lorentzSign (frameU (ginvOf v1.1)).fr X γ *
        gradOfpq (v1.2.1 μ ν) (fun a => v1.2.2 a μ ν) X) γ l σ))
    (Fin.cases 0 A) H ψ

theorem Fsysψ_eq (v : StateP m V S S') :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.1 =
      Gψ SM.D v.1 v.2.1 v.2.2.2.2.1 v.2.2.2.2.2.2.2.1 := rfl

theorem Fsysψb_eq (v : StateP m V S S') :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.2.1 =
      Gψ SM.Db v.1 v.2.1 v.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.1 := rfl

/-- The Dirac head-row forcing depends only on the metric block, the potential, the Higgs field and
the spinor. -/
theorem Fsysψ_congr {v w : StateP m V S S'} (h1 : v.1 = w.1) (hA : v.2.1 = w.2.1)
    (hH : v.2.2.2.2.1 = w.2.2.2.2.1) (hψ : v.2.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.2.1) :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.1 = (toP (Fsys SM (ofP w))).2.2.2.2.2.2.2.1 := by
  rw [Fsysψ_eq, Fsysψ_eq, h1, hA, hH, hψ]

theorem Fsysψb_congr {v w : StateP m V S S'} (h1 : v.1 = w.1) (hA : v.2.1 = w.2.1)
    (hH : v.2.2.2.2.1 = w.2.2.2.2.1) (hψ : v.2.2.2.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.2.2.2.1) :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.2.1 = (toP (Fsys SM (ofP w))).2.2.2.2.2.2.2.2.2.1 := by
  rw [Fsysψb_eq, Fsysψb_eq, h1, hA, hH, hψ]

/-- **The Dirac equations of the tuple from the Dirac head rows of `W`.** -/
theorem dirac_of_rows {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'} {a b : ℝ}
    (hW : MSol SM W z a b) (hmet : ∀ x ∈ openSlab a b, (W x).1 = (stateF SM z x).1) :
    ∀ x ∈ openSlab a b, dirF SM z x = 0 := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpdψ := pd_block_eq' hO hW1 hUd (prψ m V S S')
    (fun y hy => by rw [prψ_apply, prψ_apply, hW.ψ y hy]; rfl)
  have hpdψb := pd_block_eq' hO hW1 hUd (prψb m V S S')
    (fun y hy => by rw [prψb_apply, prψb_apply, hW.ψb y hy]; rfl)
  intro x hx
  have hgU : frameU (ginvOf (stateF SM z x).1.1) = frameU (z.gi x) := by
    rw [GenDefJet.stateF_fst_fst]; rfl
  have hgW : frameU (ginvOf (W x).1.1) = frameU (z.gi x) := frameU_W hW hx
  have hU := writer_pde_err SM z x
  have hWr := hW.row x hx
  have hA : (W x).2.1 = (stateF SM z x).2.1 := funext fun i => hW.A x hx i
  have hN := (frameU (z.gi x)).N_pos
  -- the `Ψ` block
  have hψ : (dirF SM z x).1 = 0 := by
    have h1 := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.2.2.1) hU
    have h2 := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.2.2.1) hWr
    simp only [Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum] at h1 h2
    have hF : (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.2.1 =
        (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.2.2.1 :=
      Fsysψ_congr (hmet x hx) hA (hW.H x hx) (hW.ψ x hx)
    have hP : ∀ j : Fin 3, (AJKatoMod.princPM SM (W x) j (pd W j.succ x)).2.2.2.2.2.2.2.1 =
        (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).2.2.2.2.2.2.2.1 := by
      intro j
      show diracP (frameU (ginvOf (W x).1.1)) SM.D.Fr j (pd W j.succ x).2.2.2.2.2.2.2.1 =
        diracP (frameU (ginvOf (stateF SM z x).1.1)) SM.D.Fr j
          (pd (stateF SM z) j.succ x).2.2.2.2.2.2.2.1
      rw [hgW, hgU]
      congr 1
      exact hpdψ x hx j.succ
    have hP0 : (pd W 0 x).2.2.2.2.2.2.2.1 = (pd (stateF SM z) 0 x).2.2.2.2.2.2.2.1 := hpdψ x hx 0
    have hFM : (toP (AJKatoMod.FsysM SM (ofP (W x)))).2.2.2.2.2.2.2.1 =
        (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.2.1 := rfl
    rw [hFM, hF, hP0] at h2
    simp only [hP] at h2
    rw [h2, errF_psi] at h1
    have h3 : (frameU (ginvOf (ofP (stateF SM z x)).g)).N • (SM.D.Fr.c 0 • (dirF SM z x).1) = 0 := by
      have := congrArg (fun v => v - (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.2.2.1) h1
      simp only [add_sub_cancel_left, sub_self] at this
      exact neg_eq_zero.1 this.symm
    have hN' : (frameU (ginvOf (ofP (stateF SM z x)).g)).N ≠ 0 :=
      (frameU (ginvOf (ofP (stateF SM z x)).g)).N_pos.ne'
    have h4 := (smul_eq_zero.1 h3).resolve_left hN'
    have h5 : SM.D.Fr.c 0 • (SM.D.Fr.c 0 • (dirF SM z x).1) = (dirF SM z x).1 := by
      rw [← mul_smul, c0_mul_c0, one_smul]
    rw [← h5, h4, smul_zero]
  -- the `Ψ̄` block
  have hψb : (dirF SM z x).2 = 0 := by
    have h1 := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.2.2.2.2.1) hU
    have h2 := congrArg (fun v : StateP m V S S' => v.2.2.2.2.2.2.2.2.2.1) hWr
    simp only [Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum] at h1 h2
    have hF : (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.2.2.2.1 =
        (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.2.2.2.2.1 :=
      Fsysψb_congr (hmet x hx) hA (hW.H x hx) (hW.ψb x hx)
    have hP : ∀ j : Fin 3, (AJKatoMod.princPM SM (W x) j (pd W j.succ x)).2.2.2.2.2.2.2.2.2.1 =
        (princL SM (stateF SM z x) j (pd (stateF SM z) j.succ x)).2.2.2.2.2.2.2.2.2.1 := by
      intro j
      show diracP (frameU (ginvOf (W x).1.1)) SM.Db.Fr j (pd W j.succ x).2.2.2.2.2.2.2.2.2.1 =
        diracP (frameU (ginvOf (stateF SM z x).1.1)) SM.Db.Fr j
          (pd (stateF SM z) j.succ x).2.2.2.2.2.2.2.2.2.1
      rw [hgW, hgU]
      congr 1
      exact hpdψb x hx j.succ
    have hP0 : (pd W 0 x).2.2.2.2.2.2.2.2.2.1 = (pd (stateF SM z) 0 x).2.2.2.2.2.2.2.2.2.1 :=
      hpdψb x hx 0
    have hFM : (toP (AJKatoMod.FsysM SM (ofP (W x)))).2.2.2.2.2.2.2.2.2.1 =
        (toP (Fsys SM (ofP (W x)))).2.2.2.2.2.2.2.2.2.1 := rfl
    rw [hFM, hF, hP0] at h2
    simp only [hP] at h2
    rw [h2, errF_psib] at h1
    have h3 : (frameU (ginvOf (ofP (stateF SM z x)).g)).N • (SM.Db.Fr.c 0 • (dirF SM z x).2) =
        0 := by
      have := congrArg (fun v => v - (toP (Fsys SM (ofP (stateF SM z x)))).2.2.2.2.2.2.2.2.2.1) h1
      simp only [add_sub_cancel_left, sub_self] at this
      exact neg_eq_zero.1 this.symm
    have hN' : (frameU (ginvOf (ofP (stateF SM z x)).g)).N ≠ 0 :=
      (frameU (ginvOf (ofP (stateF SM z x)).g)).N_pos.ne'
    have h4 := (smul_eq_zero.1 h3).resolve_left hN'
    have h5 : SM.Db.Fr.c 0 • (SM.Db.Fr.c 0 • (dirF SM z x).2) = (dirF SM z x).2 := by
      rw [← mul_smul, c0_mul_c0, one_smul]
    rw [← h5, h4, smul_zero]
  exact Prod.ext hψ hψb

end Dirac

/-! ### The tuple with vanishing spinors -/

section ZeroSp

/-- The tuple with the metric, potential and Higgs field of `z` and vanishing spinors. -/
def zeroSp (z : Tuple m V S S') : Tuple m V S S' :=
  { z with
    ψ := (fun _ => 0)
    ψb := (fun _ => 0)
    ψ_smooth := contDiff_const
    ψb_smooth := contDiff_const
    ψ_per := (fun _ _ => rfl)
    ψb_per := (fun _ _ => rfl) }

theorem pd_zero_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : Fin 4)
    (x : ST 3) : pd (fun _ : ST 3 => (0 : E)) γ x = 0 := by
  simp [SobolevOpen.pd]

theorem Xs_zero_spinor {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (A : Fin 4) :
    J.Xs D 0 (fun _ => 0) A = 0 := by
  rw [ActualJetBridge.Xs_eq]
  simp

variable (m V S S') in
/-- The bosonic blocks `(g, p, q, A, E, B, H, Π, Q)` of a state. -/
abbrev BosS := MetP × (Fin 3 → MatLie m) × (Fin 3 → MatLie m) × (Fin 3 → MatLie m) × V × V ×
  (Fin 3 → V)

variable (m V S S') in
/-- The projection onto the bosonic blocks. -/
def prB : StateP m V S S' →L[ℝ] BosS m V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1,
        v.2.2.2.2.2.2.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem prB_apply (v : StateP m V S S') : prB m V S S' v =
    (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1) := rfl

theorem prB_eq_iff {v w : StateP m V S S'} : prB m V S S' v = prB m V S S' w ↔
    v.1 = w.1 ∧ v.2.1 = w.2.1 ∧ v.2.2.1 = w.2.2.1 ∧ v.2.2.2.1 = w.2.2.2.1 ∧
      v.2.2.2.2.1 = w.2.2.2.2.1 ∧ v.2.2.2.2.2.1 = w.2.2.2.2.2.1 ∧
        v.2.2.2.2.2.2.1 = w.2.2.2.2.2.2.1 := by
  simp only [prB_apply, Prod.mk.injEq]

variable (m V S S') in
/-- The spinor blocks `(Ψ, X, Ψ̄, X̄)` of a state. -/
def prS : StateP m V S S' →L[ℝ] S × (Fin 3 → S) × S' × (Fin 3 → S') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem prS_apply (v : StateP m V S S') : prS m V S S' v = v.2.2.2.2.2.2.2 := rfl

theorem eq_of_prB_prS {v w : StateP m V S S'} (hB : prB m V S S' v = prB m V S S' w)
    (hS : prS m V S S' v = prS m V S S' w) : v = w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := prB_eq_iff.1 hB
  rw [prS_apply, prS_apply] at hS
  obtain ⟨v1, vA, vE, vB, vH, vP, vQ, vs⟩ := v
  obtain ⟨w1, wA, wE, wB, wH, wP, wQ, ws⟩ := w
  simp only at h1 h2 h3 h4 h5 h6 h7 hS
  subst h1 h2 h3 h4 h5 h6 h7 hS
  rfl

theorem prB_stateF_zeroSp (z : Tuple m V S S') (x : ST 3) :
    prB m V S S' (stateF SM (zeroSp z) x) = prB m V S S' (stateF SM z x) := rfl

theorem prS_stateF_zeroSp (z : Tuple m V S S') (x : ST 3) :
    prS m V S S' (stateF SM (zeroSp z) x) = 0 := by
  have h1 : (fun γ => pd (zeroSp z).ψ γ x) = fun _ => (0 : S) := funext fun γ => pd_zero_fun γ x
  have h2 : (fun γ => pd (zeroSp z).ψb γ x) = fun _ => (0 : S') :=
    funext fun γ => pd_zero_fun γ x
  show (((zeroSp z).jet x).ψ, (fun (a : Fin 3) => ((zeroSp z).jet x).Xs SM.D ((zeroSp z).jet x).ψ
      ((zeroSp z).jet x).cψ a.succ), ((zeroSp z).jet x).ψb,
      (fun (a : Fin 3) => ((zeroSp z).jet x).Xs SM.Db ((zeroSp z).jet x).ψb ((zeroSp z).jet x).cψb a.succ)) = 0
  have e1 : ((zeroSp z).jet x).ψ = 0 := rfl
  have e2 : ((zeroSp z).jet x).ψb = 0 := rfl
  have e3 : ((zeroSp z).jet x).cψ = fun _ => 0 := h1
  have e4 : ((zeroSp z).jet x).cψb = fun _ => 0 := h2
  rw [e1, e2, e3, e4]
  simp only [Xs_zero_spinor]
  rfl

theorem CF_zeroSp (z : Tuple m V S S') : CF (zeroSp z) = CF z := rfl

theorem dirF_zeroSp (z : Tuple m V S S') (x : ST 3) : dirF SM (zeroSp z) x = 0 := by
  have h1 : (fun γ => pd (zeroSp z).ψ γ x) = fun _ => (0 : S) := funext fun γ => pd_zero_fun γ x
  have h2 : (fun γ => pd (zeroSp z).ψb γ x) = fun _ => (0 : S') :=
    funext fun γ => pd_zero_fun γ x
  refine Prod.ext ?_ ?_
  · show ((zeroSp z).jet x).rD SM.D ((zeroSp z).ψ x) (fun γ => pd (zeroSp z).ψ γ x) = 0
    rw [rD_eq', h1, show (zeroSp z).ψ x = 0 from rfl]
    simp only [Xs_zero_spinor]
    simp
  · show ((zeroSp z).jet x).rD SM.Db ((zeroSp z).ψb x) (fun γ => pd (zeroSp z).ψb γ x) = 0
    rw [rD_eq', h2, show (zeroSp z).ψb x = 0 from rfl]
    simp only [Xs_zero_spinor]
    simp

end ZeroSp


/-! ### Decoupled spinors: the bosonic rows do not see the spinor variables -/

section Bosonic

variable (SM) in
/-- With decoupled spinors the bosonic residuals do not see the spinors. -/
theorem bosF_zeroSp (hD : AJKatoMod.Decoupled SM) (z : Tuple m V S S') (x : ST 3) :
    bosF SM (zeroSp z) x = bosF SM z x := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (((zeroSp z).jet x).res SM).Etr = ((z.jet x).res SM).Etr
    simp only [ActualJet.res, ActualJet.Tact, hD.coord_eq_zero, add_zero]
    rfl
  · show (((zeroSp z).jet x).res SM).rA = ((z.jet x).res SM).rA
    simp only [ActualJet.res]
    rw [hD.J_spin _ _ _ _ _ _ ((z.jet x).ψ) ((z.jet x).ψb)]
    rfl
  · show (((zeroSp z).jet x).res SM).rH = ((z.jet x).res SM).rH
    simp only [ActualJet.res]
    rw [hD.SH_spin _ _ _ _ _ ((z.jet x).ψ) ((z.jet x).ψb)]
    rfl

variable (SM) in
/-- The bosonic blocks of the lower-order terms depend only on the bosonic first jets (decoupled
spinors). -/
theorem lowerOf_bos_congr (hD : AJKatoMod.Decoupled SM) (fj fj' : FirstJet (MatLie m) V S S')
    (hg : fj.g = fj'.g) (hgi : fj.gi = fj'.gi) (hdg : fj.dg = fj'.dg) (hAF : fj.AF = fj'.AF)
    (hde : fj.de = fj'.de) (hA : fj.A = fj'.A) (hF : fj.F = fj'.F) (hH : fj.H = fj'.H)
    (hDH : fj.DH = fj'.DH) :
    prB m V S S' (toP (lowerOf SM fj)) = prB m V S S' (toP (lowerOf SM fj')) := by
  obtain ⟨g, gi, dg, AF, de, A, F, H, DH, ψ, X, ψb, Xb⟩ := fj
  obtain ⟨g', gi', dg', AF', de', A', F', H', DH', ψ', X', ψb', Xb'⟩ := fj'
  simp only at hg hgi hdg hAF hde hA hF hH hDH
  subst hg hgi hdg hAF hde hA hF hH hDH
  have hst : ∀ fj : FirstJet (MatLie m) V S S', stressF SM fj = fun μ ν =>
      ymStressB SM.ipG fj.g fj.gi fj.F μ ν +
        higgsStressB SM.ipV SM.lamH SM.vH fj.g fj.gi fj.H fj.DH μ ν := fun fj =>
    funext fun μ => funext fun ν => by simp only [stressF, hD.coord_eq_zero, add_zero]
  simp only [prB_apply, toP, lowerOf, hst,
    hD.J_spin g gi H DH ψ ψb ψ' ψb', hD.SH_spin g gi H ψ ψb ψ' ψb']

variable (SM) in
/-- **The bosonic blocks of the forcing depend only on the bosonic blocks of the state** (decoupled
spinors). -/
theorem Fsys_bos_congr (hD : AJKatoMod.Decoupled SM) {v w : StateP m V S S'}
    (h : prB m V S S' v = prB m V S S' w) :
    prB m V S S' (toP (Fsys SM (ofP v))) = prB m V S S' (toP (Fsys SM (ofP w))) := by
  obtain ⟨h1, hA, hE, hB, hH, hP, hQ⟩ := prB_eq_iff.1 h
  unfold Fsys
  apply lowerOf_bos_congr SM hD <;> simp only [recon, ofP, h1, hA, hE, hB, hH, hP, hQ]

variable (SM) in
/-- The bosonic blocks of the principal part depend only on the metric and the bosonic blocks of
the increment. -/
theorem princL_bos_congr {v v' w w' : StateP m V S S'} (hv : v.1.1 = v'.1.1) (j : Fin 3)
    (hw : prB m V S S' w = prB m V S S' w') :
    prB m V S S' (princL SM v j w) = prB m V S S' (princL SM v' j w') := by
  obtain ⟨h1, hA, hE, hB, hH, hP, hQ⟩ := prB_eq_iff.1 hw
  show prB m V S S' (toP (ActualJetSystem.princ (frameU (ginvOf v.1.1)) SM.D.Fr SM.Db.Fr j (ofP w))) =
    prB m V S S' (toP (ActualJetSystem.princ (frameU (ginvOf v'.1.1)) SM.D.Fr SM.Db.Fr j (ofP w')))
  simp only [prB_apply, toP, ActualJetSystem.princ, ofP, hv, h1, hA, hE, hB, hH, hP, hQ]

variable (SM) in
/-- The spinor blocks of the principal part vanish on increments with vanishing spinor blocks. -/
theorem prS_princL_zero (v : StateP m V S S') (j : Fin 3) {w : StateP m V S S'}
    (hw : prS m V S S' w = 0) : prS m V S S' (princL SM v j w) = 0 := by
  rw [prS_apply] at hw
  obtain ⟨w1, wA, wE, wB, wH, wP, wQ, ws⟩ := w
  simp only at hw
  subst hw
  show prS m V S S' (toP (ActualJetSystem.princ (frameU (ginvOf v.1.1)) SM.D.Fr SM.Db.Fr j
    (ofP (w1, wA, wE, wB, wH, wP, wQ, (0 : S × (Fin 3 → S) × S' × (Fin 3 → S')))))) = 0
  simp [prS_apply, toP, ActualJetSystem.princ, ofP, diracP]
  exact ⟨rfl, rfl⟩

/-- The prolonged spinor row vanishes on vanishing spinor variables. -/
theorem XrowF_zero {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (κ Λ : ℝ) (g gi : Met) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4 → MatLie m) (F : Fin 4 → Fin 4 → MatLie m)
    (H : V) (DH : Fin 4 → V) (T : Met) (a : Fin 4) :
    XrowF D κ Λ g gi dg AF de A F H DH 0 (fun _ => 0) T a = 0 := by
  simp [XrowF]

theorem Xfull_zero {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (H : V) : (Fin.cases (XnatU D 0 (fun _ => 0) H) (fun _ => 0) : Fin 4 → S₀) = fun _ => 0 := by
  funext c
  induction c using Fin.cases with
  | zero => simp [XnatU]
  | succ c => rfl

theorem FsysX_eq (v : StateP m V S S') :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.1 = fun a =>
      (recon SM (ofP v)).AF.N • XrowF SM.D SM.κ SM.Λ (recon SM (ofP v)).g (recon SM (ofP v)).gi
        (recon SM (ofP v)).dg (recon SM (ofP v)).AF (recon SM (ofP v)).de (recon SM (ofP v)).A
        (recon SM (ofP v)).F (recon SM (ofP v)).H (recon SM (ofP v)).DH v.2.2.2.2.2.2.2.1
        (Fin.cases (XnatU SM.D v.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.1 v.2.2.2.2.1)
          v.2.2.2.2.2.2.2.2.1) (stressF SM (recon SM (ofP v))) a.succ := rfl

theorem FsysXb_eq (v : StateP m V S S') :
    (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.2.2 = fun a =>
      (recon SM (ofP v)).AF.N • XrowF SM.Db SM.κ SM.Λ (recon SM (ofP v)).g (recon SM (ofP v)).gi
        (recon SM (ofP v)).dg (recon SM (ofP v)).AF (recon SM (ofP v)).de (recon SM (ofP v)).A
        (recon SM (ofP v)).F (recon SM (ofP v)).H (recon SM (ofP v)).DH v.2.2.2.2.2.2.2.2.2.1
        (Fin.cases (XnatU SM.Db v.2.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.2 v.2.2.2.2.1)
          v.2.2.2.2.2.2.2.2.2.2) (stressF SM (recon SM (ofP v))) a.succ := rfl

variable (SM) in
/-- The spinor blocks of the forcing vanish on states with vanishing spinor blocks. -/
theorem prS_Fsys_zero {v : StateP m V S S'} (hv : prS m V S S' v = 0) :
    prS m V S S' (toP (Fsys SM (ofP v))) = 0 := by
  rw [prS_apply] at hv
  have hψ : v.2.2.2.2.2.2.2.1 = 0 := congrArg Prod.fst hv
  have hX : v.2.2.2.2.2.2.2.2.1 = 0 := congrArg (fun s => s.2.1) hv
  have hψb : v.2.2.2.2.2.2.2.2.2.1 = 0 := congrArg (fun s => s.2.2.1) hv
  have hXb : v.2.2.2.2.2.2.2.2.2.2 = 0 := congrArg (fun s => s.2.2.2) hv
  rw [prS_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · show (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.1 = 0
    rw [Fsysψ_eq, hψ]
    simp [Gψ, psiF]
  · show (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.1 = 0
    rw [FsysX_eq, hψ, hX]
    funext a
    rw [show (0 : Fin 3 → S) = fun _ => 0 from rfl, Xfull_zero, XrowF_zero, smul_zero]
  · show (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.2.1 = 0
    rw [Fsysψb_eq, hψb]
    simp [Gψ, psiF]
  · show (toP (Fsys SM (ofP v))).2.2.2.2.2.2.2.2.2.2 = 0
    rw [FsysXb_eq, hψb, hXb]
    funext a
    rw [show (0 : Fin 3 → S') = fun _ => 0 from rfl, Xfull_zero, XrowF_zero, smul_zero]

end Bosonic


/-! ### The original rows of `W` and the symmetric system for the spinor-free tuple -/

section Rows

theorem extraP_congr {b : ℝ} {w w' : StateP m V S S'} (h1 : w.1.1 = w'.1.1)
    (hH : w.2.2.2.2.1 = w'.2.2.2.2.1) : AJKatoMod.extraP b w = AJKatoMod.extraP b w' := by
  unfold AJKatoMod.extraP
  rw [h1, hH]

variable (SM) in
theorem fDiff_congr (hD : AJKatoMod.Decoupled SM) {v w : StateP m V S S'}
    (h : prB m V S S' v = prB m V S S' w) : AJKatoMod.fDiff SM v = AJKatoMod.fDiff SM w := by
  have hF := prB_eq_iff.1 (Fsys_bos_congr SM hD h)
  obtain ⟨h1, hA, -, -, hH, hP, -⟩ := prB_eq_iff.1 h
  have hg : (Fsys SM (ofP v)).g = (Fsys SM (ofP w)).g := congrArg Prod.fst hF.1
  have hFH : (Fsys SM (ofP v)).H = (Fsys SM (ofP w)).H := hF.2.2.2.2.1
  unfold AJKatoMod.fDiff
  rw [h1, hA, hH, hP, hg, hFH]

variable (SM) in
/-- **A solution of the shift-transported system whose bosonic blocks are actual solves the
original system** (the shift-transport terms cancel on actual metric and Higgs jets). -/
theorem orig_row_of_MSol (hD : AJKatoMod.Decoupled SM) {W : ST 3 → StateP m V S S'}
    {z : Tuple m V S S'} {a b : ℝ} (hW : MSol SM W z a b)
    (hB : ∀ y ∈ openSlab a b, prB m V S S' (W y) = prB m V S S' (stateF SM z y)) :
    ∀ x ∈ openSlab a b, pd W 0 x + ∑ j : Fin 3, princL SM (W x) j (pd W j.succ x) =
      toP (Fsys SM (ofP (W x))) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hUd : DifferentiableOn ℝ (stateF SM z) (openSlab a b) :=
    ((contDiff_stateF SM z).differentiable (by simp)).differentiableOn
  have hpd := pd_block_eq' hO hW1 hUd (prB m V S S') hB
  intro x hx
  have hrow := hW.row x hx
  rw [AJKatoMod.FsysM_eq] at hrow
  simp only [AJKatoMod.princPM_eq, Finset.sum_add_distrib] at hrow
  have hext : ∑ j : Fin 3, AJKatoMod.extraP ((frameU (ginvOf (W x).1.1)).β j) (pd W j.succ x) =
      AJKatoMod.fDiff SM (W x) := by
    have h1 : (W x).1.1 = (stateF SM z x).1.1 := congrArg Prod.fst (prB_eq_iff.1 (hB x hx)).1
    rw [h1, fDiff_congr SM hD (hB x hx), ← AJKatoMod.sum_extra_eq_fDiff]
    refine Finset.sum_congr rfl fun j _ => extraP_congr ?_ ?_
    · exact congrArg Prod.fst (prB_eq_iff.1 (hpd x hx j.succ)).1
    · exact (prB_eq_iff.1 (hpd x hx j.succ)).2.2.2.2.1
  rw [hext, ← add_assoc] at hrow
  exact add_right_cancel hrow

variable (SM) in
/-- **The spinor-free tuple solves the symmetric system** wherever `W` solves the
shift-transported system with actual bosonic blocks (decoupled spinors). -/
theorem symEqAt_zeroSp (hD : AJKatoMod.Decoupled SM) {W : ST 3 → StateP m V S S'}
    {z : Tuple m V S S'} {a b : ℝ} (hW : MSol SM W z a b)
    (hB : ∀ y ∈ openSlab a b, prB m V S S' (W y) = prB m V S S' (stateF SM z y)) :
    ∀ x ∈ openSlab a b, SymEqAt SM (zeroSp z) x := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := hW.smooth.of_le (by norm_cast)
  have hZ1 : ContDiffOn ℝ 1 (stateF SM (zeroSp z)) (openSlab a b) :=
    ((contDiff_stateF SM (zeroSp z)).of_le (by norm_cast)).contDiffOn
  have hB' : ∀ y ∈ openSlab a b, prB m V S S' (stateF SM (zeroSp z) y) = prB m V S S' (W y) :=
    fun y hy => (prB_stateF_zeroSp z y).trans (hB y hy).symm
  have hpdB := pd_block_eq' hO hZ1 (hW1.differentiableOn (by norm_num)) (prB m V S S') hB'
  have hpdS0 := pd_block_eq' hO hZ1 (differentiableOn_const (c := (0 : StateP m V S S')))
    (prS m V S S') (fun y _ => by rw [prS_stateF_zeroSp, map_zero])
  have hpdS : ∀ x ∈ openSlab a b, ∀ γ, prS m V S S' (pd (stateF SM (zeroSp z)) γ x) = 0 := by
    intro x hx γ
    rw [hpdS0 x hx γ, pd_zero_fun, map_zero]
  intro x hx
  have hA := orig_row_of_MSol SM hD hW hB x hx
  unfold SymEqAt
  apply eq_of_prB_prS
  · rw [map_add, map_sum, Fsys_bos_congr SM hD (hB' x hx), ← hA, map_add, map_sum, hpdB x hx 0]
    congr 1
    refine Finset.sum_congr rfl fun j _ => princL_bos_congr SM ?_ j (hpdB x hx j.succ)
    exact congrArg Prod.fst (prB_eq_iff.1 (hB' x hx)).1
  · rw [map_add, map_sum, prS_Fsys_zero SM (prS_stateF_zeroSp z x), hpdS x hx 0]
    simp only [prS_princL_zero SM _ _ (hpdS x hx _), Finset.sum_const_zero, add_zero]

end Rows


end RenewalGeometry.GenSpinorDefect
