/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledEinstein

/-!
# The spinor rows of the coupled defect system

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  For a coupled solution (`GenCplRows.CplSol`) the auxiliary spinor jets of `W`
differ from the actual ones of the head tuple by the **spinor defect**
`Y_a = X_a(W) - X_a(z)` (`a = 1, 2, 3`), extended to a one-form by the normal component
`Y_0 = c_0Σ_ic_iY_i` (the difference of the residual-free normal jets).

* `Yt`, `Yf` (and the dual `Ybt`, `Ybf`) — the defects;
* `Xfull_sub` — the residual-free spinor one-forms of `W` and `z` differ by `Yf`;
* `errF_X` — the spinor block of the residual forcing of `z` when `r_D ≡ 0` is
  `-N c_0 ricTerm(𝓔^{tr})` (the Ricci elimination of the actual Einstein residual);
* **`x_row_cpl`** — `∂_tY_a + Σ_j diracP_j∂_jY_a = N(XrowFX(Y)_a + c_0 ricTerm(∇_{(μ}C_{ν)})_a)`:
  the auxiliary stress cancels between the metric and the spinor rows (`GenCplEin.etr_eq`), and
  the spinor defect is forced only by itself and by first derivatives of the harmonic defect.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplX

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState GenConstraint
  GenSpinorDefect GenHiggsDefect SymHypEnergy GenCplRows GenStress GenCplEin

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (W : ST 3 → StateP m V S S') (z : Tuple m V S S')

/-- The tangential spinor defect `Y_a = X_a(W) - X_a(z)`. -/
def Yt (y : ST 3) : Fin 3 → S := (W y).2.2.2.2.2.2.2.2.1 - (stateF SM z y).2.2.2.2.2.2.2.2.1

/-- The tangential dual spinor defect. -/
def Ybt (y : ST 3) : Fin 3 → S' := (W y).2.2.2.2.2.2.2.2.2.2 - (stateF SM z y).2.2.2.2.2.2.2.2.2.2

/-- The one-form extension `Y = (c_0Σ_ic_iY_i, Y_a)`. -/
def oneForm {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (Y : Fin 3 → S₀) : Fin 4 → S₀ :=
  Fin.cases (D.Fr.c 0 • ∑ i : Fin 3, D.Fr.c i.succ • Y i) Y

/-- The spinor defect one-form. -/
def Yf (y : ST 3) : Fin 4 → S := oneForm SM.D (Yt SM W z y)

/-- The dual spinor defect one-form. -/
def Ybf (y : ST 3) : Fin 4 → S' := oneForm SM.Db (Ybt SM W z y)

variable {SM W z}

omit [FiniteDimensional ℝ V] in
theorem Xfull_sub_gen {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (ψ : S₀) (X X' : Fin 3 → S₀) (H : V) :
    (Fin.cases (XnatU D ψ X H) X : Fin 4 → S₀) - Fin.cases (XnatU D ψ X' H) X' =
      oneForm D (X - X') := by
  funext c
  induction c using Fin.cases with
  | zero =>
    simp only [Pi.sub_apply, Fin.cases_zero, oneForm, XnatU, Pi.sub_apply, map_sub, smul_sub,
      Finset.sum_sub_distrib, Module.End.smul_def]
    abel
  | succ c => rfl

variable {a b : ℝ}

/-- The reconstructed spinor one-forms of `W` and `z` differ by the defect one-form. -/
theorem recon_X_sub (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) :
    (recon SM (ofP (W x))).X - (recon SM (ofP (stateF SM z x))).X = Yf SM W z x := by
  have hψ := h.ψ_eq hx
  have hH : (W x).2.2.2.2.1 = (stateF SM z x).2.2.2.2.1 := (prB_eq_iff.1 (h.bos x hx)).2.2.2.2.1
  show (Fin.cases (XnatU SM.D (W x).2.2.2.2.2.2.2.1 (W x).2.2.2.2.2.2.2.2.1 (W x).2.2.2.2.1)
      (W x).2.2.2.2.2.2.2.2.1 : Fin 4 → S) - Fin.cases (XnatU SM.D (stateF SM z x).2.2.2.2.2.2.2.1
      (stateF SM z x).2.2.2.2.2.2.2.2.1 (stateF SM z x).2.2.2.2.1)
      (stateF SM z x).2.2.2.2.2.2.2.2.1 = _
  rw [hψ, hH, Xfull_sub_gen]
  rfl

theorem recon_Xb_sub (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) :
    (recon SM (ofP (W x))).Xb - (recon SM (ofP (stateF SM z x))).Xb = Ybf SM W z x := by
  have hψ := h.ψb_eq hx
  have hH : (W x).2.2.2.2.1 = (stateF SM z x).2.2.2.2.1 := (prB_eq_iff.1 (h.bos x hx)).2.2.2.2.1
  show (Fin.cases (XnatU SM.Db (W x).2.2.2.2.2.2.2.2.2.1 (W x).2.2.2.2.2.2.2.2.2.2
      (W x).2.2.2.2.1) (W x).2.2.2.2.2.2.2.2.2.2 : Fin 4 → S') - Fin.cases (XnatU SM.Db
      (stateF SM z x).2.2.2.2.2.2.2.2.2.1 (stateF SM z x).2.2.2.2.2.2.2.2.2.2
      (stateF SM z x).2.2.2.2.1) (stateF SM z x).2.2.2.2.2.2.2.2.2.2 = _
  rw [hψ, hH, Xfull_sub_gen]
  rfl

/-- The spinor block of the residual forcing when the Dirac residuals vanish to first order. -/
theorem errF_X (x : ST 3) (hD : dirF SM z x = 0) (hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0)
    (a : Fin 3) : (errF SM z x).2.2.2.2.2.2.2.2.1 a =
      (frameU (z.gi x)).N • -(SM.D.Fr.c 0 • ricTerm SM.D (z.g x) (z.gi x) (frameU (z.gi x))
        (bosF SM z x).1 (z.ψ x) a.succ) := by
  unfold errF
  rw [hD]
  simp only [hdD, map_zero, add_zero, Finset.sum_const_zero]
  have hG : (GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
      ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x)).2.2.2.2.2.2.2.2.1 = 0 := by
    simp only [GcL, GdL, toP, pState, Prod.snd_sum, Prod.snd_add, Prod.fst_add, Prod.fst_sum,
      LinearMap.coe_mk, AddHom.coe_mk]
    funext i
    simp
  rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add,
    Prod.snd_add, Prod.snd_add, Prod.fst_add, Pi.add_apply, hG, Pi.zero_apply, add_zero]
  have hst : stressR SM (recon SM (ofP (stateF SM z x)))
      (ofR (bosR (S := S) (S' := S') (bosF SM z x))) = fun _ _ => 0 := by
    funext μ ν
    simp [stressR, DiracStressForm.stressRes, ofR, bosR]
  show (recon SM (ofP (stateF SM z x))).AF.N • XrowB SM.D SM.κ _ _ _ _ _ _ _ a.succ 0 _
    (stressR SM (recon SM (ofP (stateF SM z x))) (ofR (bosR (S := S) (S' := S') (bosF SM z x)))) =
    _
  rw [hst, XrowB_zero_rD]
  rfl

/-- The dual spinor block of the residual forcing when the Dirac residuals vanish to first order. -/
theorem errF_Xb (x : ST 3) (hD : dirF SM z x = 0) (hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0)
    (a : Fin 3) : (errF SM z x).2.2.2.2.2.2.2.2.2.2 a =
      (frameU (z.gi x)).N • -(SM.Db.Fr.c 0 • ricTerm SM.Db (z.g x) (z.gi x) (frameU (z.gi x))
        (bosF SM z x).1 (z.ψb x) a.succ) := by
  unfold errF
  rw [hD]
  simp only [hdD, map_zero, add_zero, Finset.sum_const_zero]
  have hG : (GcL (stateF SM z x) (CF z x) + GdL 0 (stateF SM z x) (pd (CF z) 0 x) +
      ∑ j : Fin 3, GdL j.succ (stateF SM z x) (pd (CF z) j.succ x)).2.2.2.2.2.2.2.2.2.2 = 0 := by
    simp only [GcL, GdL, toP, pState, Prod.snd_sum, Prod.snd_add, Prod.fst_add, Prod.fst_sum,
      LinearMap.coe_mk, AddHom.coe_mk]
    funext i
    simp
  rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add,
    Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, Pi.add_apply, hG, Pi.zero_apply,
    add_zero]
  have hst : stressR SM (recon SM (ofP (stateF SM z x)))
      (ofR (bosR (S := S) (S' := S') (bosF SM z x))) = fun _ _ => 0 := by
    funext μ ν
    simp [stressR, DiracStressForm.stressRes, ofR, bosR]
  show (recon SM (ofP (stateF SM z x))).AF.N • XrowB SM.Db SM.κ _ _ _ _ _ _ _ a.succ 0 _
    (stressR SM (recon SM (ofP (stateF SM z x))) (ofR (bosR (S := S) (S' := S') (bosF SM z x)))) =
    _
  rw [hst, XrowB_zero_rD]
  rfl

end RenewalGeometry.GenCplX

namespace RenewalGeometry.GenCplX

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState GenConstraint
  GenSpinorDefect GenHiggsDefect SymHypEnergy GenCplRows GenStress GenCplEin

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
  {a b : ℝ}

variable (m V S S') in
/-- The `X`-block of a state. -/
def prX : StateP m V S S' →L[ℝ] (Fin 3 → S) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.2.2.1, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }

variable (m V S S') in
/-- The `X̄`-block of a state. -/
def prXb : StateP m V S S' →L[ℝ] (Fin 3 → S') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v.2.2.2.2.2.2.2.2.2.2, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }

/-- The reconstructed first jets of `W` and `z` agree off the spinor jets. -/
theorem recon_fields (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) :
    let fW := recon SM (ofP (W x))
    let fU := recon SM (ofP (stateF SM z x))
    fW.g = fU.g ∧ fW.gi = fU.gi ∧ fW.dg = fU.dg ∧ fW.AF = fU.AF ∧ fW.de = fU.de ∧
      fW.A = fU.A ∧ fW.F = fU.F ∧ fW.H = fU.H ∧ fW.DH = fU.DH ∧ fW.ψ = fU.ψ ∧ fW.ψb = fU.ψb := by
  have hrec := recon_withX (SM := SM) (h.bos x hx) (h.ψ_eq hx) (h.ψb_eq hx)
  intro fW fU
  have : fW = withX fU fW.X fW.Xb := hrec
  rw [this]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The spinor rows of the coupled defect system** (exact). -/
theorem x_row_cpl (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (a' : Fin 3) :
    pd (Yt SM W z) 0 x a' + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.D.Fr j
        (pd (Yt SM W z) j.succ x a') =
      (frameU (z.gi x)).N • (XrowFX SM.D (z.g x) (z.gi x) (z.dg x) (frameU (z.gi x)) (z.de x)
        (z.A x) (z.H x) (Yf SM W z x) a'.succ +
        SM.D.Fr.c 0 • ricTerm SM.D (z.g x) (z.gi x) (frameU (z.gi x))
          (fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν) (z.ψ x) a'.succ) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hD : dirF SM z x = 0 := h.dir x hx
  have hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0 := fun j =>
    pd_eq_zero_of_eventually (Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => h.dir y hy)
      j.succ
  have hrow := congrArg (fun v : StateP m V S S' => prX m V S S' v a') (diff_row h hx)
  have hYt : Yt SM W z = fun y => prX m V S S' (W y - stateF SM z y) := by
    funext y; simp [Yt, prX]
  have hpdY : ∀ γ, pd (Yt SM W z) γ x = prX m V S S' (pd (fun y => W y - stateF SM z y) γ x) :=
    fun γ => by rw [hYt]; exact GenHarmonic.pd_clm _ (hdW.fun_sub hdU) γ
  simp only [map_add, map_sum, map_sub, Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at hrow
  have hpr : ∀ (j : Fin 3) (u : StateP m V S S'), prX m V S S' (princL SM (stateF SM z x) j u) a' =
      diracP (frameU (z.gi x)) SM.D.Fr j (prX m V S S' u a') := fun j u => rfl
  simp only [hpr] at hrow
  simp only [hpdY]
  rw [hrow]
  -- the forcing
  obtain ⟨hg, hgi, hdg, hAF, hde, hA, hF, hH, hDH, hψ, -⟩ := recon_fields h hx
  set fW := recon SM (ofP (W x)) with hfW
  set fU := recon SM (ofP (stateF SM z x)) with hfU
  have eW : prX m V S S' (toP (Fsys SM (ofP (W x)))) a' = fU.AF.N • XrowF SM.D SM.κ SM.Λ fU.g fU.gi
      fU.dg fU.AF fU.de fU.A fU.F fU.H fU.DH fU.ψ fW.X (stressF SM fW) a'.succ := by
    show fW.AF.N • XrowF SM.D SM.κ SM.Λ fW.g fW.gi fW.dg fW.AF fW.de fW.A fW.F fW.H fW.DH fW.ψ
      fW.X (stressF SM fW) a'.succ = _
    rw [hg, hgi, hdg, hAF, hde, hA, hF, hH, hDH, hψ]
  have eU : prX m V S S' (toP (Fsys SM (ofP (stateF SM z x)))) a' = fU.AF.N • XrowF SM.D SM.κ
      SM.Λ fU.g fU.gi fU.dg fU.AF fU.de fU.A fU.F fU.H fU.DH fU.ψ fU.X (stressF SM fU) a'.succ :=
    rfl
  have eE : prX m V S S' (errF SM z x) a' = (frameU (z.gi x)).N • -(SM.D.Fr.c 0 •
      ricTerm SM.D (z.g x) (z.gi x) (frameU (z.gi x)) (bosF SM z x).1 (z.ψ x) a'.succ) :=
    errF_X x hD hdD a'
  rw [eW, eU, eE, ← smul_sub, XrowF_sub, recon_X_sub h hx]
  have hN : fU.AF = frameU (z.gi x) := rfl
  have hfg : fU.g = z.g x := rfl
  have hfgi : fU.gi = z.gi x := rfl
  have hfdg : fU.dg = z.dg x := (ActualJetState.jet_dg_eq SM z x).symm
  have hfde : fU.de = z.de x := by
    show frameJet fU.gi (fun γ l σ => dginv fU.gi fU.dg γ l σ) = _
    rw [hfgi, hfdg]; rfl
  have hfA : fU.A = z.A x := by
    funext μ
    induction μ using Fin.cases with
    | zero => exact (z.temporal x).symm
    | succ i => rfl
  have hfH : fU.H = z.H x := rfl
  have hfψ : fU.ψ = z.ψ x := rfl
  rw [hN, hfg, hfgi, hfdg, hfde, hfA, hfH, hfψ]
  -- the Einstein residual and the stress difference
  have hEt : (bosF SM z x).1 = fun μ ν => SM.κ * traceRev (z.g x) (z.gi x)
      (stressDiff SM W z x) μ ν + symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν :=
    funext fun μ => funext fun ν => etr_eq h hx μ ν
  have hTr : (fun μ ν => SM.κ * (traceRev (z.g x) (z.gi x) (stressF SM fW) μ ν -
      traceRev (z.g x) (z.gi x) (stressF SM fU) μ ν)) =
      fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν := by
    funext μ ν
    rw [← ActualJetSystem.traceRev_sub]
    rfl
  rw [hTr, hEt]
  have hric := ricTerm_sub SM.D (z.g x) (z.gi x) (frameU (z.gi x))
    (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν +
      symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν)
    (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν) (z.ψ x) a'.succ
  have e : (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν +
      symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν -
      SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν) =
      fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν := by
    funext μ ν; ring
  rw [e] at hric
  rw [← hric]
  simp only [smul_sub, smul_neg, smul_add]
  abel

/-- **The dual spinor rows of the coupled defect system** (exact). -/
theorem x_row_cpl_b (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (a' : Fin 3) :
    pd (Ybt SM W z) 0 x a' + ∑ j : Fin 3, diracP (frameU (z.gi x)) SM.Db.Fr j
        (pd (Ybt SM W z) j.succ x a') =
      (frameU (z.gi x)).N • (XrowFX SM.Db (z.g x) (z.gi x) (z.dg x) (frameU (z.gi x)) (z.de x)
        (z.A x) (z.H x) (Ybf SM W z x) a'.succ +
        SM.Db.Fr.c 0 • ricTerm SM.Db (z.g x) (z.gi x) (frameU (z.gi x))
          (fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν) (z.ψb x) a'.succ) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hD : dirF SM z x = 0 := h.dir x hx
  have hdD : ∀ j : Fin 3, pd (dirF SM z) j.succ x = 0 := fun j =>
    pd_eq_zero_of_eventually (Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => h.dir y hy)
      j.succ
  have hrow := congrArg (fun v : StateP m V S S' => prXb m V S S' v a') (diff_row h hx)
  have hYbt : Ybt SM W z = fun y => prXb m V S S' (W y - stateF SM z y) := by
    funext y; simp [Ybt, prXb]
  have hpdY : ∀ γ, pd (Ybt SM W z) γ x = prXb m V S S' (pd (fun y => W y - stateF SM z y) γ x) :=
    fun γ => by rw [hYbt]; exact GenHarmonic.pd_clm _ (hdW.fun_sub hdU) γ
  simp only [map_add, map_sum, map_sub, Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at hrow
  have hpr : ∀ (j : Fin 3) (u : StateP m V S S'), prXb m V S S' (princL SM (stateF SM z x) j u) a' =
      diracP (frameU (z.gi x)) SM.Db.Fr j (prXb m V S S' u a') := fun j u => rfl
  simp only [hpr] at hrow
  simp only [hpdY]
  rw [hrow]
  -- the forcing
  obtain ⟨hg, hgi, hdg, hAF, hde, hA, hF, hH, hDH, -, hψ⟩ := recon_fields h hx
  set fW := recon SM (ofP (W x)) with hfW
  set fU := recon SM (ofP (stateF SM z x)) with hfU
  have eW : prXb m V S S' (toP (Fsys SM (ofP (W x)))) a' = fU.AF.N • XrowF SM.Db SM.κ SM.Λ fU.g fU.gi
      fU.dg fU.AF fU.de fU.A fU.F fU.H fU.DH fU.ψb fW.Xb (stressF SM fW) a'.succ := by
    show fW.AF.N • XrowF SM.Db SM.κ SM.Λ fW.g fW.gi fW.dg fW.AF fW.de fW.A fW.F fW.H fW.DH fW.ψb
      fW.Xb (stressF SM fW) a'.succ = _
    rw [hg, hgi, hdg, hAF, hde, hA, hF, hH, hDH, hψ]
  have eU : prXb m V S S' (toP (Fsys SM (ofP (stateF SM z x)))) a' = fU.AF.N • XrowF SM.Db SM.κ
      SM.Λ fU.g fU.gi fU.dg fU.AF fU.de fU.A fU.F fU.H fU.DH fU.ψb fU.Xb (stressF SM fU) a'.succ :=
    rfl
  have eE : prXb m V S S' (errF SM z x) a' = (frameU (z.gi x)).N • -(SM.Db.Fr.c 0 •
      ricTerm SM.Db (z.g x) (z.gi x) (frameU (z.gi x)) (bosF SM z x).1 (z.ψb x) a'.succ) :=
    errF_Xb x hD hdD a'
  rw [eW, eU, eE, ← smul_sub, XrowF_sub, recon_Xb_sub h hx]
  have hN : fU.AF = frameU (z.gi x) := rfl
  have hfg : fU.g = z.g x := rfl
  have hfgi : fU.gi = z.gi x := rfl
  have hfdg : fU.dg = z.dg x := (ActualJetState.jet_dg_eq SM z x).symm
  have hfde : fU.de = z.de x := by
    show frameJet fU.gi (fun γ l σ => dginv fU.gi fU.dg γ l σ) = _
    rw [hfgi, hfdg]; rfl
  have hfA : fU.A = z.A x := by
    funext μ
    induction μ using Fin.cases with
    | zero => exact (z.temporal x).symm
    | succ i => rfl
  have hfH : fU.H = z.H x := rfl
  have hfψ : fU.ψb = z.ψb x := rfl
  rw [hN, hfg, hfgi, hfdg, hfde, hfA, hfH, hfψ]
  -- the Einstein residual and the stress difference
  have hEt : (bosF SM z x).1 = fun μ ν => SM.κ * traceRev (z.g x) (z.gi x)
      (stressDiff SM W z x) μ ν + symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν :=
    funext fun μ => funext fun ν => etr_eq h hx μ ν
  have hTr : (fun μ ν => SM.κ * (traceRev (z.g x) (z.gi x) (stressF SM fW) μ ν -
      traceRev (z.g x) (z.gi x) (stressF SM fU) μ ν)) =
      fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν := by
    funext μ ν
    rw [← ActualJetSystem.traceRev_sub]
    rfl
  rw [hTr, hEt]
  have hric := ricTerm_sub SM.Db (z.g x) (z.gi x) (frameU (z.gi x))
    (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν +
      symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν)
    (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν) (z.ψb x) a'.succ
  have e : (fun μ ν => SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν +
      symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν -
      SM.κ * traceRev (z.g x) (z.gi x) (stressDiff SM W z x) μ ν) =
      fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν := by
    funext μ ν; ring
  rw [e] at hric
  rw [← hric]
  simp only [smul_sub, smul_neg, smul_add]
  abel

end RenewalGeometry.GenCplX
