/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledNormal

/-!
# The normal prolongation defect and its Dirac equation

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  For a coupled solution `W` (smooth on space-time) with head tuple `z` and
spinor defect one-form `Y = Yf` (`κ(Y) = 0` identically), the covariant rows give
`(𝒟'Y)_a = R_a` for `a = 1, 2, 3` (`GenCplCov.q_row`).  The **normal prolongation defect**
`P = (𝒟'Y)_0 - R_0` (the defect of the missing `a = 0` prolonged row, equivalently of the
Clifford-curl / Lichnerowicz constraint of the auxiliary jets) closes the system:

* `Pf`, `Q_eq` — `𝒟'Y = R + P e_0` on the slab;
* **`P_dirac`** — the Dirac equation of `P`:
  `ε_0c_0𝒟P = ½Σ_{ab}ε_aε_bκ(c_ac_bR'_{ab}Y) - κ𝒟'R + Σ_{A,a}ε_Aε_aΓ_{aA}{}^0c_Ac_aP`.
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplP

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenSpinorDefect

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

/-! ### The one-form extension -/

/-- The one-form extension as a linear map. -/
def oneFormL (D : DiracData (MatLie m) V S₀) : (Fin 3 → S₀) →ₗ[ℝ] (Fin 4 → S₀) where
  toFun := oneForm D
  map_add' u v := by
    funext c
    induction c using Fin.cases with
    | zero => simp [oneForm, smul_add, Finset.sum_add_distrib, Module.End.smul_def]
    | succ c => rfl
  map_smul' r u := by
    funext c
    induction c using Fin.cases with
    | zero => simp [oneForm, Finset.smul_sum, Module.End.smul_def]
    | succ c => rfl

/-- **The one-form extension is Clifford-traceless**: `κ(Y) = Σ_Aε_Ac_AY_A = 0`. -/
theorem kap_oneForm (D : DiracData (MatLie m) V S₀) (Y : Fin 3 → S₀) :
    kap D.Fr (oneForm D Y) = 0 := by
  rw [kap_apply, Fin.sum_univ_succ]
  have hε0 : D.Fr.ε 0 = -1 := D.lorentz.1
  have hεi : ∀ i : Fin 3, D.Fr.ε i.succ = 1 := D.lorentz.2
  simp only [oneForm, Fin.cases_zero, Fin.cases_succ, hε0, hεi, neg_smul, one_smul,
    Module.End.smul_def, c0c0, map_sum]
  abel

/-- The unit vector `e_0` in the form index. -/
def e0L : S₀ →ₗ[ℝ] (Fin 4 → S₀) := LinearMap.single ℝ (fun _ : Fin 4 => S₀) 0

theorem e0L_apply (p : S₀) (A : Fin 4) : e0L p A = if A = 0 then p else 0 := by
  unfold e0L
  rw [LinearMap.single_apply, Pi.single_apply]

variable (SM : SMData (MatLie m) V S S') (W : ST 3 → StateP m V S S') (z : Tuple m V S S')

theorem contDiff_Yt (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Yt SM W z) := by
  have : Yt SM W z = fun y => prX m V S S' (W y - stateF SM z y) := by
    funext y; simp [Yt, prX]
  rw [this]
  exact (prX m V S S').contDiff.comp (hW.sub (contDiff_stateF SM z))

theorem contDiff_Yf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Yf SM W z) := by
  have : Yf SM W z = fun y => oneFormL SM.D (Yt SM W z y) := rfl
  rw [this]
  exact (LinearMap.toContinuousLinearMap (oneFormL SM.D)).contDiff.comp (contDiff_Yt SM W z hW)

theorem kap_Yf (y : ST 3) : kap SM.D.Fr (Yf SM W z y) = 0 := kap_oneForm SM.D _

/-- `𝒟'Y` of the spinor defect. -/
def Qf (y : ST 3) : Fin 4 → S := QF z SM.D (Yf SM W z) y

/-- The forcing `R` of the spinor defect rows. -/
def Rf (y : ST 3) : Fin 4 → S := fun A => RF z SM.D z.ψ (Yf SM W z) y A

/-- **The normal prolongation defect** `P = (𝒟'Y)_0 - R_0`. -/
def Pf (y : ST 3) : S := Qf SM W z y 0 - Rf SM W z y 0

variable {SM W z} {a b : ℝ}

/-- **`𝒟'Y = R + Pe_0`** on the slab. -/
theorem Q_eq (h : CplSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    Qf SM W z y = Rf SM W z y + e0L (Pf SM W z y) := by
  funext A
  rw [Pi.add_apply, e0L_apply]
  induction A using Fin.cases with
  | zero => simp [Pf]
  | succ a' =>
    simp only [Fin.succ_ne_zero, if_false, add_zero]
    exact q_row z h hy a'

theorem fd_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ST 3 → E}
    {x : ST 3} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (B : Fin 4) :
    fd z (fun y => f y + g y) B x = fd z f B x + fd z g B x := by
  rw [fd_eq_sum, fd_eq_sum, fd_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← smul_add]
  congr 1
  unfold SobolevOpen.pd
  rw [fderiv_fun_add hf hg]
  rfl

theorem contDiff_sD (μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => sD z y μ ν) := by
  have h1 := z.contDiff_gc
  have h2 := z.contDiff_gi
  have h3 := z.contDiff_dg
  have h4 := z.contDiff_ddg
  simp only [sD, symDefect, nablaDefect, nablaC, cUp, dcUp, cDown, dchr, dchr1, dchr2, chr, dginv]
  fun_prop

theorem contDiff_fr (A μ : Fin 4) : ContDiff ℝ ∞ (fun y => (frameU (z.gi y)).fr A μ) := by
  have := z.contDiff_e A μ
  simpa only [GenGauss.e_eq_frameU] using this

theorem contDiff_ricTerm (D : DiracData (MatLie m) V S₀) {ψ : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψ)
    (T : ST 3 → Fin 4 → Fin 4 → ℝ) (hT : ∀ μ ν, ContDiff ℝ ∞ (fun y => T y μ ν)) (A : Fin 4) :
    ContDiff ℝ ∞ (fun y => ricTerm D (z.g y) (z.gi y) (frameU (z.gi y)) (T y) (ψ y) A) := by
  have hfr := contDiff_fr (z := z)
  have hc : ∀ b, ContDiff ℝ ∞ (fun y => D.Fr.c b (ψ y)) := fun b =>
    (LinearMap.toContinuousLinearMap (D.Fr.c b)).contDiff.comp hψ
  have e : ∀ y, ricTerm D (z.g y) (z.gi y) (frameU (z.gi y)) (T y) (ψ y) A =
      (1 / 2 : ℝ) • ∑ b, (lorentzSign b * frT2 (frameU (z.gi y)).fr (T y) A b) • D.Fr.c b (ψ y) := by
    intro y
    unfold ricTerm
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.smul_def]
  simp only [e]
  unfold frT2
  refine ContDiff.const_smul _ (ContDiff.sum fun b _ => ContDiff.smul ?_ (hc b))
  refine contDiff_const.mul (ContDiff.sum fun μ _ => ContDiff.sum fun ν _ => ?_)
  exact ((hfr A μ).mul (hfr b ν)).mul (hT μ ν)

theorem contDiff_RF (D : DiracData (MatLie m) V S₀) {ψ : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψ)
    {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (A : Fin 4) :
    ContDiff ℝ ∞ (fun y => RF z D ψ Y y A) := by
  unfold RF
  refine ContDiff.sub ?_ (contDiff_ricTerm (z := z) D hψ (sD z) (contDiff_sD (z := z)) A)
  simp only [mass, LinearMap.add_apply]
  refine ((LinearMap.toContinuousLinearMap D.m0).contDiff.comp (contDiff_comp_apply hY A)).add ?_
  exact contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.bilinApply D.L z.H_smooth.contDiffAt (contDiff_comp_apply hY A).contDiffAt

theorem contDiff_Rf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Rf SM W z) :=
  contDiff_pi.2 fun A => contDiff_RF (z := z) SM.D z.ψ_smooth (contDiff_Yf SM W z hW) A

theorem contDiff_Qf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Qf SM W z) :=
  contDiff_QF z SM.D (contDiff_Yf SM W z hW)

theorem contDiff_Pf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Pf SM W z) :=
  ((contDiff_pi.1 (contDiff_Qf hW) 0).sub (contDiff_pi.1 (contDiff_Rf hW) 0))

/-- **The Dirac equation of the normal prolongation defect** (exact). -/
theorem P_dirac (hW : ContDiff ℝ ∞ W) (h : CplSol SM W z a b) {x : ST 3}
    (hx : x ∈ openSlab a b) :
    SM.D.Fr.ε 0 • SM.D.Fr.c 0 (∑ a', SM.D.Fr.ε a' • SM.D.Fr.c a' (fd z (Pf SM W z) a' x +
        ωF z SM.D x a' (Pf SM W z x))) =
      (1 / 2 : ℝ) • ∑ a', ∑ b', (SM.D.Fr.ε a' * SM.D.Fr.ε b') • kap SM.D.Fr
        (((liftFr SM.D.Fr).c a' * (liftFr SM.D.Fr).c b') • (curv (lcΛ SM.D.Fr.ε (Jx z SM.D x).G)
          (omegaP (ωF z SM.D x) (ΓF z x)) (dωP z SM.D x) a' b' • Yf SM W z x)) -
      kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' • ((liftFr SM.D.Fr).c a' •
        (fd z (Rf SM W z) a' x + omegaP (ωF z SM.D x) (ΓF z x) a' (Rf SM W z x)))) +
      ∑ A, ∑ a', (SM.D.Fr.ε A * SM.D.Fr.ε a' * ΓF z x a' A 0) •
        SM.D.Fr.c A (SM.D.Fr.c a' (Pf SM W z x)) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hYs := contDiff_Yf SM W z hW
  have hκ : (fun y => kap SM.D.Fr (Yf SM W z y)) =ᶠ[𝓝 x] 0 :=
    Filter.Eventually.of_forall fun y => kap_Yf SM W z y
  have hmain := kap_DQ z SM.D hYs hκ
  have hQx := Q_eq h hx
  have hev : Qf SM W z =ᶠ[𝓝 x] fun y => Rf SM W z y + e0L (Pf SM W z y) :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => Q_eq h hy
  have hfdQ : ∀ a', fd z (QF z SM.D (Yf SM W z)) a' x =
      fd z (Rf SM W z) a' x + e0L (fd z (Pf SM W z) a' x) := by
    intro a'
    have h1 : fd z (QF z SM.D (Yf SM W z)) a' x =
        fd z (fun y => Rf SM W z y + e0L (Pf SM W z y)) a' x := by
      unfold fd
      congr 1
      funext μ
      exact GenHarmonic.pd_eq_of_eventuallyEq hev μ
    rw [h1]
    have hg : DifferentiableAt ℝ (fun y => (e0L : S →ₗ[ℝ] Fin 4 → S) (Pf SM W z y)) x :=
      (LinearMap.toContinuousLinearMap (e0L (S₀ := S))).differentiableAt.comp x
        ((contDiff_Pf hW).differentiable (by simp) x)
    rw [fd_add (z := z) (f := Rf SM W z) (g := fun y => e0L (Pf SM W z y))
      ((contDiff_Rf hW).differentiable (by simp) x) hg,
      fd_lin z (E := S) e0L ((contDiff_Pf hW).differentiable (by simp) x)]
  -- expand the left side of `kap_DQ`
  have hQ0 : QF z SM.D (Yf SM W z) x = Rf SM W z x + e0L (Pf SM W z x) := hQx
  simp only [hfdQ, hQ0, map_add, smul_add, Finset.sum_add_distrib] at hmain
  rw [← hmain]
  -- the `P e_0` part
  have hP : kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' • ((liftFr SM.D.Fr).c a' •
      e0L (fd z (Pf SM W z) a' x))) + kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' •
      ((liftFr SM.D.Fr).c a' • omegaP (ωF z SM.D x) (ΓF z x) a' (e0L (Pf SM W z x)))) =
      SM.D.Fr.ε 0 • SM.D.Fr.c 0 (∑ a', SM.D.Fr.ε a' • SM.D.Fr.c a' (fd z (Pf SM W z) a' x +
        ωF z SM.D x a' (Pf SM W z x))) -
      ∑ A, ∑ a', (SM.D.Fr.ε A * SM.D.Fr.ε a' * ΓF z x a' A 0) •
        SM.D.Fr.c A (SM.D.Fr.c a' (Pf SM W z x)) := by
    simp only [kap_apply, Finset.sum_apply, Pi.smul_apply, Module.End.smul_def, liftE_apply,
      omegaP_apply, e0L_apply, liftFr]
    have e1 : ∀ x2 x1 : Fin 4, (∑ x3, ΓF z x x2 x1 x3 • if x3 = 0 then Pf SM W z x else 0) =
        ΓF z x x2 x1 0 • Pf SM W z x := by
      intro x2 x1
      rw [Finset.sum_eq_single 0 (fun c _ hc => by rw [if_neg hc, smul_zero]) (by simp)]
      simp
    simp only [e1]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun x_1 => SM.D.Fr.ε x_1 • (SM.D.Fr.c x_1)
      (∑ x_2, SM.D.Fr.ε x_2 • (SM.D.Fr.c x_2) ((ωF z SM.D x x_2) (if x_1 = 0 then Pf SM W z x
        else 0) - ΓF z x x_2 x_1 0 • Pf SM W z x)))]
    simp only [if_true, Fin.succ_ne_zero, if_false, map_zero, smul_zero, Finset.sum_const_zero,
      add_zero, zero_sub]
    rw [Fin.sum_univ_succ (f := fun A => ∑ a', (SM.D.Fr.ε A * SM.D.Fr.ε a' * ΓF z x a' A 0) •
      (SM.D.Fr.c A) ((SM.D.Fr.c a') (Pf SM W z x)))]
    simp only [map_add, map_sub, map_neg, map_sum, map_smul, smul_add, smul_sub, smul_neg,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, smul_smul,
      Finset.smul_sum]
    have e2 : ∀ (i : Fin 3) (a' : Fin 4), SM.D.Fr.ε i.succ * (SM.D.Fr.ε a' * ΓF z x a' i.succ 0) =
        SM.D.Fr.ε i.succ * SM.D.Fr.ε a' * ΓF z x a' i.succ 0 := fun i a' => by ring
    have e3 : ∀ a' : Fin 4, SM.D.Fr.ε 0 * (SM.D.Fr.ε a' * ΓF z x a' 0 0) =
        SM.D.Fr.ε 0 * SM.D.Fr.ε a' * ΓF z x a' 0 0 := fun a' => by ring
    simp only [e2, e3]
    abel
  have hR : kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' • ((liftFr SM.D.Fr).c a' •
      (fd z (Rf SM W z) a' x + omegaP (ωF z SM.D x) (ΓF z x) a' (Rf SM W z x)))) =
      kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' • ((liftFr SM.D.Fr).c a' • fd z (Rf SM W z) a' x)) +
        kap SM.D.Fr (∑ a', (liftFr SM.D.Fr).ε a' • ((liftFr SM.D.Fr).c a' •
          omegaP (ωF z SM.D x) (ΓF z x) a' (Rf SM W z x))) := by
    rw [← map_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [smul_add, smul_add]
  rw [hR, sub_eq_iff_eq_add.mp hP.symm]
  abel

/-! ### The dual block -/

variable (SM W z)

theorem contDiff_Ybt (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Ybt SM W z) := by
  have : Ybt SM W z = fun y => prXb m V S S' (W y - stateF SM z y) := by
    funext y; simp [Ybt, prXb]
  rw [this]
  exact (prXb m V S S').contDiff.comp (hW.sub (contDiff_stateF SM z))

theorem contDiff_Ybf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Ybf SM W z) := by
  have : Ybf SM W z = fun y => oneFormL SM.Db (Ybt SM W z y) := rfl
  rw [this]
  exact (LinearMap.toContinuousLinearMap (oneFormL SM.Db)).contDiff.comp (contDiff_Ybt SM W z hW)

theorem kap_Ybf (y : ST 3) : kap SM.Db.Fr (Ybf SM W z y) = 0 := kap_oneForm SM.Db _

/-- `𝒟'Y` of the spinor defect. -/
def Qbf (y : ST 3) : Fin 4 → S' := QF z SM.Db (Ybf SM W z) y

/-- The forcing `R` of the spinor defect rows. -/
def Rbf (y : ST 3) : Fin 4 → S' := fun A => RF z SM.Db z.ψb (Ybf SM W z) y A

/-- **The normal prolongation defect** `P = (𝒟'Y)_0 - R_0`. -/
def Pbf (y : ST 3) : S' := Qbf SM W z y 0 - Rbf SM W z y 0

variable {SM W z} {a b : ℝ}

/-- **`𝒟'Y = R + Pe_0`** on the slab. -/
theorem Q_eq_b (h : CplSol SM W z a b) {y : ST 3} (hy : y ∈ openSlab a b) :
    Qbf SM W z y = Rbf SM W z y + e0L (Pbf SM W z y) := by
  funext A
  rw [Pi.add_apply, e0L_apply]
  induction A using Fin.cases with
  | zero => simp [Pbf]
  | succ a' =>
    simp only [Fin.succ_ne_zero, if_false, add_zero]
    exact q_row_b z h hy a'

theorem contDiff_Rbf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Rbf SM W z) :=
  contDiff_pi.2 fun A => contDiff_RF (z := z) SM.Db z.ψb_smooth (contDiff_Ybf SM W z hW) A

theorem contDiff_Qbf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Qbf SM W z) :=
  contDiff_QF z SM.Db (contDiff_Ybf SM W z hW)

theorem contDiff_Pbf (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (Pbf SM W z) :=
  ((contDiff_pi.1 (contDiff_Qbf hW) 0).sub (contDiff_pi.1 (contDiff_Rbf hW) 0))

/-- **The Dirac equation of the normal prolongation defect** (exact). -/
theorem P_dirac_b (hW : ContDiff ℝ ∞ W) (h : CplSol SM W z a b) {x : ST 3}
    (hx : x ∈ openSlab a b) :
    SM.Db.Fr.ε 0 • SM.Db.Fr.c 0 (∑ a', SM.Db.Fr.ε a' • SM.Db.Fr.c a' (fd z (Pbf SM W z) a' x +
        ωF z SM.Db x a' (Pbf SM W z x))) =
      (1 / 2 : ℝ) • ∑ a', ∑ b', (SM.Db.Fr.ε a' * SM.Db.Fr.ε b') • kap SM.Db.Fr
        (((liftFr SM.Db.Fr).c a' * (liftFr SM.Db.Fr).c b') • (curv (lcΛ SM.Db.Fr.ε (Jx z SM.Db x).G)
          (omegaP (ωF z SM.Db x) (ΓF z x)) (dωP z SM.Db x) a' b' • Ybf SM W z x)) -
      kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' • ((liftFr SM.Db.Fr).c a' •
        (fd z (Rbf SM W z) a' x + omegaP (ωF z SM.Db x) (ΓF z x) a' (Rbf SM W z x)))) +
      ∑ A, ∑ a', (SM.Db.Fr.ε A * SM.Db.Fr.ε a' * ΓF z x a' A 0) •
        SM.Db.Fr.c A (SM.Db.Fr.c a' (Pbf SM W z x)) := by
  have hO := isOpen_openSlab (d := 3) a b
  have hYs := contDiff_Ybf SM W z hW
  have hκ : (fun y => kap SM.Db.Fr (Ybf SM W z y)) =ᶠ[𝓝 x] 0 :=
    Filter.Eventually.of_forall fun y => kap_Ybf SM W z y
  have hmain := kap_DQ z SM.Db hYs hκ
  have hQx := Q_eq_b h hx
  have hev : Qbf SM W z =ᶠ[𝓝 x] fun y => Rbf SM W z y + e0L (Pbf SM W z y) :=
    Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => Q_eq_b h hy
  have hfdQ : ∀ a', fd z (QF z SM.Db (Ybf SM W z)) a' x =
      fd z (Rbf SM W z) a' x + e0L (fd z (Pbf SM W z) a' x) := by
    intro a'
    have h1 : fd z (QF z SM.Db (Ybf SM W z)) a' x =
        fd z (fun y => Rbf SM W z y + e0L (Pbf SM W z y)) a' x := by
      unfold fd
      congr 1
      funext μ
      exact GenHarmonic.pd_eq_of_eventuallyEq hev μ
    rw [h1]
    have hg : DifferentiableAt ℝ (fun y => (e0L : S' →ₗ[ℝ] Fin 4 → S') (Pbf SM W z y)) x :=
      (LinearMap.toContinuousLinearMap (e0L (S₀ := S'))).differentiableAt.comp x
        ((contDiff_Pbf hW).differentiable (by simp) x)
    rw [fd_add (z := z) (f := Rbf SM W z) (g := fun y => e0L (Pbf SM W z y))
      ((contDiff_Rbf hW).differentiable (by simp) x) hg,
      fd_lin z (E := S') e0L ((contDiff_Pbf hW).differentiable (by simp) x)]
  -- expand the left side of `kap_DQ`
  have hQ0 : QF z SM.Db (Ybf SM W z) x = Rbf SM W z x + e0L (Pbf SM W z x) := hQx
  simp only [hfdQ, hQ0, map_add, smul_add, Finset.sum_add_distrib] at hmain
  rw [← hmain]
  -- the `P e_0` part
  have hP : kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' • ((liftFr SM.Db.Fr).c a' •
      e0L (fd z (Pbf SM W z) a' x))) + kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' •
      ((liftFr SM.Db.Fr).c a' • omegaP (ωF z SM.Db x) (ΓF z x) a' (e0L (Pbf SM W z x)))) =
      SM.Db.Fr.ε 0 • SM.Db.Fr.c 0 (∑ a', SM.Db.Fr.ε a' • SM.Db.Fr.c a' (fd z (Pbf SM W z) a' x +
        ωF z SM.Db x a' (Pbf SM W z x))) -
      ∑ A, ∑ a', (SM.Db.Fr.ε A * SM.Db.Fr.ε a' * ΓF z x a' A 0) •
        SM.Db.Fr.c A (SM.Db.Fr.c a' (Pbf SM W z x)) := by
    simp only [kap_apply, Finset.sum_apply, Pi.smul_apply, Module.End.smul_def, liftE_apply,
      omegaP_apply, e0L_apply, liftFr]
    have e1 : ∀ x2 x1 : Fin 4, (∑ x3, ΓF z x x2 x1 x3 • if x3 = 0 then Pbf SM W z x else 0) =
        ΓF z x x2 x1 0 • Pbf SM W z x := by
      intro x2 x1
      rw [Finset.sum_eq_single 0 (fun c _ hc => by rw [if_neg hc, smul_zero]) (by simp)]
      simp
    simp only [e1]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun x_1 => SM.Db.Fr.ε x_1 • (SM.Db.Fr.c x_1)
      (∑ x_2, SM.Db.Fr.ε x_2 • (SM.Db.Fr.c x_2) ((ωF z SM.Db x x_2) (if x_1 = 0 then Pbf SM W z x
        else 0) - ΓF z x x_2 x_1 0 • Pbf SM W z x)))]
    simp only [if_true, Fin.succ_ne_zero, if_false, map_zero, smul_zero, Finset.sum_const_zero,
      add_zero, zero_sub]
    rw [Fin.sum_univ_succ (f := fun A => ∑ a', (SM.Db.Fr.ε A * SM.Db.Fr.ε a' * ΓF z x a' A 0) •
      (SM.Db.Fr.c A) ((SM.Db.Fr.c a') (Pbf SM W z x)))]
    simp only [map_add, map_sub, map_neg, map_sum, map_smul, smul_add, smul_sub, smul_neg,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, smul_smul,
      Finset.smul_sum]
    have e2 : ∀ (i : Fin 3) (a' : Fin 4), SM.Db.Fr.ε i.succ * (SM.Db.Fr.ε a' * ΓF z x a' i.succ 0) =
        SM.Db.Fr.ε i.succ * SM.Db.Fr.ε a' * ΓF z x a' i.succ 0 := fun i a' => by ring
    have e3 : ∀ a' : Fin 4, SM.Db.Fr.ε 0 * (SM.Db.Fr.ε a' * ΓF z x a' 0 0) =
        SM.Db.Fr.ε 0 * SM.Db.Fr.ε a' * ΓF z x a' 0 0 := fun a' => by ring
    simp only [e2, e3]
    abel
  have hR : kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' • ((liftFr SM.Db.Fr).c a' •
      (fd z (Rbf SM W z) a' x + omegaP (ωF z SM.Db x) (ΓF z x) a' (Rbf SM W z x)))) =
      kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' • ((liftFr SM.Db.Fr).c a' • fd z (Rbf SM W z) a' x)) +
        kap SM.Db.Fr (∑ a', (liftFr SM.Db.Fr).ε a' • ((liftFr SM.Db.Fr).c a' •
          omegaP (ωF z SM.Db x) (ΓF z x) a' (Rbf SM W z x))) := by
    rw [← map_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [smul_add, smul_add]
  rw [hR, sub_eq_iff_eq_add.mp hP.symm]
  abel

end RenewalGeometry.GenCplP
