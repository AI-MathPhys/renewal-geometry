/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledCov

/-!
# The square of the twisted Dirac operator on spinor-valued one-form fields

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors: the evolution of the **normal prolongation defect**.  Along a smooth tuple `z`,
for a smooth `S₀`-valued one-form field `Y` on space-time:

* `Jx`, `dωP`, `ddY` — the jets at a point: the twisted Levi-Civita spin connection of `z`
  (`ActualJet.LJ`), the frame derivative of the one-form connection `ω'`, and the second frame
  derivatives of `Y`;
* **`fd_covF`** — the frame derivative of the field `∇_BY` is the jet `dcov` (product rule,
  `ActualJetBridge.Tuple.line_Xs`, `line_G`);
* **`fd_QF`** — the frame derivative of `𝒟'Y` is the jet `ddirac`;
* **`kap_DQ`** — if `κ(Y) = Σ_Aε_Ac_AY_A` vanishes near `x`, then
  `κ(Σ_aε_ac_a(e_a(𝒟'Y) + ω'_a𝒟'Y))(x) = ½Σ_{a,b}ε_aε_bκ(c_ac_bR'_{ab}Y(x))`: the Clifford
  contraction of `(𝒟')²Y` is of order zero (`GenSFJ.kap_dirac_dirac`).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplN

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (z : Tuple m V S S') (D : DiracData (MatLie m) V S₀)

/-- The twisted Levi-Civita spin-connection jets of `z` at `x`. -/
def Jx (x : ST 3) : LCJet D.Fr := (z.jet x).LJ D

theorem frU_eq (x : ST 3) (B μ : Fin 4) : (z.FJ x).e B μ = (frameU (z.gi x)).fr B μ :=
  GenGauss.e_eq_frameU z x B μ

theorem jetAF (x : ST 3) : (z.jet x).AF = frameU (z.gi x) := (ActualJet.frameU_eq' _).symm

theorem ωF_eq (x : ST 3) (B : Fin 4) : ωF z D x B = (Jx z D x).ω B := by
  unfold Jx
  rw [ActualJet.LJ_ω, jetAF]
  rfl

theorem ΓF_eq (x : ST 3) : ΓF z x = lcΓ D.Fr.ε (Jx z D x).G := by
  unfold Jx
  rw [ActualJet.LJ_G, jetAF]
  rfl

/-- The frame derivatives of the one-form connection `ω'`. -/
def dωP (x : ST 3) (a b : Fin 4) : Module.End ℝ (Fin 4 → S₀) :=
  liftE ((Jx z D x).dω a b) - formΓ (lcΓ D.Fr.ε ((Jx z D x).dG a) b)

/-- The second frame derivatives `e_ae_bY` of a one-form field. -/
def ddY (Y : ST 3 → Fin 4 → S₀) (x : ST 3) (a b : Fin 4) : Fin 4 → S₀ :=
  ActualJetSpinor.ddψf (z.FJ x) (fun γ => pd Y γ x) (fun δ γ => pd (pd Y γ) δ x) a b

/-- Frame derivatives of a differentiable field in the frame of the tuple. -/
theorem fd_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ST 3 → E) (B : Fin 4)
    (x : ST 3) : fd z f B x = ∑ γ, (z.FJ x).e B γ • pd f γ x := by
  unfold fd ActualJetGauge.fD
  simp only [frU_eq]

/-- **`∇_BY` as the spinor covariant derivative of the components minus the form connection.** -/
theorem covF_Xs {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (y : ST 3) (B A : Fin 4) :
    covF z D Y y B A = (z.jet y).Xs D (Y y A) (fun γ => pd (fun y => Y y A) γ y) B -
      ∑ C, ΓF z y B A C • Y y C := by
  rw [covF_apply, fd_apply z (hY.differentiable (by simp) y) B A, ωF_eq z D y B]
  unfold Jx ActualJet.Xs cov ActualJetSpinor.dψf
  rw [fd_eq_sum, show (z.jet y).FJ = z.FJ y from rfl]
  simp only [Module.End.smul_def]
  abel

theorem contDiff_comp_apply {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (A : Fin 4) :
    ContDiff ℝ ∞ (fun y => Y y A) := contDiff_pi.1 hY A

/-- `line_G` for the lowered connection coefficients `Γ_{BA}{}^C = ε_CG_{BAC}`. -/
theorem line_ΓF (x : ST 3) (δ B A C : Fin 4) :
    HasDerivAt (fun s : ℝ => ΓF z (x + s • ev δ) B A C)
      (lorentzSign C * (z.FJ x).dGc δ B A C) 0 := by
  have h := (z.line_G x δ B A C).const_mul (lorentzSign C)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show ΓF z (x + s • ev δ) B A C = lorentzSign C * (z.FJ (x + s • ev δ)).G B A C
  have hG := ActualJet.G_eq (z.jet (x + s • ev δ))
  unfold ΓF lcΓ
  rw [← jetAF]
  exact congrArg (lorentzSign C * ·) (congrFun (congrFun (congrFun hG B) A) C).symm

theorem ΓF_eq_G (y : ST 3) (B A C : Fin 4) :
    ΓF z y B A C = lorentzSign C * (z.FJ y).G B A C := by
  have hG := ActualJet.G_eq (z.jet y)
  unfold ΓF lcΓ
  rw [← jetAF]
  exact congrArg (lorentzSign C * ·) (congrFun (congrFun (congrFun hG B) A) C).symm

theorem contDiff_ΓF (B A C : Fin 4) : ContDiff ℝ ∞ (fun y => ΓF z y B A C) := by
  simp only [ΓF_eq_G]
  exact contDiff_const.mul (z.contDiff_G B A C)

theorem contDiff_covF {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (B A : Fin 4) :
    ContDiff ℝ ∞ (fun y => covF z D Y y B A) := by
  simp only [covF_Xs z D hY]
  refine (z.contDiff_Xs D (contDiff_comp_apply hY A) B).sub (ContDiff.sum fun C _ => ?_)
  exact (contDiff_ΓF z B A C).smul (contDiff_comp_apply hY C)

theorem pd_apply_smooth {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3) (γ : Fin 4)
    (A : Fin 4) : pd (fun y => Y y A) γ x = pd Y γ x A :=
  pd_apply (hY.differentiable (by simp) x) γ A

theorem pd_pd_apply_smooth {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3)
    (δ γ : Fin 4) (A : Fin 4) :
    pd (pd (fun y => Y y A) γ) δ x = pd (pd Y γ) δ x A := by
  have h1 : pd (fun y => Y y A) γ = fun y => pd Y γ y A :=
    funext fun y => pd_apply_smooth hY y γ A
  rw [h1]
  exact pd_apply ((contDiff_pd hY γ).differentiable (by simp) x) δ A

/-- **The frame derivative of `∇_BY` is the jet `dcov`.** -/
theorem fd_covF {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3) (a B : Fin 4) :
    fd z (fun y => covF z D Y y B) a x =
      dcov (omegaP (ωF z D x) (ΓF z x)) (dωP z D x) (Y x) (fun B => fd z Y B x) (ddY z Y x) a B := by
  funext A
  have hcov : ContDiff ℝ ∞ (fun y => covF z D Y y B) := contDiff_pi.2 fun A =>
    contDiff_covF z D hY B A
  rw [fd_apply z (hcov.differentiable (by simp) x) a A]
  -- the coordinate derivatives of the component
  have hψ := contDiff_comp_apply hY A
  have hpd : ∀ γ, pd (fun y => covF z D Y y B A) γ x =
      (z.jet x).dXs D (Y x A) (fun γ => pd (fun y => Y y A) γ x)
        (fun δ γ => pd (pd (fun y => Y y A) γ) δ x) γ B -
        ∑ C, ((lorentzSign C * (z.FJ x).dGc γ B A C) • Y x C + ΓF z x B A C • pd Y γ x C) := by
    intro γ
    refine pd_eq_of_line ((contDiff_covF z D hY B A).differentiable (by simp) x) ?_
    have h1 := z.line_Xs x γ D hψ B
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun C _ =>
      (line_ΓF z x γ B A C).fun_smul (hasDerivAt_line0_apply (hY.differentiable (by simp) x) γ C)
    have h := h1.fun_sub h2
    simp only [zero_smul, add_zero] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
    · exact covF_Xs z D hY _ B A
    · congr 1
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [add_comm]
  rw [fd_eq_sum]
  simp only [hpd, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_add]
  -- the spinor part: `dcov_eq`
  have hd := ActualJetSpinor.dcov_eq (z.FJ x) D.Fr ((z.jet x).hε D) (fun μ => D.ρ (z.A x μ))
    (fun γ μ => D.ρ (pd z.A γ x μ)) (fun μ b => D.comm (z.A x μ) b) (Y x A)
    (fun γ => pd (fun y => Y y A) γ x) (fun δ γ => pd (pd (fun y => Y y A) γ) δ x) a B
  have hdX : ∀ δ, (z.jet x).dXs D (Y x A) (fun γ => pd (fun y => Y y A) γ x)
      (fun δ γ => pd (pd (fun y => Y y A) γ) δ x) δ B =
      ActualJetSpinor.dXc (z.FJ x) D.Fr ((z.jet x).hε D) (fun μ => D.ρ (z.A x μ))
        (fun γ μ => D.ρ (pd z.A γ x μ)) (fun μ b => D.comm (z.A x μ) b) (Y x A)
        (fun γ => pd (fun y => Y y A) γ x) (fun δ γ => pd (pd (fun y => Y y A) γ) δ x) δ B :=
    fun δ => rfl
  simp only [hdX]
  rw [← hd]
  -- the right side, componentwise
  have hJ : (z.FJ x).toLCJet D.Fr ((z.jet x).hε D) (fun μ => D.ρ (z.A x μ))
      (fun γ μ => D.ρ (pd z.A γ x μ)) (fun μ b => D.comm (z.A x μ) b) = Jx z D x := rfl
  rw [hJ]
  unfold dcov dωP
  simp only [Pi.add_apply, Module.End.smul_def, LinearMap.sub_apply, liftE_apply, formΓ_apply,
    Pi.sub_apply, omegaP_apply]
  have hε : D.Fr.ε = lorentzSign := (z.jet x).hε D
  have hddψ : ActualJetSpinor.ddψf (z.FJ x) (fun γ => pd (fun y => Y y A) γ x)
      (fun δ γ => pd (pd (fun y => Y y A) γ) δ x) a B = ddY z Y x a B A := by
    unfold ddY ActualJetSpinor.ddψf
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, pd_apply_smooth hY,
      pd_pd_apply_smooth hY]
  have hdψ : ∀ B', ActualJetSpinor.dψf (z.FJ x) (fun γ => pd (fun y => Y y A) γ x) B' =
      fd z Y B' x A := by
    intro B'
    rw [fd_eq_sum]
    unfold ActualJetSpinor.dψf
    simp only [Finset.sum_apply, Pi.smul_apply, pd_apply_smooth hY]
  rw [hddψ, hdψ a, ← ωF_eq]
  have hsum1 : ∑ γ, ∑ C, (z.FJ x).e a γ • (lorentzSign C * (z.FJ x).dGc γ B A C) • Y x C =
      ∑ C, lcΓ D.Fr.ε ((Jx z D x).dG a) B A C • Y x C := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    have e : lcΓ D.Fr.ε ((Jx z D x).dG a) B A C =
        lorentzSign C * ∑ δ, (z.FJ x).e a δ * (z.FJ x).dGc δ B A C := by
      unfold lcΓ; rw [hε]; rfl
    rw [e, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [smul_smul]
    congr 1
    ring
  have hsum2 : ∑ γ, ∑ C, (z.FJ x).e a γ • ΓF z x B A C • pd Y γ x C =
      ∑ C, ΓF z x B A C • fd z Y a x C := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [fd_eq_sum, Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Pi.smul_apply, smul_comm]
  simp only [Finset.sum_add_distrib]
  rw [hsum1, hsum2]
  abel

/-- Frame derivatives commute with fixed linear maps (finite dimension). -/
theorem fd_lin {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F) {f : ST 3 → E} {x : ST 3}
    (hf : DifferentiableAt ℝ f x) (B : Fin 4) :
    fd z (fun y => L (f y)) B x = L (fd z f B x) := by
  rw [fd_eq_sum, fd_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have h := GenHarmonic.pd_clm (LinearMap.toContinuousLinearMap L) hf γ
  rw [map_smul, show (fun y => L (f y)) = fun y => (LinearMap.toContinuousLinearMap L) (f y)
    from rfl, h]
  rfl

theorem fd_sum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : Finset ι)
    {f : ι → ST 3 → E} {x : ST 3} (hf : ∀ i ∈ t, DifferentiableAt ℝ (f i) x) (B : Fin 4) :
    fd z (fun y => ∑ i ∈ t, f i y) B x = ∑ i ∈ t, fd z (f i) B x := by
  rw [fd_eq_sum]
  simp only [fd_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  unfold SobolevOpen.pd
  rw [fderiv_fun_sum hf]
  simp

theorem fd_eq_zero_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ST 3 → E} {x : ST 3} (h : f =ᶠ[𝓝 x] 0) (B : Fin 4) : fd z f B x = 0 := by
  rw [fd_eq_sum]
  simp [GenConstraint.pd_eq_zero_of_eventually h]

theorem contDiff_QF {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun y => QF z D Y y) := by
  refine contDiff_pi.2 fun A => ?_
  simp only [QF_apply]
  refine ContDiff.sum fun B _ => ContDiff.const_smul _ ?_
  exact (LinearMap.toContinuousLinearMap (D.Fr.c B)).contDiff.comp (contDiff_covF z D hY B A)

/-- **The frame derivative of `𝒟'Y` is the jet `ddirac`.** -/
theorem fd_QF {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (x : ST 3) (a : Fin 4) :
    fd z (QF z D Y) a x = ddirac (liftFr D.Fr) (omegaP (ωF z D x) (ΓF z x)) (dωP z D x) (Y x)
      (fun B => fd z Y B x) (ddY z Y x) a := by
  have hcov : ∀ B, ContDiff ℝ ∞ (fun y => covF z D Y y B) := fun B =>
    contDiff_pi.2 fun A => contDiff_covF z D hY B A
  have hQ : QF z D Y = fun y => ∑ B, (D.Fr.ε B • liftE (D.Fr.c B)) (covF z D Y y B) := by
    funext y A
    rw [QF_apply, Finset.sum_apply]
    rfl
  have hdiff : ∀ B ∈ (Finset.univ : Finset (Fin 4)), DifferentiableAt ℝ
      (fun y => (D.Fr.ε B • liftE (D.Fr.c B)) (covF z D Y y B)) x := fun B _ =>
    (LinearMap.toContinuousLinearMap (D.Fr.ε B • liftE (D.Fr.c B))).differentiableAt.comp x
      ((hcov B).differentiable (by simp) x)
  rw [hQ, fd_sum z Finset.univ (f := fun B y => (D.Fr.ε B • liftE (D.Fr.c B)) (covF z D Y y B))
    hdiff a]
  unfold ddirac
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [fd_lin z _ ((hcov B).differentiable (by simp) x) a, fd_covF z D hY x a B]
  rfl

theorem hcl_x (x : ST 3) (a b : Fin 4) :
    ωF z D x a * D.Fr.c b - D.Fr.c b * ωF z D x a = ∑ c, ΓF z x a b c • D.Fr.c c := by
  rw [ΓF_eq z D x]
  simp only [ωF_eq]
  exact (Jx z D x).clifford_parallel a b

theorem hmc_x (x : ST 3) (a b c : Fin 4) :
    D.Fr.ε c * ΓF z x a b c = -(D.Fr.ε b * ΓF z x a c b) := by
  rw [ΓF_eq z D x]
  exact (Jx z D x).metric_compat a b c

/-- `κ(∇_bY) = e_b(κY) + ω_bκ(Y)`. -/
theorem kap_covF {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) (y : ST 3) (b : Fin 4) :
    kap D.Fr (covF z D Y y b) = fd z (fun y => kap D.Fr (Y y)) b y + ωF z D y b (kap D.Fr (Y y)) := by
  unfold covF cov
  rw [map_add, Module.End.smul_def, kap_omegaP D.Fr (ωF z D y) (ΓF z y) (hcl_x z D y)
    (hmc_x z D y), fd_lin z (E := Fin 4 → S₀) (kap D.Fr) (hY.differentiable (by simp) y)]

/-- **The Clifford contraction of `(𝒟')²Y` is of order zero** where `κ(Y) ≡ 0` near `x`. -/
theorem kap_DQ {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) {x : ST 3}
    (hκ : (fun y => kap D.Fr (Y y)) =ᶠ[𝓝 x] 0) :
    kap D.Fr (∑ a, (liftFr D.Fr).ε a • ((liftFr D.Fr).c a •
        (fd z (QF z D Y) a x + omegaP (ωF z D x) (ΓF z x) a (QF z D Y x)))) =
      (1 / 2 : ℝ) • ∑ a, ∑ b, (D.Fr.ε a * D.Fr.ε b) • kap D.Fr (((liftFr D.Fr).c a *
        (liftFr D.Fr).c b) • (curv (lcΛ D.Fr.ε (Jx z D x).G) (omegaP (ωF z D x) (ΓF z x))
          (dωP z D x) a b • Y x)) := by
  have hcov0 : ∀ᶠ y in 𝓝 x, ∀ b, kap D.Fr (covF z D Y y b) = 0 := by
    have hev := hκ.eventually_nhds
    filter_upwards [hev] with y hy b
    rw [kap_covF z D hY y b, fd_eq_zero_of_eventually z hy b]
    have : kap D.Fr (Y y) = 0 := hy.self_of_nhds
    rw [this, map_zero, add_zero]
  have hk1 : ∀ b, kap D.Fr (cov (omegaP (ωF z D x) (ΓF z x)) (Y x) (fun B => fd z Y B x) b) = 0 :=
    fun b => hcov0.self_of_nhds b
  have hk2 : ∀ a b, kap D.Fr (dcov (omegaP (ωF z D x) (ΓF z x)) (dωP z D x) (Y x)
      (fun B => fd z Y B x) (ddY z Y x) a b) = 0 := by
    intro a b
    have hcovs : ContDiff ℝ ∞ (fun y => covF z D Y y b) := contDiff_pi.2 fun A =>
      contDiff_covF z D hY b A
    rw [← fd_covF z D hY x a b,
      ← fd_lin z (E := Fin 4 → S₀) (kap D.Fr) (hcovs.differentiable (by simp) x)]
    exact fd_eq_zero_of_eventually z (hcov0.mono fun y hy => hy b) a
  have hψ : ∀ a b, ddY z Y x a b - ddY z Y x b a =
      ∑ c, lcΛ D.Fr.ε (Jx z D x).G a b c • (fun B => fd z Y B x) c := by
    intro a b
    have hs : ∀ δ γ, pd (pd Y γ) δ x = pd (pd Y δ) γ x := fun δ γ =>
      pd_pd_comm' hY γ δ x
    have h := FrameJet.hψ_frame (z.FJ x) (fun γ => pd Y γ x) (fun δ γ => pd (pd Y γ) δ x) hs a b
    unfold ddY ActualJetSpinor.ddψf
    rw [h]
    have hε : (z.FJ x).ε = D.Fr.ε := ((z.jet x).hε D).symm
    rw [hε]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = lcΛ D.Fr.ε (Jx z D x).G a b c • fd z Y c x
    rw [fd_eq_sum]
    rfl
  have htf : ∀ a b c, ΓF z x a b c - ΓF z x b a c = lcΛ D.Fr.ε (Jx z D x).G a b c := by
    intro a b c
    rw [ΓF_eq z D x]
    rfl
  have hmain := kap_dirac_dirac D.Fr (lcΛ D.Fr.ε (Jx z D x).G) (ΓF z x) (ωF z D x) (dωP z D x)
    (Y x) (fun B => fd z Y B x) (ddY z Y x) hψ htf (hcl_x z D x) (hmc_x z D x) hk1 hk2
  rw [← hmain]
  congr 2
  funext a
  congr 2
  unfold covDirac
  rw [fd_QF z D hY x a]
  rfl

end RenewalGeometry.GenCplN
