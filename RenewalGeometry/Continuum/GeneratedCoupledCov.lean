/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledXRows
import RenewalGeometry.Continuum.GeneratedSpinorFormJet

/-!
# The spinor defect rows in covariant form

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  Along the head tuple `z` of a coupled solution:

* `fd` — frame derivatives `e_B(f) = Σ_μ e_B{}^μ∂_μf` in the adapted frame `frameU(g⁻¹)`;
* `ωF`, `ΓF` — the twisted spin connection and the Levi-Civita frame connection coefficients
  `Γ_{BA}{}^C = ε_CG_{BAC}` of `z`;
* `covF` — the twisted covariant derivative `∇_BY` of an `S`-valued one-form field;
* `QF` — the twisted Dirac operator on one-forms `(𝒟'Y)_A = Σ_Bε_Bc_B(∇_BY)_A`;
* `RF` — `R_A = 𝓜(H)Y_A - ½Σ_bε_bS_{Ab}c_bΨ` (`ricTerm` of `∇_{(μ}C_{ν)}`);
* **`q_row`** — the spinor rows of the coupled defect system are exactly
  `(𝒟'Y)_a = R_a` for `a = 1, 2, 3` (`GenCplX.x_row_cpl` divided by `-Nc_0`).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplCov

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState GenConstraint
  GenSpinorDefect GenHiggsDefect SymHypEnergy GenCplRows GenStress GenCplEin GenCplX GenSFJ

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (z : Tuple m V S S')

/-- Frame derivatives `e_B(f)(x) = Σ_μ e_B{}^μ(x)∂_μf(x)`. -/
def fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ST 3 → E) (B : Fin 4)
    (x : ST 3) : E :=
  ActualJetGauge.fD (frameU (z.gi x)) (fun μ => pd f μ x) B

/-- The twisted spin connection of `z` on a Dirac block. -/
def ωF (D : DiracData (MatLie m) V S₀) (x : ST 3) (B : Fin 4) : Module.End ℝ S₀ :=
  omegaU D (z.g x) (z.gi x) (z.dg x) (frameU (z.gi x)).fr (z.de x) (z.A x) B

/-- The Levi-Civita frame connection coefficients `Γ_{BA}{}^C` of `z`. -/
def ΓF (x : ST 3) (B A C : Fin 4) : ℝ :=
  lcΓ lorentzSign (Gfun (z.g x) (z.gi x) (z.dg x) (frameU (z.gi x)).fr (z.de x)) B A C

/-- **The twisted covariant derivative of a spinor-valued one-form field** `∇_BY`. -/
def covF (D : DiracData (MatLie m) V S₀) (Y : ST 3 → Fin 4 → S₀) (x : ST 3) (B : Fin 4) :
    Fin 4 → S₀ :=
  cov (omegaP (ωF z D x) (ΓF z x)) (Y x) (fun B => fd z Y B x) B

/-- **The twisted Dirac operator on one-forms** `(𝒟'Y)_A = Σ_Bε_Bc_B(∇_BY)_A`. -/
def QF (D : DiracData (MatLie m) V S₀) (Y : ST 3 → Fin 4 → S₀) (x : ST 3) : Fin 4 → S₀ :=
  dirac (liftFr D.Fr) (omegaP (ωF z D x) (ΓF z x)) (Y x) (fun B => fd z Y B x)

/-- The frame components `S_{Ab}` of `∇_{(μ}C_{ν)}`. -/
def sD (x : ST 3) : Fin 4 → Fin 4 → ℝ := fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν

/-- **The forcing of the covariant spinor rows** `R_A = 𝓜(H)Y_A - ricTerm(∇_{(μ}C_{ν)})_A`. -/
def RF (D : DiracData (MatLie m) V S₀) (ψ : ST 3 → S₀) (Y : ST 3 → Fin 4 → S₀) (x : ST 3)
    (A : Fin 4) : S₀ :=
  mass D.m0 D.L (z.H x) (Y x A) - ricTerm D (z.g x) (z.gi x) (frameU (z.gi x)) (sD z x) (ψ x) A

theorem QF_apply (D : DiracData (MatLie m) V S₀) (Y : ST 3 → Fin 4 → S₀) (x : ST 3) (A : Fin 4) :
    QF z D Y x A = ∑ B, D.Fr.ε B • D.Fr.c B (covF z D Y x B A) := by
  unfold QF dirac
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

theorem covF_apply (D : DiracData (MatLie m) V S₀) (Y : ST 3 → Fin 4 → S₀) (x : ST 3)
    (B A : Fin 4) :
    covF z D Y x B A = fd z Y B x A + (ωF z D x B (Y x A) - ∑ C, ΓF z x B A C • Y x C) := by
  unfold covF cov
  simp only [Pi.add_apply, Module.End.smul_def, omegaP_apply]

/-- Frame derivatives of a component of a differentiable vector field. -/
theorem fd_apply {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ST 3 → ι → E} {x : ST 3} (hf : DifferentiableAt ℝ f x) (B : Fin 4) (i : ι) :
    fd z f B x i = fd z (fun y => f y i) B x := by
  unfold fd ActualJetGauge.fD
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pd_apply hf μ i]

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {a b : ℝ}

/-- `c_0²` cancels: `c_0(c_0v) = v`. -/
theorem c0c0 (D : DiracData (MatLie m) V S₀) (v : S₀) : D.Fr.c 0 (D.Fr.c 0 v) = v := by
  rw [← Module.End.mul_apply, c0_mul_c0, Module.End.one_apply]

/-- **The spinor rows in covariant form**: `(𝒟'Y)_a = R_a`, `a = 1, 2, 3`. -/
theorem q_row (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (a' : Fin 3) :
    QF z SM.D (Yf SM W z) x a'.succ = RF z SM.D z.ψ (Yf SM W z) x a'.succ := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hdYt : DifferentiableAt ℝ (Yt SM W z) x := by
    have : Yt SM W z = fun y => prX m V S S' (W y - stateF SM z y) := by
      funext y; simp [Yt, prX]
    rw [this]
    exact (prX m V S S').differentiableAt.comp x (hdW.sub hdU)
  have hdYf : DifferentiableAt ℝ (Yf SM W z) x := by
    have : Yf SM W z = fun y => oneForm SM.D (Yt SM W z y) := rfl
    rw [this]
    let L : (Fin 3 → S) →ₗ[ℝ] (Fin 4 → S) :=
      { toFun := oneForm SM.D
        map_add' := fun u v => by
          funext c
          induction c using Fin.cases with
          | zero => simp [oneForm, smul_add, Finset.sum_add_distrib, Module.End.smul_def]
          | succ c => rfl
        map_smul' := fun r u => by
          funext c
          induction c using Fin.cases with
          | zero => simp [oneForm, Finset.smul_sum, Module.End.smul_def]
          | succ c => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt.comp x hdYt
  -- frame derivatives of the tangential components
  have hfd : ∀ B, fd z (Yf SM W z) B x a'.succ = ActualJetGauge.fD (frameU (z.gi x))
      (fun μ => pd (Yt SM W z) μ x a') B := by
    intro B
    rw [fd_apply z hdYf B a'.succ]
    unfold fd
    congr 1
    funext μ
    have : (fun y => Yf SM W z y a'.succ) = fun y => Yt SM W z y a' := rfl
    rw [this, ← pd_apply hdYt μ a']
  have hrow := x_row_cpl h hx a'
  set AF := frameU (z.gi x) with hAF
  set X : Fin 4 → S := fun μ => pd (Yt SM W z) μ x a' with hX
  -- the coordinate operator in frame form
  have hL : pd (Yt SM W z) 0 x a' + ∑ j : Fin 3, diracP AF SM.D.Fr j (pd (Yt SM W z) j.succ x a') =
      AF.N • (ActualJetGauge.fD AF X 0 - SM.D.Fr.c 0 • ∑ i : Fin 3, SM.D.Fr.c i.succ •
        ActualJetGauge.fD AF X i.succ) := by
    have h0 := ActualJetGauge.N_fD_zero AF X
    have hs := fun i => ActualJetGauge.fD_succ AF X i
    simp only [diracP, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [smul_sub, h0]
    simp only [hs, Finset.smul_sum, smul_sub, Module.End.smul_def]
    have e : ∀ i j, AF.N • SM.D.Fr.c 0 (SM.D.Fr.c i.succ (AF.E i j • X j.succ)) =
        AF.N • AF.E i j • (SM.D.Fr.c 0 * SM.D.Fr.c i.succ) (X j.succ) := by
      intro i j
      rw [map_smul, map_smul, Module.End.mul_apply]
    simp only [e, smul_smul]
    rw [Finset.sum_comm (f := fun i j => (AF.N * AF.E i j) • (SM.D.Fr.c 0 * SM.D.Fr.c i.succ)
      (X j.succ))]
    simp only [X, Finset.smul_sum, smul_smul]
    abel
  rw [hL] at hrow
  have hN := AF.N_pos
  have hrow' : ActualJetGauge.fD AF X 0 - SM.D.Fr.c 0 • ∑ i : Fin 3, SM.D.Fr.c i.succ •
      ActualJetGauge.fD AF X i.succ =
      XrowFX SM.D (z.g x) (z.gi x) (z.dg x) AF (z.de x) (z.A x) (z.H x) (Yf SM W z x) a'.succ +
        SM.D.Fr.c 0 • ricTerm SM.D (z.g x) (z.gi x) AF (sD z x) (z.ψ x) a'.succ :=
    smul_right_injective _ hN.ne' hrow
  -- the covariant form
  rw [QF_apply, Fin.sum_univ_succ]
  simp only [covF_apply, hfd]
  unfold XrowFX at hrow'
  unfold RF
  have hε0 : SM.D.Fr.ε 0 = -1 := SM.D.lorentz.1
  have hεi : ∀ i : Fin 3, SM.D.Fr.ε i.succ = 1 := SM.D.lorentz.2
  simp only [hε0, hεi, neg_smul, one_smul]
  -- apply `c_0` to the row
  have hc := congrArg (SM.D.Fr.c 0) hrow'
  simp only [map_sub, map_add, map_neg, Module.End.smul_def, c0c0, map_sum] at hc
  have hω : ∀ B, omegaU SM.D (z.g x) (z.gi x) (z.dg x) AF.fr (z.de x) (z.A x) B = ωF z SM.D x B :=
    fun B => rfl
  have hΓ : ∀ B A C, lcΓ lorentzSign (Gfun (z.g x) (z.gi x) (z.dg x) AF.fr (z.de x)) B A C =
      ΓF z x B A C := fun B A C => rfl
  simp only [hω, hΓ] at hc
  simp only [map_sub, map_add, map_neg, map_sum, map_smul, Finset.sum_add_distrib, smul_add,
    Finset.smul_sum, Finset.sum_sub_distrib, smul_sub] at hc ⊢
  simp only [← hAF] at hc ⊢
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at hc
  rw [← neg_eq_zero, ← hc]
  abel

/-- **The dual spinor rows in covariant form**: `(𝒟'Y)_a = R_a`, `a = 1, 2, 3`. -/
theorem q_row_b (h : CplSol SM W z a b) {x : ST 3} (hx : x ∈ openSlab a b) (a' : Fin 3) :
    QF z SM.Db (Ybf SM W z) x a'.succ = RF z SM.Db z.ψb (Ybf SM W z) x a'.succ := by
  have hO := isOpen_openSlab (d := 3) a b
  have hW1 : ContDiffOn ℝ 1 W (openSlab a b) := h.ms.smooth.of_le (by norm_cast)
  have hdW : DifferentiableAt ℝ W x := GenHarmonic.diffAt_of_contDiffOn hO hW1 one_ne_zero hx
  have hdU : DifferentiableAt ℝ (stateF SM z) x := (contDiff_stateF SM z).differentiable (by simp) x
  have hdYbt : DifferentiableAt ℝ (Ybt SM W z) x := by
    have : Ybt SM W z = fun y => prXb m V S S' (W y - stateF SM z y) := by
      funext y; simp [Ybt, prXb]
    rw [this]
    exact (prXb m V S S').differentiableAt.comp x (hdW.sub hdU)
  have hdYbf : DifferentiableAt ℝ (Ybf SM W z) x := by
    have : Ybf SM W z = fun y => oneForm SM.Db (Ybt SM W z y) := rfl
    rw [this]
    let L : (Fin 3 → S') →ₗ[ℝ] (Fin 4 → S') :=
      { toFun := oneForm SM.Db
        map_add' := fun u v => by
          funext c
          induction c using Fin.cases with
          | zero => simp [oneForm, smul_add, Finset.sum_add_distrib, Module.End.smul_def]
          | succ c => rfl
        map_smul' := fun r u => by
          funext c
          induction c using Fin.cases with
          | zero => simp [oneForm, Finset.smul_sum, Module.End.smul_def]
          | succ c => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt.comp x hdYbt
  -- frame derivatives of the tangential components
  have hfd : ∀ B, fd z (Ybf SM W z) B x a'.succ = ActualJetGauge.fD (frameU (z.gi x))
      (fun μ => pd (Ybt SM W z) μ x a') B := by
    intro B
    rw [fd_apply z hdYbf B a'.succ]
    unfold fd
    congr 1
    funext μ
    have : (fun y => Ybf SM W z y a'.succ) = fun y => Ybt SM W z y a' := rfl
    rw [this, ← pd_apply hdYbt μ a']
  have hrow := x_row_cpl_b h hx a'
  set AF := frameU (z.gi x) with hAF
  set X : Fin 4 → S' := fun μ => pd (Ybt SM W z) μ x a' with hX
  -- the coordinate operator in frame form
  have hL : pd (Ybt SM W z) 0 x a' + ∑ j : Fin 3, diracP AF SM.Db.Fr j (pd (Ybt SM W z) j.succ x a') =
      AF.N • (ActualJetGauge.fD AF X 0 - SM.Db.Fr.c 0 • ∑ i : Fin 3, SM.Db.Fr.c i.succ •
        ActualJetGauge.fD AF X i.succ) := by
    have h0 := ActualJetGauge.N_fD_zero AF X
    have hs := fun i => ActualJetGauge.fD_succ AF X i
    simp only [diracP, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [smul_sub, h0]
    simp only [hs, Finset.smul_sum, smul_sub, Module.End.smul_def]
    have e : ∀ i j, AF.N • SM.Db.Fr.c 0 (SM.Db.Fr.c i.succ (AF.E i j • X j.succ)) =
        AF.N • AF.E i j • (SM.Db.Fr.c 0 * SM.Db.Fr.c i.succ) (X j.succ) := by
      intro i j
      rw [map_smul, map_smul, Module.End.mul_apply]
    simp only [e, smul_smul]
    rw [Finset.sum_comm (f := fun i j => (AF.N * AF.E i j) • (SM.Db.Fr.c 0 * SM.Db.Fr.c i.succ)
      (X j.succ))]
    simp only [X, Finset.smul_sum, smul_smul]
    abel
  rw [hL] at hrow
  have hN := AF.N_pos
  have hrow' : ActualJetGauge.fD AF X 0 - SM.Db.Fr.c 0 • ∑ i : Fin 3, SM.Db.Fr.c i.succ •
      ActualJetGauge.fD AF X i.succ =
      XrowFX SM.Db (z.g x) (z.gi x) (z.dg x) AF (z.de x) (z.A x) (z.H x) (Ybf SM W z x) a'.succ +
        SM.Db.Fr.c 0 • ricTerm SM.Db (z.g x) (z.gi x) AF (sD z x) (z.ψb x) a'.succ :=
    smul_right_injective _ hN.ne' hrow
  -- the covariant form
  rw [QF_apply, Fin.sum_univ_succ]
  simp only [covF_apply, hfd]
  unfold XrowFX at hrow'
  unfold RF
  have hε0 : SM.Db.Fr.ε 0 = -1 := SM.Db.lorentz.1
  have hεi : ∀ i : Fin 3, SM.Db.Fr.ε i.succ = 1 := SM.Db.lorentz.2
  simp only [hε0, hεi, neg_smul, one_smul]
  -- apply `c_0` to the row
  have hc := congrArg (SM.Db.Fr.c 0) hrow'
  simp only [map_sub, map_add, map_neg, Module.End.smul_def, c0c0, map_sum] at hc
  have hω : ∀ B, omegaU SM.Db (z.g x) (z.gi x) (z.dg x) AF.fr (z.de x) (z.A x) B = ωF z SM.Db x B :=
    fun B => rfl
  have hΓ : ∀ B A C, lcΓ lorentzSign (Gfun (z.g x) (z.gi x) (z.dg x) AF.fr (z.de x)) B A C =
      ΓF z x B A C := fun B A C => rfl
  simp only [hω, hΓ] at hc
  simp only [map_sub, map_add, map_neg, map_sum, map_smul, Finset.sum_add_distrib, smul_add,
    Finset.smul_sum, Finset.sum_sub_distrib, smul_sub] at hc ⊢
  simp only [← hAF] at hc ⊢
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at hc
  rw [← neg_eq_zero, ← hc]
  abel

end RenewalGeometry.GenCplCov
