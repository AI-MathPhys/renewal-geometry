/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDefiningJetPropagation
import RenewalGeometry.Continuum.KatoSmoothness

/-!
# The shift-transported actual-jet system and its Kato realization

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`,
`lem:generated-physical-identification` (`app:generated-dynamics`).

## The modified head rows

The head rows of the metric and of the Higgs field in `eq:actual-jet-writer` are algebraic,
`∂_tg = Np + βʲ∂̃_jg`, `∂_tH = NΠ + βʲD̃_jH`, with the spatial derivatives *reconstructed from the
auxiliary variables* `q`, `Q`.  For these rows the defining-jet defects obey weakly hyperbolic
systems (`GenDefJet`).  The **shift-transported** head rows
`∂_tg - βʲ∂_jg = Np`, `∂_tH - βʲD_jH = NΠ` (`D_jH = ∂_jH + [A_j, H]`) have the symmetric principal
parts `-βʲ` on the `g`- and `H`-blocks (`princM`, `princM_symm`) and **agree with the original rows
on actual-jet states** (`extra_eq_actual`, **`symEqAtM_iff`**): the actual-jet state of a smooth
tuple solves the modified system at a point iff it solves the original one.

## Main results

* `princM`, `princLM`, `FsysM`, `SymEqAtM` — the modified principal operators, forcing and system;
* **`symEqAtM_iff`** — `SymEqAtM SM z x ↔ SymEqAt SM z x`;
* `tauP` — the transposition of the metric blocks `(g, p, q)` (an involutive isometry of the block
  inner product), the modified principal operators commute with it;
* **`modified_kato_realization`** — Euclidean coordinates and globally smooth, symmetric,
  `τ`-equivariant coefficient maps which on the symmetric states of a compact chart set `K` are
  the modified actual-jet principal operators and forcing (the forcing at symmetric states is
  symmetric for symmetric gauge/Higgs forms and vanishing Dirac stress, `Decoupled`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.AJKatoMod

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenConstraint TwistedHalfRicci
  SpinorProlongation ActualJetSpinor

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The modified principal operators and forcing -/

section Defs

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]
variable {S : Type*} [AddCommGroup S] [Module ℝ S]
variable {S' : Type*} [AddCommGroup S'] [Module ℝ S']

/-- **The modified principal operators**: those of `eq:actual-jet-writer` plus the shift transport
`-βʲ` on the metric and Higgs head blocks. -/
def princM (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (Frb : CliffordFrame (Fin 4) (Module.End ℝ S')) (j : Fin 3) (W : State 𝔤 V S S') :
    State 𝔤 V S S' :=
  { princ AF Fr Frb j W with
    g := fun μ ν => -(AF.β j * W.g μ ν)
    H := -(AF.β j • W.H) }

/-- **The modified forcing**: `N p` in the metric head row, `NΠ + βʲ[A_j, H]` in the Higgs head
row, the forcing `𝓕` of `eq:actual-jet-writer` in all other rows. -/
def FsysM (SM : SMData 𝔤 V S S') (U : State 𝔤 V S S') : State 𝔤 V S S' :=
  { Fsys SM U with
    g := fun μ ν => (frameU (ginvOf U.g)).N * U.p μ ν
    H := (frameU (ginvOf U.g)).N • U.Pm + ∑ j : Fin 3, (frameU (ginvOf U.g)).β j • ⁅U.A j, U.H⁆ }

theorem princM_symm (AF : AdaptedFrame) (Fr : CliffordFrame (Fin 4) (Module.End ℝ S))
    (Frb : CliffordFrame (Fin 4) (Module.End ℝ S')) (bG : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (hc0 : ∀ x y, bS (Fr.c 0 • x) y = bS x (Fr.c 0 • y))
    (hci : ∀ (i : Fin 3) x y, bS (Fr.c i.succ • x) y = -bS x (Fr.c i.succ • y))
    (hc0b : ∀ x y, bS' (Frb.c 0 • x) y = bS' x (Frb.c 0 • y))
    (hcib : ∀ (i : Fin 3) x y, bS' (Frb.c i.succ • x) y = -bS' x (Frb.c i.succ • y))
    (j : Fin 3) (W W' : State 𝔤 V S S') :
    ipState bG bV bS bS' (princM AF Fr Frb j W) W' =
      ipState bG bV bS bS' W (princM AF Fr Frb j W') := by
  have h := princ_symm AF Fr Frb bG bV bS bS' hc0 hci hc0b hcib j W W'
  have e1 : ipState bG bV bS bS' (princM AF Fr Frb j W) W' =
      ipState bG bV bS bS' (ActualJetSystem.princ AF Fr Frb j W) W' +
        (∑ μ, ∑ ν, (-(AF.β j * W.g μ ν)) * W'.g μ ν + bV (-(AF.β j • W.H)) W'.H) := by
    unfold ipState
    simp only [princM, ActualJetSystem.princ, zero_mul, map_zero, LinearMap.zero_apply,
      Finset.sum_add_distrib]
    ring
  have e2 : ipState bG bV bS bS' W (princM AF Fr Frb j W') =
      ipState bG bV bS bS' W (ActualJetSystem.princ AF Fr Frb j W') +
        (∑ μ, ∑ ν, W.g μ ν * (-(AF.β j * W'.g μ ν)) + bV W.H (-(AF.β j • W'.H))) := by
    unfold ipState
    simp only [princM, ActualJetSystem.princ, mul_zero, map_zero, Finset.sum_add_distrib]
    ring
  have hg : ∑ μ, ∑ ν, ((-(AF.β j * W.g μ ν)) * W'.g μ ν) =
      ∑ μ, ∑ ν, (W.g μ ν * (-(AF.β j * W'.g μ ν))) := by
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  have hH : bV (-(AF.β j • W.H)) W'.H = bV W.H (-(AF.β j • W'.H)) := by
    simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [e1, e2, h, hg, hH]

end Defs

/-! ### The modified system agrees with the original one on actual-jet states -/

section Agree

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S')

/-- The modified principal part of a state increment `W` in direction `j` at the state `v`. -/
def princPM (v : StateP m V S S') (j : Fin 3) (W : StateP m V S S') : StateP m V S S' :=
  toP (princM (frameU (ginvOf v.1.1)) SM.D.Fr SM.Db.Fr j (ofP W))

/-- **The modified system** `∂_t𝒰 + Σ_j 𝒜_M^j∂_j𝒰 = 𝓕_M(𝒰)` for the actual-jet state field at `x`. -/
def SymEqAtM (z : Tuple m V S S') (x : ST 3) : Prop :=
  pd (stateF SM z) 0 x + ∑ j : Fin 3, princPM SM (stateF SM z x) j (pd (stateF SM z) j.succ x) =
    toP (FsysM SM (ofP (stateF SM z x)))

/-- The head-block part `(-βʲW_g, -βʲW_H)` of the modified principal operators. -/
def extraP (b : ℝ) (W : StateP m V S S') : StateP m V S S' :=
  ((fun μ ν => -(b * W.1.1 μ ν), 0, 0), (0, 0, 0, -(b • W.2.2.2.2.1), 0, 0, 0, 0, 0, 0))

theorem princPM_eq (v : StateP m V S S') (j : Fin 3) (W : StateP m V S S') :
    princPM SM v j W = princL SM v j W + extraP ((frameU (ginvOf v.1.1)).β j) W := by
  unfold princPM princL extraP
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  ext <;> simp [toP, ofP, princM, ActualJetSystem.princ]

/-- The head-block difference of the forcings. -/
def fDiff (v : StateP m V S S') : StateP m V S S' :=
  ((fun μ ν => (frameU (ginvOf v.1.1)).N * v.1.2.1 μ ν - (Fsys SM (ofP v)).g μ ν, 0, 0),
    (0, 0, 0, ((frameU (ginvOf v.1.1)).N • v.2.2.2.2.2.1 +
      ∑ j : Fin 3, (frameU (ginvOf v.1.1)).β j • ⁅v.2.1 j, v.2.2.2.2.1⁆) - (Fsys SM (ofP v)).H,
      0, 0, 0, 0, 0, 0))

theorem FsysM_eq (v : StateP m V S S') :
    toP (FsysM SM (ofP v)) = toP (Fsys SM (ofP v)) + fDiff SM v := by
  unfold fDiff
  ext <;> simp [toP, ofP, FsysM]

variable {SM}

/-- **The shift-transported Higgs head row holds on actual-jet states**:
`∂_tH - βʲ∂_jH = NΠ + βʲ[A_j, H]` (temporal gauge, `Π = D_{e_0}H`). -/
theorem higgs_head_row_actual (z : Tuple m V S S') (x : ST 3) :
    (pd (stateF SM z) 0 x).2.2.2.2.1 -
        ∑ j : Fin 3, (frameU (z.gi x)).β j • (pd (stateF SM z) j.succ x).2.2.2.2.1 =
      (frameU (z.gi x)).N • (stateF SM z x).2.2.2.2.2.1 +
        ∑ j : Fin 3, (frameU (z.gi x)).β j • ⁅(stateF SM z x).2.1 j, (stateF SM z x).2.2.2.2.1⁆ := by
  simp only [pd_stateF]
  set J := z.jet x with hJ
  have hAF : J.AF = frameU (z.gi x) := (ActualJet.frameU_eq' J).symm
  show J.dH 0 - ∑ j : Fin 3, (frameU (z.gi x)).β j • J.dH j.succ =
    (frameU (z.gi x)).N • frV J.AF J.A J.H J.dH 0 +
      ∑ j : Fin 3, (frameU (z.gi x)).β j • ⁅J.A j.succ, J.H⁆
  rw [hAF]
  have h := ActualJetGauge.N_fD_zero (frameU (z.gi x)) (ActualJetGauge.DH J.A J.H J.dH)
  have hfD : fD (frameU (z.gi x)) (ActualJetGauge.DH J.A J.H J.dH) 0 =
      frV (frameU (z.gi x)) J.A J.H J.dH 0 := rfl
  rw [hfD] at h
  rw [h]
  simp only [ActualJetGauge.DH, J.temporal, zero_lie, add_zero, smul_add, Finset.sum_add_distrib]
  abel

/-- The modified principal part minus the original one, summed along the actual jets. -/
theorem sum_extra_eq_fDiff (z : Tuple m V S S') (x : ST 3) :
    ∑ j : Fin 3, extraP ((frameU (ginvOf (stateF SM z x).1.1)).β j) (pd (stateF SM z) j.succ x) =
      fDiff SM (stateF SM z x) := by
  have hg : ginvOf (stateF SM z x).1.1 = z.gi x := by
    rw [GenDefJet.stateF_fst_fst]; rfl
  have hFg : ∀ μ ν, (Fsys SM (ofP (stateF SM z x))).g μ ν = (pd (stateF SM z) 0 x).1.1 μ ν := by
    intro μ ν
    have h := ActualJet.row_g (z.jet x) SM μ ν
    simp only [ActualJetSystem.princ, ActualJetSystem.Bsys, ActualJetSystem.Qsys,
      ActualJetSystem.Gsys, Finset.sum_const_zero, add_zero] at h
    rw [pd_stateF]
    exact h.symm
  have hFH : (Fsys SM (ofP (stateF SM z x))).H = (pd (stateF SM z) 0 x).2.2.2.2.1 := by
    have h := ActualJet.row_H (z.jet x) SM
    simp only [ActualJetSystem.princ, ActualJetSystem.Bsys, ActualJetSystem.Qsys,
      ActualJetSystem.Gsys, Finset.sum_const_zero, add_zero] at h
    rw [pd_stateF]
    exact h.symm
  have hmg := GenDefJet.metric_head_row_actual SM z x
  have hmH := higgs_head_row_actual (SM := SM) z x
  unfold fDiff extraP
  rw [hg]
  ext μ ν
  · simp only [Prod.fst_sum, Finset.sum_apply]
    rw [hFg μ ν, ← hmg μ ν]
    simp only [Finset.sum_neg_distrib]
    ring
  · simp [Prod.fst_sum, Prod.snd_sum]
  · simp [Prod.fst_sum, Prod.snd_sum]
  · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · simp only [Prod.snd_sum, Prod.fst_sum]
    rw [hFH, ← hmH]
    simp only [Finset.sum_neg_distrib]
    abel
  all_goals simp [Prod.snd_sum]

/-- **The writer identity for the modified system**: on actual-jet states the modified system
carries the same residual and gauge forcing as the original one. -/
theorem writer_pde_errM (z : Tuple m V S S') (x : ST 3) :
    pd (stateF SM z) 0 x + ∑ j : Fin 3, princPM SM (stateF SM z x) j (pd (stateF SM z) j.succ x) =
      toP (FsysM SM (ofP (stateF SM z x))) + errF SM z x := by
  simp only [princPM_eq, Finset.sum_add_distrib, FsysM_eq]
  rw [sum_extra_eq_fDiff, ← add_assoc, writer_pde_err SM z x]
  abel

/-- **The modified and the original system agree on actual-jet states**. -/
theorem symEqAtM_iff (z : Tuple m V S S') (x : ST 3) : SymEqAtM SM z x ↔ SymEqAt SM z x := by
  rw [symEqAt_iff]
  unfold SymEqAtM
  rw [writer_pde_errM]
  exact add_eq_left

end Agree

/-! ### Transposition of the metric blocks and symmetry of the forcing -/

section Transpose

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- Transposition of a `4 × 4` array. -/
def trM : Met →L[ℝ] Met :=
  ContinuousLinearMap.pi fun μ => ContinuousLinearMap.pi fun ν =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) ν)

@[simp] theorem trM_apply (M : Met) (μ ν : Fin 4) : trM M μ ν = M ν μ := rfl

variable (m V S S') in
/-- **The transposition `τ` of the metric blocks** `(g, p, q)` of a state. -/
def tauP : StateP m V S S' →L[ℝ] StateP m V S S' :=
  (trM.prodMap (trM.prodMap (ContinuousLinearMap.pi fun a =>
    trM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Met) a)))).prodMap
    (ContinuousLinearMap.id ℝ _)

theorem tauP_apply (v : StateP m V S S') :
    tauP m V S S' v = ((trM v.1.1, trM v.1.2.1, fun a => trM (v.1.2.2 a)), v.2) := rfl

theorem tauP_tauP (v : StateP m V S S') : tauP m V S S' (tauP m V S S' v) = v := by
  rw [tauP_apply, tauP_apply]
  ext <;> simp

/-- A state is symmetric when its metric blocks are symmetric. -/
def IsSymmP (v : StateP m V S S') : Prop := tauP m V S S' v = v

theorem isSymmP_iff (v : StateP m V S S') : IsSymmP v ↔
    (∀ μ ν, v.1.1 μ ν = v.1.1 ν μ) ∧ (∀ μ ν, v.1.2.1 μ ν = v.1.2.1 ν μ) ∧
      ∀ a μ ν, v.1.2.2 a μ ν = v.1.2.2 a ν μ := by
  unfold IsSymmP
  rw [tauP_apply]
  constructor
  · intro h
    have h1 := congrArg (fun w : StateP m V S S' => w.1.1) h
    have h2 := congrArg (fun w : StateP m V S S' => w.1.2.1) h
    have h3 := congrArg (fun w : StateP m V S S' => w.1.2.2) h
    simp only at h1 h2 h3
    refine ⟨fun μ ν => ?_, fun μ ν => ?_, fun a μ ν => ?_⟩
    · exact (congrFun (congrFun h1 μ) ν).symm
    · exact (congrFun (congrFun h2 μ) ν).symm
    · exact (congrFun (congrFun (congrFun h3 a) μ) ν).symm
  · rintro ⟨h1, h2, h3⟩
    ext <;> simp [h1, h2, h3]

/-- **Theory data with symmetric gauge/Higgs forms and decoupled spinors**: the invariant forms
`⟨·,·⟩_𝔤`, `⟨·,·⟩_V` of the Yang–Mills and Higgs stresses are symmetric, the Dirac stress form
vanishes (`T^D = 0`), and the Yang–Mills and Higgs sources do not depend on the spinors.
(Hypotheses on the theory data; satisfied by the variational Yang–Mills–Higgs data
`GenNoether.adjSM` and by the vanishing-coupling data.) -/
structure Decoupled (SM : SMData (MatLie m) V S S') : Prop where
  ipG_symm : ∀ x y, SM.ipG x y = SM.ipG y x
  ipV_symm : ∀ x y, SM.ipV x y = SM.ipV y x
  TD_P : ∀ A B C, SM.TD.P A B C = 0
  TD_P' : ∀ A B C, SM.TD.P' A B C = 0
  TD_P'' : ∀ A B w, SM.TD.P'' A B w = 0
  J_spin : ∀ g gi H DH ψ ψb ψ' ψb', SM.Jcur g gi H DH ψ ψb = SM.Jcur g gi H DH ψ' ψb'
  SH_spin : ∀ g gi H ψ ψb ψ' ψb', SM.SH g gi H ψ ψb = SM.SH g gi H ψ' ψb'

variable {SM : SMData (MatLie m) V S S'}

theorem Decoupled.coord_eq_zero (hD : Decoupled SM) (g : Met) (ε : Fin 4 → ℝ) (e : Met) (H : V)
    (ψ : S) (X : Fin 4 → S) (ψb : S') (Xb : Fin 4 → S') (μ ν : Fin 4) :
    SM.TD.coord g ε e H ψ X ψb Xb μ ν = 0 := by
  unfold DiracStressForm.coord DiracStressForm.frame
  simp [hD.TD_P, hD.TD_P', hD.TD_P'']

theorem Decoupled.stressRes_eq_zero (hD : Decoupled SM) (g : Met) (ε : Fin 4 → ℝ) (e : Met)
    (ψ : S) (ψb : S') (kr : S) (kbr : S') (μ ν : Fin 4) :
    SM.TD.stressRes g ε e ψ ψb kr kbr μ ν = 0 := by
  unfold DiracStressForm.stressRes
  simp [hD.TD_P, hD.TD_P']

/-- The inverse of a symmetric matrix is symmetric. -/
theorem ginvOf_symm {g : Met} (hg : ∀ μ ν, g μ ν = g ν μ) (μ ν : Fin 4) :
    ginvOf g μ ν = ginvOf g ν μ := by
  have hT : Matrix.transpose (Matrix.of g) = Matrix.of g := by ext i j; simp [hg j i]
  unfold ginvOf
  have := Matrix.transpose_nonsing_inv (Matrix.of g)
  rw [hT] at this
  have h := congrFun (congrFun this ν) μ
  simp only [Matrix.transpose_apply] at h
  exact h

theorem sum4_rev' (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ c, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d := Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

section RicciJ

variable {gi : Met} {dg : Fin 4 → Met}

theorem dginv_symm'' (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (α l σ : Fin 4) : dginv gi dg α l σ = dginv gi dg α σ l := by
  unfold dginv
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hgi l b, hgi a σ, hdg α b a]; ring

theorem dchr1_symm (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (α l μ ν : Fin 4) :
    dchr1 gi dg α l μ ν = dchr1 gi dg α l ν μ := by
  unfold dchr1
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]; ring

theorem chr_symm'' (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (l μ ν : Fin 4) :
    chr gi dg l μ ν = chr gi dg l ν μ := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]; ring

/-- `Σ_α ∂_νΓ^α_{μα}` (inverse-metric part) is symmetric in `μ, ν`. -/
theorem sum_dchr1_trace_symm (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (μ ν : Fin 4) :
    ∑ α, dchr1 gi dg ν α μ α = ∑ α, dchr1 gi dg μ α ν α := by
  have key : ∀ μ ν, ∑ α, dchr1 gi dg ν α μ α =
      (1 / 2) * ∑ α, ∑ σ, dginv gi dg ν α σ * dg μ σ α := by
    intro μ ν
    have h0 : ∑ α, ∑ σ, dginv gi dg ν α σ * (dg α σ μ - dg σ α μ) = 0 := by
      have hs : ∑ α, ∑ σ, dginv gi dg ν α σ * dg α σ μ =
          ∑ α, ∑ σ, dginv gi dg ν α σ * dg σ α μ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [dginv_symm'' hgi hdg]
      simp only [mul_sub, Finset.sum_sub_distrib, hs, sub_self]
    unfold dchr1
    rw [← Finset.mul_sum]
    congr 1
    calc ∑ α, ∑ σ, dginv gi dg ν α σ * (dg μ σ α + dg α σ μ - dg σ μ α)
        = ∑ α, ∑ σ, dginv gi dg ν α σ * dg μ σ α +
            ∑ α, ∑ σ, dginv gi dg ν α σ * (dg α σ μ - dg σ α μ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hdg σ μ α]; ring
      _ = _ := by rw [h0, add_zero]
  rw [key μ ν, key ν μ]
  congr 1
  unfold dginv
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  congr 1
  rw [sum4_rev']
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun α _ => ?_
  rw [hdg]; ring

/-- The first-derivative part of the Ricci tensor is symmetric for symmetric jets. -/
theorem ricciJ_dchr1_symm (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (μ ν : Fin 4) :
    ricciJ (chr gi dg) (dchr1 gi dg) μ ν = ricciJ (chr gi dg) (dchr1 gi dg) ν μ := by
  unfold ricciJ
  have h1 : ∑ α, dchr1 gi dg α α μ ν = ∑ α, dchr1 gi dg α α ν μ :=
    Finset.sum_congr rfl fun α _ => dchr1_symm hdg α α μ ν
  have h2 := sum_dchr1_trace_symm hgi hdg μ ν
  have h3 : ∑ α, ∑ l, chr gi dg α α l * chr gi dg l μ ν =
      ∑ α, ∑ l, chr gi dg α α l * chr gi dg l ν μ :=
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => by rw [chr_symm'' hdg l μ ν]
  have h4 : ∑ α, ∑ l, chr gi dg α ν l * chr gi dg l μ α =
      ∑ α, ∑ l, chr gi dg α μ l * chr gi dg l ν α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h1, h2, h3, h4]

theorem qRem_symm {g : Met} (_hg : ∀ a b, g a b = g b a) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (μ ν : Fin 4) :
    qRem g gi dg μ ν = qRem g gi dg ν μ := by
  unfold qRem
  rw [ricciJ_dchr1_symm hgi hdg μ ν, add_comm (nablaC g gi dg (dginv gi dg) (chr gi dg)
    (dchr1 gi dg) μ ν)]

end RicciJ

theorem ymStressB_symm {ipG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ} (hG : ∀ x y, ipG x y = ipG y x)
    {g gi : Met} (hg : ∀ a b, g a b = g b a) (hgi : ∀ a b, gi a b = gi b a)
    (F : Fin 4 → Fin 4 → MatLie m) (μ ν : Fin 4) :
    ymStressB ipG g gi F μ ν = ymStressB ipG g gi F ν μ := by
  unfold ymStressB
  rw [hg μ ν]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hgi a b, hG]

theorem higgsStressB_symm {ipV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hV : ∀ x y, ipV x y = ipV y x)
    (lam v : ℝ) {g gi : Met} (hg : ∀ a b, g a b = g b a) (H : V) (DH : Fin 4 → V) (μ ν : Fin 4) :
    higgsStressB ipV lam v g gi H DH μ ν = higgsStressB ipV lam v g gi H DH ν μ := by
  unfold higgsStressB
  rw [hg μ ν, hV]

theorem traceRev_symm {g gi T : Met} (hg : ∀ a b, g a b = g b a) (hT : ∀ a b, T a b = T b a)
    (μ ν : Fin 4) : traceRev g gi T μ ν = traceRev g gi T ν μ := by
  unfold traceRev
  rw [hg μ ν, hT μ ν]

/-- **The modified forcing maps symmetric states to symmetric states** (theory data with
symmetric forms and vanishing Dirac stress). -/
theorem FsysM_symm (hD : Decoupled SM) {v : StateP m V S S'} (hv : IsSymmP v) :
    IsSymmP (toP (FsysM SM (ofP v))) := by
  rw [isSymmP_iff] at hv ⊢
  obtain ⟨hg, hp, hq⟩ := hv
  set fj := recon SM (ofP v) with hfj
  have hgs : ∀ a b, fj.g a b = fj.g b a := hg
  have hgis : ∀ a b, fj.gi a b = fj.gi b a := ginvOf_symm hg
  have hdgs : ∀ α μ ν, fj.dg α μ ν = fj.dg α ν μ := by
    intro α μ ν
    simp only [hfj, recon, ofP, hp μ ν, fun a => hq a μ ν]
  have hst : ∀ μ ν, stressF SM fj μ ν = stressF SM fj ν μ := by
    intro μ ν
    unfold stressF
    rw [hD.coord_eq_zero, hD.coord_eq_zero, ymStressB_symm hD.ipG_symm hgs hgis,
      higgsStressB_symm hD.ipV_symm _ _ hgs]
  refine ⟨fun μ ν => ?_, fun μ ν => ?_, fun a μ ν => ?_⟩
  · show (frameU (ginvOf (ofP v).g)).N * (ofP v).p μ ν =
      (frameU (ginvOf (ofP v).g)).N * (ofP v).p ν μ
    rw [show (ofP v).p μ ν = (ofP v).p ν μ from hp μ ν]
  · show (lowerOf SM fj).p μ ν = (lowerOf SM fj).p ν μ
    simp only [lowerOf]
    have hL : fj.AF.Lp fj.de (fun α => fj.dg α μ ν) = fj.AF.Lp fj.de (fun α => fj.dg α ν μ) := by
      congr 1; funext α; exact hdgs α μ ν
    rw [hL, qRem_symm hgs hgis hdgs μ ν, traceRev_symm hgs hst μ ν, hgs μ ν]
  · show (lowerOf SM fj).q a μ ν = (lowerOf SM fj).q a ν μ
    simp only [lowerOf]
    congr 2
    funext α; exact hdgs α μ ν

end Transpose

/-! ### The Kato realization of the modified system -/

section Realization

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- The modified principal matrix entries `⟨κ⁻¹e_a, 𝒜_M^j κ⁻¹e_b⟩`. -/
def princEntryM (SM : SMData (MatLie m) V S S') (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (AF : AdaptedFrame) (j : Fin 3)
    (a b : Fin (dimS m V S S')) : ℝ :=
  ipState bG bV bS bS' (ofP (κ.symm (Pi.single a 1)))
    (princM AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single b 1))))

theorem ipState_princM_symm (hU : UnitaryForms SM bG bV bS bS') (AF : AdaptedFrame) (j : Fin 3)
    (W W' : State (MatLie m) V S S') :
    ipState bG bV bS bS' (princM AF SM.D.Fr SM.Db.Fr j W) W' =
      ipState bG bV bS bS' W (princM AF SM.D.Fr SM.Db.Fr j W') :=
  princM_symm AF SM.D.Fr SM.Db.Fr bG bV bS bS' hU.c0 hU.ci hU.c0b hU.cib j W W'

theorem princEntryM_symm (hU : UnitaryForms SM bG bV bS bS')
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (AF : AdaptedFrame) (j : Fin 3)
    (a b : Fin (dimS m V S S')) :
    princEntryM SM bG bV bS bS' κ AF j a b = princEntryM SM bG bV bS bS' κ AF j b a := by
  unfold princEntryM
  rw [← ipState_princM_symm hU, ipState_comm hU]

theorem sum_princEntryM (hU : UnitaryForms SM bG bV bS bS')
    {κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)}
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) (AF : AdaptedFrame)
    (j : Fin 3) (a : Fin (dimS m V S S')) (w : Fin (dimS m V S S') → ℝ) :
    ∑ b, princEntryM SM bG bV bS bS' κ AF j a b * w b =
      κ (toS (princM AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) a := by
  rw [coord_eq_form (ipB bG bV bS bS') κ hκ, ipB_apply, ipP, ofP_toS,
    ← ipState_princM_symm hU]
  have e : ipState bG bV bS bS' (princM AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single a 1))))
      (ofP (κ.symm w)) = ipB bG bV bS bS'
        (toS (princM AF SM.D.Fr SM.Db.Fr j (ofP (κ.symm (Pi.single a 1))))) (κ.symm w) := rfl
  rw [e, symm_eq_sum κ w, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, princEntryM, ← ipState_princM_symm hU]
  rfl

theorem contDiff_princEntryM_mkFrame
    (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {L : X → ℝ} {β : X → Fin 3 → ℝ} {E : X → Fin 3 → Fin 3 → ℝ}
    (hL : ContDiff ℝ ∞ L) (hβ : ∀ j, ContDiff ℝ ∞ fun x => β x j)
    (hE : ∀ a j, ContDiff ℝ ∞ fun x => E x a j) (j : Fin 3) (a b : Fin (dimS m V S S')) :
    ContDiff ℝ ∞ fun x => princEntryM SM bG bV bS bS' κ (mkFrame (L x) (β x) (E x)) j a b := by
  have hN : ContDiff ℝ ∞ fun x => Real.exp (L x) := Real.contDiff_exp.comp hL
  have hβj := hβ j
  have hEj : ∀ a, ContDiff ℝ ∞ fun x => E x a j := fun a => hE a j
  simp only [princEntryM, ipState, princM, ActualJetSystem.princ, mkFrame, diracP, map_add,
    map_sub, map_neg, map_smul, map_sum, map_zero, smul_eq_mul]
  fun_prop

/-- The modified principal operators commute with the transposition of the metric blocks. -/
theorem princM_tauP (AF : AdaptedFrame) (j : Fin 3) (x : StateP m V S S') :
    toS (princM AF SM.D.Fr SM.Db.Fr j (ofP (tauP m V S S' x))) =
      tauP m V S S' (toS (princM AF SM.D.Fr SM.Db.Fr j (ofP x))) := by
  rw [tauP_apply, tauP_apply]
  ext <;> simp [toS, ofP, princM, ActualJetSystem.princ]

/-- The coordinate transposition `κ τ κ⁻¹`. -/
def tauK (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v : Fin (dimS m V S S') → ℝ) : Fin (dimS m V S S') → ℝ :=
  κ (tauP m V S S' (κ.symm v))

theorem tauK_tauK (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v : Fin (dimS m V S S') → ℝ) : tauK κ (tauK κ v) = v := by
  simp [tauK, tauP_tauP]

theorem tauK_add (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v w : Fin (dimS m V S S') → ℝ) : tauK κ (v + w) = tauK κ v + tauK κ w := by
  simp [tauK, map_add]

theorem tauK_smul (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) (c : ℝ)
    (v : Fin (dimS m V S S') → ℝ) : tauK κ (c • v) = c • tauK κ v := by
  simp [tauK, map_smul]

/-- The symmetrization `κ ½(1 + τ) κ⁻¹`. -/
def symK (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ)) :
    (Fin (dimS m V S S') → ℝ) →L[ℝ] (Fin (dimS m V S S') → ℝ) :=
  (LinearMap.toContinuousLinearMap ((κ.toLinearMap.comp
    (((1 / 2 : ℝ) • (LinearMap.id + (tauP m V S S').toLinearMap)).comp κ.symm.toLinearMap))))

theorem symK_apply (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v : Fin (dimS m V S S') → ℝ) :
    symK κ v = κ ((1 / 2 : ℝ) • (κ.symm v + tauP m V S S' (κ.symm v))) := rfl

theorem symK_tauK (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (v : Fin (dimS m V S S') → ℝ) : symK κ (tauK κ v) = symK κ v := by
  simp only [symK_apply, tauK, LinearEquiv.symm_apply_apply, tauP_tauP]
  rw [add_comm]

theorem symK_of_symm (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    {v : Fin (dimS m V S S') → ℝ} (hv : IsSymmP (κ.symm v)) : symK κ v = v := by
  rw [symK_apply, hv, ← two_smul ℝ (κ.symm v), smul_smul]
  norm_num

/-- **The Kato realization of the shift-transported actual-jet system.**  For theory data with
smooth sources, symmetric gauge/Higgs forms and vanishing Dirac stress (`Decoupled`), forms with
the Clifford unitarity relations and any Euclidean coordinates `κ` of the block inner product, for
every compact chart set `K` there are globally smooth coefficient maps `A^j`, `F` with
`A^j(v)` symmetric, both equivariant under the coordinate transposition `τ_κ` of the metric blocks,
which at the **symmetric** states of `K` are the modified principal operators `𝒜_M^j` and the
modified forcing `𝓕_M`. -/
theorem modified_kato_realization (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    (hD : Decoupled SM) (κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ))
    (hκ : ∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) :
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ i a b, ContDiff ℝ ∞ (A i a b)) ∧ (∀ i a b v, A i a b v = A i b a v) ∧
        (∀ a, ContDiff ℝ ∞ (F a)) ∧
        (∀ v ∈ K, IsSymmP (κ.symm v) → ∀ j a (w : Fin (dimS m V S S') → ℝ),
          ∑ b, A j a b v * w b = κ (princPM SM (κ.symm v) j (κ.symm w)) a) ∧
        (∀ v ∈ K, IsSymmP (κ.symm v) → ∀ a, F a v = κ (toP (FsysM SM (ofP (κ.symm v)))) a) ∧
        (∀ j a v w, ∑ b, A j a b (tauK κ v) * tauK κ w b =
          tauK κ (fun a' => ∑ b, A j a' b v * w b) a) ∧
        (∀ a v, F a (tauK κ v) = tauK κ (fun a' => F a' v) a) := by
  intro K hK hKc
  set O : Set (Fin (dimS m V S S') → ℝ) := κ.symm ⁻¹' chartSet with hOdef
  have hκc : Continuous κ.symm := (contDiff_linearEquiv κ.symm.toLinearMap).continuous
  have hO : IsOpen O := isOpen_chartSet.preimage hκc
  have hKO : K ⊆ O := fun v hv => hKc v hv
  have hκs : ContDiff ℝ ∞ κ.symm := contDiff_linearEquiv κ.symm.toLinearMap
  have hκf : ContDiff ℝ ∞ κ := contDiff_linearEquiv κ.toLinearMap
  have hframe : ∀ v ∈ O, ContDiffAt ℝ ∞
      (fun v => (frameU (ginvOf (κ.symm v).1.1)).N) v ∧
      (∀ j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).β j) v) ∧
      (∀ a j, ContDiffAt ℝ ∞ (fun v => (frameU (ginvOf (κ.symm v).1.1)).E a j) v) := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv
    exact ⟨h1.comp v hκs.contDiffAt, fun j => (h2 j).comp v hκs.contDiffAt,
      fun a j => (h3 a j).comp v hκs.contDiffAt⟩
  have hL : ContDiffOn ℝ ∞ (fun v => Real.log (frameU (ginvOf (κ.symm v).1.1)).N) O :=
    fun v hv => ((hframe v hv).1.log (frameU _).N_pos.ne').contDiffWithinAt
  obtain ⟨L', hL's, hL'K⟩ := SlabMoser.exists_contDiff_eqOn hO hK hKO hL
  obtain ⟨β', hβ's, hβ'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun j v => (frameU (ginvOf (κ.symm v).1.1)).β j)
    fun j v hv => ((hframe v hv).2.1 j).contDiffWithinAt
  obtain ⟨E', hE's, hE'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun p : Fin 3 × Fin 3 => fun v => (frameU (ginvOf (κ.symm v).1.1)).E p.1 p.2)
    fun p v hv => ((hframe v hv).2.2 p.1 p.2).contDiffWithinAt
  obtain ⟨F', hF's, hF'K⟩ := exists_contDiff_eqOn_family hO hK hKO
    (Φ := fun a v => κ (toP (FsysM SM (ofP (κ.symm v)))) a)
    fun a v hv => by
      have h0 : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toS (Fsys SM (ofP x))) (κ.symm v) :=
        contDiffAt_Fsys_state hS hv
      have hN : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).N) (κ.symm v) :=
        (contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv).1
      have hβ : ∀ j, ContDiffAt ℝ ∞
          (fun x : StateP m V S S' => (frameU (ginvOf x.1.1)).β j) (κ.symm v) :=
        (contDiffAt_frame_state (m := m) (V := V) (S := S) (S' := S') hv).2.1
      have hM : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => toP (FsysM SM (ofP x))) (κ.symm v) := by
        have e : (fun x : StateP m V S S' => toP (FsysM SM (ofP x))) = fun x =>
            toS (Fsys SM (ofP x)) + fDiff SM x := funext fun x => FsysM_eq SM x
        rw [e]
        refine h0.add ?_
        unfold fDiff
        have hg : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (Fsys SM (ofP x)).g) (κ.symm v) :=
          contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
            (Fsys_smooth SM hS hv).1 μ ν
        have hH : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => (Fsys SM (ofP x)).H) (κ.symm v) :=
          (Fsys_smooth SM hS hv).2.2.2.2.2.2.1
        have hp : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.1.2.1) (κ.symm v) := by fun_prop
        have hPm : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.2.2.2.2.1) (κ.symm v) := by
          fun_prop
        have hA : ∀ j, ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.1 j) (κ.symm v) := by
          intro j; fun_prop
        have hHv : ContDiffAt ℝ ∞ (fun x : StateP m V S S' => x.2.2.2.2.1) (κ.symm v) := by
          fun_prop
        have hbr : ∀ j, ContDiffAt ℝ ∞
            (fun x : StateP m V S S' => ⁅x.2.1 j, x.2.2.2.2.1⁆) (κ.symm v) := fun j =>
          ContDiffAt.lie_mod (hA j) hHv
        refine ContDiffAt.prodMk (ContDiffAt.prodMk ?_ contDiffAt_const) ?_
        · exact contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun ν =>
            (hN.mul ((contDiffAt_pi.1 (contDiffAt_pi.1 hp μ)) ν)).sub
              ((contDiffAt_pi.1 (contDiffAt_pi.1 hg μ)) ν)
        · refine ContDiffAt.prodMk contDiffAt_const (ContDiffAt.prodMk contDiffAt_const
            (ContDiffAt.prodMk contDiffAt_const (ContDiffAt.prodMk ?_ contDiffAt_const)))
          exact ((hN.smul hPm).add (ContDiffAt.sum fun j _ => (hβ j).smul (hbr j))).sub hH
      have h2 := (hκf.contDiffAt (x := toP (FsysM SM (ofP (κ.symm v))))).comp v
        (hM.comp v hκs.contDiffAt)
      exact ((contDiffAt_pi.1 h2) a).contDiffWithinAt
  -- the frame data, composed with the symmetrization
  set AF' : (Fin (dimS m V S S') → ℝ) → AdaptedFrame := fun v =>
    mkFrame (L' (symK κ v)) (fun j => β' j (symK κ v)) (fun a j => E' (a, j) (symK κ v))
    with hAF'
  have hAFK : ∀ v ∈ K, IsSymmP (κ.symm v) → AF' v = frameU (ginvOf (κ.symm v).1.1) := by
    intro v hv hs
    simp only [hAF', symK_of_symm κ hs]
    exact mkFrame_eq (hL'K v hv) (funext fun j => hβ'K j v hv) (funext fun a => funext fun j =>
      hE'K (a, j) v hv)
  have hAFτ : ∀ v, AF' (tauK κ v) = AF' v := fun v => by simp only [hAF', symK_tauK]
  set Fs : Fin (dimS m V S S') → (Fin (dimS m V S S') → ℝ) → ℝ := fun a v =>
    (1 / 2 : ℝ) * (F' a v + tauK κ (fun a' => F' a' (tauK κ v)) a) with hFs
  have hsymKs : ContDiff ℝ ∞ (symK κ) := (symK κ).contDiff
  have htauKs : ContDiff ℝ ∞ (tauK κ) := by
    have : tauK κ = (κ.toLinearMap.comp ((tauP m V S S').toLinearMap.comp κ.symm.toLinearMap)) :=
      funext fun v => rfl
    rw [this]
    exact contDiff_linearEquiv _
  refine ⟨fun j a b v => princEntryM SM bG bV bS bS' κ (AF' v) j a b, Fs, fun j a b => ?_,
    fun j a b v => princEntryM_symm hU κ (AF' v) j a b, fun a => ?_, fun v hv hs j a w => ?_,
    fun v hv hs a => ?_, fun j a v w => ?_, fun a v => ?_⟩
  · exact contDiff_princEntryM_mkFrame κ (hL's.comp hsymKs) (fun j => (hβ's j).comp hsymKs)
      (fun a j => (hE's (a, j)).comp hsymKs) j a b
  · have hT : ContDiff ℝ ∞ fun v => tauK κ (fun a' => F' a' (tauK κ v)) := by
      have hlin : tauK κ = (κ.toLinearMap.comp ((tauP m V S S').toLinearMap.comp
          κ.symm.toLinearMap)) := funext fun v => rfl
      rw [hlin]
      exact (contDiff_linearEquiv _).comp ((contDiff_pi.2 hF's).comp htauKs)
    exact contDiff_const.mul ((hF's a).add ((contDiff_pi.1 hT) a))
  · rw [sum_princEntryM hU hκ, hAFK v hv hs]
    rfl
  · have hτv : tauK κ v = v := by
      unfold tauK; rw [hs, LinearEquiv.apply_symm_apply]
    have hsF : IsSymmP (toP (FsysM SM (ofP (κ.symm v)))) := FsysM_symm hD hs
    simp only [hFs, hτv]
    have h1 : (fun a' => F' a' v) = κ (toP (FsysM SM (ofP (κ.symm v)))) :=
      funext fun a' => hF'K a' v hv
    rw [h1, hF'K a v hv]
    have h2 : tauK κ (κ (toP (FsysM SM (ofP (κ.symm v))))) = κ (toP (FsysM SM (ofP (κ.symm v)))) := by
      unfold tauK; rw [LinearEquiv.symm_apply_apply, hsF]
    rw [h2]
    ring
  · rw [sum_princEntryM hU hκ, hAFτ]
    have e : (fun a' => ∑ b, princEntryM SM bG bV bS bS' κ (AF' v) j a' b * w b) =
        κ (toS (princM (AF' v) SM.D.Fr SM.Db.Fr j (ofP (κ.symm w)))) :=
      funext fun a' => sum_princEntryM hU hκ (AF' v) j a' w
    rw [e]
    unfold tauK
    simp only [LinearEquiv.symm_apply_apply]
    rw [princM_tauP]
  · simp only [hFs, tauK_tauK]
    have e : (fun a' => (1 / 2 : ℝ) * (F' a' v + tauK κ (fun a'' => F' a'' (tauK κ v)) a')) =
        (1 / 2 : ℝ) • ((fun a' => F' a' v) + tauK κ (fun a'' => F' a'' (tauK κ v))) := by
      funext a'; simp [smul_eq_mul]
    rw [e, tauK_smul, tauK_add, tauK_tauK]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

end Realization

end RenewalGeometry.AJKatoMod
