/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedBackwardPropagation
import RenewalGeometry.Continuum.ActualJetKatoModified
import RenewalGeometry.Continuum.GeneratedPhysicalIdentificationClosed

/-!
# Propagation of the defining-jet identities: the gauge sector

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`).  Let `W` be a solution of the symmetric system whose head gauge
potential is the potential `A` of a smooth tuple `z` (exact temporal gauge `A₀ = 0`), and let `T`
be the coordinate field strength *reconstructed from its auxiliary variables* `(E, B)`.  The head
row gives `T_{0i} = ∂_tA_i`, and the `B`-row is the frame form of the Bianchi identity of `T`
along the normal: `Bian(T)_{0ij} = βᵏ Bian(T)_{kij}`.  The spatial magnetic defect
`δ_{ij} = F(A)_{ij} - T_{ij}` then obeys

* `∂_tδ_{ij} = βᵏε_{kij} ζ` with the magnetic Gauss defect `ζ = Bian^{lin}(δ)_{123}`,
* `∂_tζ - βᵏ∂_kζ = (∂_kβᵏ)ζ + βᵏ[A_k, ζ] + Σ_{cyc}[T_{0i}, δ_{jk}]`,

a linear symmetric hyperbolic system for `(δ_{23}, δ_{31}, δ_{12}, ζ)` (principal part
`diag(1, 1, 1, ∂_t - βᵏ∂_k)`).  The system for `δ` alone is only weakly hyperbolic for nonzero
shift; it closes **jointly with the magnetic Gauss defect** through the Bianchi identity of the
reconstructed field strength.

## Main results (generic: `z` any smooth tuple, `T` any smooth antisymmetric field)

* `dl`, `zeta`, `bian`, `blin` — defect, magnetic Gauss defect, Bianchi expressions;
* `pd_dl_time`, `bian_eq_neg_blin`, `pd_zeta_time` — the defect equations;
* **`gauge_defect_vanish`** — under the head row and the normal Bianchi relation on
  `(a, b) × 𝕋³`, if `T = F(A)` on the slice `t₀` then `T = F(A)` on every closed sub-slab
  (forward and backward, `GenHarmonic.sym_unique` / `GenBackward.sym_unique_backward`).
-/

open Filter Topology Set
open scoped BigOperators ContDiff NNReal

noncomputable section

namespace RenewalGeometry.GenGaugeDefect

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon GenConstraint GenNoether

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-! ### Calculus of brackets -/

section Calc

/-- The bracket of `gl(m)` as a continuous bilinear map. -/
def lieCL (m : ℕ) : MatLie m →L[ℝ] MatLie m →L[ℝ] MatLie m :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (MatLie m →ₗ[ℝ] MatLie m) ≃ₗ[ℝ]
      (MatLie m →L[ℝ] MatLie m)).toLinearMap ∘ₗ JetCurve.lieB m)

theorem lieCL_apply (a b : MatLie m) : lieCL m a b = ⁅a, b⁆ := rfl

theorem differentiableAt_lie {f g : ST 3 → MatLie m} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun y => ⁅f y, g y⁆) x := by
  have : (fun y => ⁅f y, g y⁆) = fun y => lieCL m (f y) (g y) := rfl
  rw [this]
  exact ((lieCL m).differentiableAt.comp x hf).clm_apply hg

theorem pd_lie {f g : ST 3 → MatLie m} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd (fun y => ⁅f y, g y⁆) μ x = ⁅pd f μ x, g x⁆ + ⁅f x, pd g μ x⁆ := by
  refine ActualJetBridge.pd_eq_of_line (differentiableAt_lie hf hg) ?_
  have h1 := ActualJetBridge.hasDerivAt_line0 hf μ
  have h2 := ActualJetBridge.hasDerivAt_line0 hg μ
  have := JetCurve.hasDerivAt_lie h1 h2
  simpa using this

theorem pd_smul_fun {c : ST 3 → ℝ} {g : ST 3 → MatLie m} {x : ST 3} (hc : DifferentiableAt ℝ c x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd (fun y => c y • g y) μ x = pd c μ x • g x + c x • pd g μ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_smul hc hg]
  simp [add_comm]

theorem pd_sub' {f g : ST 3 → MatLie m} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd (fun y => f y - g y) μ x = pd f μ x - pd g μ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_sub hf hg, sub_apply]

theorem pd_add' {f g : ST 3 → MatLie m} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd (fun y => f y + g y) μ x = pd f μ x + pd g μ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_add hf hg, add_apply]

/-- Partial derivatives of fields agreeing on an open set agree there. -/
theorem pd_congr_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ST 3 → E}
    {O : Set (ST 3)} (hO : IsOpen O) (h : ∀ y ∈ O, f y = g y) {x : ST 3} (hx : x ∈ O)
    (μ : Fin 4) : pd f μ x = pd g μ x := by
  have hev : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hO.mem_nhds hx) h
  exact (SlabLocal.pd_eventuallyEq hev μ).eq_of_nhds

end Calc

/-! ### The defect quantities -/

section Defects

variable (z : Tuple m V S S') (T : ST 3 → Fin 4 → Fin 4 → MatLie m)

/-- A component of the reconstructed field strength. -/
def Tc (μ ν : Fin 4) (y : ST 3) : MatLie m := T y μ ν

/-- The spatial magnetic defect `δ_{ij} = F(A)_{ij} - T_{ij}`. -/
def dl (i j : Fin 3) (y : ST 3) : MatLie m := Fld z y i.succ j.succ - T y i.succ j.succ

/-- The Bianchi expression of `T` (with the connection `A` of the tuple). -/
def bian (x : ST 3) (γ μ ν : Fin 4) : MatLie m :=
  pd (Tc T μ ν) γ x + pd (Tc T ν γ) μ x + pd (Tc T γ μ) ν x +
    (⁅z.A x γ, T x μ ν⁆ + ⁅z.A x μ, T x ν γ⁆ + ⁅z.A x ν, T x γ μ⁆)

/-- The linearized Bianchi expression of the defect (spatial indices). -/
def blin (x : ST 3) (k i j : Fin 3) : MatLie m :=
  pd (dl z T i j) k.succ x + pd (dl z T j k) i.succ x + pd (dl z T k i) j.succ x +
    (⁅z.A x k.succ, dl z T i j x⁆ + ⁅z.A x i.succ, dl z T j k x⁆ + ⁅z.A x j.succ, dl z T k i x⁆)

/-- **The magnetic Gauss defect** `ζ = Bian^{lin}(δ)_{123}`. -/
def zeta (x : ST 3) : MatLie m := blin z T x 0 1 2

end Defects

/-! ### The pointwise defect equations -/

section Equations

variable {z : Tuple m V S S'} {T : ST 3 → Fin 4 → Fin 4 → MatLie m} {O : Set (ST 3)}

theorem diffAt_Tc (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O)
    (μ ν : Fin 4) : DifferentiableAt ℝ (Tc T μ ν) x := by
  have h : DifferentiableAt ℝ T x := GenHarmonic.diffAt_of_contDiffOn hO hT (by simp) hx
  have h1 : DifferentiableAt ℝ (fun y => T y μ) x := (differentiableAt_pi.1 h) μ
  exact (differentiableAt_pi.1 h1) ν

theorem diffAt_Fld (z : Tuple m V S S') (μ ν : Fin 4) (x : ST 3) :
    DifferentiableAt ℝ (fun y => Fld z y μ ν) x :=
  (contDiff_Fld z μ ν).differentiable (by simp) x

theorem diffAt_dl (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O)
    (i j : Fin 3) : DifferentiableAt ℝ (dl z T i j) x :=
  (diffAt_Fld z _ _ x).sub (diffAt_Tc hO hT hx _ _)

theorem pd_Fld (z : Tuple m V S S') (x : ST 3) (γ μ ν : Fin 4) :
    pd (fun y => Fld z y μ ν) γ x = dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA γ μ ν :=
  ActualJetBridge.pd_eq_of_line (diffAt_Fld z μ ν x) (z.line_Fm x γ μ ν)

theorem pd_dl (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O)
    (i j : Fin 3) (γ : Fin 4) :
    pd (dl z T i j) γ x = dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA γ i.succ j.succ -
      pd (Tc T i.succ j.succ) γ x := by
  show pd (fun y => Fld z y i.succ j.succ - Tc T i.succ j.succ y) γ x = _
  rw [pd_sub' (diffAt_Fld z _ _ x) (diffAt_Tc hO hT hx _ _), pd_Fld]

theorem dl_anti (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) (i j : Fin 3) (y : ST 3) :
    dl z T j i y = -dl z T i j y := by
  unfold dl
  rw [hTa y, Fld, Fld, Fm_anti]
  abel

theorem dl_self (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) (i : Fin 3) (y : ST 3) : dl z T i i y = 0 := by
  have := dl_anti (z := z) hTa i i y
  have h2 : (2 : ℝ) • dl z T i i y = 0 := by rw [two_smul]; nth_rw 1 [this]; abel
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem pd_dl_anti (_hO : IsOpen O) (_hT : ContDiffOn ℝ ∞ T O)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) {x : ST 3} (_hx : x ∈ O) (i j : Fin 3) (γ : Fin 4) :
    pd (dl z T j i) γ x = -pd (dl z T i j) γ x := by
  have e : dl z T j i = fun y => -dl z T i j y := funext fun y => dl_anti hTa i j y
  rw [e]
  unfold SobolevOpen.pd
  rw [fderiv_fun_neg]
  rfl

/-- **The defect evolves by the normal Bianchi expression**: `∂_tδ_{ij} = -Bian(T)_{0ij}`
(temporal gauge, head row `T_{0i} = ∂_tA_i` on the open set `O`). -/
theorem pd_dl_time (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) {x : ST 3} (hx : x ∈ O)
    (i j : Fin 3) : pd (dl z T i j) 0 x = -bian z T x 0 i.succ j.succ := by
  have hA0 : z.A x 0 = 0 := z.temporal x
  -- derivatives of the head row
  have hdT0 : ∀ (k : Fin 3) (γ : Fin 4), pd (Tc T 0 k.succ) γ x = (z.jet x).ddA γ 0 k.succ := by
    intro k γ
    have e := pd_congr_open hO (f := Tc T 0 k.succ) (g := fun y => pd z.A 0 y k.succ)
      (fun y hy => hH1 y hy k) hx γ
    rw [e]
    show pd (fun y => pd z.A 0 y k.succ) γ x = pd (pd z.A 0) γ x k.succ
    exact ActualJetBridge.pd_apply ((ActualJetBridge.contDiff_pd z.A_smooth 0).differentiable
      (by simp) x) γ k.succ
  have hdTa : ∀ (k : Fin 3) (γ : Fin 4), pd (Tc T k.succ 0) γ x = -(z.jet x).ddA γ 0 k.succ := by
    intro k γ
    have e : Tc T k.succ 0 = fun y => -Tc T 0 k.succ y := funext fun y => hTa y 0 k.succ
    rw [e, ← hdT0 k γ]
    unfold SobolevOpen.pd
    rw [fderiv_fun_neg]
    rfl
  have hddA : ∀ γ μ ν, (z.jet x).ddA γ μ ν = (z.jet x).ddA μ γ ν := (z.jet x).ddA_symm
  have hT0 : ∀ k : Fin 3, T x 0 k.succ = (z.jet x).dA 0 k.succ := fun k => hH1 x hx k
  rw [pd_dl hO hT hx]
  unfold bian
  rw [hdTa j i.succ, hdT0 i j.succ, hA0]
  simp only [zero_lie, zero_add]
  rw [hTa x 0 j.succ, hT0 i, hT0 j]
  unfold dFm
  rw [hddA i.succ 0 j.succ, hddA j.succ 0 i.succ]
  have e1 : ⁅(z.jet x).A j.succ, (z.jet x).dA 0 i.succ⁆ =
      -⁅(z.jet x).dA 0 i.succ, (z.jet x).A j.succ⁆ := (lie_skew _ _).symm
  have e2 : (z.jet x).A = z.A x := rfl
  rw [e2] at e1
  rw [show (z.jet x).A = z.A x from rfl, e1, lie_neg]
  abel

/-- **The spatial Bianchi expressions of `T` are minus the linearized Bianchi expressions of the
defect** (the Bianchi identity of `F(A)`). -/
theorem bian_eq_neg_blin (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O)
    (k i j : Fin 3) : bian z T x k.succ i.succ j.succ = -blin z T x k i j := by
  have hbi := bianchi_jet (z.jet x).A (z.jet x).dA (z.jet x).ddA (z.jet x).ddA_symm k.succ i.succ
    j.succ
  have hb0 : dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA k.succ i.succ j.succ +
      dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA i.succ j.succ k.succ +
      dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA j.succ k.succ i.succ +
      brB (z.jet x).A (z.jet x).dA k.succ i.succ j.succ = 0 := by
    rw [hbi]; abel
  unfold blin bian
  rw [pd_dl hO hT hx, pd_dl hO hT hx, pd_dl hO hT hx]
  unfold dl
  unfold brB at hb0
  simp only [lie_sub]
  have e : ∀ μ ν, Fld z x μ ν = Fm (z.jet x).A (z.jet x).dA μ ν := fun μ ν => rfl
  simp only [e]
  have e2 : (z.jet x).A = z.A x := rfl
  rw [e2] at hb0
  rw [eq_neg_iff_add_eq_zero, ← hb0]
  abel

end Equations

/-! ### The closed defect system -/

section Closed

variable {z : Tuple m V S S'} {T : ST 3 → Fin 4 → Fin 4 → MatLie m} {O : Set (ST 3)}

theorem pd_dl_self (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) (i : Fin 3) (x : ST 3) (γ : Fin 4) :
    pd (dl z T i i) γ x = 0 := by
  have : dl z T i i = fun _ => 0 := funext fun y => dl_self hTa i y
  rw [this]; simp [SobolevOpen.pd]

theorem blin_rep1 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    {x : ST 3} (hx : x ∈ O) (k j : Fin 3) : blin z T x k k j = 0 := by
  unfold blin
  rw [pd_dl_anti hO hT hTa hx k j, dl_anti hTa k j, pd_dl_self hTa, dl_self hTa]
  simp only [lie_neg, lie_zero]
  abel

theorem blin_rep2 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    {x : ST 3} (hx : x ∈ O) (k i : Fin 3) : blin z T x k i k = 0 := by
  unfold blin
  rw [pd_dl_anti hO hT hTa hx k i, dl_anti hTa k i, pd_dl_self hTa, dl_self hTa]
  simp only [lie_neg, lie_zero]
  abel

theorem blin_rep3 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    {x : ST 3} (hx : x ∈ O) (k i : Fin 3) : blin z T x k i i = 0 := by
  unfold blin
  rw [pd_dl_anti hO hT hTa hx i k, dl_anti hTa i k, pd_dl_self hTa, dl_self hTa]
  simp only [lie_neg, lie_zero]
  abel

theorem blin_120 (x : ST 3) : blin z T x 1 2 0 = zeta z T x := by
  unfold zeta blin; abel

theorem blin_201 (x : ST 3) : blin z T x 2 0 1 = zeta z T x := by
  unfold zeta blin; abel

variable {β : ST 3 → Fin 3 → ℝ}

/-- The normal Bianchi relation of the `B`-row. -/
def NormalBianchi (z : Tuple m V S S') (T : ST 3 → Fin 4 → Fin 4 → MatLie m)
    (β : ST 3 → Fin 3 → ℝ) (O : Set (ST 3)) : Prop :=
  ∀ x ∈ O, ∀ i j : Fin 3,
    bian z T x 0 i.succ j.succ = ∑ k : Fin 3, β x k • bian z T x k.succ i.succ j.succ

theorem pd_dl_time_sum (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) (i j : Fin 3) :
    pd (dl z T i j) 0 x = ∑ k : Fin 3, β x k • blin z T x k i j := by
  rw [pd_dl_time hO hT hTa hH1 hx, hNB x hx i j, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bian_eq_neg_blin hO hT hx, smul_neg, neg_neg]

theorem pd_dl12 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) : pd (dl z T 1 2) 0 x = β x 0 • zeta z T x := by
  rw [pd_dl_time_sum hO hT hTa hH1 hNB hx, Fin.sum_univ_three, blin_rep1 hO hT hTa hx,
    blin_rep2 hO hT hTa hx]
  simp only [smul_zero, add_zero]
  rfl

theorem pd_dl20 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) : pd (dl z T 2 0) 0 x = β x 1 • zeta z T x := by
  rw [pd_dl_time_sum hO hT hTa hH1 hNB hx, Fin.sum_univ_three, blin_rep2 hO hT hTa hx,
    blin_rep1 hO hT hTa hx, blin_120]
  try simp

theorem pd_dl01 (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) : pd (dl z T 0 1) 0 x = β x 2 • zeta z T x := by
  rw [pd_dl_time_sum hO hT hTa hH1 hNB hx, Fin.sum_univ_three, blin_rep1 hO hT hTa hx,
    blin_rep2 hO hT hTa hx, blin_201]
  try simp

theorem contDiffOn_Tc (_hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (μ ν : Fin 4) :
    ContDiffOn ℝ ∞ (Tc T μ ν) O := by
  have h1 : ContDiffOn ℝ ∞ (fun y => T y μ) O := contDiffOn_pi.1 hT μ
  exact contDiffOn_pi.1 h1 ν

theorem contDiffOn_dl (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (dl z T i j) O :=
  (contDiff_Fld z _ _).contDiffOn.sub (contDiffOn_Tc hO hT _ _)

theorem contDiffOn_pd_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (μ : Fin 4) : ContDiffOn ℝ ∞ (pd f μ) O := by
  unfold SobolevOpen.pd
  exact (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_lieF {f g : ST 3 → MatLie m} (hf : ContDiffOn ℝ ∞ f O)
    (hg : ContDiffOn ℝ ∞ g O) : ContDiffOn ℝ ∞ (fun y => ⁅f y, g y⁆) O := by
  have : (fun y => ⁅f y, g y⁆) = fun y => lieCL m (f y) (g y) := rfl
  rw [this]
  exact ((lieCL m).contDiff.comp_contDiffOn hf).clm_apply hg

theorem contDiffOn_blin (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (k i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => blin z T x k i j) O := by
  have hA : ∀ μ, ContDiffOn ℝ ∞ (fun y => z.A y μ) O := fun μ =>
    (Tuple.contDiff_vec z.A_smooth μ).contDiffOn
  unfold blin
  exact (((contDiffOn_pd_top hO (contDiffOn_dl hO hT i j) _).add
    (contDiffOn_pd_top hO (contDiffOn_dl hO hT j k) _)).add
    (contDiffOn_pd_top hO (contDiffOn_dl hO hT k i) _)).add
    (((contDiffOn_lieF (hA _) (contDiffOn_dl hO hT i j)).add
    (contDiffOn_lieF (hA _) (contDiffOn_dl hO hT j k))).add
    (contDiffOn_lieF (hA _) (contDiffOn_dl hO hT k i)))

theorem contDiffOn_zeta (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) :
    ContDiffOn ℝ ∞ (zeta z T) O :=
  contDiffOn_blin hO hT 0 1 2

/-- One term of the time derivative of `ζ`. -/
theorem pd_zeta_term (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O)
    (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k))
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) {x : ST 3} (hx : x ∈ O)
    (i j k : Fin 3) (hdl : ∀ y ∈ O, pd (dl z T i j) 0 y = β y k • zeta z T y) :
    pd (fun y => pd (dl z T i j) k.succ y + ⁅z.A y k.succ, dl z T i j y⁆) 0 x =
      pd (fun y => β y k) k.succ x • zeta z T x + β x k • pd (zeta z T) k.succ x +
        (⁅T x 0 k.succ, dl z T i j x⁆ + β x k • ⁅z.A x k.succ, zeta z T x⁆) := by
  have hdl2 : ContDiffOn ℝ 2 (dl z T i j) O := (contDiffOn_dl hO hT i j).of_le (by norm_cast)
  have hd1 : DifferentiableAt ℝ (pd (dl z T i j) k.succ) x :=
    GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_pd_top hO (contDiffOn_dl hO hT i j) _)
      (by simp) hx
  have hAd : DifferentiableAt ℝ (fun y => z.A y k.succ) x :=
    (Tuple.contDiff_vec z.A_smooth k.succ).differentiable (by simp) x
  have hdld : DifferentiableAt ℝ (dl z T i j) x := diffAt_dl hO hT hx i j
  have hζd : DifferentiableAt ℝ (zeta z T) x :=
    GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_zeta hO hT) (by simp) hx
  have hβd : DifferentiableAt ℝ (fun y => β y k) x := (hβ k).differentiable (by simp) x
  rw [pd_add' hd1 (differentiableAt_lie hAd hdld)]
  -- the derivative term
  have h1 : pd (pd (dl z T i j) k.succ) 0 x = pd (pd (dl z T i j) 0) k.succ x :=
    GenHarmonic.pd_pd_symm_at hO hdl2 hx k.succ 0
  have h2 : pd (pd (dl z T i j) 0) k.succ x = pd (fun y => β y k • zeta z T y) k.succ x :=
    pd_congr_open hO hdl hx k.succ
  rw [h1, h2, pd_smul_fun hβd hζd]
  -- the bracket term
  rw [pd_lie hAd hdld, hdl x hx]
  have hA0 : pd (fun y => z.A y k.succ) 0 x = T x 0 k.succ := by
    rw [hH1 x hx k]
    exact ActualJetBridge.pd_apply (z.A_smooth.differentiable (by simp) x) 0 k.succ
  rw [hA0, lie_smul]
  try abel

/-- **The magnetic Gauss defect is transported along the shift**:
`∂_tζ = Σ_k ((∂_kβ_k)ζ + β_k∂_kζ + [T_{0k}, δ_{k+1,k+2}] + β_k[A_k, ζ])`. -/
theorem pd_zeta_time (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k))
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) :
    pd (zeta z T) 0 x =
      (pd (fun y => β y 0) (0 : Fin 3).succ x • zeta z T x +
        β x 0 • pd (zeta z T) (0 : Fin 3).succ x +
        (⁅T x 0 (0 : Fin 3).succ, dl z T 1 2 x⁆ + β x 0 • ⁅z.A x (0 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 1) (1 : Fin 3).succ x • zeta z T x +
        β x 1 • pd (zeta z T) (1 : Fin 3).succ x +
        (⁅T x 0 (1 : Fin 3).succ, dl z T 2 0 x⁆ + β x 1 • ⁅z.A x (1 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 2) (2 : Fin 3).succ x • zeta z T x +
        β x 2 • pd (zeta z T) (2 : Fin 3).succ x +
        (⁅T x 0 (2 : Fin 3).succ, dl z T 0 1 x⁆ + β x 2 • ⁅z.A x (2 : Fin 3).succ, zeta z T x⁆)) := by
  set P : Fin 3 → Fin 3 → Fin 3 → ST 3 → MatLie m := fun i j k y =>
    pd (dl z T i j) k.succ y + ⁅z.A y k.succ, dl z T i j y⁆ with hP
  have e : zeta z T = fun y => P 1 2 0 y + P 2 0 1 y + P 0 1 2 y := by
    funext y; simp only [hP]; unfold zeta blin; abel
  have hd : ∀ (i j k : Fin 3), DifferentiableAt ℝ (P i j k) x := by
    intro i j k
    exact (GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_pd_top hO (contDiffOn_dl hO hT i j) _)
      (by simp) hx).add (differentiableAt_lie ((Tuple.contDiff_vec z.A_smooth k.succ).differentiable
        (by simp) x) (diffAt_dl hO hT hx i j))
  have key : pd (zeta z T) 0 x = pd (fun y => P 1 2 0 y + P 2 0 1 y + P 0 1 2 y) 0 x := by
    rw [e]
  rw [key, pd_add' (f := fun y => P 1 2 0 y + P 2 0 1 y) (g := P 0 1 2)
    ((hd 1 2 0).add (hd 2 0 1)) (hd 0 1 2), pd_add' (f := P 1 2 0) (g := P 2 0 1) (hd 1 2 0)
    (hd 2 0 1)]
  simp only [hP]
  rw [pd_zeta_term hO hT hβ hH1 hx 1 2 0 (fun y hy => pd_dl12 hO hT hTa hH1 hNB hy),
    pd_zeta_term hO hT hβ hH1 hx 2 0 1 (fun y hy => pd_dl20 hO hT hTa hH1 hNB hy),
    pd_zeta_term hO hT hβ hH1 hx 0 1 2 (fun y hy => pd_dl01 hO hT hTa hH1 hNB hy)]

end Closed

/-! ### Flattening and the energy argument -/

section Energy

/-- The entries of a family of four `gl(m)` elements, as a real vector. -/
def flatL (m : ℕ) : (Fin 4 → MatLie m) →L[ℝ] (Fin 4 × Fin m × Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v n => ActualJetKato.toM (v n.1) n.2.1 n.2.2
      map_add' := fun v w => by funext n; rfl
      map_smul' := fun c v => by funext n; rfl }

theorem flatL_apply (v : Fin 4 → MatLie m) (n : Fin 4 × Fin m × Fin m) :
    flatL m v n = ActualJetKato.toM (v n.1) n.2.1 n.2.2 := rfl

/-- An entry of a `gl(m)` element as a linear functional. -/
def entryL (a b : Fin m) : MatLie m →ₗ[ℝ] ℝ where
  toFun M := ActualJetKato.toM M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem abs_toM_le (M : MatLie m) (a b : Fin m) : |ActualJetKato.toM M a b| ≤ ‖M‖ := by
  have h1 : ‖(M : Fin m → Fin m → ℝ) a‖ ≤ ‖(M : Fin m → Fin m → ℝ)‖ := norm_le_pi_norm _ a
  have h2 : ‖(M : Fin m → Fin m → ℝ) a b‖ ≤ ‖(M : Fin m → Fin m → ℝ) a‖ := norm_le_pi_norm _ b
  exact (Real.norm_eq_abs _ ▸ h2).trans h1

theorem norm_le_of_toM {M : MatLie m} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a b, |ActualJetKato.toM M a b| ≤ C) : ‖M‖ ≤ C := by
  show ‖(M : Fin m → Fin m → ℝ)‖ ≤ C
  refine (pi_norm_le_iff_of_nonneg hC).2 fun a => (pi_norm_le_iff_of_nonneg hC).2 fun b => ?_
  rw [Real.norm_eq_abs]; exact h a b

theorem norm_comp_le_flat (v : Fin 4 → MatLie m) (r : Fin 4) : ‖v r‖ ≤ ‖flatL m v‖ :=
  norm_le_of_toM (norm_nonneg _) fun a b => by
    rw [← flatL_apply v (r, a, b), ← Real.norm_eq_abs]; exact norm_le_pi_norm _ _

theorem norm_flat_le {v : Fin 4 → MatLie m} {C : ℝ} (hC : 0 ≤ C) (h : ∀ r, ‖v r‖ ≤ C) :
    ‖flatL m v‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun n => by
    rw [flatL_apply, Real.norm_eq_abs]; exact (abs_toM_le _ _ _).trans (h n.1)

variable {z : Tuple m V S S'} {T : ST 3 → Fin 4 → Fin 4 → MatLie m}
  {β : ST 3 → Fin 3 → ℝ}

/-- The unknowns `(δ_{23}, δ_{31}, δ_{12}, ζ)`. -/
def wv (z : Tuple m V S S') (T : ST 3 → Fin 4 → Fin 4 → MatLie m) (x : ST 3) :
    Fin 4 → MatLie m :=
  ![dl z T 1 2 x, dl z T 2 0 x, dl z T 0 1 x, zeta z T x]

/-- The coefficient matrices: `c⁰ = 1`, `c^{k+1} = -β_k` on the `ζ` entries. -/
def cG (β : ST 3 → Fin 3 → ℝ) (μ : Fin 4) (x : ST 3) (n n' : Fin 4 × Fin m × Fin m) : ℝ :=
  Fin.cases (if n = n' then 1 else 0) (fun k => if n = n' ∧ n.1 = 3 then -β x k else 0) μ

theorem cG_symm (μ : Fin 4) (x : ST 3) (n n' : Fin 4 × Fin m × Fin m) :
    cG (m := m) β μ x n n' = cG β μ x n' n := by
  induction μ using Fin.cases with
  | zero => simp only [cG, Fin.cases_zero]; by_cases h : n = n' <;> simp [h, eq_comm]
  | succ k =>
    simp only [cG, Fin.cases_succ]
    by_cases h : n = n'
    · subst h; rfl
    · simp [h, Ne.symm h]

/-- The right-hand side of the defect system. -/
def rhsG (z : Tuple m V S S') (T : ST 3 → Fin 4 → Fin 4 → MatLie m) (β : ST 3 → Fin 3 → ℝ)
    (x : ST 3) : Fin 4 → MatLie m :=
  ![β x 0 • zeta z T x, β x 1 • zeta z T x, β x 2 • zeta z T x,
    (pd (fun y => β y 0) (0 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (0 : Fin 3).succ, dl z T 1 2 x⁆ + β x 0 • ⁅z.A x (0 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 1) (1 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (1 : Fin 3).succ, dl z T 2 0 x⁆ + β x 1 • ⁅z.A x (1 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 2) (2 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (2 : Fin 3).succ, dl z T 0 1 x⁆ + β x 2 • ⁅z.A x (2 : Fin 3).succ, zeta z T x⁆))]

theorem diffAt_wv (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O) (r : Fin 4) :
    DifferentiableAt ℝ (fun y => wv z T y r) x := by
  fin_cases r
  · exact diffAt_dl hO hT hx 1 2
  · exact diffAt_dl hO hT hx 2 0
  · exact diffAt_dl hO hT hx 0 1
  · exact GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_zeta hO hT) (by simp) hx

theorem contDiffOn_wv (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) :
    ContDiffOn ℝ ∞ (wv z T) O := by
  refine contDiffOn_pi.2 fun r => ?_
  fin_cases r
  · exact contDiffOn_dl hO hT 1 2
  · exact contDiffOn_dl hO hT 2 0
  · exact contDiffOn_dl hO hT 0 1
  · exact contDiffOn_zeta hO hT

theorem pd_wv (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {x : ST 3} (hx : x ∈ O) (μ : Fin 4) :
    pd (wv z T) μ x = fun r => pd (fun y => wv z T y r) μ x := by
  funext r
  exact (ActualJetBridge.pd_apply (GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_wv hO hT)
    (by simp) hx) μ r).symm

/-- **The defect system in flattened form**: `Σ_μ c^μ ∂_μ W = flat(rhs)`. -/
theorem system_eq (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k))
    (hH1 : ∀ y ∈ O, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ) (hNB : NormalBianchi z T β O)
    {x : ST 3} (hx : x ∈ O) :
    (fun n => ∑ μ, ∑ n', cG β μ x n n' * pd (fun y => flatL m (wv z T y)) μ x n') =
      flatL m (rhsG z T β x) := by
  have hpd : ∀ μ, pd (fun y => flatL m (wv z T y)) μ x =
      flatL m (fun r => pd (fun y => wv z T y r) μ x) := by
    intro μ
    rw [GenHarmonic.pd_clm (flatL m) (GenHarmonic.diffAt_of_contDiffOn hO (contDiffOn_wv hO hT)
      (by simp) hx) μ, pd_wv hO hT hx]
  -- the system at the level of `gl(m)` vectors
  have hw0 : (fun y => wv z T y 0) = dl z T 1 2 := rfl
  have hw1 : (fun y => wv z T y 1) = dl z T 2 0 := rfl
  have hw2 : (fun y => wv z T y 2) = dl z T 0 1 := rfl
  have hw3 : (fun y => wv z T y 3) = zeta z T := rfl
  have hv0 : pd (fun y => wv z T y 0) 0 x = rhsG z T β x 0 := by
    rw [hw0, pd_dl12 hO hT hTa hH1 hNB hx]; rfl
  have hv1 : pd (fun y => wv z T y 1) 0 x = rhsG z T β x 1 := by
    rw [hw1, pd_dl20 hO hT hTa hH1 hNB hx]; rfl
  have hv2 : pd (fun y => wv z T y 2) 0 x = rhsG z T β x 2 := by
    rw [hw2, pd_dl01 hO hT hTa hH1 hNB hx]; rfl
  have hv3 : pd (fun y => wv z T y 3) 0 x +
      ∑ k : Fin 3, -(β x k • pd (fun y => wv z T y 3) k.succ x) = rhsG z T β x 3 := by
    rw [hw3, pd_zeta_time hO hT hTa hβ hH1 hNB hx, Fin.sum_univ_three]
    show _ = (pd (fun y => β y 0) (0 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (0 : Fin 3).succ, dl z T 1 2 x⁆ + β x 0 • ⁅z.A x (0 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 1) (1 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (1 : Fin 3).succ, dl z T 2 0 x⁆ + β x 1 • ⁅z.A x (1 : Fin 3).succ, zeta z T x⁆)) +
      (pd (fun y => β y 2) (2 : Fin 3).succ x • zeta z T x +
        (⁅T x 0 (2 : Fin 3).succ, dl z T 0 1 x⁆ + β x 2 • ⁅z.A x (2 : Fin 3).succ, zeta z T x⁆))
    abel
  funext n
  obtain ⟨r, a, b⟩ := n
  simp only [hpd]
  have hsum : ∑ μ, ∑ n', cG β μ x (r, a, b) n' *
      flatL m (fun q => pd (fun y => wv z T y q) μ x) n' =
      ActualJetKato.toM (pd (fun y => wv z T y r) 0 x) a b + ∑ k : Fin 3,
        (if r = 3 then -β x k * ActualJetKato.toM (pd (fun y => wv z T y r) k.succ x) a b
          else 0) := by
    rw [Fin.sum_univ_succ]
    congr 1
    · rw [Finset.sum_eq_single (r, a, b)]
      · simp [cG, flatL_apply]
      · intro n' _ hn'; simp [cG, Ne.symm hn']
      · simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single (r, a, b)]
      · by_cases hr : r = 3
        · simp [cG, flatL_apply, hr]
        · simp [cG, hr]
      · intro n' _ hn'; simp [cG, Ne.symm hn']
      · simp
  rw [hsum, flatL_apply]
  fin_cases r
  · simp only [Fin.zero_eta, Fin.isValue]
    simp only [show (0 : Fin 4) ≠ 3 by decide, ite_false, Finset.sum_const_zero, add_zero, hv0]
  · simp only [Fin.mk_one, Fin.isValue]
    simp only [show (1 : Fin 4) ≠ 3 by decide, ite_false, Finset.sum_const_zero, add_zero, hv1]
  · have e : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
    simp only [e]
    simp only [show (2 : Fin 4) ≠ 3 by decide, ite_false, Finset.sum_const_zero, add_zero, hv2]
  · have e : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
    simp only [e, ite_true]
    have hE : ∀ M : MatLie m, ActualJetKato.toM M a b = entryL a b M := fun M => rfl
    simp only [hE]
    rw [← hv3, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_neg, map_smul, smul_eq_mul, neg_mul]

end Energy

/-! ### Vanishing of the gauge defect -/

section Vanish

variable {z : Tuple m V S S'} {T : ST 3 → Fin 4 → Fin 4 → MatLie m} {β : ST 3 → Fin 3 → ℝ}

theorem contDiff_cG (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k)) (μ : Fin 4) :
    ContDiff ℝ ∞ (cG (m := m) β μ) := by
  refine contDiff_pi.2 fun n => contDiff_pi.2 fun n' => ?_
  induction μ using Fin.cases with
  | zero => simp only [cG, Fin.cases_zero]; exact contDiff_const
  | succ k =>
    simp only [cG, Fin.cases_succ]
    split_ifs
    · exact (hβ k).neg
    · exact contDiff_const

theorem isSPeriodic_cG (hβp : ∀ k, IsSPeriodic (fun y => β y k)) (μ : Fin 4) :
    IsSPeriodic (cG (m := m) β μ) := by
  intro q x
  funext n n'
  induction μ using Fin.cases with
  | zero => rfl
  | succ k =>
    simp only [cG, Fin.cases_succ]
    rw [show β (x + sshift q) k = β x k from hβp k q x]

theorem isSPeriodic_Fld' (z : Tuple m V S S') (μ ν : Fin 4) : IsSPeriodic (fun y => Fld z y μ ν) :=
  fun q x => by
    show Fm (z.jet (x + sshift q)).A (z.jet (x + sshift q)).dA μ ν = Fm (z.jet x).A (z.jet x).dA μ ν
    rw [ActualJetState.jet_per z q x]

theorem isSPeriodic_dl (hTp : IsSPeriodic T) (i j : Fin 3) : IsSPeriodic (dl z T i j) :=
  fun q x => by
    unfold dl
    have h1 := isSPeriodic_Fld' z i.succ j.succ q x
    simp only at h1
    rw [h1, hTp q x]

theorem isSPeriodic_zeta (hTp : IsSPeriodic T) : IsSPeriodic (zeta z T) := fun q x => by
  unfold zeta blin
  simp only [ActualJetState.isSPeriodic_pd' (isSPeriodic_dl hTp _ _) _ q x,
    isSPeriodic_dl (z := z) hTp _ _ q x, z.A_per q x]

theorem isSPeriodic_wv (hTp : IsSPeriodic T) : IsSPeriodic (wv z T) := fun q x => by
  funext r
  fin_cases r
  · exact isSPeriodic_dl hTp 1 2 q x
  · exact isSPeriodic_dl hTp 2 0 q x
  · exact isSPeriodic_dl hTp 0 1 q x
  · exact isSPeriodic_zeta hTp q x

/-- A field which vanishes on a slice and is differentiable there has vanishing spatial
derivatives on the slice. -/
theorem pd_zero_on_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    {t : ℝ} (h : ∀ y : Fin 3 → ℝ, f (Fin.cons t y) = 0) {x : ST 3} (hx : x 0 = t)
    (hf : DifferentiableAt ℝ f x) (j : Fin 3) : pd f j.succ x = 0 := by
  have := GenPhysIdClosed.pd_eq_of_slice (f := f) (f' := fun _ => (0 : E)) (fun y => h y) hx hf
    (differentiableAt_const _) j
  rw [this]; simp [SobolevOpen.pd]

/-- The defect unknowns vanish on the initial slice. -/
theorem wv_slice_zero {O : Set (ST 3)} (hO : IsOpen O) (hT : ContDiffOn ℝ ∞ T O) {t₀ : ℝ}
    (hsl : ∀ y : Fin 3 → ℝ, (Fin.cons t₀ y : ST 3) ∈ O)
    (hinit : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      T (Fin.cons t₀ y) i.succ j.succ = Fld z (Fin.cons t₀ y) i.succ j.succ)
    (y : Fin 3 → ℝ) : wv z T (Fin.cons t₀ y) = 0 := by
  have hdl0 : ∀ (i j : Fin 3) (y' : Fin 3 → ℝ), dl z T i j (Fin.cons t₀ y') = 0 := by
    intro i j y'; unfold dl; rw [hinit y' i j, sub_self]
  have hpd0 : ∀ (i j k : Fin 3), pd (dl z T i j) k.succ (Fin.cons t₀ y) = 0 := fun i j k =>
    pd_zero_on_slice (hdl0 i j) rfl (diffAt_dl hO hT (hsl y) i j) k
  funext r
  fin_cases r
  · exact hdl0 1 2 y
  · exact hdl0 2 0 y
  · exact hdl0 0 1 y
  · show blin z T (Fin.cons t₀ y) 0 1 2 = 0
    unfold blin
    simp only [hpd0, hdl0, lie_zero, add_zero]
    try rfl

/-- The coordinate field strength equals the reconstructed one where the defect unknowns vanish. -/
theorem T_eq_Fld_of_wv_zero (hTa : ∀ y μ ν, T y ν μ = -T y μ ν) {x : ST 3}
    (hH1 : ∀ i : Fin 3, T x 0 i.succ = pd z.A 0 x i.succ) (hw : wv z T x = 0) (μ ν : Fin 4) :
    T x μ ν = Fld z x μ ν := by
  have h12 : dl z T 1 2 x = 0 := congrFun hw 0
  have h20 : dl z T 2 0 x = 0 := congrFun hw 1
  have h01 : dl z T 0 1 x = 0 := congrFun hw 2
  have hsp : ∀ i j : Fin 3, T x i.succ j.succ = Fld z x i.succ j.succ := by
    have hd : ∀ i j : Fin 3, dl z T i j x = 0 := by
      intro i j
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl
      · exact dl_self hTa 0 x
      · exact h01
      · rw [dl_anti hTa 2 0 x, h20, neg_zero]
      · rw [dl_anti hTa 0 1 x, h01, neg_zero]
      · exact dl_self hTa 1 x
      · exact h12
      · exact h20
      · rw [dl_anti hTa 1 2 x, h12, neg_zero]
      · exact dl_self hTa 2 x
    intro i j
    have := hd i j
    unfold dl at this
    exact (sub_eq_zero.1 this).symm
  have h0 : ∀ i : Fin 3, T x 0 i.succ = Fld z x 0 i.succ := by
    intro i
    rw [hH1 i]
    show pd z.A 0 x i.succ = pd z.A 0 x i.succ - pd z.A i.succ x 0 + ⁅z.A x 0, z.A x i.succ⁆
    rw [z.dtemporal x i.succ, z.temporal x, zero_lie]
    abel
  have h00 : T x 0 0 = Fld z x 0 0 := by
    have hT0 : T x 0 0 = 0 := by
      have := hTa x 0 0
      have h2 : (2 : ℝ) • T x 0 0 = 0 := by rw [two_smul]; nth_rw 1 [this]; abel
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    rw [hT0]
    show (0 : MatLie m) = Fm (z.jet x).A (z.jet x).dA 0 0
    have := Fm_anti (z.jet x).A (z.jet x).dA 0 0
    have h2 : (2 : ℝ) • Fm (z.jet x).A (z.jet x).dA 0 0 = 0 := by
      rw [two_smul]; nth_rw 1 [this]; abel
    exact ((smul_eq_zero.1 h2).resolve_left two_ne_zero).symm
  induction μ using Fin.cases with
  | zero =>
    induction ν using Fin.cases with
    | zero => exact h00
    | succ j => exact h0 j
  | succ i =>
    induction ν using Fin.cases with
    | zero =>
      rw [hTa x 0 i.succ, h0 i]
      show -Fm (z.jet x).A (z.jet x).dA 0 i.succ = Fm (z.jet x).A (z.jet x).dA i.succ 0
      rw [Fm_anti, neg_neg]
    | succ j => exact hsp i j

/-- The uniform bound of the right-hand side of the defect system on a closed sub-slab. -/
theorem exists_rhs_bound {a b t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b)
    (hT : ContDiffOn ℝ ∞ T (openSlab a b)) (hTp : IsSPeriodic T)
    (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k)) (hβp : ∀ k, IsSPeriodic (fun y => β y k)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ slab t₀ t₁,
      ‖flatL m (rhsG z T β x)‖ ≤ K * ‖flatL m (wv z T x)‖ := by
  have hsl : ∀ k : Fin 3, ∃ C, ∀ x ∈ slab t₀ t₁, ‖β x k‖ ≤ C := fun k =>
    KatoGalerkin.exists_bound_slab (hβ k).continuous.continuousOn (hβp k) ha hb
  have hdsl : ∀ k : Fin 3, ∃ C, ∀ x ∈ slab t₀ t₁, ‖pd (fun y => β y k) k.succ x‖ ≤ C := fun k =>
    KatoGalerkin.exists_bound_slab
      (ActualJetBridge.contDiff_pd (hβ k) k.succ).continuous.continuousOn
      (ActualJetState.isSPeriodic_pd' (hβp k) k.succ) ha hb
  have hAsl : ∀ k : Fin 3, ∃ C, ∀ x ∈ slab t₀ t₁, ‖z.A x k.succ‖ ≤ C := fun k =>
    KatoGalerkin.exists_bound_slab (Tuple.contDiff_vec z.A_smooth k.succ).continuous.continuousOn
      (fun q x => by simp only [z.A_per q x]) ha hb
  have hTsl : ∀ k : Fin 3, ∃ C, ∀ x ∈ slab t₀ t₁, ‖T x 0 k.succ‖ ≤ C := fun k =>
    KatoGalerkin.exists_bound_slab (contDiffOn_Tc (isOpen_openSlab a b) hT 0 k.succ).continuousOn
      (fun q x => by show T (x + sshift q) 0 k.succ = T x 0 k.succ; rw [hTp q x]) ha hb
  choose Bβ hBβ using hsl
  choose Bd hBd using hdsl
  choose BA hBA using hAsl
  choose BT hBT using hTsl
  obtain ⟨Cb, hCb0, hCb⟩ := GenGauss.exists_lie_bound m
  set M : ℝ := ∑ k, (|Bβ k| + |Bd k| + |BA k| + |BT k|) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ => by positivity
  set K : ℝ := M + 3 * (M + Cb * M + M * (Cb * M)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hle : ∀ k : Fin 3, |Bβ k| ≤ M ∧ |Bd k| ≤ M ∧ |BA k| ≤ M ∧ |BT k| ≤ M := by
    intro k
    have hk : |Bβ k| + |Bd k| + |BA k| + |BT k| ≤ M :=
      Finset.single_le_sum (f := fun k => |Bβ k| + |Bd k| + |BA k| + |BT k|)
        (fun k _ => by positivity) (Finset.mem_univ k)
    refine ⟨by linarith [abs_nonneg (Bd k), abs_nonneg (BA k), abs_nonneg (BT k)],
      by linarith [abs_nonneg (Bβ k), abs_nonneg (BA k), abs_nonneg (BT k)],
      by linarith [abs_nonneg (Bd k), abs_nonneg (Bβ k), abs_nonneg (BT k)],
      by linarith [abs_nonneg (Bd k), abs_nonneg (BA k), abs_nonneg (Bβ k)]⟩
  refine ⟨K, hK0, fun x hx => ?_⟩
  set w := ‖flatL m (wv z T x)‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  have hζ : ‖zeta z T x‖ ≤ w := norm_comp_le_flat (wv z T x) 3
  have hd12 : ‖dl z T 1 2 x‖ ≤ w := norm_comp_le_flat (wv z T x) 0
  have hd20 : ‖dl z T 2 0 x‖ ≤ w := norm_comp_le_flat (wv z T x) 1
  have hd01 : ‖dl z T 0 1 x‖ ≤ w := norm_comp_le_flat (wv z T x) 2
  have hβx : ∀ k : Fin 3, |β x k| ≤ M := fun k => by
    have := hBβ k x hx; rw [Real.norm_eq_abs] at this; exact this.trans ((le_abs_self _).trans (hle k).1)
  have hdx : ∀ k : Fin 3, |pd (fun y => β y k) k.succ x| ≤ M := fun k => by
    have := hBd k x hx; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (hle k).2.1)
  have hAx : ∀ k : Fin 3, ‖z.A x k.succ‖ ≤ M := fun k =>
    (hBA k x hx).trans ((le_abs_self _).trans (hle k).2.2.1)
  have hTx : ∀ k : Fin 3, ‖T x 0 k.succ‖ ≤ M := fun k =>
    (hBT k x hx).trans ((le_abs_self _).trans (hle k).2.2.2)
  have hsmul : ∀ k : Fin 3, ‖β x k • zeta z T x‖ ≤ M * w := fun k => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hβx k) hζ (norm_nonneg _) hM0
  have hterm : ∀ (k : Fin 3) (D : MatLie m), ‖D‖ ≤ w →
      ‖pd (fun y => β y k) k.succ x • zeta z T x + (⁅T x 0 k.succ, D⁆ +
        β x k • ⁅z.A x k.succ, zeta z T x⁆)‖ ≤ (M + Cb * M + M * (Cb * M)) * w := by
    intro k D hD
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖pd (fun y => β y k) k.succ x • zeta z T x‖ ≤ M * w := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hdx k) hζ (norm_nonneg _) hM0
    have h2 : ‖⁅T x 0 k.succ, D⁆‖ ≤ Cb * M * w :=
      (hCb _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hTx k) hCb0) hD (norm_nonneg _)
        (by positivity))
    have h3 : ‖β x k • ⁅z.A x k.succ, zeta z T x⁆‖ ≤ M * (Cb * M) * w := by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul (hβx k) ?_ (norm_nonneg _) hM0
      exact (hCb _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hAx k) hCb0) hζ
        (norm_nonneg _) (by positivity))
    have := add_le_add h1 ((norm_add_le _ _).trans (add_le_add h2 h3))
    linarith
  have hc0 : 0 ≤ M + Cb * M + M * (Cb * M) := by positivity
  have hMK : M ≤ K := by rw [hK]; linarith
  have h3K : 3 * (M + Cb * M + M * (Cb * M)) ≤ K := by rw [hK]; linarith
  refine norm_flat_le (by positivity) fun r => ?_
  fin_cases r
  · exact (hsmul 0).trans (mul_le_mul_of_nonneg_right hMK hw0)
  · exact (hsmul 1).trans (mul_le_mul_of_nonneg_right hMK hw0)
  · exact (hsmul 2).trans (mul_le_mul_of_nonneg_right hMK hw0)
  · show ‖_ + _ + _‖ ≤ _
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have := add_le_add (add_le_add (hterm 0 _ hd12) (hterm 1 _ hd20)) (hterm 2 _ hd01)
    calc _ ≤ (M + Cb * M + M * (Cb * M)) * w + (M + Cb * M + M * (Cb * M)) * w +
          (M + Cb * M + M * (Cb * M)) * w := this
      _ = (3 * (M + Cb * M + M * (Cb * M))) * w := by ring
      _ ≤ K * w := mul_le_mul_of_nonneg_right h3K hw0

/-- **Propagation of the gauge defining-jet identities** (forward).  Let `z` be a smooth tuple,
`T` a smooth antisymmetric periodic field on `(a, b) × 𝕋³` and `β` a smooth periodic shift such
that the head row `T_{0i} = ∂_tA_i` and the normal Bianchi relation hold on the slab.  If
`T_{ij} = F(A)_{ij}` on the slice `t₀`, then `T = F(A)` on `[t₀, t₁] × 𝕋³`. -/
theorem gauge_defect_vanish {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hT : ContDiffOn ℝ ∞ T (openSlab a b)) (hTp : IsSPeriodic T)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k)) (hβp : ∀ k, IsSPeriodic (fun y => β y k))
    (hH1 : ∀ y ∈ openSlab a b, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ)
    (hNB : NormalBianchi z T β (openSlab a b))
    (hinit : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      T (Fin.cons t₀ y) i.succ j.succ = Fld z (Fin.cons t₀ y) i.succ j.succ) :
    ∀ x ∈ slab t₀ t₁, ∀ μ ν, T x μ ν = Fld z x μ ν := by
  have hO := isOpen_openSlab (d := 3) a b
  obtain ⟨K, hK0, hK⟩ := exists_rhs_bound (z := z) ha hb hT hTp hβ hβp
  have hz := GenHarmonic.sym_unique (W := fun x => flatL m (wv z T x)) (c := cG β)
    (a0 := fun _ => 1) ha h01 hb
    (((flatL m).contDiff.comp_contDiffOn (contDiffOn_wv hO hT)).of_le (by norm_cast))
    (fun q x => by simp only [isSPeriodic_wv hTp q x])
    (fun μ => ((contDiff_cG hβ μ).of_le (by norm_cast)).contDiffOn)
    (isSPeriodic_cG hβp) (fun μ x i k => cG_symm μ x i k) (fun x i k => rfl) one_pos
    (fun x _ => le_rfl) hK0
    (fun x hx => by
      rw [system_eq hO hT hTa hβ hH1 hNB (slab_subset_openSlab ha hb hx)]
      exact hK x hx)
    (fun y => by
      show flatL m (wv z T (Fin.cons t₀ y)) = 0
      rw [wv_slice_zero hO hT (fun y => ⟨by show a < t₀; linarith, by show t₀ < b; linarith⟩)
        hinit y, map_zero])
  intro x hx μ ν
  have hw : wv z T x = 0 := by
    have h1 := hz x hx
    refine funext fun r => norm_le_zero_iff.1 ?_
    have := norm_comp_le_flat (wv z T x) r
    rw [h1, norm_zero] at this
    exact this
  exact T_eq_Fld_of_wv_zero hTa (hH1 x (slab_subset_openSlab ha hb hx)) hw μ ν

/-- **Propagation of the gauge defining-jet identities** (backward). -/
theorem gauge_defect_vanish_backward {a t₁ t₀ b : ℝ} (ha : a < t₁) (h10 : t₁ < t₀)
    (hb : t₀ < b) (hT : ContDiffOn ℝ ∞ T (openSlab a b)) (hTp : IsSPeriodic T)
    (hTa : ∀ y μ ν, T y ν μ = -T y μ ν)
    (hβ : ∀ k, ContDiff ℝ ∞ (fun y => β y k)) (hβp : ∀ k, IsSPeriodic (fun y => β y k))
    (hH1 : ∀ y ∈ openSlab a b, ∀ i : Fin 3, T y 0 i.succ = pd z.A 0 y i.succ)
    (hNB : NormalBianchi z T β (openSlab a b))
    (hinit : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      T (Fin.cons t₀ y) i.succ j.succ = Fld z (Fin.cons t₀ y) i.succ j.succ) :
    ∀ x ∈ slab t₁ t₀, ∀ μ ν, T x μ ν = Fld z x μ ν := by
  have hO := isOpen_openSlab (d := 3) a b
  obtain ⟨K, hK0, hK⟩ := exists_rhs_bound (z := z) ha hb hT hTp hβ hβp
  have hz := GenBackward.sym_unique_backward (W := fun x => flatL m (wv z T x)) (c := cG β)
    (a0 := fun _ => 1) ha h10 hb
    (((flatL m).contDiff.comp_contDiffOn (contDiffOn_wv hO hT)).of_le (by norm_cast))
    (fun q x => by simp only [isSPeriodic_wv hTp q x])
    (fun μ => ((contDiff_cG hβ μ).of_le (by norm_cast)).contDiffOn)
    (isSPeriodic_cG hβp) (fun μ x i k => cG_symm μ x i k) (fun x i k => rfl) one_pos
    (fun x _ => le_rfl) hK0
    (fun x hx => by
      rw [system_eq hO hT hTa hβ hH1 hNB (slab_subset_openSlab ha hb hx)]
      exact hK x hx)
    (fun y => by
      show flatL m (wv z T (Fin.cons t₀ y)) = 0
      rw [wv_slice_zero hO hT (fun y => ⟨by show a < t₀; linarith, by show t₀ < b; linarith⟩)
        hinit y, map_zero])
  intro x hx μ ν
  have hw : wv z T x = 0 := by
    have h1 := hz x hx
    refine funext fun r => norm_le_zero_iff.1 ?_
    have := norm_comp_le_flat (wv z T x) r
    rw [h1, norm_zero] at this
    exact this
  exact T_eq_Fld_of_wv_zero hTa (hH1 x (slab_subset_openSlab ha hb hx)) hw μ ν

end Vanish

end RenewalGeometry.GenGaugeDefect
