/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedJetReadout
import RenewalGeometry.Continuum.GeneratedResidualSmooth
import RenewalGeometry.Continuum.GeneratedPhysicalIdentificationFinal

/-!
# Physical heads of a coordinate record and their jets

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("Physical Hermite
readout"): the physical head `(g, A, H, Ψ, Ψ̄)` of a state is a linear readout of the state
coordinates `κ`; the head of a coordinate family `W` (the Hermite record, or the actual-jet state
field of the exact solution) is a family of fields whose space-time jets are the linear readouts
of the jets of `W`.

* `Lg κ` (symmetrized metric block), `LA κ` (potential `(0, A_i)`), `LH κ`, `Lψ κ`, `Lψb κ` — the
  head readouts as continuous linear maps of the coordinates;
* `headJ κ`, `head1J κ` — the head 2-jets (1-jets) as linear functions of the coordinate 2-jets
  (1-jets) `GenHermite.j2c`; `contDiff_headJ`, `contDiff_head1J`;
* `hjF κ W x` — the head 2-jet of the head fields of `W`; **`hjF_eq`**: `hjF = headJ ∘ j2c`;
* **`hj2_eq_headJ`** — for the actual-jet state field `V = κ(𝒰(z))` of a smooth tuple:
  `hj2 z x = headJ κ (j2c V · x)`;
* `recTuple` — the head fields of a smooth periodic coordinate family in the Lorentzian chart on a
  slab, as a slab-local tuple (`SlabLocal.LocalTuple`), with the **symmetrized** metric;
  **`bosF_of_near`**, `dirF_of_near`, `hj2_of_near` — every global tuple agreeing with these head
  fields near `x` has residuals `bosR(headJ(j2c W x))`, `dirR(…)` there;
* `Q_congr_open` — slice norms only see a neighbourhood of the slice.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenReadout

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {n : ℕ}

/-! ### The head readouts -/

/-- The coordinate inverse `κ⁻¹` as a continuous linear map. -/
def κs (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] StateP m V S S' :=
  LinearMap.toContinuousLinearMap κ.symm.toLinearMap

/-- Symmetrization of a two-index array. -/
def symL : Met →L[ℝ] Met :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g μ ν => (g μ ν + g ν μ) / 2
      map_add' := by
        intro g h; funext μ ν; simp only [Pi.add_apply]; ring
      map_smul' := by
        intro c g; funext μ ν; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem symL_apply (g : Met) (μ ν : Fin 4) : symL g μ ν = (g μ ν + g ν μ) / 2 := rfl

theorem symL_of_symm {g : Met} (hg : ∀ μ ν, g μ ν = g ν μ) : symL g = g := by
  funext μ ν; rw [symL_apply, hg ν μ]; ring

theorem symL_symm (g : Met) (μ ν : Fin 4) : symL g μ ν = symL g ν μ := by
  rw [symL_apply, symL_apply]; ring

/-- The (symmetrized) metric readout. -/
def Lg (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] Met :=
  symL.comp ((prG' m V S S').comp (κs κ))

/-- The potential readout `(0, A_i)`. -/
def LA (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin 4 → MatLie m) :=
  (prA' m V S S').comp (κs κ)

/-- The Higgs readout. -/
def LH (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] V :=
  (GenHiggsDefect.prH m V S S').comp (κs κ)

/-- The spinor readout. -/
def Lψ (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] S :=
  (GenSpinorDefect.prψ m V S S').comp (κs κ)

/-- The dual-spinor readout. -/
def Lψb (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] S' :=
  (GenSpinorDefect.prψb m V S S').comp (κs κ)

variable (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ))

/-- The value part of a coordinate 2-jet. -/
def w0 (w : J2I 3 × Fin n → ℝ) : Fin n → ℝ := fun b => w (Sum.inl (), b)

/-- The first-derivative part of a coordinate 2-jet. -/
def w1 (w : J2I 3 × Fin n → ℝ) (μ : Fin 4) : Fin n → ℝ := fun b => w (Sum.inr (Sum.inl μ), b)

/-- The second-derivative part of a coordinate 2-jet (`∂_β∂_α`). -/
def w2 (w : J2I 3 × Fin n → ℝ) (β α : Fin 4) : Fin n → ℝ :=
  fun b => w (Sum.inr (Sum.inr (β, α)), b)

/-- **The head 2-jet of a coordinate 2-jet.** -/
def headJ (w : J2I 3 × Fin n → ℝ) : HJ2 m V S S' :=
  ((Lg κ (w0 w), fun α => Lg κ (w1 w α), fun β α => Lg κ (w2 w β α)),
    (LA κ (w0 w), fun γ => LA κ (w1 w γ), fun δ γ => LA κ (w2 w δ γ)),
    (LH κ (w0 w), fun γ => LH κ (w1 w γ), fun δ γ => LH κ (w2 w δ γ)),
    (Lψ κ (w0 w), fun γ => Lψ κ (w1 w γ)), (Lψb κ (w0 w), fun γ => Lψb κ (w1 w γ)))

/-- The value part of a coordinate 1-jet. -/
def v0 (w : J1I 3 × Fin n → ℝ) : Fin n → ℝ := fun b => w (Sum.inl (), b)

/-- The first-derivative part of a coordinate 1-jet. -/
def v1 (w : J1I 3 × Fin n → ℝ) (μ : Fin 4) : Fin n → ℝ := fun b => w (Sum.inr μ, b)

/-- **The head 1-jet of a coordinate 1-jet** (second-derivative slots zero). -/
def head1J (w : J1I 3 × Fin n → ℝ) : HJ2 m V S S' :=
  ((Lg κ (v0 w), fun α => Lg κ (v1 w α), fun _ _ => 0),
    (LA κ (v0 w), fun γ => LA κ (v1 w γ), fun _ _ => 0),
    (LH κ (v0 w), fun γ => LH κ (v1 w γ), fun _ _ => 0),
    (Lψ κ (v0 w), fun γ => Lψ κ (v1 w γ)), (Lψb κ (v0 w), fun γ => Lψb κ (v1 w γ)))

theorem contDiff_w0 : ContDiff ℝ ∞ (w0 (n := n)) :=
  contDiff_pi.2 fun b => contDiff_apply ℝ ℝ _

theorem contDiff_w1 (μ : Fin 4) : ContDiff ℝ ∞ (fun w : J2I 3 × Fin n → ℝ => w1 w μ) :=
  contDiff_pi.2 fun b => contDiff_apply ℝ ℝ _

theorem contDiff_w2 (β α : Fin 4) : ContDiff ℝ ∞ (fun w : J2I 3 × Fin n → ℝ => w2 w β α) :=
  contDiff_pi.2 fun b => contDiff_apply ℝ ℝ _

theorem contDiff_v0 : ContDiff ℝ ∞ (v0 (n := n)) :=
  contDiff_pi.2 fun b => contDiff_apply ℝ ℝ _

theorem contDiff_v1 (μ : Fin 4) : ContDiff ℝ ∞ (fun w : J1I 3 × Fin n → ℝ => v1 w μ) :=
  contDiff_pi.2 fun b => contDiff_apply ℝ ℝ _

theorem contDiff_headJ : ContDiff ℝ ∞ (headJ (m := m) (V := V) (S := S) (S' := S') κ) := by
  have h0 := contDiff_w0 (n := n)
  have h1 := contDiff_w1 (n := n)
  have h2 := contDiff_w2 (n := n)
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)))
  · exact ((Lg κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (Lg κ).contDiff.comp (h1 α)).prodMk
      (contDiff_pi.2 fun β => contDiff_pi.2 fun α => (Lg κ).contDiff.comp (h2 β α)))
  · exact ((LA κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (LA κ).contDiff.comp (h1 α)).prodMk
      (contDiff_pi.2 fun β => contDiff_pi.2 fun α => (LA κ).contDiff.comp (h2 β α)))
  · exact ((LH κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (LH κ).contDiff.comp (h1 α)).prodMk
      (contDiff_pi.2 fun β => contDiff_pi.2 fun α => (LH κ).contDiff.comp (h2 β α)))
  · exact ((Lψ κ).contDiff.comp h0).prodMk (contDiff_pi.2 fun α => (Lψ κ).contDiff.comp (h1 α))
  · exact ((Lψb κ).contDiff.comp h0).prodMk (contDiff_pi.2 fun α => (Lψb κ).contDiff.comp (h1 α))

theorem contDiff_head1J : ContDiff ℝ ∞ (head1J (m := m) (V := V) (S := S) (S' := S') κ) := by
  have h0 := contDiff_v0 (n := n)
  have h1 := contDiff_v1 (n := n)
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)))
  · exact ((Lg κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (Lg κ).contDiff.comp (h1 α)).prodMk
      contDiff_const)
  · exact ((LA κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (LA κ).contDiff.comp (h1 α)).prodMk
      contDiff_const)
  · exact ((LH κ).contDiff.comp h0).prodMk ((contDiff_pi.2 fun α => (LH κ).contDiff.comp (h1 α)).prodMk
      contDiff_const)
  · exact ((Lψ κ).contDiff.comp h0).prodMk (contDiff_pi.2 fun α => (Lψ κ).contDiff.comp (h1 α))
  · exact ((Lψb κ).contDiff.comp h0).prodMk (contDiff_pi.2 fun α => (Lψb κ).contDiff.comp (h1 α))

/-- The Dirac residual only reads the 1-jet. -/
theorem dirR_headJ (SM : SMData (MatLie m) V S S') (w : J2I 3 × Fin n → ℝ)
    (w' : J1I 3 × Fin n → ℝ) (h0 : v0 w' = w0 w) (h1 : ∀ μ, v1 w' μ = w1 w μ) :
    GenResMaps.dirR SM (headJ κ w) = GenResMaps.dirR SM (head1J κ w') := by
  have h1' : v1 w' = w1 w := funext h1
  unfold GenResMaps.dirR headJ head1J
  rw [h0, h1']

/-! ### Jets of linear readouts of families -/

/-- Spatial-temporal derivatives of a linear readout of a smooth family. -/
theorem pd_famL {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : (Fin n → ℝ) →L[ℝ] Y)
    {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b)) (μ : Fin 4) (x : ST 3) :
    pd (fun y => L (fun b => W b y)) μ x = L (fun b => pd (W b) μ x) := by
  have hd : ∀ b, DifferentiableAt ℝ (W b) x := fun b => (hW b).differentiable (by simp) x
  rw [GenHarmonic.pd_clm L (differentiableAt_pi.2 hd) μ, pd_pi_apply hd μ]

theorem pd_famL_fun {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : (Fin n → ℝ) →L[ℝ] Y) {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (μ : Fin 4) :
    pd (fun y => L (fun b => W b y)) μ = fun x => L (fun b => pd (W b) μ x) :=
  funext fun x => pd_famL L hW μ x

theorem pd_pd_famL {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : (Fin n → ℝ) →L[ℝ] Y) {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (α β : Fin 4) (x : ST 3) :
    pd (pd (fun y => L (fun b => W b y)) α) β x = L (fun b => pd (pd (W b) α) β x) := by
  rw [pd_famL_fun L hW α]
  exact pd_famL L (fun b => contDiff_pd_top (hW b) α) β x

/-! ### Head fields of a coordinate family -/

/-- The head 2-jet of the head fields of a coordinate family. -/
def hjF (W : Fin n → ST 3 → ℝ) (x : ST 3) : HJ2 m V S S' :=
  let fg := fun y => Lg κ (fun b => W b y)
  let fA := fun y => LA κ (fun b => W b y)
  let fH := fun y => LH κ (fun b => W b y)
  let fψ := fun y => Lψ κ (fun b => W b y)
  let fψb := fun y => Lψb κ (fun b => W b y)
  ((fg x, fun α => pd fg α x, fun β α => pd (pd fg α) β x),
    (fA x, fun γ => pd fA γ x, fun δ γ => pd (pd fA γ) δ x),
    (fH x, fun γ => pd fH γ x, fun δ γ => pd (pd fH γ) δ x),
    (fψ x, fun γ => pd fψ γ x), (fψb x, fun γ => pd fψb γ x))

/-- **The head 2-jet of the head fields is the head readout of the coordinate 2-jet.** -/
theorem hjF_eq {W : Fin n → ST 3 → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b)) (x : ST 3) :
    hjF (m := m) (V := V) (S := S) (S' := S') κ W x = headJ κ (fun p => j2c W p x) := by
  unfold hjF headJ w0 w1 w2 j2c jop2
  simp only [pd_famL _ hW, pd_pd_famL _ hW]

/-- The 1-jet of the head fields agrees with the head 1-jet readout. -/
theorem dirR_hjF (SM : SMData (MatLie m) V S S') {W : Fin n → ST 3 → ℝ}
    (hW : ∀ b, ContDiff ℝ ∞ (W b)) (x : ST 3) :
    GenResMaps.dirR SM (hjF κ W x) = GenResMaps.dirR SM (head1J κ (fun p => j1c W p x)) := by
  rw [hjF_eq κ hW]
  exact dirR_headJ κ SM _ _ rfl fun μ => rfl

/-! ### The exact solution -/

/-- The coordinate actual-jet state field of a tuple. -/
def stC (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') : Fin n → ST 3 → ℝ :=
  fun b y => κ (stateF SM z y) b

theorem stC_vec (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (y : ST 3) :
    (fun b => stC κ SM z b y) = κ (stateF SM z y) := rfl

theorem contDiff_stC (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (b : Fin n) :
    ContDiff ℝ ∞ (stC κ SM z b) := by
  have hκ : ContDiff ℝ ∞ (fun v : StateP m V S S' => κ v b) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).comp
      (LinearMap.toContinuousLinearMap κ.toLinearMap)).contDiff
  exact hκ.comp (contDiff_stateF SM z)

theorem isSPeriodic_stC (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (b : Fin n) :
    IsSPeriodic (stC κ SM z b) := fun k y => by
  unfold stC
  rw [isSPeriodic_stateF SM z k y]

/-- **The head jets of the exact solution are the head readouts of its coordinate jets.** -/
theorem hj2_eq_headJ (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (x : ST 3) :
    hj2 z x = headJ κ (fun p => j2c (stC κ SM z) p x) := by
  rw [← hjF_eq κ (contDiff_stC κ SM z) x]
  have hg : (fun y => Lg κ (fun b => stC κ SM z b y)) = z.g := by
    funext y
    rw [stC_vec, Lg, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    show symL (prG' m V S S' (κ.symm (κ (stateF SM z y)))) = z.g y
    rw [LinearEquiv.symm_apply_apply]
    exact symL_of_symm (z.g_symm y)
  have hA : (fun y => LA κ (fun b => stC κ SM z b y)) = z.A := by
    rw [A_eq_prA' (SM := SM) z]
    funext y
    rw [stC_vec, LA, ContinuousLinearMap.comp_apply]
    show prA' m V S S' (κ.symm (κ (stateF SM z y))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hH : (fun y => LH κ (fun b => stC κ SM z b y)) = z.H := by
    funext y
    rw [stC_vec, LH, ContinuousLinearMap.comp_apply]
    show GenHiggsDefect.prH m V S S' (κ.symm (κ (stateF SM z y))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hψ : (fun y => Lψ κ (fun b => stC κ SM z b y)) = z.ψ := by
    funext y
    rw [stC_vec, Lψ, ContinuousLinearMap.comp_apply]
    show GenSpinorDefect.prψ m V S S' (κ.symm (κ (stateF SM z y))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hψb : (fun y => Lψb κ (fun b => stC κ SM z b y)) = z.ψb := by
    funext y
    rw [stC_vec, Lψb, ContinuousLinearMap.comp_apply]
    show GenSpinorDefect.prψb m V S S' (κ.symm (κ (stateF SM z y))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hg' : Lg κ (fun b => stC κ SM z b x) = z.g x := congrFun hg x
  have hA' : LA κ (fun b => stC κ SM z b x) = z.A x := congrFun hA x
  have hH' : LH κ (fun b => stC κ SM z b x) = z.H x := congrFun hH x
  have hψ' : Lψ κ (fun b => stC κ SM z b x) = z.ψ x := congrFun hψ x
  have hψb' : Lψb κ (fun b => stC κ SM z b x) = z.ψb x := congrFun hψb x
  unfold hjF hj2
  simp only [hg, hA, hH, hψ, hψb]
  rw [hg', hA', hH', hψ', hψb']

/-! ### The record as a slab-local tuple -/

/-- The chart condition for the head metric of a coordinate state. -/
def HeadChart (w : Fin n → ℝ) : Prop :=
  (Matrix.of (Lg κ w)).det ≠ 0 ∧ IsLorChart (ginvOf (Lg κ w))

/-- **The head fields of a coordinate family in the chart, as a slab-local tuple** (metric
symmetrized, potential `(0, A_i)`). -/
def recTuple (W : Fin n → ST 3 → ℝ) (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (hWp : ∀ b, IsSPeriodic (W b)) {a b : ℝ}
    (hc : ∀ y ∈ openSlab a b, HeadChart κ (fun c => W c y)) :
    SlabLocal.LocalTuple m V S S' a b where
  g y := Lg κ (fun c => W c y)
  A y := LA κ (fun c => W c y)
  H y := LH κ (fun c => W c y)
  ψ y := Lψ κ (fun c => W c y)
  ψb y := Lψb κ (fun c => W c y)
  g_smooth := ((Lg κ).contDiff.comp (contDiff_pi.2 hW)).contDiffOn
  A_smooth := ((LA κ).contDiff.comp (contDiff_pi.2 hW)).contDiffOn
  H_smooth := ((LH κ).contDiff.comp (contDiff_pi.2 hW)).contDiffOn
  ψ_smooth := ((Lψ κ).contDiff.comp (contDiff_pi.2 hW)).contDiffOn
  ψb_smooth := ((Lψb κ).contDiff.comp (contDiff_pi.2 hW)).contDiffOn
  g_per := fun k x => by simp only [hWp _ k x]
  A_per := fun k x => by simp only [hWp _ k x]
  H_per := fun k x => by simp only [hWp _ k x]
  ψ_per := fun k x => by simp only [hWp _ k x]
  ψb_per := fun k x => by simp only [hWp _ k x]
  g_symm := fun y _ μ ν => symL_symm _ μ ν
  temporal := fun _ _ => rfl
  det_ne := fun y hy => (hc y hy).1
  lor := fun y hy => (hc y hy).2

/-- **A global tuple agreeing with the head fields near `x` has the head jets `hjF` there.** -/
theorem hj2_of_near {W : Fin n → ST 3 → ℝ} {z' : Tuple m V S S'} {x : ST 3}
    (hg : z'.g =ᶠ[𝓝 x] fun y => Lg κ (fun c => W c y))
    (hA : z'.A =ᶠ[𝓝 x] fun y => LA κ (fun c => W c y))
    (hH : z'.H =ᶠ[𝓝 x] fun y => LH κ (fun c => W c y))
    (hψ : z'.ψ =ᶠ[𝓝 x] fun y => Lψ κ (fun c => W c y))
    (hψb : z'.ψb =ᶠ[𝓝 x] fun y => Lψb κ (fun c => W c y)) :
    hj2 z' x = hjF κ W x := by
  unfold hj2 hjF
  simp only
  rw [hg.eq_of_nhds, hA.eq_of_nhds, hH.eq_of_nhds, hψ.eq_of_nhds, hψb.eq_of_nhds]
  have e1 : ∀ α, pd z'.g α x = pd (fun y => Lg κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hg α).eq_of_nhds
  have e2 : ∀ α β, pd (pd z'.g α) β x = pd (pd (fun y => Lg κ (fun c => W c y)) α) β x :=
    fun α β => (SlabLocal.pd_eventuallyEq (SlabLocal.pd_eventuallyEq hg α) β).eq_of_nhds
  have e3 : ∀ α, pd z'.A α x = pd (fun y => LA κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hA α).eq_of_nhds
  have e4 : ∀ α β, pd (pd z'.A α) β x = pd (pd (fun y => LA κ (fun c => W c y)) α) β x :=
    fun α β => (SlabLocal.pd_eventuallyEq (SlabLocal.pd_eventuallyEq hA α) β).eq_of_nhds
  have e5 : ∀ α, pd z'.H α x = pd (fun y => LH κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hH α).eq_of_nhds
  have e6 : ∀ α β, pd (pd z'.H α) β x = pd (pd (fun y => LH κ (fun c => W c y)) α) β x :=
    fun α β => (SlabLocal.pd_eventuallyEq (SlabLocal.pd_eventuallyEq hH α) β).eq_of_nhds
  have e7 : ∀ α, pd z'.ψ α x = pd (fun y => Lψ κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hψ α).eq_of_nhds
  have e8 : ∀ α, pd z'.ψb α x = pd (fun y => Lψb κ (fun c => W c y)) α x := fun α =>
    (SlabLocal.pd_eventuallyEq hψb α).eq_of_nhds
  simp only [e1, e2, e3, e4, e5, e6, e7, e8]

/-! ### Slice norms only see a neighbourhood of the slice -/

theorem sd_eqOn {f g : ST 3 → ℝ} {O : Set (ST 3)} (hO : IsOpen O) (h : EqOn f g O) :
    ∀ w : List (Fin 3), EqOn (sd w f) (sd w g) O
  | [] => h
  | i :: w => by
    rw [sd_cons, sd_cons]
    refine sd_eqOn hO (fun x hx => ?_) w
    have hev : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hO.mem_nhds hx) h
    exact (SlabLocal.pd_eventuallyEq hev i.succ).eq_of_nhds

/-- **`Q` only sees a neighbourhood of the slice.** -/
theorem Q_congr_open {f g : ST 3 → ℝ} {O : Set (ST 3)} (hO : IsOpen O) (h : EqOn f g O) {k : ℕ}
    {t : ℝ} (ht : ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) ∈ O) : Q k f t = Q k g t :=
  Q_congr fun w _ y => sd_eqOn hO h w (ht y)

end RenewalGeometry.GenReadout
