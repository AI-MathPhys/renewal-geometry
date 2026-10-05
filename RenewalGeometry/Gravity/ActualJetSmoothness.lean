/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetSystem

/-!
# Smoothness of the coefficient maps of the actual-jet system (`prop:actual-jet-writer`)

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`: "the other
coefficient maps are smooth on bounded actual-jet sets".

The state space of `ActualJetSystem` is realized as a finite-dimensional normed space
(`StateP = MetP × MatP`: metric variables `(g, p, q)` and matter variables), with the gauge algebra
`gl(m, ℝ)` (`MatLie m`, commutator bracket; every real matrix Lie algebra — in particular the
Standard-Model algebra `𝔰𝔲(3) ⊕ 𝔰𝔲(2) ⊕ 𝔲(1)` — is a subalgebra, and fields valued in a subalgebra
are a special case) and arbitrary finite-dimensional normed Higgs and spinor spaces.  On the
Lorentzian chart `MetChart` (`det g ≠ 0`, `g⁻¹` in the chart of `ActualJetFrame.frameOf`), for
theory data whose generic sources are smooth (`SMSmooth`; the Standard-Model currents, Higgs
source and Dirac–Yukawa stress coefficients are polynomial):

* `contDiffAt_ginvOf'`, `ContDiffAt.frameU_N`/`frameU_β`/`frameU_E`/`frameU_fr`,
  `ContDiffAt.frameJet` — the inverse metric, the lapse, shift and spatial frame and the frame
  derivative jets are smooth (real-analytic) functions of the metric 1-jet;
* **`Fsys_smooth`** — every block of the forcing `𝓕(𝒰)` is a smooth function of the state;
* `smooth_Bsys_*` — the residual multiplier `𝓑(𝒰)(·)` is smooth jointly in state and residuals;
* `smooth_Qsys_X`, `smooth_Qsys_Xb` — the coefficients `𝒬^j(g)` of `∂_j(r_D, r̄_D)`;
* `smooth_JC`, `smooth_Jd` — the gauge-forcing coefficients `𝒥_C(𝒰)`, `𝒥_C^μ(g)`;
* the principal operators `𝒜^j(g)` depend on `(N, β, e)` only (`ContDiffAt.frameU_*`).
-/

open RenewalGeometry ActualJetSystem ActualJetFrame ActualJetWriter HarmonicDefect FrameCurvature
  ActualJetRecon ActualJetGauge SpinorProlongation TwistedHalfRicci ActualJetSpinor
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace RenewalGeometry.ActualJetSmooth

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem contDiffAt_ginvOf' {g : Fin 4 → Fin 4 → ℝ} (h : (Matrix.of g).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ω (fun g => ginvOf g i j) g := by
  have hU : IsUnit (Matrix.of g) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  let L : (Fin 4 → Fin 4 → ℝ) →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hL : ∀ g', L g' = Matrix.of g' := fun _ => rfl
  have hinv : (fun g => ginvOf g i j) = fun g => (Ring.inverse (L g)) i j := by
    funext g'; unfold ginvOf; rw [hL, Matrix.nonsing_inv_eq_ringInverse]
  rw [hinv]
  have h1 : ContDiffAt ℝ ω (fun M : Matrix (Fin 4) (Fin 4) ℝ => Ring.inverse M) (L g) := by
    rw [hL]
    exact (analyticAt_inverse (𝕜 := ℝ) hU.unit).contDiffAt
  have h2 : ContDiffAt ℝ ω (fun g => Ring.inverse (L g)) g := h1.comp g L.contDiff.contDiffAt
  let P : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.proj j).comp (LinearMap.proj i : (Fin 4 → Fin 4 → ℝ) →ₗ[ℝ] _))
  exact (P.contDiff.contDiffAt).comp g h2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse metric of a smooth metric family is smooth where `det g ≠ 0`. -/
@[fun_prop]
theorem ContDiffAt.ginvOf {g : E → Fin 4 → Fin 4 → ℝ} {x : E} {n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g x) (hdet : (Matrix.of (g x)).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ n (fun y => ginvOf (g y) i j) x :=
  ((contDiffAt_ginvOf' hdet i j).of_le le_top).comp x hg


section FrameSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frameU_of_chart {gi : IMet} (h : IsLorChart gi) : frameU gi = frameOf gi h := by
  unfold frameU; rw [dif_pos h]

theorem frameU_N_eq {gi : IMet} (h : IsLorChart gi) : (frameU gi).N = lapse gi := by
  rw [frameU_of_chart h]; rfl

theorem frameU_β_eq {gi : IMet} (h : IsLorChart gi) (j : Fin 3) : (frameU gi).β j = shift gi j := by
  rw [frameU_of_chart h]; rfl

theorem frameU_E_eq {gi : IMet} (h : IsLorChart gi) (a j : Fin 3) :
    (frameU gi).E a j = Lmat gi j a := by
  rw [frameU_of_chart h]; rfl

theorem frameU_fr_eq {gi : IMet} (h : IsLorChart gi) (A μ : Fin 4) :
    (frameU gi).fr A μ = frU gi A μ := by
  rw [frameU_of_chart h]; rfl

theorem eventually_chart {gi : E → IMet} {x : E} (hc : ContinuousAt gi x)
    (h : IsLorChart (gi x)) : ∀ᶠ y in nhds x, IsLorChart (gi y) :=
  hc.eventually (isOpen_isLorChart.mem_nhds h)

@[fun_prop]
theorem ContDiffAt.frameU_N {gi : E → IMet} {x : E} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n gi x)
    (h : IsLorChart (gi x)) : ContDiffAt ℝ n (fun y => (frameU (gi y)).N) x := by
  refine (((contDiffAt_lapse h).of_le le_top).comp x hg).congr_of_eventuallyEq ?_
  filter_upwards [eventually_chart hg.continuousAt h] with y hy
  exact frameU_N_eq hy

@[fun_prop]
theorem ContDiffAt.frameU_β {gi : E → IMet} {x : E} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n gi x)
    (h : IsLorChart (gi x)) (j : Fin 3) : ContDiffAt ℝ n (fun y => (frameU (gi y)).β j) x := by
  refine (((contDiffAt_shift h j).of_le le_top).comp x hg).congr_of_eventuallyEq ?_
  filter_upwards [eventually_chart hg.continuousAt h] with y hy
  exact frameU_β_eq hy j

@[fun_prop]
theorem ContDiffAt.frameU_E {gi : E → IMet} {x : E} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n gi x)
    (h : IsLorChart (gi x)) (a j : Fin 3) : ContDiffAt ℝ n (fun y => (frameU (gi y)).E a j) x := by
  refine (((contDiffAt_Lmat h j a).of_le le_top).comp x hg).congr_of_eventuallyEq ?_
  filter_upwards [eventually_chart hg.continuousAt h] with y hy
  exact frameU_E_eq hy a j

@[fun_prop]
theorem ContDiffAt.frameU_fr {gi : E → IMet} {x : E} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n gi x)
    (h : IsLorChart (gi x)) (A μ : Fin 4) : ContDiffAt ℝ n (fun y => (frameU (gi y)).fr A μ) x := by
  refine (((contDiffAt_frU h A μ).of_le le_top).comp x hg).congr_of_eventuallyEq ?_
  filter_upwards [eventually_chart hg.continuousAt h] with y hy
  exact frameU_fr_eq hy A μ

/-- The frame-derivative jets are smooth in the inverse-metric 1-jet on the chart. -/
@[fun_prop]
theorem ContDiffAt.frameJet {gi : E → IMet} {dgi : E → Fin 4 → IMet} {x : E} {n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n gi x) (hdg : ContDiffAt ℝ n dgi x) (h : IsLorChart (gi x))
    (γ A μ : Fin 4) : ContDiffAt ℝ n (fun y => ActualJetFrame.frameJet (gi y) (dgi y) γ A μ) x := by
  have h1 : ContDiffAt ℝ n (fun g => fderiv ℝ (fun gi => frU gi A μ) g) (gi x) :=
    ((contDiffAt_frU h A μ).fderiv_right (m := n) (by simp)).of_le le_rfl
  have h2 : ContDiffAt ℝ n (fun y => fderiv ℝ (fun gi => frU gi A μ) (gi y)) x := h1.comp x hg
  have h3 : ContDiffAt ℝ n (fun y => dgi y γ) x := by fun_prop
  exact h2.clm_apply h3

end FrameSmooth


section Bilin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Linear maps out of finite-dimensional spaces preserve smoothness. -/
@[fun_prop]
theorem ContDiffAt.linApply (T : F →ₗ[ℝ] G) {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y => T (f y)) x :=
  (LinearMap.toContinuousLinearMap T).contDiff.contDiffAt.comp x hf

/-- Bilinear maps on finite-dimensional spaces preserve smoothness. -/
@[fun_prop]
theorem ContDiffAt.bilinApply (B : F →ₗ[ℝ] G →ₗ[ℝ] H) {f : E → F} {g : E → G} {x : E}
    {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => B (f y) (g y)) x := by
  let B' : F →L[ℝ] G →L[ℝ] H :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (G →ₗ[ℝ] H) ≃ₗ[ℝ] (G →L[ℝ] H)).toLinearMap ∘ₗ B)
  have h : (fun y => B (f y) (g y)) = fun y => B' (f y) (g y) := rfl
  rw [h]
  exact (B'.contDiff.contDiffAt.comp x hf).clm_apply hg

end Bilin

/-! ### The metric-sector reconstruction is smooth -/

section MetricSector

abbrev Met := Fin 4 → Fin 4 → ℝ

/-- The metric variables `(g, p, q)` of the state. -/
abbrev MetP := Met × Met × (Fin 3 → Met)

/-- The chart condition on the metric variables. -/
def MetChart (x : MetP) : Prop := (Matrix.of x.1).det ≠ 0 ∧ IsLorChart (ginvOf x.1)

/-- The reconstructed metric first jet `∂g` from `(g, p, q)`. -/
def dgOf (x : MetP) (γ μ ν : Fin 4) : ℝ :=
  ∑ X, cof x.1 lorentzSign (frameU (ginvOf x.1)).fr X γ * gradOfpq (x.2.1 μ ν)
    (fun a => x.2.2 a μ ν) X

@[fun_prop]
theorem ContDiffAt.gradOfpq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E → ℝ}
    {q : E → Fin 3 → ℝ} {x : E} {n : WithTop ℕ∞} (hp : ContDiffAt ℝ n p x)
    (hq : ContDiffAt ℝ n q x) (X : Fin 4) : ContDiffAt ℝ n (fun y => gradOfpq (p y) (q y) X) x := by
  induction X using Fin.cases with
  | zero => exact hp
  | succ a => exact (contDiffAt_pi.mp hq) a

theorem contDiffAt_dgOf {x : MetP} (hx : MetChart x) (γ μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y : MetP => dgOf y γ μ ν) x := by
  have h1 : ContDiffAt ℝ ∞ (fun y : MetP => y.1) x := by fun_prop
  have hgi : ∀ i j, ContDiffAt ℝ ∞ (fun y : MetP => ginvOf y.1 i j) x := fun i j =>
    ContDiffAt.ginvOf h1 hx.1 i j
  have hgi' : ContDiffAt ℝ ∞ (fun y : MetP => ginvOf y.1) x := by
    rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j; exact hgi i j
  unfold dgOf cof lorentzSign
  fun_prop (disch := exact hx.2)

end MetricSector


/-! ### `gl(m, ℝ)` as a normed Lie algebra -/

/-- `gl(m, ℝ)` (commutator bracket) with its entrywise norm. -/
def MatLie (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℝ

namespace MatLie
variable (m : ℕ)
instance : Ring (MatLie m) := inferInstanceAs (Ring (Matrix (Fin m) (Fin m) ℝ))
instance : Algebra ℝ (MatLie m) := inferInstanceAs (Algebra ℝ (Matrix (Fin m) (Fin m) ℝ))
instance : NormedAddCommGroup (MatLie m) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
instance : NormedSpace ℝ (MatLie m) := inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
instance : FiniteDimensional ℝ (MatLie m) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin m → Fin m → ℝ))
instance : LieRing (MatLie m) := LieRing.ofAssociativeRing
instance : LieAlgebra ℝ (MatLie m) := LieAlgebra.ofAssociativeAlgebra
end MatLie

section LieSmooth

variable {m : ℕ}

/-- The bracket of `gl(m)` preserves smoothness. -/
@[fun_prop]
theorem ContDiffAt.lie_mat {f g : E → MatLie m} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => ⁅f y, g y⁆) x :=
  ContDiffAt.bilinApply (LinearMap.mk₂ ℝ (fun a b : MatLie m => ⁅a, b⁆) add_lie smul_lie lie_add
    lie_smul) hf hg

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]

/-- The Lie module action of `gl(m)` preserves smoothness. -/
@[fun_prop]
theorem ContDiffAt.lie_mod {f : E → MatLie m} {g : E → V} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => ⁅f y, g y⁆) x :=
  ContDiffAt.bilinApply (LinearMap.mk₂ ℝ (fun (a : MatLie m) (v : V) => ⁅a, v⁆) add_lie smul_lie
    lie_add lie_smul) hf hg

end LieSmooth

/-- Smoothness of a `Fin.cases` family. -/
@[fun_prop]
theorem ContDiffAt.fin_cases4 {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {f0 : E → M}
    {fs : E → Fin 3 → M} {x : E} {n : WithTop ℕ∞} (h0 : ContDiffAt ℝ n f0 x)
    (hs : ContDiffAt ℝ n fs x) (X : Fin 4) :
    ContDiffAt ℝ n (fun y => (Fin.cases (f0 y) (fs y) X : M)) x := by
  induction X using Fin.cases with
  | zero => exact h0
  | succ a => exact (contDiffAt_pi.mp hs) a

@[fun_prop]
theorem ContDiffAt.ginvOf_fun {g : E → Fin 4 → Fin 4 → ℝ} {x : E} {n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g x) (hdet : (Matrix.of (g x)).det ≠ 0) :
    ContDiffAt ℝ n (fun y => ActualJetSystem.ginvOf (g y)) x := by
  rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j
  exact ContDiffAt.ginvOf hg hdet i j

/-! ### State coordinates -/

section StateCoords

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- The matter variables `(A_i, E_a, B_a, H, Π, Q_a, Ψ, X_a, Ψ̄, X̄_a)`. -/
abbrev MatP := (Fin 3 → MatLie m) × (Fin 3 → MatLie m) × (Fin 3 → MatLie m) × V × V ×
  (Fin 3 → V) × S × (Fin 3 → S) × S' × (Fin 3 → S')

variable (m V S S') in
/-- The realified actual-jet state as a finite-dimensional normed space. -/
abbrev StateP := MetP × MatP m V S S'

/-- The state with coordinates `x`. -/
def ofP (x : StateP m V S S') : State (MatLie m) V S S' where
  g := x.1.1
  p := x.1.2.1
  q := x.1.2.2
  A := x.2.1
  E := x.2.2.1
  B := x.2.2.2.1
  H := x.2.2.2.2.1
  Pm := x.2.2.2.2.2.1
  Q := x.2.2.2.2.2.2.1
  ψ := x.2.2.2.2.2.2.2.1
  X := x.2.2.2.2.2.2.2.2.1
  ψb := x.2.2.2.2.2.2.2.2.2.1
  Xb := x.2.2.2.2.2.2.2.2.2.2

variable (SM : SMData (MatLie m) V S S')

theorem smooth_g {x0 : StateP m V S S'} (hx : MetChart x0.1) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).g μ ν) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfpq, lorentzSign]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_q {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).q a μ ν) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfpq, lorentzSign, AdaptedFrame.Lq, dginv]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

end StateCoords


/-! ### Smoothness of the matter-sector operations -/

section MatterSmooth

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

@[fun_prop]
theorem ContDiffAt.fieldOfEB {Ef Bf : E → Fin 3 → MatLie m} {x : E} {n : WithTop ℕ∞}
    (hE : ContDiffAt ℝ n Ef x) (hB : ContDiffAt ℝ n Bf x) (X Y : Fin 4) :
    ContDiffAt ℝ n (fun y => ActualJetRecon.fieldOfEB (Ef y) (Bf y) X Y) x := by
  have hE' : ∀ c, ContDiffAt ℝ n (fun y => Ef y c) x := fun c => contDiffAt_pi.mp hE c
  have hB' : ∀ c, ContDiffAt ℝ n (fun y => Bf y c) x := fun c => contDiffAt_pi.mp hB c
  induction X using Fin.cases with
  | zero =>
    induction Y using Fin.cases with
    | zero => exact contDiffAt_const
    | succ c => exact hE' c
  | succ b =>
    induction Y using Fin.cases with
    | zero => exact (hE' b).neg
    | succ c =>
      show ContDiffAt ℝ n (fun y => -∑ d, eps3 b c d • Bf y d) x
      fun_prop

/-- Smoothness hypotheses on the generic sources of the theory data (the Standard-Model
currents, Higgs source and Dirac–Yukawa stress coefficients are polynomial, hence smooth). -/
structure SMSmooth (SM : SMData (MatLie m) V S S') : Prop where
  J : ∀ ν, ContDiff ℝ ∞ (fun p : Met × Met × V × (Fin 4 → V) × S × S' =>
    SM.Jcur p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ν)
  SH : ContDiff ℝ ∞ (fun p : Met × Met × V × S × S' =>
    SM.SH p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  P2 : ∀ A B, ContDiff ℝ ∞ (fun p : V × S' × S => SM.TD.P'' A B p.1 p.2.1 p.2.2)

variable {SM : SMData (MatLie m) V S S'}

@[fun_prop]
theorem ContDiffAt.Jcur (hS : SMSmooth SM) {f1 f2 : E → Met} {f3 : E → V} {f4 : E → Fin 4 → V}
    {f5 : E → S} {f6 : E → S'} {x : E} (h1 : ContDiffAt ℝ ∞ f1 x) (h2 : ContDiffAt ℝ ∞ f2 x)
    (h3 : ContDiffAt ℝ ∞ f3 x) (h4 : ContDiffAt ℝ ∞ f4 x) (h5 : ContDiffAt ℝ ∞ f5 x)
    (h6 : ContDiffAt ℝ ∞ f6 x) (ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => SM.Jcur (f1 y) (f2 y) (f3 y) (f4 y) (f5 y) (f6 y) ν) x :=
  (hS.J ν).contDiffAt.comp (f := fun y => (f1 y, f2 y, f3 y, f4 y, f5 y, f6 y)) x
    (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk h6)))))

@[fun_prop]
theorem ContDiffAt.SH (hS : SMSmooth SM) {f1 f2 : E → Met} {f3 : E → V} {f5 : E → S}
    {f6 : E → S'} {x : E} (h1 : ContDiffAt ℝ ∞ f1 x) (h2 : ContDiffAt ℝ ∞ f2 x)
    (h3 : ContDiffAt ℝ ∞ f3 x) (h5 : ContDiffAt ℝ ∞ f5 x) (h6 : ContDiffAt ℝ ∞ f6 x) :
    ContDiffAt ℝ ∞ (fun y => SM.SH (f1 y) (f2 y) (f3 y) (f5 y) (f6 y)) x :=
  hS.SH.contDiffAt.comp (f := fun y => (f1 y, f2 y, f3 y, f5 y, f6 y)) x
    (h1.prodMk (h2.prodMk (h3.prodMk (h5.prodMk h6))))

@[fun_prop]
theorem ContDiffAt.P2 (hS : SMSmooth SM) {f3 : E → V} {f5 : E → S} {f6 : E → S'} {x : E}
    (h3 : ContDiffAt ℝ ∞ f3 x) (h6 : ContDiffAt ℝ ∞ f6 x) (h5 : ContDiffAt ℝ ∞ f5 x)
    (A B : Fin 4) : ContDiffAt ℝ ∞ (fun y => SM.TD.P'' A B (f3 y) (f6 y) (f5 y)) x :=
  (hS.P2 A B).contDiffAt.comp (f := fun y => (f3 y, f6 y, f5 y)) x (h3.prodMk (h6.prodMk h5))

end MatterSmooth

section Blocks

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')

theorem smooth_B {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).B a) x0 := by
  simp (config := { maxSteps := 4000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, LBf, lowT, brCf, dginv]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_A {x0 : StateP m V S S'} (hx : MetChart x0.1) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).A i) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, lorentzSign]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_H {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).H) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfPQ, lorentzSign]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Q {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Q a) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfpq, gradOfPQ, lorentzSign, LQf, lowVf, dginv]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_E (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).E a) x0 := by
  simp (config := { maxSteps := 4000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, LEf, lowT, ymCorrF, dginv, chr]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

theorem smooth_Pm (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Pm) x0 := by
  simp only [Fsys, recon, lowerOf, ofP, cof, gradOfpq, gradOfPQ, lorentzSign, LPif, lowVf,
    dginv, chr]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

end Blocks


section Blocks2

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')

set_option maxHeartbeats 3000000 in
theorem smooth_ψ {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψ) x0 := by
  simp (config := { maxSteps := 4000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    lorentzSign, psiF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, Module.End.smul_def,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

set_option maxHeartbeats 3000000 in
theorem smooth_ψb {x0 : StateP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψb) x0 := by
  simp (config := { maxSteps := 4000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    lorentzSign, psiF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, Module.End.smul_def,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

set_option maxHeartbeats 3000000 in
theorem smooth_p (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).p μ ν) x0 := by
  simp (config := { maxSteps := 8000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, AdaptedFrame.Lp, qRem, ricciJ, dchr1, nablaC, cUp, dcUp, cDown, chr,
    dginv, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, XnatU, mass, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

end Blocks2


section Blocks3

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')

set_option maxHeartbeats 8000000 in
theorem smooth_X (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).X a) x0 := by
  simp (config := { maxSteps := 16000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, XrowF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, DHf,
    frT2, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, rhoF, XnatU, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

set_option maxHeartbeats 8000000 in
theorem smooth_Xb (hS : SMSmooth SM) {x0 : StateP m V S S'} (hx : MetChart x0.1) (a : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Xb a) x0 := by
  simp (config := { maxSteps := 16000000 }) only [Fsys, recon, lowerOf, ofP, cof, gradOfpq,
    gradOfPQ, lorentzSign, XrowF, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, DHf,
    frT2, traceRev, trG, stressF, ymStressB, higgsStressB, DiracStressForm.coord,
    DiracStressForm.frame, rhoF, XnatU, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2 | exact hS)

end Blocks3

/-! ### The residual multiplier, the differentiated-residual term and the gauge-forcing
coefficients -/

/-- An `if` on a fixed decidable proposition preserves smoothness. -/
@[fun_prop]
theorem ContDiffAt.ite_const {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (c : Prop)
    [Decidable c] {f g : E → M} {x : E} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g x) : ContDiffAt ℝ n (fun y => if c then f y else g y) x := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using hg

section Coefficients

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')

variable (m V S S') in
/-- Residual coordinates `(𝓔^{tr}, r^A, r_H, r_D, r̄_D)`. -/
abbrev ResP := Met × (Fin 4 → MatLie m) × V × S × S'

/-- The residuals with coordinates `r`. -/
def ofR (r : ResP m V S S') : Res (MatLie m) V S S' := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **The residual multiplier `𝓑(𝒰)(·)` is smooth** (jointly in the state and the residuals) on
the chart. -/
theorem smooth_Bsys_X {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1)
    (a : Fin 3) : ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).X a) (x0, r0) := by
  simp (config := { maxSteps := 16000000 }) only [Bsys, recon, ofP, ofR, cof, gradOfpq, gradOfPQ,
    lorentzSign, XrowB, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, frT2, traceRev,
    trG, stressR, DiracStressForm.stressRes, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

set_option maxHeartbeats 8000000 in
theorem smooth_Bsys_Xb {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1)
    (a : Fin 3) : ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).Xb a) (x0, r0) := by
  simp (config := { maxSteps := 16000000 }) only [Bsys, recon, ofP, ofR, cof, gradOfpq, gradOfPQ,
    lorentzSign, XrowB, omegaU, Gfun, spinPart, mass, ipg, cv1, chr, dginv, lcΓ, frT2, traceRev,
    trG, stressR, DiracStressForm.stressRes, Module.End.smul_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

set_option maxHeartbeats 4000000 in
theorem smooth_Bsys_p {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1)
    (μ ν : Fin 4) : ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).p μ ν) (x0, r0) := by
  simp (config := { maxSteps := 16000000 }) only [Bsys, recon, ofP, ofR, cof, gradOfpq, gradOfPQ,
    lorentzSign, traceRev, trG, stressR, DiracStressForm.stressRes, Module.End.smul_def]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Bsys_E {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1)
    (a : Fin 3) : ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).E a) (x0, r0) := by
  simp only [Bsys, recon, ofP, ofR]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Bsys_Pm {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).Pm) (x0, r0) := by
  simp only [Bsys, recon, ofP, ofR]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Bsys_ψ {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).ψ) (x0, r0) := by
  simp only [Bsys, recon, ofP, ofR, Module.End.smul_def]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Bsys_ψb {x0 : StateP m V S S'} {r0 : ResP m V S S'} (hx : MetChart x0.1) :
    ContDiffAt ℝ ∞ (fun z : StateP m V S S' × ResP m V S S' =>
      (Bsys SM (ofP z.1) (ofR z.2)).ψb) (x0, r0) := by
  simp only [Bsys, recon, ofP, ofR, Module.End.smul_def]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

/-- **The differentiated Dirac-residual coefficients `𝒬^j(g)` are smooth** (they depend on the
metric only). -/
theorem smooth_Qsys_X {x0 : StateP m V S S'} {d0 : S × S'} (hx : MetChart x0.1) (j a : Fin 3) :
    ContDiffAt ℝ ∞ (fun z : StateP m V S S' × (S × S') =>
      (Qsys SM (ofP z.1) j z.2.1 z.2.2).X a) (x0, d0) := by
  simp only [Qsys, ofP, Module.End.smul_def]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Qsys_Xb {x0 : StateP m V S S'} {d0 : S × S'} (hx : MetChart x0.1) (j a : Fin 3) :
    ContDiffAt ℝ ∞ (fun z : StateP m V S S' × (S × S') =>
      (Qsys SM (ofP z.1) j z.2.1 z.2.2).Xb a) (x0, d0) := by
  simp only [Qsys, ofP, Module.End.smul_def]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

/-- **The gauge-forcing coefficients are smooth**: `𝒥_C(𝒰)` (`JC`, on the reconstructed metric
first jet) and `𝒥_C^μ(g)` (`Jd`). -/
theorem smooth_JC {x0 : MetP} (hx : MetChart x0) (μ ν l : Fin 4) :
    ContDiffAt ℝ ∞ (fun x : MetP => JC (frameU (ginvOf x.1)) x.1 (ginvOf x.1)
      (fun γ μ ν => ∑ X, cof x.1 lorentzSign (frameU (ginvOf x.1)).fr X γ *
        gradOfpq (x.2.1 μ ν) (fun a => x.2.2 a μ ν) X) μ ν l) x0 := by
  simp only [JC, chr, cof, gradOfpq, lorentzSign]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

theorem smooth_Jd {x0 : MetP} (hx : MetChart x0) (α μ ν l : Fin 4) :
    ContDiffAt ℝ ∞ (fun x : MetP => Jd (frameU (ginvOf x.1)) x.1 α μ ν l) x0 := by
  simp only [Jd]
  fun_prop (disch := first | exact hx.1 | exact hx.2)

end Coefficients

/-! ### The forcing is smooth -/

section Package

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **`prop:actual-jet-writer`: the forcing `𝓕(𝒰)` is a smooth function of the actual-jet state**
on the Lorentzian chart (every block). -/
theorem Fsys_smooth (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM) {x0 : StateP m V S S'}
    (hx : MetChart x0.1) :
    (∀ μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).g μ ν) x0) ∧
    (∀ μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).p μ ν) x0) ∧
    (∀ a μ ν, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).q a μ ν) x0) ∧
    (∀ i, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).A i) x0) ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).E a) x0) ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).B a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).H) x0 ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Pm) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Q a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψ) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).X a) x0) ∧
    ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).ψb) x0 ∧
    (∀ a, ContDiffAt ℝ ∞ (fun x => (Fsys SM (ofP x)).Xb a) x0) :=
  ⟨smooth_g SM hx, smooth_p SM hS hx, smooth_q SM hx, smooth_A SM hx, smooth_E SM hS hx,
    smooth_B SM hx, smooth_H SM hx, smooth_Pm SM hS hx, smooth_Q SM hx, smooth_ψ SM hx,
    smooth_X SM hS hx, smooth_ψb SM hx, smooth_Xb SM hS hx⟩

end Package

/-! ### Non-vacuity -/

section NonVacuity

theorem minkInv_det : (Matrix.of minkInv).det ≠ 0 := by
  have h : Matrix.of minkInv * Matrix.of minkInv = 1 := by
    ext a c; rw [Matrix.mul_apply, Matrix.one_apply]; exact minkInv_sq a c
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem ginvOf_minkInv : ginvOf minkInv = minkInv := by
  have h : Matrix.of minkInv * Matrix.of minkInv = 1 := by
    ext a c; rw [Matrix.mul_apply, Matrix.one_apply]; exact minkInv_sq a c
  funext i j; unfold ginvOf; rw [Matrix.inv_eq_right_inv h]; rfl

theorem metChart_mink : MetChart (minkInv, 0, 0) :=
  ⟨minkInv_det, by rw [ginvOf_minkInv]; exact minkInv_isLorChart⟩

/-- A Dirac block on the zero spinor space for the gauge algebra `gl(1)`. -/
def trivDiracM : DiracData (MatLie 1) (MatLie 1) PUnit where
  Fr := trivFrame
  ρ := 0
  ρ_lie := fun _ _ => Subsingleton.elim _ _
  m0 := 0
  L := 0
  lorentz := ⟨by simp [trivFrame, lorentzSign], fun a => by
    simp [trivFrame, lorentzSign, Fin.succ_ne_zero]⟩
  comm := fun _ _ => Subsingleton.elim _ _
  mass_cl := fun _ _ _ => Subsingleton.elim _ _
  mass_eq := fun _ _ => Subsingleton.elim _ _

/-- Theory data with vanishing sources (gauge algebra `gl(1)`, adjoint Higgs). -/
def trivSMM : SMData (MatLie 1) (MatLie 1) PUnit PUnit where
  Λ := 0
  κ := 1
  D := trivDiracM
  Db := trivDiracM
  Jcur := fun _ _ _ _ _ _ _ => 0
  SH := fun _ _ _ _ _ => 0
  ipG := 0
  ipV := 0
  lamH := 0
  vH := 0
  TD := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

theorem trivSMM_smooth : SMSmooth trivSMM where
  J := fun _ => contDiff_const
  SH := contDiff_const
  P2 := fun A B => by
    have : (fun p : MatLie 1 × PUnit × PUnit => trivSMM.TD.P'' A B p.1 p.2.1 p.2.2) =
        fun _ => (0 : ℝ) := by funext p; rfl
    rw [this]; exact contDiff_const

/-- **Non-vacuity**: the hypotheses of `Fsys_smooth` hold (Minkowski metric, vanishing sources). -/
example : MetChart ((minkInv, 0, 0) : MetP) ∧ SMSmooth trivSMM := ⟨metChart_mink, trivSMM_smooth⟩

end NonVacuity

end RenewalGeometry.ActualJetSmooth
