/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetCurveCalculus
import RenewalGeometry.Continuum.SlabWaveEnergyHk

/-!
# From smooth slab fields to actual jets (`prop:coupled-bootstrap`, the pointwise bridge)

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap` and
`thm:native-closure` ("the state `𝒰_h` is built from the actual derivatives and curvatures of
`z_h`; no independent jet variables are supplied").

A **smooth actual field tuple** (`Tuple`) on space-time `ℝ^{1+3}` (spatially periodic) consists of
a metric `g_{μν}`, a gauge potential `A_μ ∈ gl(m)` in exact temporal gauge `A_0 ≡ 0`, a Higgs field
and both spinors, all `C^∞`, with the metric in the Lorentzian foliated chart (`MetChart`).
At every point `x` the actual derivatives of the fields form an `ActualJetSystem.ActualJet`
(`Tuple.jet`): the metric 2-jet, the 2-jet of the fixed adapted frame `frU(g⁻¹)` (its first
derivative is the frame jet `frameJet(g⁻¹, ∂g⁻¹)` by the chain rule, its second derivative is the
actual second derivative), and the 2-jets of the matter fields.

## Main results

* `Tuple.frameJet` — the frame 2-jet at a point is an orthonormal `FrameCurvature.FrameJet`
  (orthonormality from the adapted-frame identity `frameOf_adapted`; its first and second
  derivatives `orth1`, `orth2` by differentiating along lines);
* `Tuple.jet` — the actual jet at a point;
* the derivative identities of the frame fields (`pd_e`, `pd_gi`) used by the state bridge.
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetBridge

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci JetCurve

set_option linter.unusedSectionVars false

/-! ### Calculus of vector-valued partial derivatives -/

section Calc

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial derivatives commute with evaluation of a component. -/
theorem pd_apply {ι : Type*} [Fintype ι] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : ST d → ι → E'} {x : ST d} (hF : DifferentiableAt ℝ F x) (μ : Fin (d + 1)) (i : ι) :
    pd (fun y => F y i) μ x = pd F μ x i := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun y => F y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E') i).hasFDerivAt.comp x
      hF.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- Smoothness of a partial derivative of a smooth vector-valued field. -/
theorem contDiff_pd {F : ST d → E} (hF : ContDiff ℝ ∞ F) (μ : Fin (d + 1)) :
    ContDiff ℝ ∞ (pd F μ) := by
  unfold SobolevOpen.pd
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Symmetry of second partial derivatives of a smooth vector-valued field. -/
theorem pd_pd_comm' {F : ST d → E} (hF : ContDiff ℝ ∞ F) (μ ν : Fin (d + 1)) (x : ST d) :
    pd (pd F μ) ν x = pd (pd F ν) μ x := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have hsymm := (hF2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ F y (Pi.single μ 1)) x (Pi.single ν 1) =
    fderiv ℝ (fun y => fderiv ℝ F y (Pi.single ν 1)) x (Pi.single μ 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp
  exact hsymm _ _

/-- The derivative of a field along the line `s ↦ x + s e_μ` at `s = 0`. -/
theorem hasDerivAt_line0 {F : ST d → E} {x : ST d} (hF : DifferentiableAt ℝ F x)
    (μ : Fin (d + 1)) : HasDerivAt (fun s : ℝ => F (x + s • ev μ)) (pd F μ x) 0 := by
  have h := PeriodicCube.hasDerivAt_line (f := F) (x := x) μ (s := 0) (by simpa using hF)
  simpa using h

/-- Components of a vector-valued field along a line. -/
theorem hasDerivAt_line0_apply {ι : Type*} [Fintype ι] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {F : ST d → ι → E'} {x : ST d} (hF : DifferentiableAt ℝ F x)
    (μ : Fin (d + 1)) (i : ι) :
    HasDerivAt (fun s : ℝ => F (x + s • ev μ) i) (pd F μ x i) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_line0 hF μ) i

/-- If a field has derivative `D` along the line `x + s e_μ` at `0` and is differentiable at `x`,
then its partial derivative is `D`. -/
theorem pd_eq_of_line {F : ST d → E} {x : ST d} (hF : DifferentiableAt ℝ F x) {μ : Fin (d + 1)}
    {D : E} (h : HasDerivAt (fun s : ℝ => F (x + s • ev μ)) D 0) : pd F μ x = D :=
  (hasDerivAt_line0 hF μ).unique h

end Calc

/-! ### Orthonormality from the adapted-frame identity -/

/-- If `g g⁻¹ = 1` and `g^{μν} = Σ_A ε_A e_A^μ e_A^ν` with `ε_A² = 1`, the frame is orthonormal:
`g(e_A, e_B) = ε_A δ_{AB}`. -/
theorem orth_of_compl {g gi e : Fin 4 → Fin 4 → ℝ} {ε : Fin 4 → ℝ}
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hε : ∀ A, ε A ^ 2 = 1) (hcompl : ∀ μ ν, gi μ ν = ∑ A, ε A * e A μ * e A ν) (A B : Fin 4) :
    ipg g (e A) (e B) = if A = B then ε A else 0 := by
  set G := Matrix.of g
  set Gi := Matrix.of gi
  set Em := Matrix.of e
  set D := Matrix.diagonal ε
  have hGGi : G * Gi = 1 := by
    ext a c; rw [Matrix.mul_apply, Matrix.one_apply]; exact hinv a c
  have hGi : Gi = Em.transpose * D * Em := by
    ext μ ν
    simp only [Gi, Em, D, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [hcompl]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  have hDD : D * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a c
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [← sq, hε]
  -- `E` is invertible
  have hdetGi : Gi.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hGGi
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetE : Em.det ≠ 0 := by
    intro h0
    apply hdetGi
    rw [hGi, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hEu : IsUnit Em.det := isUnit_iff_ne_zero.mpr hdetE
  -- `E G Eᵀ D = 1`
  have key : Em * G * Em.transpose * D = 1 := by
    have h1 : G * (Em.transpose * D * Em) = 1 := by rw [← hGi]; exact hGGi
    have h2 : (Em * G * Em.transpose * D) * Em = Em := by
      calc (Em * G * Em.transpose * D) * Em = Em * (G * (Em.transpose * D * Em)) := by
            simp only [Matrix.mul_assoc]
        _ = Em := by rw [h1, Matrix.mul_one]
    have h3 := congrArg (fun M => M * Em⁻¹) h2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hEu, Matrix.mul_one] at h3
    simpa [Matrix.mul_assoc] using h3
  have key2 : Em * G * Em.transpose = D := by
    have := congrArg (fun M => M * D) key
    simp only [Matrix.mul_assoc, hDD, Matrix.mul_one, Matrix.one_mul] at this
    simpa [Matrix.mul_assoc] using this
  have h := congrFun (congrFun key2 A) B
  simp only [Em, G, D, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.diagonal_apply] at h
  rw [← h]
  unfold ipg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring


/-! ### Smooth actual field tuples -/

section Tuple

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- **A smooth actual field tuple** on `ℝ × 𝕋³` (`prop:coupled-bootstrap`: "a smooth actual field
tuple on the slab and foliated chart, in exact temporal internal gauge"): metric `g_{μν}`, gauge
potential `A_μ ∈ gl(m)` with `A_0 ≡ 0`, Higgs field and both spinors, all `C^∞` and `ℤ³`-periodic in
space, with the metric in the Lorentzian foliated chart at every point. -/
structure Tuple where
  g : ST 3 → Fin 4 → Fin 4 → ℝ
  A : ST 3 → Fin 4 → MatLie m
  H : ST 3 → V
  ψ : ST 3 → S
  ψb : ST 3 → S'
  g_smooth : ContDiff ℝ ∞ g
  A_smooth : ContDiff ℝ ∞ A
  H_smooth : ContDiff ℝ ∞ H
  ψ_smooth : ContDiff ℝ ∞ ψ
  ψb_smooth : ContDiff ℝ ∞ ψb
  g_per : SymHypEnergy.IsSPeriodic g
  A_per : SymHypEnergy.IsSPeriodic A
  H_per : SymHypEnergy.IsSPeriodic H
  ψ_per : SymHypEnergy.IsSPeriodic ψ
  ψb_per : SymHypEnergy.IsSPeriodic ψb
  g_symm : ∀ x μ ν, g x μ ν = g x ν μ
  temporal : ∀ x, A x 0 = 0
  det_ne : ∀ x, (Matrix.of (g x)).det ≠ 0
  lor : ∀ x, IsLorChart (ginvOf (g x))

namespace Tuple

variable (z : Tuple m V S S')

/-- The inverse metric field. -/
def gi (y : ST 3) : Fin 4 → Fin 4 → ℝ := ginvOf (z.g y)

/-- The metric first jet `∂_αg_{μν}`. -/
def dg (y : ST 3) : Fin 4 → Fin 4 → Fin 4 → ℝ := fun α => pd z.g α y

/-- The metric second jet `∂_β∂_αg_{μν}`. -/
def ddg (y : ST 3) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun β α => pd (pd z.g α) β y

/-- The adapted frame field `e_A{}^μ = frU(g⁻¹)`. -/
def e (y : ST 3) : Fin 4 → Fin 4 → ℝ := fun A μ => frU (z.gi y) A μ

/-- The frame jet `∂_γe_A{}^μ = frameJet(g⁻¹, ∂g⁻¹)`. -/
def de (y : ST 3) : Fin 4 → Fin 4 → Fin 4 → ℝ := fun γ A μ =>
  ActualJetFrame.frameJet (z.gi y) (fun γ l σ => dginv (z.gi y) (z.dg y) γ l σ) γ A μ

/-- The second frame jet: the actual derivative of the frame-jet field. -/
def dde (y : ST 3) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun δ γ A μ =>
  pd (fun y => z.de y γ A μ) δ y

/-! #### Smoothness of the jet fields -/

theorem contDiff_gc (μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => z.g y μ ν) :=
  contDiff_pi.1 (contDiff_pi.1 z.g_smooth μ) ν

theorem contDiff_dg (α μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => z.dg y α μ ν) :=
  contDiff_pi.1 (contDiff_pi.1 (contDiff_pd z.g_smooth α) μ) ν

theorem contDiff_ddg (β α μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => z.ddg y β α μ ν) :=
  contDiff_pi.1 (contDiff_pi.1 (contDiff_pd (contDiff_pd z.g_smooth α) β) μ) ν

theorem contDiffAt_gi_fun (y : ST 3) : ContDiffAt ℝ ∞ (fun y => z.gi y) y :=
  ContDiffAt.ginvOf_fun z.g_smooth.contDiffAt (z.det_ne y)

theorem contDiff_gi (l σ : Fin 4) : ContDiff ℝ ∞ (fun y => z.gi y l σ) :=
  contDiff_iff_contDiffAt.2 fun y => ContDiffAt.ginvOf z.g_smooth.contDiffAt (z.det_ne y) l σ

theorem contDiff_e (A μ : Fin 4) : ContDiff ℝ ∞ (fun y => z.e y A μ) :=
  contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.comp (g := fun gi => frU gi A μ) (f := fun y => z.gi y) y
      ((contDiffAt_frU (z.lor y) A μ).of_le le_top) (z.contDiffAt_gi_fun y)

theorem contDiff_dginv (γ l σ : Fin 4) :
    ContDiff ℝ ∞ (fun y => dginv (z.gi y) (z.dg y) γ l σ) := by
  have h1 := z.contDiff_gi
  have h2 := z.contDiff_dg
  unfold dginv
  fun_prop

theorem contDiff_de (γ A μ : Fin 4) : ContDiff ℝ ∞ (fun y => z.de y γ A μ) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  have hdgi : ContDiffAt ℝ ∞ (fun y => fun γ l σ => dginv (z.gi y) (z.dg y) γ l σ) y := by
    rw [contDiffAt_pi]; intro γ; rw [contDiffAt_pi]; intro l; rw [contDiffAt_pi]; intro σ
    exact (z.contDiff_dginv γ l σ).contDiffAt
  exact ContDiffAt.frameJet (z.contDiffAt_gi_fun y) hdgi (z.lor y) γ A μ

theorem contDiff_dde (δ γ A μ : Fin 4) : ContDiff ℝ ∞ (fun y => z.dde y δ γ A μ) :=
  contDiff_pd (z.contDiff_de γ A μ) δ

/-! #### Line derivatives of the jet fields -/

variable (x : ST 3) (δ : Fin 4)

theorem line_g (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => z.g (x + s • ev δ) μ ν) (z.dg x δ μ ν) 0 := by
  have h := hasDerivAt_line0_apply (z.g_smooth.differentiable (by simp) x) δ μ
  exact hasDerivAt_pi.1 h ν

theorem line_dg (α μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => z.dg (x + s • ev δ) α μ ν) (z.ddg x δ α μ ν) 0 := by
  have h := hasDerivAt_line0_apply ((contDiff_pd z.g_smooth α).differentiable (by simp) x) δ μ
  exact hasDerivAt_pi.1 h ν

theorem line_gi (l σ : Fin 4) :
    HasDerivAt (fun s : ℝ => z.gi (x + s • ev δ) l σ) (dginv (z.gi x) (z.dg x) δ l σ) 0 := by
  have h := hasDerivAt_ginvOf (g := fun s : ℝ => z.g (x + s • ev δ)) (t := 0) (dg := z.dg x) δ
    (fun μ ν => z.line_g x δ μ ν) (by simpa using z.det_ne x) l σ
  simpa [gi] using h

theorem line_e (A μ : Fin 4) :
    HasDerivAt (fun s : ℝ => z.e (x + s • ev δ) A μ) (z.de x δ A μ) 0 := by
  have h := hasDerivAt_frU (gi := fun s : ℝ => z.gi (x + s • ev δ)) (t := 0)
    (dgi := fun γ l σ => dginv (z.gi x) (z.dg x) γ l σ) δ (fun l σ => z.line_gi x δ l σ)
    (by simpa [gi] using z.lor x) A μ
  simpa [e, de] using h

theorem line_de (γ A μ : Fin 4) :
    HasDerivAt (fun s : ℝ => z.de (x + s • ev δ) γ A μ) (z.dde x δ γ A μ) 0 :=
  hasDerivAt_line0 ((z.contDiff_de γ A μ).differentiable (by simp) x) δ

/-- **The frame jet is the actual derivative of the frame field.** -/
theorem pd_e (A μ : Fin 4) : pd (fun y => z.e y A μ) δ x = z.de x δ A μ :=
  pd_eq_of_line ((z.contDiff_e A μ).differentiable (by simp) x) (z.line_e x δ A μ)

theorem dde_symm (δ' : Fin 4) (A μ : Fin 4) : z.dde x δ δ' A μ = z.dde x δ' δ A μ := by
  have hfun : ∀ γ, (fun y => z.de y γ A μ) = pd (fun y => z.e y A μ) γ := fun γ =>
    funext fun y => (z.pd_e y γ A μ).symm
  show pd (fun y => z.de y δ' A μ) δ x = pd (fun y => z.de y δ A μ) δ' x
  rw [hfun δ', hfun δ]
  exact pd_pd_comm' (z.contDiff_e A μ) δ' δ x

end Tuple

end Tuple

/-! ### The frame jet and the actual jet at a point -/

section Jet

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

theorem ginvOf_symm {g : Fin 4 → Fin 4 → ℝ} (hg : ∀ μ ν, g μ ν = g ν μ) (l σ : Fin 4) :
    ginvOf g l σ = ginvOf g σ l := by
  have hT : (Matrix.of g).transpose = Matrix.of g := by
    ext a b; simp [hg b a]
  unfold ginvOf
  have := congrFun (congrFun (Matrix.transpose_nonsing_inv (Matrix.of g)) σ) l
  rw [hT] at this
  simpa using this

theorem mul_ginvOf {g : Fin 4 → Fin 4 → ℝ} (hdet : (Matrix.of g).det ≠ 0) (a c : Fin 4) :
    ∑ b, g a b * ginvOf g b c = if a = c then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (Matrix.of g) (isUnit_iff_ne_zero.mpr hdet)
  have := congrFun (congrFun h a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [ginvOf] using this

theorem lorentzSign_sq (A : Fin 4) : lorentzSign A ^ 2 = 1 := by
  unfold lorentzSign; split_ifs <;> norm_num

namespace Tuple

variable (z : Tuple m V S S') (x : ST 3)

theorem gi_symm (l σ : Fin 4) : z.gi x l σ = z.gi x σ l := ginvOf_symm (z.g_symm x) l σ

theorem hinv (a c : Fin 4) : ∑ b, z.g x a b * z.gi x b c = if a = c then 1 else 0 :=
  mul_ginvOf (z.det_ne x) a c

/-- Completeness of the adapted frame: `g^{μν} = Σ_A ε_A e_A^μ e_A^ν`. -/
theorem compl (μ ν : Fin 4) : z.gi x μ ν = ∑ A, lorentzSign A * z.e x A μ * z.e x A ν := by
  have h := frameOf_adapted (z.gi_symm x) (z.lor x) μ ν
  rw [Fin.sum_univ_succ]
  simp only [lorentzSign, Fin.succ_ne_zero, ite_false, ite_true, one_mul]
  rw [h]
  simp only [e]
  rw [neg_one_mul, neg_mul]
  rfl

theorem orth_at (A B : Fin 4) :
    ipg (z.g x) (z.e x A) (z.e x B) = if A = B then lorentzSign A else 0 :=
  orth_of_compl (z.hinv x) lorentzSign_sq (z.compl x) A B

theorem dg_apply (α μ ν : Fin 4) : z.dg x α μ ν = pd (fun y => z.g y μ ν) α x := by
  have h1 := pd_apply (z.g_smooth.differentiable (by simp) x) α μ
  have h2 := pd_apply (F := fun y => z.g y μ)
    ((contDiff_pi.1 z.g_smooth μ).differentiable (by simp) x) α ν
  rw [h2, h1]; rfl

theorem dg_symm (α μ ν : Fin 4) : z.dg x α μ ν = z.dg x α ν μ := by
  rw [z.dg_apply, z.dg_apply]
  congr 1
  funext y
  exact z.g_symm y μ ν

theorem ddg_apply (β α μ ν : Fin 4) :
    z.ddg x β α μ ν = pd (pd (fun y => z.g y μ ν) α) β x := by
  have hfun : pd (fun y => z.g y μ ν) α = fun y => z.dg y α μ ν :=
    funext fun y => (z.dg_apply y α μ ν).symm
  rw [hfun]
  have h1 := pd_apply ((contDiff_pd z.g_smooth α).differentiable (by simp) x) β μ
  have h2 := pd_apply (F := fun y => pd z.g α y μ)
    ((contDiff_pi.1 (contDiff_pd z.g_smooth α) μ).differentiable (by simp) x) β ν
  show pd (pd z.g α) β x μ ν = pd (fun y => pd z.g α y μ ν) β x
  rw [h2, h1]

theorem ddg_symm1 (α β μ ν : Fin 4) : z.ddg x α β μ ν = z.ddg x β α μ ν := by
  show pd (pd z.g β) α x μ ν = pd (pd z.g α) β x μ ν
  rw [pd_pd_comm' z.g_smooth β α x]

theorem ddg_symm2 (α β μ ν : Fin 4) : z.ddg x α β μ ν = z.ddg x α β ν μ := by
  rw [z.ddg_apply, z.ddg_apply]
  have : (fun y => z.g y μ ν) = fun y => z.g y ν μ := funext fun y => z.g_symm y μ ν
  rw [this]

theorem orth1 (γ A B : Fin 4) :
    dipg (z.g x) (z.dg x) (z.e x A) (fun γ μ => z.de x γ A μ) (z.e x B)
      (fun γ μ => z.de x γ B μ) γ = 0 := by
  have h := hasDerivAt_ipg (g := fun s : ℝ => z.g (x + s • ev γ))
    (X := fun s : ℝ => z.e (x + s • ev γ) A) (Y := fun s : ℝ => z.e (x + s • ev γ) B)
    (t := 0) (dg := z.dg x) (dX := fun γ μ => z.de x γ A μ) (dY := fun γ μ => z.de x γ B μ) γ
    (z.line_g x γ) (z.line_e x γ A) (z.line_e x γ B)
  simp only [zero_smul, add_zero] at h
  have hc : (fun s : ℝ => ipg (z.g (x + s • ev γ)) (z.e (x + s • ev γ) A)
      (z.e (x + s • ev γ) B)) = fun _ => if A = B then lorentzSign A else 0 :=
    funext fun s => z.orth_at _ A B
  rw [hc] at h
  exact h.unique (hasDerivAt_const _ _)

theorem orth2 (δ γ A B : Fin 4) :
    ddipg (z.g x) (z.dg x) (z.ddg x) (z.e x A) (fun γ μ => z.de x γ A μ)
      (fun δ γ μ => z.dde x δ γ A μ) (z.e x B) (fun γ μ => z.de x γ B μ)
      (fun δ γ μ => z.dde x δ γ B μ) δ γ = 0 := by
  have h := hasDerivAt_dipg (g := fun s : ℝ => z.g (x + s • ev δ))
    (dg := fun s : ℝ => z.dg (x + s • ev δ)) (X := fun s : ℝ => z.e (x + s • ev δ) A)
    (Y := fun s : ℝ => z.e (x + s • ev δ) B)
    (dX := fun s : ℝ => fun γ μ => z.de (x + s • ev δ) γ A μ)
    (dY := fun s : ℝ => fun γ μ => z.de (x + s • ev δ) γ B μ) (t := 0) (ddg := z.ddg x)
    (ddX := fun δ γ μ => z.dde x δ γ A μ) (ddY := fun δ γ μ => z.dde x δ γ B μ) δ γ
    (by simpa using z.line_g x δ) (fun μ ν => z.line_dg x δ γ μ ν)
    (by simpa using z.line_e x δ A) (fun μ => z.line_de x δ γ A μ)
    (by simpa using z.line_e x δ B) (fun μ => z.line_de x δ γ B μ)
  simp only [zero_smul, add_zero] at h
  have hc : (fun s : ℝ => dipg (z.g (x + s • ev δ)) (z.dg (x + s • ev δ))
      (z.e (x + s • ev δ) A) (fun γ μ => z.de (x + s • ev δ) γ A μ) (z.e (x + s • ev δ) B)
      (fun γ μ => z.de (x + s • ev δ) γ B μ) γ) = fun _ => 0 :=
    funext fun s => z.orth1 _ γ A B
  rw [hc] at h
  exact h.unique (hasDerivAt_const _ _)

/-- **The frame 2-jet of the tuple at `x`** (an orthonormal `FrameJet`). -/
def FJ : FrameJet (Fin 4) (Fin 4) where
  g := z.g x
  gi := z.gi x
  dg := z.dg x
  ddg := z.ddg x
  ε := lorentzSign
  e := z.e x
  de := z.de x
  dde := z.dde x
  g_symm := z.g_symm x
  gi_symm := z.gi_symm x
  hinv := z.hinv x
  dg_symm := z.dg_symm x
  ddg_symm1 := z.ddg_symm1 x
  ddg_symm2 := z.ddg_symm2 x
  dde_symm := fun δ γ A μ => z.dde_symm x δ γ A μ
  sign_sq := lorentzSign_sq
  orth := z.orth_at x
  compl := z.compl x
  orth1 := z.orth1 x
  orth2 := z.orth2 x

theorem vec_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ST 3 → Fin 4 → E}
    (hF : ContDiff ℝ ∞ F) (α β μ : Fin 4) : pd (pd F β) α x μ = pd (pd F α) β x μ := by
  rw [pd_pd_comm' hF β α x]

theorem vec_symm' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ST 3 → E}
    (hF : ContDiff ℝ ∞ F) (α β : Fin 4) : pd (pd F β) α x = pd (pd F α) β x :=
  pd_pd_comm' hF β α x

theorem dtemporal (γ : Fin 4) : pd z.A γ x 0 = 0 := by
  rw [← pd_apply (z.A_smooth.differentiable (by simp) x) γ 0]
  have : (fun y => z.A y 0) = fun _ => (0 : MatLie m) := funext z.temporal
  rw [this]
  simp [SobolevOpen.pd]

/-- **The actual jet of the tuple at `x`**: the actual derivatives of the fields. -/
def jet : ActualJet (MatLie m) V S S' where
  FJ := z.FJ x
  chart := z.lor x
  sign := rfl
  frame := fun _ _ => rfl
  dframe := fun _ _ _ => rfl
  A := z.A x
  dA := fun γ μ => pd z.A γ x μ
  ddA := fun δ γ μ => pd (pd z.A γ) δ x μ
  temporal := z.temporal x
  dtemporal := z.dtemporal x
  ddA_symm := fun α β μ => Tuple.vec_symm x z.A_smooth α β μ
  H := z.H x
  dH := fun γ => pd z.H γ x
  ddH := fun δ γ => pd (pd z.H γ) δ x
  ddH_symm := fun α β => Tuple.vec_symm' x z.H_smooth α β
  ψ := z.ψ x
  cψ := fun γ => pd z.ψ γ x
  ccψ := fun δ γ => pd (pd z.ψ γ) δ x
  ccψ_symm := fun δ γ => Tuple.vec_symm' x z.ψ_smooth δ γ
  ψb := z.ψb x
  cψb := fun γ => pd z.ψb γ x
  ccψb := fun δ γ => pd (pd z.ψb γ) δ x
  ccψb_symm := fun δ γ => Tuple.vec_symm' x z.ψb_smooth δ γ

end Tuple

end Jet

/-! ### Line derivatives of the derived jet quantities -/

section Derived

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- The spinor jet `X_A = e_A^γ∂_γΨ + ω_AΨ` in expanded form. -/
theorem Xs_eq {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (ψ : S₀) (cψ : Fin 4 → S₀)
    (A : Fin 4) :
    J.Xs D ψ cψ A = ∑ γ, J.FJ.e A γ • cψ γ + spinPart D.Fr (J.FJ.G A) • ψ +
      ∑ μ, J.FJ.e A μ • D.ρ (J.A μ) ψ := by
  unfold ActualJet.Xs cov ActualJet.LJ LCJet.ω FrameJet.toLCJet ActualJetSpinor.dψf
  simp only [add_smul, Finset.sum_smul, smul_assoc, Module.End.smul_def]
  abel

/-- The coordinate derivative jet `∂_γX_A` in expanded form. -/
theorem dXs_eq {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (ψ : S₀) (cψ : Fin 4 → S₀)
    (ccψ : Fin 4 → Fin 4 → S₀) (γ A : Fin 4) :
    J.dXs D ψ cψ ccψ γ A = ∑ μ, (J.FJ.de γ A μ • cψ μ + J.FJ.e A μ • ccψ γ μ) +
      (spinPart D.Fr (J.FJ.dGc γ A) • ψ +
        ∑ μ, (J.FJ.de γ A μ • D.ρ (J.A μ) ψ + J.FJ.e A μ • D.ρ (J.dA γ μ) ψ)) +
      (spinPart D.Fr (J.FJ.G A) • cψ γ + ∑ μ, J.FJ.e A μ • D.ρ (J.A μ) (cψ γ)) := by
  unfold ActualJet.dXs ActualJetSpinor.dXc ActualJetSpinor.dωc LCJet.ω FrameJet.toLCJet
  simp only [add_smul, Finset.sum_smul, smul_assoc, Module.End.smul_def]

namespace Tuple

variable (z : Tuple m V S S') (x : ST 3) (δ : Fin 4)

theorem FJ_e (y : ST 3) : (z.FJ y).e = z.e y := rfl

theorem line_chr (l μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => chr (z.gi (x + s • ev δ)) (z.dg (x + s • ev δ)) l μ ν)
      (dchr (z.gi x) (z.dg x) (z.ddg x) δ l μ ν) 0 := by
  have h := hasDerivAt_chr (gi := fun s : ℝ => z.gi (x + s • ev δ))
    (dg := fun s : ℝ => z.dg (x + s • ev δ)) (t := 0) (ddg := z.ddg x) δ
    (by simpa using z.line_gi x δ) (fun α μ ν => z.line_dg x δ α μ ν) l μ ν
  simpa using h

theorem line_Ne (B γ μ : Fin 4) :
    HasDerivAt (fun s : ℝ => (z.FJ (x + s • ev δ)).Ne B γ μ) ((z.FJ x).dNe B δ γ μ) 0 := by
  have h := hasDerivAt_cv1 (Γ := fun s : ℝ => chr (z.gi (x + s • ev δ)) (z.dg (x + s • ev δ)))
    (V := fun s : ℝ => z.e (x + s • ev δ) B) (dV := fun s : ℝ => fun γ μ => z.de (x + s • ev δ) γ B μ)
    (t := 0) (dΓ := dchr (z.gi x) (z.dg x) (z.ddg x)) (ddV := fun δ γ μ => z.dde x δ γ B μ) δ
    (fun l μ ν => z.line_chr x δ l μ ν) (by simpa using z.line_e x δ B)
    (fun γ μ => z.line_de x δ γ B μ) γ μ
  simp only [zero_smul, add_zero] at h
  exact h

theorem line_P (γ B C : Fin 4) :
    HasDerivAt (fun s : ℝ => (z.FJ (x + s • ev δ)).P γ B C) ((z.FJ x).dP δ γ B C) 0 := by
  have h := hasDerivAt_ipg (g := fun s : ℝ => z.g (x + s • ev δ))
    (X := fun s : ℝ => fun μ => (z.FJ (x + s • ev δ)).Ne B γ μ)
    (Y := fun s : ℝ => z.e (x + s • ev δ) C) (t := 0) (dg := z.dg x)
    (dX := fun δ μ => (z.FJ x).dNe B δ γ μ) (dY := fun δ μ => z.de x δ C μ) δ
    (z.line_g x δ) (fun μ => z.line_Ne x δ B γ μ) (z.line_e x δ C)
  simp only [zero_smul, add_zero] at h
  exact h

/-- **The connection coefficients `G_{ABC}` of the frame field have the jet `dGc`.** -/
theorem line_G (A B C : Fin 4) :
    HasDerivAt (fun s : ℝ => (z.FJ (x + s • ev δ)).G A B C) ((z.FJ x).dGc δ A B C) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun γ _ =>
    (z.line_e x δ A γ).fun_mul (z.line_P x δ γ B C)
  simp only [zero_smul, add_zero] at h
  exact h

/-- The spin-connection bilinear map `ρ(a)ψ`. -/
theorem line_rho {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]
    (D : DiracData (MatLie m) V S₀) {v : ℝ → S₀} {v' : S₀} (hv : HasDerivAt v v' 0) (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => D.ρ (z.A (x + s • ev δ) μ) (v s))
      (D.ρ (pd z.A δ x μ) (v 0) + D.ρ (z.A x μ) v') 0 := by
  have hA := hasDerivAt_line0_apply (z.A_smooth.differentiable (by simp) x) δ μ
  have h := hasDerivAt_bilin D.ρ hA hv
  simpa using h

end Tuple

end Derived

/-! ### The spinor jets, the Dirac residual and the harmonic defect along lines -/

section Spinor

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

namespace Tuple

variable (z : Tuple m V S S') (x : ST 3) (δ : Fin 4)

/-- **The tangential spinor jets of a smooth spinor field have the jet `dXs`.** -/
theorem line_Xs (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf)
    (A : Fin 4) :
    HasDerivAt (fun s : ℝ => (z.jet (x + s • ev δ)).Xs D (ψf (x + s • ev δ))
        (fun γ => pd ψf γ (x + s • ev δ)) A)
      ((z.jet x).dXs D (ψf x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) δ A) 0 := by
  simp only [Xs_eq, dXs_eq]
  have hψl : HasDerivAt (fun s : ℝ => ψf (x + s • ev δ)) (pd ψf δ x) 0 :=
    hasDerivAt_line0 (hψ.differentiable (by simp) x) δ
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun γ _ =>
    (z.line_e x δ A γ).fun_smul
      (hasDerivAt_line0 ((contDiff_pd hψ γ).differentiable (by simp) x) δ)
  have h2 := hasDerivAt_spinPart_apply D.Fr (fun c d => z.line_G x δ A c d) hψl
  have h3 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    (z.line_e x δ A μ).fun_smul (z.line_rho x δ D hψl μ)
  have h := (h1.fun_add h2).fun_add h3
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  simp only [smul_add, Finset.sum_add_distrib]
  show _ = ∑ μ, z.de x δ A μ • pd ψf μ x + ∑ μ, z.e x A μ • pd (pd ψf μ) δ x +
      (spinPart D.Fr ((z.FJ x).dGc δ A) • ψf x + (∑ μ, z.de x δ A μ • D.ρ (z.A x μ) (ψf x) +
        ∑ μ, z.e x A μ • D.ρ (pd z.A δ x μ) (ψf x))) +
      (spinPart D.Fr ((z.FJ x).G A) • pd ψf δ x + ∑ μ, z.e x A μ • D.ρ (z.A x μ) (pd ψf δ x))
  abel

/-- **The Dirac residual of a smooth spinor field has the jet `drD`.** -/
theorem line_rD (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf) :
    HasDerivAt (fun s : ℝ => (z.jet (x + s • ev δ)).rD D (ψf (x + s • ev δ))
        (fun γ => pd ψf γ (x + s • ev δ)))
      ((z.jet x).drD D (ψf x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) δ) 0 := by
  have hψl : HasDerivAt (fun s : ℝ => ψf (x + s • ev δ)) (pd ψf δ x) 0 :=
    hasDerivAt_line0 (hψ.differentiable (by simp) x) δ
  have hHl : HasDerivAt (fun s : ℝ => z.H (x + s • ev δ)) (pd z.H δ x) 0 :=
    hasDerivAt_line0 (z.H_smooth.differentiable (by simp) x) δ
  have hdirac := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_lin (D.Fr.c b) (z.line_Xs x δ D hψ b)).const_smul (D.Fr.ε b)
  have hm0 := hasDerivAt_lin D.m0 hψl
  have hL := hasDerivAt_bilin D.L hHl hψl
  have h := hdirac.fun_sub (hm0.fun_add hL)
  simp only [zero_smul, add_zero] at h
  have e1 : ∀ y, (z.jet y).rD D (ψf y) (fun γ => pd ψf γ y) =
      ∑ b, D.Fr.ε b • D.Fr.c b ((z.jet y).Xs D (ψf y) (fun γ => pd ψf γ y) b) -
        (D.m0 (ψf y) + D.L (z.H y) (ψf y)) := by
    intro y
    unfold ActualJet.rD resD dirac mass
    simp only [Module.End.smul_def, LinearMap.add_apply]
    rfl
  have e2 : (z.jet x).drD D (ψf x) (fun γ => pd ψf γ x) (fun δ γ => pd (pd ψf γ) δ x) δ =
      ∑ b, D.Fr.ε b • D.Fr.c b ((z.jet x).dXs D (ψf x) (fun γ => pd ψf γ x)
        (fun δ γ => pd (pd ψf γ) δ x) δ b) -
        (D.m0 (pd ψf δ x) + (D.L (pd z.H δ x) (ψf x) + D.L (z.H x) (pd ψf δ x))) := by
    unfold ActualJet.drD ActualJetSpinor.drc mass
    simp only [Module.End.smul_def, LinearMap.add_apply]
    conv_lhs => rw [add_left_comm]
    rfl
  simp only [e1, e2]
  exact h

/-- **The harmonic defect `C^l = g^{αβ}Γ^l_{αβ}` of the metric field has the jet `dC`.** -/
theorem line_C (l : Fin 4) :
    HasDerivAt (fun s : ℝ => ActualJetWriter.C (z.gi (x + s • ev δ)) (z.dg (x + s • ev δ)) l)
      (ActualJetWriter.dC (z.gi x) (z.dg x) (z.ddg x) δ l) 0 := by
  have h := hasDerivAt_cUp (gi := fun s : ℝ => z.gi (x + s • ev δ))
    (Γ := fun s : ℝ => chr (z.gi (x + s • ev δ)) (z.dg (x + s • ev δ))) (t := 0)
    (dgi := dginv (z.gi x) (z.dg x)) (dΓ := dchr (z.gi x) (z.dg x) (z.ddg x)) δ
    (fun a b => z.line_gi x δ a b) (fun l a b => z.line_chr x δ l a b) l
  simp only [zero_smul, add_zero] at h
  exact h

end Tuple

end Spinor

/-! ### The state components along lines: `∂_δ𝒰 = dstate δ` -/

section State

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

namespace Tuple

variable (z : Tuple m V S S') (SM : SMData (MatLie m) V S S') (x : ST 3) (δ : Fin 4)

theorem jet_AF_fr (y : ST 3) (A μ : Fin 4) : (z.jet y).AF.fr A μ = z.e y A μ := rfl

theorem line_A (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => z.A (x + s • ev δ) μ) (pd z.A δ x μ) 0 :=
  hasDerivAt_line0_apply (z.A_smooth.differentiable (by simp) x) δ μ

theorem line_dA (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => pd z.A μ (x + s • ev δ) ν) (pd (pd z.A μ) δ x ν) 0 :=
  hasDerivAt_line0_apply ((contDiff_pd z.A_smooth μ).differentiable (by simp) x) δ ν

theorem line_H : HasDerivAt (fun s : ℝ => z.H (x + s • ev δ)) (pd z.H δ x) 0 :=
  hasDerivAt_line0 (z.H_smooth.differentiable (by simp) x) δ

theorem line_dH (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => pd z.H μ (x + s • ev δ)) (pd (pd z.H μ) δ x) 0 :=
  hasDerivAt_line0 ((contDiff_pd z.H_smooth μ).differentiable (by simp) x) δ

theorem line_Fm (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => Fm (z.jet (x + s • ev δ)).A (z.jet (x + s • ev δ)).dA μ ν)
      (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA δ μ ν) 0 := by
  have h := hasDerivAt_Fm (A := fun s : ℝ => z.A (x + s • ev δ))
    (dA := fun s : ℝ => fun μ ν => pd z.A μ (x + s • ev δ) ν) (t := 0)
    (ddA := fun δ μ ν => pd (pd z.A μ) δ x ν) δ (by simpa using z.line_A x δ)
    (fun μ ν => z.line_dA x δ μ ν) μ ν
  simp only [zero_smul, add_zero] at h
  exact h

/-- `∂_δp_{μν} = dpJ`. -/
theorem line_p (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).p μ ν)
      (((z.jet x).dstate SM δ).p μ ν) 0 := by
  show HasDerivAt (fun s : ℝ => ∑ β, z.e (x + s • ev δ) 0 β * z.dg (x + s • ev δ) β μ ν)
    (∑ β, (z.de x δ 0 β * z.dg x β μ ν + z.e x 0 β * z.ddg x δ β μ ν)) 0
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun β _ =>
    (z.line_e x δ 0 β).fun_mul (z.line_dg x δ β μ ν)
  simp only [zero_smul, add_zero] at h
  exact h

/-- `∂_δq_{a,μν} = dqJ`. -/
theorem line_q (a : Fin 3) (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).q a μ ν)
      (((z.jet x).dstate SM δ).q a μ ν) 0 := by
  show HasDerivAt (fun s : ℝ => ∑ β, z.e (x + s • ev δ) a.succ β * z.dg (x + s • ev δ) β μ ν)
    (∑ β, (z.de x δ a.succ β * z.dg x β μ ν + z.e x a.succ β * z.ddg x δ β μ ν)) 0
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun β _ =>
    (z.line_e x δ a.succ β).fun_mul (z.line_dg x δ β μ ν)
  simp only [zero_smul, add_zero] at h
  exact h

theorem line_frT (b c : Fin 4) :
    HasDerivAt (fun s : ℝ => frT (z.jet (x + s • ev δ)).AF
        (Fm (z.jet (x + s • ev δ)).A (z.jet (x + s • ev δ)).dA) b c)
      (dfrT (z.jet x).AF (z.jet x).FJ.de (Fm (z.jet x).A (z.jet x).dA)
        (dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA) δ b c) 0 := by
  have h := hasDerivAt_frT (fr := fun s : ℝ => z.e (x + s • ev δ))
    (T := fun s : ℝ => Fm (z.jet (x + s • ev δ)).A (z.jet (x + s • ev δ)).dA) (t := 0)
    (de := z.de x) (dT := dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA) δ
    (fun A μ => z.line_e x δ A μ) (fun μ ν => z.line_Fm x δ μ ν) b c
  simp only [zero_smul, add_zero] at h
  exact h

/-- `∂_δE_a = delec`. -/
theorem line_E (a : Fin 3) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).E a)
      (((z.jet x).dstate SM δ).E a) 0 :=
  z.line_frT x δ 0 a.succ

/-- `∂_δB_a = dmagn`. -/
theorem line_B (a : Fin 3) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).B a)
      (((z.jet x).dstate SM δ).B a) 0 :=
  hasDerivAt_dualVec (fun b c => z.line_frT x δ b.succ c.succ) a

theorem line_frV (B : Fin 4) :
    HasDerivAt (fun s : ℝ => frV (z.jet (x + s • ev δ)).AF (z.jet (x + s • ev δ)).A
        (z.jet (x + s • ev δ)).H (z.jet (x + s • ev δ)).dH B)
      (dfrV (z.jet x).AF (z.jet x).FJ.de (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH
        (z.jet x).ddH δ B) 0 := by
  have hDH := hasDerivAt_DH (A := fun s : ℝ => z.A (x + s • ev δ))
    (dA := fun s : ℝ => fun μ ν => pd z.A μ (x + s • ev δ) ν)
    (H := fun s : ℝ => z.H (x + s • ev δ)) (dH := fun s : ℝ => fun μ => pd z.H μ (x + s • ev δ))
    (t := 0) (ddH := fun δ μ => pd (pd z.H μ) δ x) δ (by simpa using z.line_A x δ)
    (by simpa using z.line_H x δ) (fun μ => z.line_dH x δ μ)
  have h := hasDerivAt_frV (fr := fun s : ℝ => z.e (x + s • ev δ))
    (X := fun s : ℝ => fun μ => DH (z.A (x + s • ev δ)) (z.H (x + s • ev δ))
      (fun μ => pd z.H μ (x + s • ev δ)) μ) (t := 0) (de := z.de x)
    (dX := fun δ μ => dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
      (fun δ μ => pd (pd z.H μ) δ x) δ μ) δ (fun A μ => z.line_e x δ A μ)
    (fun μ => by simpa using hDH μ) B
  simp only [zero_smul, add_zero] at h
  exact h

theorem line_Pm :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).Pm)
      (((z.jet x).dstate SM δ).Pm) 0 :=
  z.line_frV x δ 0

theorem line_Q (a : Fin 3) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).Q a)
      (((z.jet x).dstate SM δ).Q a) 0 :=
  z.line_frV x δ a.succ

theorem line_X (a : Fin 3) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).X a)
      (((z.jet x).dstate SM δ).X a) 0 :=
  z.line_Xs x δ SM.D z.ψ_smooth a.succ

theorem line_Xb (a : Fin 3) :
    HasDerivAt (fun s : ℝ => ((z.jet (x + s • ev δ)).state SM).Xb a)
      (((z.jet x).dstate SM δ).Xb a) 0 :=
  z.line_Xs x δ SM.Db z.ψb_smooth a.succ

end Tuple

end State

/-! ### Smoothness of the state and residual fields -/

section Smooth

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

/-- `spinPart` acting on a vector, expanded. -/
theorem spinPart_apply_eq (Fr : CliffordFrame (Fin 4) (Module.End ℝ S₀)) (W : Fin 4 → Fin 4 → ℝ)
    (v : S₀) : spinPart Fr W • v =
      (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * W c d) • ((Fr.c c * Fr.c d) v) := by
  unfold spinPart
  simp only [Module.End.smul_def, LinearMap.smul_apply, LinearMap.sum_apply]

namespace Tuple

variable (z : Tuple m V S S')

theorem contDiff_vec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ST 3 → Fin 4 → E}
    (hF : ContDiff ℝ ∞ F) (μ : Fin 4) : ContDiff ℝ ∞ (fun y => F y μ) := contDiff_pi.1 hF μ

theorem contDiff_pdc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ST 3 → Fin 4 → E} (hF : ContDiff ℝ ∞ F) (γ μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => pd F γ y μ) := contDiff_pi.1 (contDiff_pd hF γ) μ

theorem contDiff_pdpdc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ST 3 → Fin 4 → E} (hF : ContDiff ℝ ∞ F) (δ γ μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => pd (pd F γ) δ y μ) := contDiff_pi.1 (contDiff_pd (contDiff_pd hF γ) δ) μ

theorem contDiff_chr (l μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => chr (z.gi y) (z.dg y) l μ ν) := by
  have h1 := z.contDiff_gi
  have h2 := z.contDiff_dg
  unfold chr
  fun_prop

theorem contDiff_G (A B C : Fin 4) : ContDiff ℝ ∞ (fun y => (z.FJ y).G A B C) := by
  have h1 := z.contDiff_gc
  have h3 := z.contDiff_e
  have h4 := z.contDiff_de
  have h5 := z.contDiff_chr
  show ContDiff ℝ ∞ (fun y => ∑ γ, z.e y A γ * ipg (z.g y)
    (fun μ => cv1 (chr (z.gi y) (z.dg y)) (z.e y B) (fun γ μ => z.de y γ B μ) γ μ) (z.e y C))
  unfold ipg cv1
  fun_prop

theorem contDiff_Xs (D : DiracData (MatLie m) V S₀) {ψf : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψf)
    (A : Fin 4) :
    ContDiff ℝ ∞ (fun y => (z.jet y).Xs D (ψf y) (fun γ => pd ψf γ y) A) := by
  simp only [Xs_eq, spinPart_apply_eq]
  have h3 := z.contDiff_e
  have hG := z.contDiff_G
  have hA := contDiff_vec z.A_smooth
  have hp : ∀ γ, ContDiff ℝ ∞ (pd ψf γ) := fun γ => contDiff_pd hψ γ
  have hT : ∀ c d, ContDiff ℝ ∞ (fun y => (D.Fr.c c * D.Fr.c d) (ψf y)) := fun c d =>
    (LinearMap.toContinuousLinearMap (D.Fr.c c * D.Fr.c d)).contDiff.comp hψ
  have hρ : ∀ μ, ContDiff ℝ ∞ (fun y => D.ρ (z.A y μ) (ψf y)) := fun μ =>
    contDiff_iff_contDiffAt.2 fun y =>
      ContDiffAt.bilinApply D.ρ (hA μ).contDiffAt hψ.contDiffAt
  show ContDiff ℝ ∞ (fun y => ∑ γ, z.e y A γ • pd ψf γ y +
    (1 / 4 : ℝ) • ∑ c, ∑ d, (D.Fr.ε c * D.Fr.ε d * (z.FJ y).G A c d) •
      ((D.Fr.c c * D.Fr.c d) (ψf y)) + ∑ μ, z.e y A μ • D.ρ (z.A y μ) (ψf y))
  fun_prop

end Tuple

end Smooth
end RenewalGeometry.ActualJetBridge
