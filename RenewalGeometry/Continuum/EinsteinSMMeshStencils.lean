/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMComparisonBounds

/-!
# The Standard-Model comparison stencils and their first variations

Pointwise layer of `prop:mesh-consistency` (Einstein–Standard-Model action-closure manuscript,
`app:reconstruction`).  The Standard-Model density at a point depends on the fields only through
the *packet jet* `(e, F, H, D_AH, Ψ, Ψ̄, ∇Ψ, ∇Ψ̄)` (`smPt_redJet_eq_contJet`), and the comparison
density is the same jet density evaluated on the lattice comparison quantities (`stencilJet`).

* `spinConnMap`, `cospinConnMap`: the (dual) spin–gauge connection as a smooth function of the
  coframe, its first jet and the connection (`contDiffOn_spinConnMap`), with
  `spinConnection_eq_map`.
* `contJetDeriv z d x`: the first variation of the continuum packet jet along a direction `d`
  (`hasDerivAt_contJet`), linear in `d`.
* `smPt_redJet_eq_contJet`: `𝓛_{SM}(z)(x) = smPt(contJet z x)`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus TransportPlaquetteConsistency TransportStencilVariation

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-! ### The spin–gauge connection as a smooth map of the jet -/

/-- The first jet `(∂_i e)_i` of a coframe field. -/
def eJet (e : E4 → CoframeFibre) (y : E4) : CoframeJet := fun i => pd e i y

theorem spinGen_eq_spinGenE {e : E4 → CoframeFibre} {x : E4} (he : DifferentiableAt ℝ e x)
    (hx : e x ∈ coframeGL) : spinGen e x = spinGenE (e x) (eJet e x) := by
  funext μ s s'
  simp only [spinGen, spinGenE, spinConn_eq_spinConnL he hx]
  rfl

/-- `ω ↦ Ω_μ = ¼ ω_{μab}γ^aγ^b` (one component) as a continuous linear map. -/
def spinGenOfL (μ : Fin 4) : SpinConnFibre →L[ℝ] (Fin 4 → Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun om s s' => (1 / 4 : ℂ) * ∑ a, ∑ b,
        ((∑ c, minkowskiEta a c * om μ c b : ℝ) : ℂ) * mmul (gammaW a) (gammaW b) s s'
      map_add' := fun om om' => by
        funext s s'
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, add_mul]
      map_smul' := fun r om => by
        funext s s'
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul,
          Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring }

theorem spinGenE_apply_eq (e : CoframeFibre) (de : CoframeJet) (μ : Fin 4) :
    spinGenE e de μ = spinGenOfL μ (spinConnL e de) := by
  funext s s'
  simp only [spinGenOfL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- `(S, M) ↦ spinConnOp S M` as a continuous linear map. -/
def spinConnOpL : ((Fin 4 → Fin 4 → ℂ) × (FC.C → FC.C → ℂ)) →L[ℝ]
    (SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => spinConnOp FC p.1 p.2
      map_add' := fun p q => by
        ext ψ s c
        simp [spinConnOp, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun r p => by
        ext ψ s c
        simp only [spinConnOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
          AddHom.coe_mk, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply,
          ContinuousLinearMap.coe_smul', smul_add, Finset.smul_sum, smul_mul_assoc] }

/-- `(S, M) ↦ cospinConnOp S M` as a continuous linear map. -/
def cospinConnOpL : ((Fin 4 → Fin 4 → ℂ) × (FC.C → FC.C → ℂ)) →L[ℝ]
    (SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => cospinConnOp FC p.1 p.2
      map_add' := fun p q => by
        ext ψ s c
        simp [cospinConnOp, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun r p => by
        ext ψ s c
        simp only [cospinConnOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
          AddHom.coe_mk, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply,
          ContinuousLinearMap.coe_smul', smul_sub, smul_neg, Finset.smul_sum, mul_smul_comm] }

/-- The jet variables `(e, ∂e, A_μ)` of the spin–gauge connection. -/
abbrev SJet : Type := CoframeFibre × CoframeJet × LieFibre

/-- **The spin–gauge connection `Ω_μ + ρ_F(A_μ)` as a function of `(e, ∂e, A_μ)`.** -/
def spinConnMap (μ : Fin 4) (p : SJet) : SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  spinConnOpL FC (spinGenOfL μ (spinConnL p.1 p.2.1), FC.rho p.2.2)

/-- The dual spin–gauge connection as a function of `(e, ∂e, A_μ)`. -/
def cospinConnMap (μ : Fin 4) (p : SJet) : SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  cospinConnOpL FC (spinGenOfL μ (spinConnL p.1 p.2.1), FC.rho p.2.2)

/-- The nondegenerate jet chart. -/
def sjetGL : Set SJet := {p | p.1 ∈ coframeGL}

theorem isOpen_sjetGL : IsOpen sjetGL := isOpen_coframeGL.preimage continuous_fst

theorem contDiffOn_spinConnL_apply' {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun p : SJet => spinConnL p.1 p.2.1) sjetGL := by
  have h1 : ContDiffOn ℝ n (fun p : SJet => spinConnL p.1) sjetGL :=
    contDiffOn_spinConnL.comp contDiff_fst.contDiffOn (fun p hp => hp)
  exact h1.clm_apply (contDiff_fst.comp contDiff_snd).contDiffOn

theorem contDiffOn_spinConnMap (μ : Fin 4) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (spinConnMap FC μ) sjetGL := by
  have hρ : ContDiff ℝ n fun p : SJet => FC.rho p.2.2 :=
    ((LinearMap.toContinuousLinearMap FC.rho).contDiff).comp (contDiff_snd.comp contDiff_snd)
  unfold spinConnMap
  exact (spinConnOpL FC).contDiff.comp_contDiffOn
    (((spinGenOfL μ).contDiff.comp_contDiffOn contDiffOn_spinConnL_apply').prodMk hρ.contDiffOn)

theorem contDiffOn_cospinConnMap (μ : Fin 4) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (cospinConnMap FC μ) sjetGL := by
  have hρ : ContDiff ℝ n fun p : SJet => FC.rho p.2.2 :=
    ((LinearMap.toContinuousLinearMap FC.rho).contDiff).comp (contDiff_snd.comp contDiff_snd)
  unfold cospinConnMap
  exact (cospinConnOpL FC).contDiff.comp_contDiffOn
    (((spinGenOfL μ).contDiff.comp_contDiffOn contDiffOn_spinConnL_apply').prodMk hρ.contDiffOn)

/-- The jet `(e, ∂e, A_μ)` of fields at a point. -/
def sjetOf (z : FieldTuple FC.C) (μ : Fin 4) (y : E4) : SJet := (z.e y, eJet z.e y, z.A y μ)

theorem spinConnection_eq_map (z : FieldTuple FC.C) (μ : Fin 4) {y : E4}
    (he : DifferentiableAt ℝ z.e y) (hy : z.e y ∈ coframeGL) :
    spinConnection FC z μ y = spinConnMap FC μ (sjetOf FC z μ y) := by
  rw [spinConnection, spinGen_eq_spinGenE he hy, spinGenE_apply_eq]
  simp only [spinConnMap, spinConnOpL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, sjetOf]

theorem cospinConnection_eq_map (z : FieldTuple FC.C) (μ : Fin 4) {y : E4}
    (he : DifferentiableAt ℝ z.e y) (hy : z.e y ∈ coframeGL) :
    cospinConnection FC z μ y = cospinConnMap FC μ (sjetOf FC z μ y) := by
  rw [cospinConnection, spinGen_eq_spinGenE he hy, spinGenE_apply_eq]
  simp only [cospinConnMap, cospinConnOpL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, sjetOf]

/-! ### The continuum packet jet and its first variation -/

/-- `δ(Ω_μ + ρ_F(A_μ))[d]`: the variation of the spin–gauge connection along a direction `d`. -/
def spinConnDeriv (z d : FieldTuple FC.C) (μ : Fin 4) (y : E4) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  fderiv ℝ (spinConnMap FC μ) (sjetOf FC z μ y) (sjetOf FC d μ y)

/-- The variation of the dual spin–gauge connection. -/
def cospinConnDeriv (z d : FieldTuple FC.C) (μ : Fin 4) (y : E4) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  fderiv ℝ (cospinConnMap FC μ) (sjetOf FC z μ y) (sjetOf FC d μ y)

/-- `Ḟ_{μν} = ∂_μa_ν - ∂_νa_μ + [A_μ,a_ν] + [a_μ,A_ν]`. -/
def curvDeriv (A a : E4 → ConnFibre) (x : E4) : Fin 4 → ConnFibre := fun μ ν =>
  pd (fun y => a y ν) μ x - pd (fun y => a y μ) ν x + comm (A x μ) (a x ν) + comm (a x μ) (A x ν)

/-- `K̇_μ = ∂_μη + ρ_H(a_μ)H + ρ_H(A_μ)η`. -/
def higgsDeriv (A : E4 → ConnFibre) (H : E4 → HiggsFibre) (a : E4 → ConnFibre)
    (η : E4 → HiggsFibre) (x : E4) : Fin 4 → HiggsFibre := fun μ =>
  pd η μ x + higgsAct (a x μ) (H x) + higgsAct (A x μ) (η x)

/-- **The first variation of the continuum packet jet along a direction `d`.** -/
def contJetDeriv (z d : FieldTuple FC.C) (x : E4) : RJet FC.C :=
  RJet.mk (d.e x) 0 0 (curvDeriv z.A d.A x) (d.H x) (higgsDeriv z.A z.H d.A d.H x) (d.Ψ x)
    (fun μ => pd d.Ψ μ x + spinConnDeriv FC z d μ x (z.Ψ x) + spinConnection FC z μ x (d.Ψ x))
    (d.Ψb x)
    (fun μ => pd d.Ψb μ x + cospinConnDeriv FC z d μ x (z.Ψb x) + cospinConnection FC z μ x (d.Ψb x))

/-- Differentiability of all five components at a point. -/
structure DiffAt (z : FieldTuple FC.C) (x : E4) : Prop where
  e : DifferentiableAt ℝ z.e x
  A : DifferentiableAt ℝ z.A x
  H : DifferentiableAt ℝ z.H x
  Ψ : DifferentiableAt ℝ z.Ψ x
  Ψb : DifferentiableAt ℝ z.Ψb x

theorem pd_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F} {x : E4}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (t : ℝ) (i : Fin 4) :
    pd (fun y => f y + t • g y) i x = pd f i x + t • pd g i x := by
  unfold pd
  have hg' : DifferentiableAt ℝ (fun y => t • g y) x := hg.const_smul t
  rw [fderiv_fun_add hf hg', fderiv_fun_const_smul hg]
  rfl

theorem differentiableAt_comp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → Fin 4 → F} {x : E4} (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    DifferentiableAt ℝ (fun y => f y μ) x := differentiableAt_pi.mp hf μ

/-- Bilinearity of the commutator along lines. -/
theorem comm_line (X Y X' Y' : LieFibre) (t : ℝ) :
    comm (X + t • Y) (X' + t • Y') =
      comm X X' + t • (comm X Y' + comm Y X') + t ^ 2 • comm Y Y' := by
  funext i j
  simp only [comm, mmul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `F(A + t a) = F(A) + t Ḟ + t² [a, a]`. -/
theorem curvatureF_line {A a : E4 → ConnFibre} {x : E4} (hA : DifferentiableAt ℝ A x)
    (ha : DifferentiableAt ℝ a x) (t : ℝ) :
    curvatureF (A + t • a) x = curvatureF A x + t • curvDeriv A a x +
      t ^ 2 • fun μ ν => comm (a x μ) (a x ν) := by
  funext μ ν
  have h1 := pd_line (differentiableAt_comp_apply hA ν) (differentiableAt_comp_apply ha ν) t μ
  have h2 := pd_line (differentiableAt_comp_apply hA μ) (differentiableAt_comp_apply ha μ) t ν
  simp only [curvatureF, Pi.add_apply, Pi.smul_apply] at h1 h2 ⊢
  rw [h1, h2, comm_line]
  simp only [curvDeriv]
  module

theorem hasDerivAt_curvatureF_line {A a : E4 → ConnFibre} {x : E4} (hA : DifferentiableAt ℝ A x)
    (ha : DifferentiableAt ℝ a x) :
    HasDerivAt (fun t : ℝ => curvatureF (A + t • a) x) (curvDeriv A a x) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (curvDeriv A a x)).const_add (curvatureF A x)
  have h2 := ((hasDerivAt_pow 2 (0 : ℝ)).smul_const (fun μ ν => comm (a x μ) (a x ν)))
  have := h.add h2
  norm_num at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact curvatureF_line hA ha t

theorem hasDerivAt_line_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (u v : F) :
    HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u

theorem higgsAct_line (X Y : LieFibre) (u v : HiggsFibre) (t : ℝ) :
    higgsAct (X + t • Y) (u + t • v) =
      higgsAct X u + t • (higgsAct Y u + higgsAct X v) + t ^ 2 • higgsAct Y v := by
  funext i
  simp only [higgsAct, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `D_{A + ta}(H + tη) = D_AH + t K̇ + t² ρ_H(a)η`. -/
theorem covDerivHiggs_line {A a : E4 → ConnFibre} {H η : E4 → HiggsFibre} {x : E4}
    (hH : DifferentiableAt ℝ H x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    covDerivHiggs (A + t • a) (H + t • η) x = covDerivHiggs A H x + t • higgsDeriv A H a η x +
      t ^ 2 • fun μ => higgsAct (a x μ) (η x) := by
  funext μ
  have h1 := pd_line hH hη t μ
  simp only [covDerivHiggs, Pi.add_apply, Pi.smul_apply] at h1 ⊢
  rw [show (fun y => H y + t • η y) = H + t • η from rfl] at h1
  rw [h1, higgsAct_line]
  simp only [higgsDeriv]
  module

theorem hasDerivAt_covDerivHiggs_line {A a : E4 → ConnFibre} {H η : E4 → HiggsFibre} {x : E4}
    (hH : DifferentiableAt ℝ H x) (hη : DifferentiableAt ℝ η x) :
    HasDerivAt (fun t : ℝ => covDerivHiggs (A + t • a) (H + t • η) x) (higgsDeriv A H a η x) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (higgsDeriv A H a η x)).const_add
    (covDerivHiggs A H x)
  have h2 := ((hasDerivAt_pow 2 (0 : ℝ)).smul_const (fun μ => higgsAct (a x μ) (η x)))
  have := h.add h2
  norm_num at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact covDerivHiggs_line hH hη t

/-- The jet of fields along a line: `sjetOf (z + t d) = sjetOf z + t sjetOf d`. -/
theorem sjetOf_line {z d : FieldTuple FC.C} {y : E4} (hz : DifferentiableAt ℝ z.e y)
    (hd : DifferentiableAt ℝ d.e y) (μ : Fin 4) (t : ℝ) :
    sjetOf FC (z + t • d) μ y = sjetOf FC z μ y + t • sjetOf FC d μ y := by
  have hj : eJet (z + t • d).e y = eJet z.e y + t • eJet d.e y := by
    funext i
    exact pd_line hz hd t i
  simp only [sjetOf, hj]
  rfl

theorem fieldTuple_line_e (z d : FieldTuple FC.C) (t : ℝ) : (z + t • d).e = z.e + t • d.e := rfl
theorem fieldTuple_line_A (z d : FieldTuple FC.C) (t : ℝ) : (z + t • d).A = z.A + t • d.A := rfl
theorem fieldTuple_line_H (z d : FieldTuple FC.C) (t : ℝ) : (z + t • d).H = z.H + t • d.H := rfl
theorem fieldTuple_line_Ψ (z d : FieldTuple FC.C) (t : ℝ) : (z + t • d).Ψ = z.Ψ + t • d.Ψ := rfl
theorem fieldTuple_line_Ψb (z d : FieldTuple FC.C) (t : ℝ) : (z + t • d).Ψb = z.Ψb + t • d.Ψb :=
  rfl

/-- **The spin–gauge connection along a line of fields** is differentiable with derivative
`spinConnDeriv`. -/
theorem hasDerivAt_spinConnection_line {z d : FieldTuple FC.C} {y : E4} (hz : DiffAt FC z y)
    (hd : DiffAt FC d y) (hy : z.e y ∈ coframeGL) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => spinConnection FC (z + t • d) μ y) (spinConnDeriv FC z d μ y) 0 := by
  have hdiff : DifferentiableAt ℝ (spinConnMap FC μ) (sjetOf FC z μ y) :=
    ((contDiffOn_spinConnMap FC μ (n := 1)).contDiffAt
      (isOpen_sjetGL.mem_nhds hy)).differentiableAt one_ne_zero
  have hl : HasDerivAt (fun t : ℝ => sjetOf FC z μ y + t • sjetOf FC d μ y) (sjetOf FC d μ y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sjetOf FC d μ y)).const_add
      (sjetOf FC z μ y)
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)
  -- eventually the varied coframe is nondegenerate
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), spinConnection FC (z + t • d) μ y =
      spinConnMap FC μ (sjetOf FC z μ y + t • sjetOf FC d μ y) := by
    have hcont : ContinuousAt (fun t : ℝ => z.e y + t • d.e y) 0 := by fun_prop
    have hopen : (fun t : ℝ => z.e y + t • d.e y) ⁻¹' coframeGL ∈ 𝓝 (0 : ℝ) :=
      hcont.preimage_mem_nhds (by simpa using isOpen_coframeGL.mem_nhds hy)
    filter_upwards [hopen] with t ht
    have hde : DifferentiableAt ℝ (z + t • d).e y := by
      rw [fieldTuple_line_e]; exact hz.e.add (hd.e.const_smul t)
    rw [spinConnection_eq_map FC _ μ hde ht, sjetOf_line FC hz.e hd.e μ t]
  exact hc.congr_of_eventuallyEq hev

theorem hasDerivAt_cospinConnection_line {z d : FieldTuple FC.C} {y : E4} (hz : DiffAt FC z y)
    (hd : DiffAt FC d y) (hy : z.e y ∈ coframeGL) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => cospinConnection FC (z + t • d) μ y) (cospinConnDeriv FC z d μ y)
      0 := by
  have hdiff : DifferentiableAt ℝ (cospinConnMap FC μ) (sjetOf FC z μ y) :=
    ((contDiffOn_cospinConnMap FC μ (n := 1)).contDiffAt
      (isOpen_sjetGL.mem_nhds hy)).differentiableAt one_ne_zero
  have hl : HasDerivAt (fun t : ℝ => sjetOf FC z μ y + t • sjetOf FC d μ y) (sjetOf FC d μ y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sjetOf FC d μ y)).const_add
      (sjetOf FC z μ y)
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), cospinConnection FC (z + t • d) μ y =
      cospinConnMap FC μ (sjetOf FC z μ y + t • sjetOf FC d μ y) := by
    have hcont : ContinuousAt (fun t : ℝ => z.e y + t • d.e y) 0 := by fun_prop
    have hopen : (fun t : ℝ => z.e y + t • d.e y) ⁻¹' coframeGL ∈ 𝓝 (0 : ℝ) :=
      hcont.preimage_mem_nhds (by simpa using isOpen_coframeGL.mem_nhds hy)
    filter_upwards [hopen] with t ht
    have hde : DifferentiableAt ℝ (z + t • d).e y := by
      rw [fieldTuple_line_e]; exact hz.e.add (hd.e.const_smul t)
    rw [cospinConnection_eq_map FC _ μ hde ht, sjetOf_line FC hz.e hd.e μ t]
  exact hc.congr_of_eventuallyEq hev

/-- **The continuum packet jet along a line of fields** is differentiable with derivative
`contJetDeriv`. -/
theorem hasDerivAt_contJet_line {z d : FieldTuple FC.C} {x : E4} (hz : DiffAt FC z x)
    (hd : DiffAt FC d x) (hx : z.e x ∈ coframeGL) :
    HasDerivAt (fun t : ℝ => contJet FC (z + t • d) x) (contJetDeriv FC z d x) 0 := by
  have he : HasDerivAt (fun t : ℝ => (z + t • d).e x) (d.e x) 0 :=
    hasDerivAt_line_apply (z.e x) (d.e x)
  have hH : HasDerivAt (fun t : ℝ => (z + t • d).H x) (d.H x) 0 :=
    hasDerivAt_line_apply (z.H x) (d.H x)
  have hΨ : HasDerivAt (fun t : ℝ => (z + t • d).Ψ x) (d.Ψ x) 0 :=
    hasDerivAt_line_apply (z.Ψ x) (d.Ψ x)
  have hΨb : HasDerivAt (fun t : ℝ => (z + t • d).Ψb x) (d.Ψb x) 0 :=
    hasDerivAt_line_apply (z.Ψb x) (d.Ψb x)
  have hF : HasDerivAt (fun t : ℝ => curvatureF (z + t • d).A x) (curvDeriv z.A d.A x) 0 := by
    simpa only [fieldTuple_line_A] using hasDerivAt_curvatureF_line hz.A hd.A
  have hK : HasDerivAt (fun t : ℝ => covDerivHiggs (z + t • d).A (z + t • d).H x)
      (higgsDeriv z.A z.H d.A d.H x) 0 := by
    simpa only [fieldTuple_line_A, fieldTuple_line_H] using hasDerivAt_covDerivHiggs_line hz.H hd.H
  have hD : HasDerivAt (fun t : ℝ => covDerivSpinor FC (z + t • d).e (z + t • d).A (z + t • d).Ψ x)
      (fun μ => pd d.Ψ μ x + spinConnDeriv FC z d μ x (z.Ψ x) + spinConnection FC z μ x (d.Ψ x))
      0 := by
    refine hasDerivAt_pi.mpr fun μ => ?_
    have hp : ∀ t : ℝ, pd (z + t • d).Ψ μ x = pd z.Ψ μ x + t • pd d.Ψ μ x := fun t =>
      pd_line hz.Ψ hd.Ψ t μ
    have hpd : HasDerivAt (fun t : ℝ => pd (z + t • d).Ψ μ x) (pd d.Ψ μ x) 0 := by
      simp only [hp]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pd d.Ψ μ x)).const_add (pd z.Ψ μ x)
    have hc := (hasDerivAt_spinConnection_line FC hz hd hx μ).clm_apply hΨ
    have := hpd.add hc
    simp only [zero_smul, add_zero, one_smul] at this
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · show covDerivSpinor FC (z + t • d).e (z + t • d).A (z + t • d).Ψ x μ = _
      rw [covDerivSpinor_eq]; rfl
    · abel
  have hDb : HasDerivAt
      (fun t : ℝ => covDerivCospinor FC (z + t • d).e (z + t • d).A (z + t • d).Ψb x)
      (fun μ => pd d.Ψb μ x + cospinConnDeriv FC z d μ x (z.Ψb x) +
        cospinConnection FC z μ x (d.Ψb x)) 0 := by
    refine hasDerivAt_pi.mpr fun μ => ?_
    have hp : ∀ t : ℝ, pd (z + t • d).Ψb μ x = pd z.Ψb μ x + t • pd d.Ψb μ x := fun t =>
      pd_line hz.Ψb hd.Ψb t μ
    have hpd : HasDerivAt (fun t : ℝ => pd (z + t • d).Ψb μ x) (pd d.Ψb μ x) 0 := by
      simp only [hp]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pd d.Ψb μ x)).const_add (pd z.Ψb μ x)
    have hc := (hasDerivAt_cospinConnection_line FC hz hd hx μ).clm_apply hΨb
    have := hpd.add hc
    simp only [zero_smul, add_zero, one_smul] at this
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · show covDerivCospinor FC (z + t • d).e (z + t • d).A (z + t • d).Ψb x μ = _
      rw [covDerivCospinor_eq]; rfl
    · abel
  have h0 : HasDerivAt (fun _ : ℝ => (0 : CoframeJet)) 0 0 := hasDerivAt_const _ _
  have h0' : HasDerivAt (fun _ : ℝ => (0 : ConnFibre)) 0 0 := hasDerivAt_const _ _
  exact he.prodMk (h0.prodMk (h0'.prodMk (hF.prodMk (hH.prodMk (hK.prodMk (hΨ.prodMk
    (hD.prodMk (hΨb.prodMk hDb))))))))

/-! ### The Standard-Model density through the packet jet -/

theorem spinGenE_zero (e : CoframeFibre) : spinGenE e 0 = 0 := by
  funext μ s s'
  simp [spinGenE]

/-- `𝓛_D` in packet form: the kinetic form on `(∇Ψ, ∇Ψ̄)` plus the Yukawa term. -/
theorem diracDensity_eq_packet (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4) :
    diracDensity FC θ z x =
      kinForm (gammaE (z.e x)) (z.Ψb x, z.Ψ x)
          (covDerivSpinor FC z.e z.A z.Ψ x, covDerivCospinor FC z.e z.A z.Ψb x) +
        potForm FC (gammaE (z.e x)) (spinGenE (z.e x) 0) 0 (FC.yukawa θ (z.H x)) (z.Ψb x)
          (z.Ψ x) := by
  rw [spinGenE_zero]
  simp only [diracDensity, kinForm, potForm, Pi.zero_apply, map_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, ← Complex.add_re]
  congr 1
  simp only [gammaE, curvedGamma]
  ring

/-- **`𝓛_{SM}(z)(x) = smPt(redJet z x) = smPt(contJet z x)`**: the Standard-Model density depends
on the fields only through the packet jet. -/
theorem smPt_redJet_eq_contJet (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4)
    (he : DifferentiableAt ℝ z.e x) (hx : z.e x ∈ coframeGL) :
    smPt FC θ (redJet z x) = smPt FC θ (contJet FC z x) := by
  unfold smPt
  congr 1
  rw [← diracDensity_mul_vol FC θ z x he hx, diracDensity_eq_packet]
  simp only [diracPt, kinCoeff_apply, potCoeff_apply, contJet, RJet.mk_e, RJet.mk_de, RJet.mk_A,
    RJet.mk_H, RJet.mk_Ψ, RJet.mk_dΨ, RJet.mk_Ψb, RJet.mk_dΨb]
  ring

theorem contJet_mem_jetGL (z : FieldTuple FC.C) {x : E4} (hx : z.e x ∈ coframeGL) :
    contJet FC z x ∈ jetGL FC.C := hx

theorem differentiableAt_smPt (θ : CoefficientBank Ysec) {R : RJet FC.C} (hR : R ∈ jetGL FC.C) :
    DifferentiableAt ℝ (smPt FC θ) R :=
  (((contDiffOn_bosonPt θ (n := 1)).add (contDiffOn_diracPt FC θ (n := 1))).contDiffAt
    (isOpen_jetGL.mem_nhds hR)).differentiableAt one_ne_zero

/-- The covector of the continuum Standard-Model variation is the derivative of `smPt`. -/
theorem smCov_eq_fderiv (θ : CoefficientBank Ysec) {R : RJet FC.C} (hR : R ∈ jetGL FC.C)
    (T' : RJet FC.C) :
    (bosonCov θ R + diracCov FC θ R) T' = fderiv ℝ (smPt FC θ) R (redVar R T') := by
  have hb := hasFDerivAt_bosonPt θ hR
  have hd := hasFDerivAt_diracPt FC θ hR
  rw [show smPt FC θ = fun R => bosonPt θ R + diracPt FC θ R from rfl,
    fderiv_fun_add hb.1 hd.1]
  simp only [ContinuousLinearMap.add_apply]
  rw [hb.2, ← bosonCov_apply, fderiv_diracPt_redVar FC θ hR]

/-- **Identification of the continuum integrand**: for fields differentiable at `x` with a
nondegenerate coframe and a test `v` differentiable at `x`,
`(bosonCov + diracCov)(redJet z x)(testJet v x) = DsmPt(contJet z x)[δ contJet[vh]]`. -/
theorem smCov_eq_contJetDeriv (θ : CoefficientBank Ysec) {z v : FieldTuple FC.C} {x : E4}
    (hz : DiffAt FC z x) (hv : DiffAt FC v x) (hx : z.e x ∈ coframeGL) :
    (bosonCov θ (redJet z x) + diracCov FC θ (redJet z x)) (testJet v x) =
      fderiv ℝ (smPt FC θ) (contJet FC z x)
        (contJetDeriv FC z (variationDirection z v) x) := by
  set vh := variationDirection z v
  have hvh : DiffAt FC vh x := ⟨differentiableAt_metricLift hz.e hv.e, hv.A, hv.H, hv.Ψ, hv.Ψb⟩
  have hR : redJet z x ∈ jetGL FC.C := hx
  -- first computation: the jet expansion
  have h1 : HasDerivAt (fun t : ℝ => smPt FC θ (redJet (z + t • vh) x))
      (fderiv ℝ (smPt FC θ) (redJet z x) (redVar (redJet z x) (testJet v x))) 0 := by
    have hcurve : HasDerivAt (fun t : ℝ => redJet z x + t • redVar (redJet z x) (testJet v x) +
        t ^ 2 • redVar2 (testJet v x)) (redVar (redJet z x) (testJet v x)) 0 := by
      have a1 := hasDerivAt_line_apply (redJet z x) (redVar (redJet z x) (testJet v x))
      have a2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const (redVar2 (testJet v x))
      have := a1.add a2
      norm_num at this
      exact this
    have hc := (differentiableAt_smPt FC θ hR).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
      hcurve (by simp)
    refine hc.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show smPt FC θ (redJet (z + t • vh) x) = smPt FC θ (redJet z x +
      t • redVar (redJet z x) (testJet v x) + t ^ 2 • redVar2 (testJet v x))
    rw [redJet_variation hz.e hz.A hz.H hz.Ψ hz.Ψb hv.e hv.A hv.H hv.Ψ hv.Ψb t]
  -- second computation: the packet jet
  have h2 : HasDerivAt (fun t : ℝ => smPt FC θ (redJet (z + t • vh) x))
      (fderiv ℝ (smPt FC θ) (contJet FC z x) (contJetDeriv FC z vh x)) 0 := by
    have hc := (differentiableAt_smPt FC θ (contJet_mem_jetGL FC z hx)).hasFDerivAt.comp_hasDerivAt_of_eq
      (x := (0 : ℝ)) (hasDerivAt_contJet_line FC hz hvh hx) (by simp)
    refine hc.congr_of_eventuallyEq ?_
    have hcont : ContinuousAt (fun t : ℝ => z.e x + t • vh.e x) 0 := by fun_prop
    have hopen : (fun t : ℝ => z.e x + t • vh.e x) ⁻¹' coframeGL ∈ 𝓝 (0 : ℝ) :=
      hcont.preimage_mem_nhds (by simpa using isOpen_coframeGL.mem_nhds hx)
    filter_upwards [hopen] with t ht
    have hde : DifferentiableAt ℝ (z + t • vh).e x := by
      rw [fieldTuple_line_e]; exact hz.e.add (hvh.e.const_smul t)
    exact smPt_redJet_eq_contJet FC θ (z + t • vh) x hde ht
  rw [smCov_eq_fderiv FC θ hR, h1.unique h2]

/-! ### The Yang–Mills stencil -/

theorem norm_proj_le_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Fin 4) :
    ‖(ContinuousLinearMap.proj μ : (Fin 4 → F) →L[ℝ] F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact norm_le_pi_norm f μ

theorem norm_unitE_le (μ : Fin 4) : ‖unitE μ‖ ≤ 1 := norm_single_E4_le μ

/-- Components of a `C^{1,1}` connection are `C^{1,1}`. -/
theorem isC11_comp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E4 → Fin 4 → F} {B : ℝ} (hA : IsC11 A B) (μ : Fin 4) :
    IsC11 (fun y => A y μ) B :=
  (hA.clm (ContinuousLinearMap.proj μ)).mono
    (by have := norm_proj_le_one (F := F) μ; have := hA.nonneg; nlinarith)

theorem isC11_ymConn {A : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (μ : Fin 4) :
    IsC11 (ymConn A μ) (‖toYM‖ * B) :=
  (isC11_comp_apply hA μ).clm toYM

theorem fderiv_ymConn_apply {A : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (μ ν : Fin 4)
    (x : E4) : fderiv ℝ (ymConn A ν) x (unitE μ) = toYM (pd (fun y => A y ν) μ x) := by
  have h1 := (isC11_comp_apply hA ν).hasFDerivAt x
  have h2 : HasFDerivAt (fun y => toYM (A y ν)) (toYM.comp (fderiv ℝ (fun y => A y ν) x)) x :=
    toYM.hasFDerivAt.comp x h1
  rw [show ymConn A ν = fun y => toYM (A y ν) from rfl, h2.fderiv]
  rfl

theorem ymConn_line (A a : E4 → ConnFibre) (t : ℝ) (μ : Fin 4) :
    ymConn (A + t • a) μ = ymConn A μ + t • ymConn a μ := by
  funext y
  simp [ymConn, map_add, map_smul]

/-- The curvature from the transport-algebra limit. -/
theorem fromYM_curv {A : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (x : E4) (μ ν : Fin 4) :
    fromYM (fderiv ℝ (ymConn A ν) x (unitE μ) - fderiv ℝ (ymConn A μ) x (unitE ν) +
      (ymConn A μ x * ymConn A ν x - ymConn A ν x * ymConn A μ x)) = curvatureF A x μ ν := by
  rw [fderiv_ymConn_apply hA, fderiv_ymConn_apply hA]
  simp only [ymConn, ← toYM_comm, ← map_sub, ← map_add, fromYM_toYM]
  rfl

theorem fromYM_curvDeriv {A a : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (ha : IsC11 a B)
    (x : E4) (μ ν : Fin 4) :
    fromYM (fderiv ℝ (ymConn a ν) x (unitE μ) - fderiv ℝ (ymConn a μ) x (unitE ν) +
      (ymConn A μ x * ymConn a ν x + ymConn a μ x * ymConn A ν x - ymConn A ν x * ymConn a μ x -
        ymConn a ν x * ymConn A μ x)) = curvDeriv A a x μ ν := by
  rw [fderiv_ymConn_apply ha, fderiv_ymConn_apply ha]
  have e : ymConn A μ x * ymConn a ν x + ymConn a μ x * ymConn A ν x -
      ymConn A ν x * ymConn a μ x - ymConn a ν x * ymConn A μ x =
      toYM (comm (A x μ) (a x ν)) + toYM (comm (a x μ) (A x ν)) := by
    simp only [ymConn, toYM_comm]; abel
  rw [e]
  simp only [← map_sub, ← map_add, fromYM_toYM]
  simp only [curvDeriv, add_assoc]

theorem curvatureF_antisymm (A : E4 → ConnFibre) (x : E4) (μ ν : Fin 4) :
    curvatureF A x ν μ = -curvatureF A x μ ν := by
  simp only [curvatureF, comm]
  abel

theorem curvatureF_diag (A : E4 → ConnFibre) (x : E4) (μ : Fin 4) : curvatureF A x μ μ = 0 := by
  simp [curvatureF, comm]

theorem curvDeriv_antisymm (A a : E4 → ConnFibre) (x : E4) (μ ν : Fin 4) :
    curvDeriv A a x ν μ = -curvDeriv A a x μ ν := by
  simp only [curvDeriv, comm]
  abel

theorem curvDeriv_diag (A a : E4 → ConnFibre) (x : E4) (μ : Fin 4) : curvDeriv A a x μ μ = 0 := by
  simp only [curvDeriv, comm, sub_self, zero_add]
  abel

/-- Constants of the Yang–Mills stencil estimates. -/
def ymK (B : ℝ) : ℝ := ‖toYM‖ * B
def ymCp (B : ℝ) : ℝ := plaquetteConst (max (ymK B) (ymK B)) (ymK B) (4 * ymK B)
def ymCd (B : ℝ) : ℝ :=
  plaquetteConst (max (ymK B + ymK B) (ymK B + ymK B)) (ymK B + ymK B) (4 * (ymK B + ymK B))
def ymCval (B : ℝ) : ℝ :=
  ymCp B + 2 * (2 * ymK B + 2 * ymK B ^ 2 + ymCp B) ^ 2
def ymCvar (B : ℝ) : ℝ :=
  4 * (ymCp B + (2 * ymK B + 2 * ymK B ^ 2)) * ((2 * ymK B + 4 * ymK B * ymK B) + ymCd B) + ymCd B
def ymS (B : ℝ) : ℝ :=
  |ymCp B + (2 * ymK B + 2 * ymK B ^ 2)| + |2 * ymK B + 2 * ymK B ^ 2 + ymCp B|

/-- The Yang–Mills stencil for `μ, ν` (the logarithmic plaquette), with explicit constants. -/
theorem ym_core {A a : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (ha : IsC11 a B) (x : E4)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hs1 : (2 * ymK B + 2 * ymK B ^ 2 + ymCp B) * h ^ 2 ≤ 1 / 2)
    (hs2 : (ymCp B + (2 * ymK B + 2 * ymK B ^ 2)) * h ^ 2 ≤ 1 / 8) (μ ν : Fin 4) :
    ‖logPlaq h A x μ ν - curvatureF A x μ ν‖ ≤ ‖fromYM‖ * ymCval B * h ∧
    ∃ DF : LieFibre, HasDerivAt (fun t : ℝ => logPlaq h (A + t • a) x μ ν) DF 0 ∧
      ‖DF - curvDeriv A a x μ ν‖ ≤ ‖fromYM‖ * ymCvar B * h := by
  have hB := hA.nonneg
  have hK : 0 ≤ ymK B := by unfold ymK; positivity
  have hAμ : IsC11 (ymConn A μ) (ymK B) := isC11_ymConn hA μ
  have hAν : IsC11 (ymConn A ν) (ymK B) := isC11_ymConn hA ν
  have haμ : IsC11 (ymConn a μ) (ymK B) := isC11_ymConn ha μ
  have haν : IsC11 (ymConn a ν) (ymK B) := isC11_ymConn ha ν
  have hfY := norm_nonneg fromYM
  have hv := norm_linkLogPlaquette_sub_curvature_le hAμ.hasFDerivAt hAν.hasFDerivAt hAμ.norm_le
    hAν.norm_le hAμ.norm_fderiv_le hAν.norm_fderiv_le hAμ.lip hAν.lip (norm_unitE_le μ)
    (norm_unitE_le ν) hK x hh hh1 hs1
  obtain ⟨hd, hdv⟩ := logPlaquette_variation hAμ.hasFDerivAt hAν.hasFDerivAt haμ.hasFDerivAt
    haν.hasFDerivAt hAμ.norm_le hAν.norm_le haμ.norm_le haν.norm_le hAμ.norm_fderiv_le
    hAν.norm_fderiv_le haμ.norm_fderiv_le haν.norm_fderiv_le hAμ.lip hAν.lip haμ.lip haν.lip
    (norm_unitE_le μ) (norm_unitE_le ν) hK hK x hh hh1 hs2
  have hD := (fromYM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).congr_of_eventuallyEq
    (f₁ := fun t : ℝ => logPlaq h (A + t • a) x μ ν) (Eventually.of_forall fun t => by
      show logPlaq h (A + t • a) x μ ν = fromYM _
      rw [logPlaq, ymConn_line, ymConn_line])
  refine ⟨?_, _, hD, ?_⟩
  · rw [logPlaq, ← fromYM_curv hA x μ ν, ← map_sub]
    refine (fromYM.le_opNorm _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv hfY
  · rw [← fromYM_curvDeriv hA ha x μ ν, ← map_sub]
    refine (fromYM.le_opNorm _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hdv hfY

/-- **The Yang–Mills comparison stencil and its variation** (`F^h = F + O(h)`,
`δF^h = Ḟ + O(h)`), uniformly over connections and variations that are `C^{1,1}` with
constant `B`. -/
theorem exists_ym_stencil (B : ℝ) : ∃ C h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ A a : E4 → ConnFibre,
    IsC11 A B → IsC11 a B → ∀ (x : E4) (h : ℝ), 0 < h → h ≤ h₀ → ∀ μ ν : Fin 4,
      ‖fieldStrengthH h A x μ ν - curvatureF A x μ ν‖ ≤ C * h ∧
      ∃ DF : LieFibre, HasDerivAt (fun t : ℝ => fieldStrengthH h (A + t • a) x μ ν) DF 0 ∧
        ‖DF - curvDeriv A a x μ ν‖ ≤ C * h := by
  have hS0 : 0 ≤ ymS B := by unfold ymS; positivity
  refine ⟨‖fromYM‖ * (|ymCval B| + |ymCvar B|), min 1 (1 / (8 * (ymS B + 1))),
    lt_min one_pos (by positivity), min_le_left _ _, fun A a hA ha x h hh hh₀ μ ν => ?_⟩
  have hh1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
  have hh8 : h ≤ 1 / (8 * (ymS B + 1)) := hh₀.trans (min_le_right _ _)
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hSh : ymS B * h ^ 2 ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hh8
    nlinarith
  have e1 : (2 * ymK B + 2 * ymK B ^ 2 + ymCp B) ≤ ymS B :=
    (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  have e2 : (ymCp B + (2 * ymK B + 2 * ymK B ^ 2)) ≤ ymS B :=
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hs1 : (2 * ymK B + 2 * ymK B ^ 2 + ymCp B) * h ^ 2 ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right e1 (sq_nonneg h)]
  have hs2 : (ymCp B + (2 * ymK B + 2 * ymK B ^ 2)) * h ^ 2 ≤ 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right e2 (sq_nonneg h)]
  have hfY := norm_nonneg fromYM
  have hc1 : ‖fromYM‖ * ymCval B * h ≤ ‖fromYM‖ * (|ymCval B| + |ymCvar B|) * h := by
    gcongr; exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hc2 : ‖fromYM‖ * ymCvar B * h ≤ ‖fromYM‖ * (|ymCval B| + |ymCvar B|) * h := by
    gcongr; exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  rcases lt_trichotomy μ ν with hμν | hμν | hμν
  · obtain ⟨c1, DF, c2, c3⟩ := ym_core hA ha x hh hh1 hs1 hs2 μ ν
    simp only [fieldStrengthH, if_pos hμν]
    exact ⟨c1.trans hc1, DF, c2, c3.trans hc2⟩
  · subst hμν
    simp only [fieldStrengthH, lt_irrefl, if_false, curvatureF_diag, curvDeriv_diag, sub_zero,
      norm_zero]
    have hC : 0 ≤ ‖fromYM‖ * (|ymCval B| + |ymCvar B|) * h := by positivity
    exact ⟨hC, 0, hasDerivAt_const _ _, by simpa using hC⟩
  · obtain ⟨c1, DF, c2, c3⟩ := ym_core hA ha x hh hh1 hs1 hs2 ν μ
    have hn : ¬ μ < ν := not_lt.mpr hμν.le
    simp only [fieldStrengthH, if_neg hn, if_pos hμν]
    refine ⟨?_, -DF, c2.neg, ?_⟩
    · rw [curvatureF_antisymm, neg_sub_neg, norm_sub_rev]; exact c1.trans hc1
    · rw [curvDeriv_antisymm, neg_sub_neg, norm_sub_rev]; exact c3.trans hc2

/-! ### The Higgs stencil -/

theorem isC11_higgsConn {A : E4 → ConnFibre} {B : ℝ} (hA : IsC11 A B) (μ : Fin 4) :
    IsC11 (higgsConn A μ) (‖higgsOpL‖ * B) :=
  (isC11_comp_apply hA μ).clm higgsOpL

theorem higgsConn_line (A a : E4 → ConnFibre) (t : ℝ) (μ : Fin 4) :
    higgsConn (A + t • a) μ = higgsConn A μ + t • higgsConn a μ := by
  funext y
  simp [higgsConn, map_add, map_smul]

theorem pd_eq_fderiv_unitE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4 → F)
    (μ : Fin 4) (x : E4) : pd f μ x = fderiv ℝ f x (unitE μ) := rfl

theorem norm_sub_shift_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    {B : ℝ} (hf : IsC11 f B) (x : E4) {h : ℝ} (hh : 0 ≤ h) (μ : Fin 4) :
    ‖f (x + h • unitE μ) - f x‖ ≤ B * h := by
  refine (hf.lipschitz _ _).trans ?_
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hh (norm_unitE_le μ)) hf.nonneg

/-- **The Higgs comparison stencil and its variation** (`K^h = D_AH + O(h)`,
`δK^h = K̇ + O(h)`), uniformly over `C^{1,1}` data with constant `B`. -/
theorem exists_higgs_stencil (B : ℝ) : ∃ C : ℝ, ∀ (A a : E4 → ConnFibre) (H η : E4 → HiggsFibre),
    IsC11 A B → IsC11 a B → IsC11 H B → IsC11 η B → ∀ (x : E4) (h : ℝ), 0 < h → h ≤ 1 →
    ∀ μ : Fin 4,
      ‖higgsLinkH h A H x μ - covDerivHiggs A H x μ‖ ≤ C * h ∧
      ∃ DK : HiggsFibre, HasDerivAt (fun t : ℝ => higgsLinkH h (A + t • a) (H + t • η) x μ) DK 0 ∧
        ‖DK - higgsDeriv A H a η x μ‖ ≤ C * h := by
  set K := ‖higgsOpL‖ * B
  refine ⟨((K ^ 2 * Real.exp K + K) * B + B + K * (B + B)) +
      ((((K + K) ^ 2 * Real.exp (K + K) + (K + K)) * B + K * B) +
        ((K ^ 2 * Real.exp K + K) * B + B + K * (B + B))),
    fun A a H η hA ha hH hη x h hh hh1 μ => ?_⟩
  have hB := hA.nonneg
  have hK : 0 ≤ K := by positivity
  have hAμ := isC11_higgsConn hA μ
  have haμ := isC11_higgsConn ha μ
  have hval := norm_higgsLink_sub_covDeriv_le (A := higgsConn A μ) (H := H)
    (H' := fun y => fderiv ℝ H y) hK hAμ.lipschitz hAμ.norm_le hH.hasFDerivAt hH.lip hB hH.norm_le
    (norm_unitE_le μ) x hh hh1
  have hH' : ‖fderiv ℝ H x (unitE μ)‖ ≤ B :=
    ((fderiv ℝ H x).le_opNorm _).trans ((mul_le_mul (hH.norm_fderiv_le x) (norm_unitE_le μ)
      (norm_nonneg _) hB).trans (by rw [mul_one]))
  have hη' : ‖fderiv ℝ η x (unitE μ)‖ ≤ B :=
    ((fderiv ℝ η x).le_opNorm _).trans ((mul_le_mul (hη.norm_fderiv_le x) (norm_unitE_le μ)
      (norm_nonneg _) hB).trans (by rw [mul_one]))
  have hd := hasDerivAt_fwdDiff hAμ.continuous haμ.continuous hAμ.norm_le haμ.norm_le H η
    (unitE μ) x hh.le
  have hvar := norm_fwdDiff_variation_sub_le hK hK hAμ.lipschitz haμ.lipschitz hAμ.norm_le
    haμ.norm_le hH.norm_le hη.hasFDerivAt hη.lip hB hη.norm_le (norm_unitE_le μ) x hh hh1
    (norm_sub_shift_le hH x hh.le μ)
  have hpos1 : 0 ≤ ((K ^ 2 * Real.exp K + K) * B + B + K * (B + B)) := by positivity
  have hpos2 : 0 ≤ ((((K + K) ^ 2 * Real.exp (K + K) + (K + K)) * B + K * B) +
      ((K ^ 2 * Real.exp K + K) * B + B + K * (B + B))) := by positivity
  have hD := hd.congr_of_eventuallyEq
    (f₁ := fun t : ℝ => higgsLinkH h (A + t • a) (H + t • η) x μ) (Eventually.of_forall fun t => by
      show fwdDiff (higgsConn (A + t • a) μ) (H + t • η) (unitE μ) x h = _
      rw [higgsConn_line])
  refine ⟨?_, _, hD, ?_⟩
  · show ‖fwdDiff (higgsConn A μ) H (unitE μ) x h - covDerivHiggs A H x μ‖ ≤ _
    rw [covDerivHiggs_eq]
    refine hval.trans ?_
    have : (K ^ 2 * Real.exp K + K) * B + B + K * (‖fderiv ℝ H x (unitE μ)‖ + B) ≤
        (K ^ 2 * Real.exp K + K) * B + B + K * (B + B) := by gcongr
    calc _ ≤ ((K ^ 2 * Real.exp K + K) * B + B + K * (B + B)) * h :=
          mul_le_mul_of_nonneg_right this hh.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hpos2) hh.le
  · have e : higgsDeriv A H a η x μ = higgsConn a μ x (H x) +
        (fderiv ℝ η x (unitE μ) + higgsConn A μ x (η x)) := by
      simp only [higgsDeriv, higgsConn, higgsOpL, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_mk, AddHom.coe_mk, higgsActL_apply, pd_eq_fderiv_unitE]
      abel
    rw [e]
    refine hvar.trans ?_
    have : (((K + K) ^ 2 * Real.exp (K + K) + (K + K)) * B + K * B) +
        ((K ^ 2 * Real.exp K + K) * B + B + K * (‖fderiv ℝ η x (unitE μ)‖ + B)) ≤
        (((K + K) ^ 2 * Real.exp (K + K) + (K + K)) * B + K * B) +
          ((K ^ 2 * Real.exp K + K) * B + B + K * (B + B)) := by gcongr
    calc _ ≤ _ := mul_le_mul_of_nonneg_right this hh.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hpos1) hh.le

/-! ### The spin–gauge stencils -/

/-- **A centred covariant stencil along a non-affine family of connections** `Ω_t = Φ(p + t q)`
(generic, for a `C²` connection map `Φ` on the jet chart): value and first-variation estimates,
uniform over `p` in a compact chart set and `C^{0,1}` data with constant `B`. -/
theorem exists_centred_stencil {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [Nontrivial F] {Φ : SJet → F →L[ℝ] F} (hΦ : ContDiffOn ℝ 2 Φ sjetGL)
    {Kc : Set SJet} (hKc : IsCompact Kc) (hsub : Kc ⊆ sjetGL) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, ∀ (p q : E4 → SJet) (Ψ η : E4 → F) (Ω : ℝ → E4 → F →L[ℝ] F),
      (∀ y, p y ∈ Kc) → (∀ y y', ‖p y - p y'‖ ≤ B * ‖y - y'‖) → (∀ y, ‖q y‖ ≤ B) →
      (∀ y y', ‖q y - q y'‖ ≤ B * ‖y - y'‖) → IsC11 Ψ B → IsC11 η B →
      (∀ (t : ℝ) y, p y + t • q y ∈ sjetGL → Ω t y = Φ (p y + t • q y)) →
      ∀ (x : E4) (h : ℝ) (μ : Fin 4), 0 < h → h ≤ 1 →
        ‖centredDiff (Ω 0) Ψ (unitE μ) x h - (fderiv ℝ Ψ x (unitE μ) + Ω 0 x (Ψ x))‖ ≤ C * h ∧
        ∃ D : F, HasDerivAt (fun t : ℝ => centredDiff (Ω t) (Ψ + t • η) (unitE μ) x h) D 0 ∧
          ‖D - (fderiv ℝ Φ (p x) (q x) (Ψ x) + (fderiv ℝ η x (unitE μ) + Ω 0 x (η x)))‖ ≤
            C * h := by
  obtain ⟨δ, M₀, M₁, L₀, L₁, Cq, hcd⟩ := exists_chartData isOpen_sjetGL hΦ hKc hsub
  obtain ⟨δ', hδ', hδ'U⟩ := hKc.exists_cthickening_subset_open isOpen_sjetGL hsub
  set δ₀ := min δ δ'
  have hδ₀ : 0 < δ₀ := lt_min hcd.δ_pos hδ'
  set τ := δ₀ / (2 * (B + 1))
  have hτ : 0 < τ := by positivity
  have hτB : τ * B < δ₀ := by
    simp only [τ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set Λ := L₀ * B
  set Λa := L₁ * B * B + M₁ * B
  set Kv := M₁ * B
  set C1 := (M₀ ^ 2 * Real.exp M₀ + 2 * Λ) * B + B + M₀ * B
  set C2 := ((M₀ ^ 2 * Real.exp M₀ + 2 * Λ) * B + B + M₀ * B) +
    (((M₀ + Kv) ^ 2 * Real.exp (M₀ + Kv) + (Λ + Λa)) * B + Kv * B + Λa * B)
  refine ⟨|C1| + |C2|, fun p q Ψ η Ω hpK hpL hqB hqL hΨ hη hΩ x h μ hh hh1 => ?_⟩
  have hM₀ := hcd.M₀_nonneg; have hM₁ := hcd.M₁_nonneg; have hL₀ := hcd.L₀_nonneg
  have hL₁ := hcd.L₁_nonneg
  -- the family on `|t| ≤ τ`
  have hsmall : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖t • q y‖ < δ₀ := by
    intro t ht y
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖q y‖ ≤ τ * B := mul_le_mul ht (hqB y) (norm_nonneg _) hτ.le
      _ < δ₀ := hτB
  have hmem : ∀ t : ℝ, |t| ≤ τ → ∀ y, p y + t • q y ∈ sjetGL := fun t ht y =>
    hδ'U (mem_cthickening_of_dist_le _ (p y) δ' Kc (hpK y) (by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact ((hsmall t ht y).le).trans (min_le_right _ _)))
  have hΩt : ∀ t : ℝ, |t| ≤ τ → Ω t = fun y => Φ (p y + t • q y) := fun t ht =>
    funext fun y => hΩ t y (hmem t ht y)
  have hΩ0 : Ω 0 = fun y => Φ (p y) := by
    rw [hΩt 0 (by simp [hτ.le])]; simp
  have hpc : Continuous p := continuous_of_norm_sub_le hB hpL
  have hqc : Continuous q := continuous_of_norm_sub_le hB hqL
  have hΩc : ∀ t : ℝ, |t| ≤ τ → Continuous (Ω t) := by
    intro t ht
    rw [hΩt t ht]
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ContinuousAt.comp (hcd.contAt _ (hpK y) _ ((hsmall t ht y).trans_le (min_le_left _ _)))
      (hpc.add (hqc.const_smul t)).continuousAt
  have hfdc : ContinuousOn (fderiv ℝ Φ) sjetGL :=
    hΦ.continuousOn_fderiv_of_isOpen isOpen_sjetGL (by norm_num)
  set α : E4 → F →L[ℝ] F := fun y => fderiv ℝ Φ (p y) (q y)
  have hαc : Continuous α :=
    (hfdc.comp_continuous hpc fun y => hsub (hpK y)).clm_apply hqc
  have hK : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y‖ ≤ M₀ := by
    intro t ht y
    rw [hΩt t ht]
    exact hcd.bound _ (hpK y) _ (((hsmall t ht y).le).trans (min_le_left _ _))
  have hKa : ∀ y, ‖α y‖ ≤ Kv := fun y =>
    ((fderiv ℝ Φ (p y)).le_opNorm _).trans (mul_le_mul (hcd.dbound _ (hpK y)) (hqB y)
      (norm_nonneg _) hM₁)
  have hq : ∀ t : ℝ, |t| ≤ τ → ∀ y, ‖Ω t y - (Ω 0 y + t • α y)‖ ≤ (Cq * B ^ 2) * t ^ 2 := by
    intro t ht y
    rw [hΩt t ht, hΩ0]
    have := hcd.taylor _ (hpK y) (t • q y) (((hsmall t ht y).le).trans (min_le_left _ _))
    rw [map_smul] at this
    simp only [α]
    rw [show Φ (p y + t • q y) - (Φ (p y) + t • fderiv ℝ Φ (p y) (q y)) =
      Φ (p y + t • q y) - Φ (p y) - t • fderiv ℝ Φ (p y) (q y) by abel]
    refine this.trans ?_
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have : ‖q y‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hqB y) 2
    have h2 := mul_le_mul_of_nonneg_left this (mul_nonneg hcd.Cq_nonneg (sq_nonneg t))
    linarith
  -- Lipschitz data of `Ω 0` and `α`
  have hAL : ∀ y y', ‖Ω 0 y - Ω 0 y'‖ ≤ Λ * ‖y - y'‖ := by
    intro y y'
    rw [hΩ0]
    exact (hcd.lip _ (hpK y) _ (hpK y')).trans (by
      simp only [Λ]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hpL y y') hL₀)
  have hαL : ∀ y y', ‖α y - α y'‖ ≤ Λa * ‖y - y'‖ := by
    intro y y'
    have e : α y - α y' = (fderiv ℝ Φ (p y) - fderiv ℝ Φ (p y')) (q y) +
        fderiv ℝ Φ (p y') (q y - q y') := by
      simp only [α, ContinuousLinearMap.sub_apply, map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(fderiv ℝ Φ (p y) - fderiv ℝ Φ (p y')) (q y)‖ ≤ L₁ * (B * ‖y - y'‖) * B :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul ((hcd.dlip _ (hpK y) _ (hpK y')).trans
        (mul_le_mul_of_nonneg_left (hpL y y') hL₁)) (hqB y) (norm_nonneg _) (by positivity))
    have t2 : ‖fderiv ℝ Φ (p y') (q y - q y')‖ ≤ M₁ * (B * ‖y - y'‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hcd.dbound _ (hpK y')) (hqL y y')
        (norm_nonneg _) hM₁)
    calc _ ≤ L₁ * (B * ‖y - y'‖) * B + M₁ * (B * ‖y - y'‖) := add_le_add t1 t2
      _ = Λa * ‖y - y'‖ := by simp only [Λa]; ring
  have hK0 : ∀ y, ‖Ω 0 y‖ ≤ M₀ := hK 0 (by simp [hτ.le])
  have hΛ : 0 ≤ Λ := by positivity
  have hΛa : 0 ≤ Λa := by positivity
  -- value
  have hval := norm_spinDifference_sub_covDeriv_le (A := Ω 0) (Ψ := Ψ)
    (Ψ' := fun y => fderiv ℝ Ψ y) hΛ hAL hK0 hΨ.hasFDerivAt hΨ.lip hB hΨ.norm_le
    (norm_unitE_le μ) x hh hh1
  -- variation
  have hd := hasDerivAt_centredDiff hτ hΩc hαc hK hKa hq Ψ η (unitE μ) x hh.le
  have hvar := norm_centredDiff_variation_sub_le (A := Ω 0) (a := α) (Ψ := Ψ) (η := η)
    (η' := fun y => fderiv ℝ η y) hΛ hΛa hAL hαL hK0 hKa hΨ.norm_le hΨ.lipschitz hB
    hη.hasFDerivAt hη.lip hB hη.norm_le (norm_unitE_le μ) x hh hh1
  refine ⟨?_, _, hd, ?_⟩
  · refine hval.trans (mul_le_mul_of_nonneg_right ?_ hh.le)
    exact (le_abs_self C1).trans (le_add_of_nonneg_right (abs_nonneg _))
  · refine hvar.trans (mul_le_mul_of_nonneg_right ?_ hh.le)
    exact (le_abs_self C2).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- **`C^{1,1}` field tuples** with a common constant `B`. -/
structure FieldC11 (z : FieldTuple FC.C) (B : ℝ) : Prop where
  e : IsC11 z.e B
  A : IsC11 z.A B
  H : IsC11 z.H B
  Ψ : IsC11 z.Ψ B
  Ψb : IsC11 z.Ψb B

theorem FieldC11.diffAt {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) (x : E4) :
    DiffAt FC z x :=
  ⟨hz.e.differentiable x, hz.A.differentiable x, hz.H.differentiable x, hz.Ψ.differentiable x,
    hz.Ψb.differentiable x⟩

theorem norm_eJet_le_fderiv {f : E4 → CoframeFibre} (y : E4) : ‖eJet f y‖ ≤ ‖fderiv ℝ f y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  exact ((fderiv ℝ f y).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_unitE_le i) (norm_nonneg _)).trans (by rw [mul_one]))

theorem norm_eJet_sub_le {f : E4 → CoframeFibre} (y y' : E4) :
    ‖eJet f y - eJet f y'‖ ≤ ‖fderiv ℝ f y - fderiv ℝ f y'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  show ‖fderiv ℝ f y (unitE i) - fderiv ℝ f y' (unitE i)‖ ≤ _
  rw [← ContinuousLinearMap.sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_left (norm_unitE_le i) (norm_nonneg _)).trans (by rw [mul_one]))

theorem sjetOf_norm_le {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) (μ : Fin 4)
    (y : E4) : ‖sjetOf FC z μ y‖ ≤ B := by
  have hB := hz.e.nonneg
  refine norm_prod_le_iff.mpr ⟨hz.e.norm_le y, norm_prod_le_iff.mpr
    ⟨(norm_eJet_le_fderiv y).trans (hz.e.norm_fderiv_le y), (norm_le_pi_norm _ μ).trans
      (hz.A.norm_le y)⟩⟩

theorem sjetOf_lip {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) (μ : Fin 4)
    (y y' : E4) : ‖sjetOf FC z μ y - sjetOf FC z μ y'‖ ≤ B * ‖y - y'‖ := by
  refine norm_prod_le_iff.mpr ⟨hz.e.lipschitz y y', norm_prod_le_iff.mpr
    ⟨(norm_eJet_sub_le y y').trans (hz.e.lip y y'), ?_⟩⟩
  show ‖z.A y μ - z.A y' μ‖ ≤ _
  exact (norm_le_pi_norm (z.A y - z.A y') μ).trans (hz.A.lipschitz y y')

/-- The compact jet chart set `𝒦_e × B̄(0,B) × B̄(0,B)`. -/
def sjetBox (Ke : Set CoframeFibre) (B : ℝ) : Set SJet :=
  Ke ×ˢ (Metric.closedBall 0 B ×ˢ Metric.closedBall 0 B)

theorem isCompact_sjetBox {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (B : ℝ) :
    IsCompact (sjetBox Ke B) :=
  hKe.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

theorem sjetBox_subset {Ke : Set CoframeFibre} (hKe : Ke ⊆ coframeGL) (B : ℝ) :
    sjetBox Ke B ⊆ sjetGL := fun p hp => hKe hp.1

theorem sjetOf_mem {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) {Ke : Set CoframeFibre}
    (hzK : ∀ y, z.e y ∈ Ke) (μ : Fin 4) (y : E4) : sjetOf FC z μ y ∈ sjetBox Ke B :=
  ⟨hzK y, mem_closedBall_zero_iff.mpr ((norm_eJet_le_fderiv y).trans (hz.e.norm_fderiv_le y)),
    mem_closedBall_zero_iff.mpr ((norm_le_pi_norm _ μ).trans (hz.A.norm_le y))⟩

/-- **The spin–gauge comparison stencils** (`∇^hΨ = ∇Ψ + O(h)`, `δ∇^hΨ = ∇̇Ψ + O(h)`) and their
duals, uniformly over `C^{1,1}` fields with coframe values in a compact chart set. -/
theorem exists_dirac_stencil [Nonempty FC.C] (B : ℝ) (hB : 0 ≤ B) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hKeGL : Ke ⊆ coframeGL) : ∃ C : ℝ, ∀ z w : FieldTuple FC.C, FieldC11 FC z B →
    FieldC11 FC w B → (∀ y, z.e y ∈ Ke) → ∀ (x : E4) (h : ℝ) (μ : Fin 4), 0 < h → h ≤ 1 →
      (‖spinorDiffH FC h z x μ - covDerivSpinor FC z.e z.A z.Ψ x μ‖ ≤ C * h ∧
        ∃ D, HasDerivAt (fun t : ℝ => spinorDiffH FC h (z + t • w) x μ) D 0 ∧
          ‖D - (pd w.Ψ μ x + spinConnDeriv FC z w μ x (z.Ψ x) +
            spinConnection FC z μ x (w.Ψ x))‖ ≤ C * h) ∧
      (‖cospinorDiffH FC h z x μ - covDerivCospinor FC z.e z.A z.Ψb x μ‖ ≤ C * h ∧
        ∃ D, HasDerivAt (fun t : ℝ => cospinorDiffH FC h (z + t • w) x μ) D 0 ∧
          ‖D - (pd w.Ψb μ x + cospinConnDeriv FC z w μ x (z.Ψb x) +
            cospinConnection FC z μ x (w.Ψb x))‖ ≤ C * h) := by
  have hS : ∀ μ : Fin 4, ∃ C : ℝ, _ := fun μ => exists_centred_stencil (contDiffOn_spinConnMap FC μ)
    (isCompact_sjetBox hKe B) (sjetBox_subset hKeGL B) B hB
  have hCo : ∀ μ : Fin 4, ∃ C : ℝ, _ := fun μ =>
    exists_centred_stencil (contDiffOn_cospinConnMap FC μ) (isCompact_sjetBox hKe B)
      (sjetBox_subset hKeGL B) B hB
  choose C hC using hS
  choose C' hC' using hCo
  refine ⟨∑ μ, (|C μ| + |C' μ|), fun z w hz hw hzK x h μ hh hh1 => ?_⟩
  have hle : |C μ| + |C' μ| ≤ ∑ ν, (|C ν| + |C' ν|) :=
    Finset.single_le_sum (f := fun ν => |C ν| + |C' ν|) (fun _ _ => by positivity)
      (Finset.mem_univ μ)
  have hCμ : C μ * h ≤ (∑ ν, (|C ν| + |C' ν|)) * h :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((le_add_of_nonneg_right
      (abs_nonneg _)).trans hle)) hh.le
  have hC'μ : C' μ * h ≤ (∑ ν, (|C ν| + |C' ν|)) * h :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((le_add_of_nonneg_left
      (abs_nonneg _)).trans hle)) hh.le
  have hdline : ∀ (t : ℝ) (y : E4), sjetOf FC z μ y + t • sjetOf FC w μ y ∈ sjetGL →
      DifferentiableAt ℝ (z + t • w).e y ∧ (z + t • w).e y ∈ coframeGL := by
    intro t y hy
    have hdd : DifferentiableAt ℝ (z.e + t • w.e) y :=
      (hz.e.differentiable y).add ((hw.e.differentiable y).const_smul t)
    exact ⟨hdd, hy⟩
  obtain ⟨v1, D1, hd1, hv1⟩ := hC μ (sjetOf FC z μ) (sjetOf FC w μ) z.Ψ w.Ψ
    (fun t => spinConnection FC (z + t • w) μ) (sjetOf_mem FC hz hzK μ) (sjetOf_lip FC hz μ)
    (sjetOf_norm_le FC hw μ) (sjetOf_lip FC hw μ) hz.Ψ hw.Ψ (fun t y hy => by
      obtain ⟨h1, h2⟩ := hdline t y hy
      rw [spinConnection_eq_map FC _ μ h1 h2, sjetOf_line FC (hz.e.differentiable y)
        (hw.e.differentiable y) μ t]) x h μ hh hh1
  obtain ⟨v2, D2, hd2, hv2⟩ := hC' μ (sjetOf FC z μ) (sjetOf FC w μ) z.Ψb w.Ψb
    (fun t => cospinConnection FC (z + t • w) μ) (sjetOf_mem FC hz hzK μ) (sjetOf_lip FC hz μ)
    (sjetOf_norm_le FC hw μ) (sjetOf_lip FC hw μ) hz.Ψb hw.Ψb (fun t y hy => by
      obtain ⟨h1, h2⟩ := hdline t y hy
      rw [cospinConnection_eq_map FC _ μ h1 h2, sjetOf_line FC (hz.e.differentiable y)
        (hw.e.differentiable y) μ t]) x h μ hh hh1
  have z0 : z + (0 : ℝ) • w = z := by simp
  simp only [z0] at v1 hv1 v2 hv2
  refine ⟨⟨?_, D1, hd1, ?_⟩, ⟨?_, D2, hd2, ?_⟩⟩
  · rw [covDerivSpinor_eq]; exact v1.trans hCμ
  · refine le_trans (le_of_eq ?_) (hv1.trans hCμ)
    congr 1; simp only [spinConnDeriv, pd_eq_fderiv_unitE]; abel
  · rw [covDerivCospinor_eq]; exact v2.trans hC'μ
  · refine le_trans (le_of_eq ?_) (hv2.trans hC'μ)
    congr 1; simp only [cospinConnDeriv, pd_eq_fderiv_unitE]; abel

/-! ### The comparison stencil jet -/

theorem norm_rjet_le {e : CoframeFibre} {de : CoframeJet} {A : ConnFibre} {F : Fin 4 → ConnFibre}
    {H : HiggsFibre} {K : Fin 4 → HiggsFibre} {Ψ : SpinorFibre FC.C} {dΨ : Fin 4 → SpinorFibre FC.C}
    {Ψb : SpinorFibre FC.C} {dΨb : Fin 4 → SpinorFibre FC.C} {c : ℝ} (he : ‖e‖ ≤ c)
    (hde : ‖de‖ ≤ c) (hA : ‖A‖ ≤ c) (hF : ‖F‖ ≤ c) (hH : ‖H‖ ≤ c) (hK : ‖K‖ ≤ c) (hΨ : ‖Ψ‖ ≤ c)
    (hdΨ : ‖dΨ‖ ≤ c) (hΨb : ‖Ψb‖ ≤ c) (hdΨb : ‖dΨb‖ ≤ c) :
    ‖RJet.mk e de A F H K Ψ dΨ Ψb dΨb‖ ≤ c :=
  norm_prod_le_iff.mpr ⟨he, norm_prod_le_iff.mpr ⟨hde, norm_prod_le_iff.mpr ⟨hA,
    norm_prod_le_iff.mpr ⟨hF, norm_prod_le_iff.mpr ⟨hH, norm_prod_le_iff.mpr ⟨hK,
      norm_prod_le_iff.mpr ⟨hΨ, norm_prod_le_iff.mpr ⟨hdΨ, norm_prod_le_iff.mpr
        ⟨hΨb, hdΨb⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem rjet_mk_sub (e e' : CoframeFibre) (de de' : CoframeJet) (A A' : ConnFibre)
    (F F' : Fin 4 → ConnFibre) (H H' : HiggsFibre) (K K' : Fin 4 → HiggsFibre)
    (Ψ Ψ' : SpinorFibre FC.C) (dΨ dΨ' : Fin 4 → SpinorFibre FC.C) (Ψb Ψb' : SpinorFibre FC.C)
    (dΨb dΨb' : Fin 4 → SpinorFibre FC.C) :
    RJet.mk e de A F H K Ψ dΨ Ψb dΨb - RJet.mk e' de' A' F' H' K' Ψ' dΨ' Ψb' dΨb' =
      RJet.mk (e - e') (de - de') (A - A') (F - F') (H - H') (K - K') (Ψ - Ψ') (dΨ - dΨ')
        (Ψb - Ψb') (dΨb - dΨb') := rfl

theorem norm_pi2_le {α : Type*} [NormedAddCommGroup α] {F : Fin 4 → Fin 4 → α} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ μ ν, ‖F μ ν‖ ≤ c) : ‖F‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).mpr fun μ => (pi_norm_le_iff_of_nonneg hc).mpr fun ν => h μ ν

theorem norm_pi1_le {α : Type*} [NormedAddCommGroup α] {F : Fin 4 → α} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ μ, ‖F μ‖ ≤ c) : ‖F‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).mpr h

/-- **Pointwise stencil consistency of the whole comparison jet** (values and first variations),
uniformly over `C^{1,1}` fields and directions with constant `B` and coframes in a compact chart
set. -/
theorem exists_stencilJet_estimates [Nonempty FC.C] (B : ℝ) (hB : 0 ≤ B) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL) : ∃ C h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
    ∀ z w : FieldTuple FC.C, FieldC11 FC z B → FieldC11 FC w B → (∀ y, z.e y ∈ Ke) →
    ∀ (x : E4) (h : ℝ), 0 < h → h ≤ h₀ →
      ‖stencilJet FC h z x - contJet FC z x‖ ≤ C * h ∧
      ∃ D : RJet FC.C, HasDerivAt (fun t : ℝ => stencilJet FC h (z + t • w) x) D 0 ∧
        ‖D - contJetDeriv FC z w x‖ ≤ C * h := by
  obtain ⟨C₁, h₀, hh₀, hh₀1, hYM⟩ := exists_ym_stencil B
  obtain ⟨C₂, hHi⟩ := exists_higgs_stencil B
  obtain ⟨C₃, hDi⟩ := exists_dirac_stencil FC B hB hKe hKeGL
  refine ⟨|C₁| + |C₂| + |C₃|, h₀, hh₀, hh₀1, fun z w hz hw hzK x h hh hhh₀ => ?_⟩
  have hh1 : h ≤ 1 := hhh₀.trans hh₀1
  have hc0 : 0 ≤ (|C₁| + |C₂| + |C₃|) * h := by positivity
  have n1 := abs_nonneg C₁
  have n2 := abs_nonneg C₂
  have n3 := abs_nonneg C₃
  have a1 : C₁ ≤ |C₁| + |C₂| + |C₃| := by have := le_abs_self C₁; linarith
  have a2 : C₂ ≤ |C₁| + |C₂| + |C₃| := by have := le_abs_self C₂; linarith
  have a3 : C₃ ≤ |C₁| + |C₂| + |C₃| := by have := le_abs_self C₃; linarith
  have b1 := mul_le_mul_of_nonneg_right a1 hh.le
  have b2 := mul_le_mul_of_nonneg_right a2 hh.le
  have b3 := mul_le_mul_of_nonneg_right a3 hh.le
  have Y := fun μ ν => hYM z.A w.A hz.A hw.A x h hh hhh₀ μ ν
  have Hg := fun μ => hHi z.A w.A z.H w.H hz.A hw.A hz.H hw.H x h hh hh1 μ
  have Dc := fun μ => hDi z w hz hw hzK x h μ hh hh1
  choose DF hDF hDFb using fun μ ν => (Y μ ν).2
  choose DK hDK hDKb using fun μ => (Hg μ).2
  choose DS hDS hDSn using fun μ => (Dc μ).1.2
  choose DSb hDSb hDSbn using fun μ => (Dc μ).2.2
  refine ⟨?_, RJet.mk (w.e x) 0 0 DF (w.H x) DK (w.Ψ x) DS (w.Ψb x) DSb, ?_, ?_⟩
  · rw [stencilJet, contJet, rjet_mk_sub]
    refine norm_rjet_le FC (by simpa using hc0) (by simpa using hc0) (by simpa using hc0)
      (norm_pi2_le hc0 fun μ ν => ?_) (by simpa using hc0) (norm_pi1_le hc0 fun μ => ?_)
      (by simpa using hc0) (norm_pi1_le hc0 fun μ => ?_) (by simpa using hc0)
      (norm_pi1_le hc0 fun μ => ?_)
    · exact (Y μ ν).1.trans b1
    · exact (Hg μ).1.trans b2
    · exact (Dc μ).1.1.trans b3
    · exact (Dc μ).2.1.trans b3
  · have he := hasDerivAt_line_apply (z.e x) (w.e x)
    have hH := hasDerivAt_line_apply (z.H x) (w.H x)
    have hΨ := hasDerivAt_line_apply (z.Ψ x) (w.Ψ x)
    have hΨb := hasDerivAt_line_apply (z.Ψb x) (w.Ψb x)
    have hF : HasDerivAt (fun t : ℝ => fieldStrengthH h (z + t • w).A x) DF 0 :=
      hasDerivAt_pi.mpr fun μ => hasDerivAt_pi.mpr fun ν => hDF μ ν
    have hK : HasDerivAt (fun t : ℝ => higgsLinkH h (z + t • w).A (z + t • w).H x) DK 0 :=
      hasDerivAt_pi.mpr fun μ => hDK μ
    have hS : HasDerivAt (fun t : ℝ => spinorDiffH FC h (z + t • w) x) DS 0 :=
      hasDerivAt_pi.mpr fun μ => hDS μ
    have hSb : HasDerivAt (fun t : ℝ => cospinorDiffH FC h (z + t • w) x) DSb 0 :=
      hasDerivAt_pi.mpr fun μ => hDSb μ
    have h0 : HasDerivAt (fun _ : ℝ => (0 : CoframeJet)) 0 0 := hasDerivAt_const _ _
    have h0' : HasDerivAt (fun _ : ℝ => (0 : ConnFibre)) 0 0 := hasDerivAt_const _ _
    exact he.prodMk (h0.prodMk (h0'.prodMk (hF.prodMk (hH.prodMk (hK.prodMk (hΨ.prodMk
      (hS.prodMk (hΨb.prodMk hSb))))))))
  · rw [contJetDeriv, rjet_mk_sub]
    refine norm_rjet_le FC (by simpa using hc0) (by simpa using hc0) (by simpa using hc0)
      (norm_pi2_le hc0 fun μ ν => ?_) (by simpa using hc0) (norm_pi1_le hc0 fun μ => ?_)
      (by simpa using hc0) (norm_pi1_le hc0 fun μ => ?_) (by simpa using hc0)
      (norm_pi1_le hc0 fun μ => ?_)
    · exact (hDFb μ ν).trans b1
    · exact (hDKb μ).trans b2
    · exact (hDSn μ).trans b3
    · exact (hDSbn μ).trans b3

end Comparison
end EinsteinSM
end RenewalGeometry
