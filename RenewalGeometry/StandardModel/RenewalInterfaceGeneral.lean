/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.NativeStandardModelPacket
import RenewalGeometry.Continuum.NativeLocalActionFrechet

/-!
# Renewal realization of the finite interface by the native local action
  (`prop:renewal-interface`; Einstein–Standard-Model action-closure manuscript)

`prop:renewal-interface`: the renewal constructions realize `def:finite-interface` on a selected
Standard-Model branch, i.e. they provide a nonempty family of finite interfaces with the structural
bundle content and the common-action normalization required by (I1)–(I5).

This file instantiates the chart encoding `SpinorFiniteInterface` (`FiniteInterfaceGeneral.lean`)
with the paper's own objects:

* **(I1)** sites: the periodic lattice `(ℤ/n)⁴`; the configuration space `𝒬_h` (`LCfg`) has the
  native variables of `eq:native-local-action` in link form (`subsec:local-action-conventions`):
  coframes `e(x) ∈ M₄(ℝ)`, internal links `U_μ(x)` in the gauge algebra, Higgs field, spinor and
  independent co-spinor at every site; the oriented incidence is `x ↦ x + e_μ`; the **admissible
  chart** (`admChart`) is the open set where all coframes are oriented and time-oriented
  (`det e > 0`, `e⁰₀ > 0`), all links are invertible, and all gauge and Cartan plaquettes lie in the
  logarithm chart `‖P - 1‖ < 1` (`isOpen_admChart`; it contains the flat configuration,
  `flatCfg_mem`).
* **(I2)** the minimal branch of `tab:SM-representations`, the gauge group `S(U(3)×U(2))` embedded
  in the gauge algebra by `ι(y) = (U₂(y), tableRep(y))` (`NativeSMPacket.iota`), the Higgs doublet.
* **(I3)** the spinor fibre `ℂ^{Dirac} ⊗ ℂ³_gen ⊗ ℂ^{15}` with the Weyl-basis Clifford module
  (`NativeSMPacket.gam`, `gam5`), the coefficient bank `θ`, and the **Dirac incidence operator built
  from the native Dirac density**: the spin–gauge links `V_μ = e^{hσ(ω_{μ,h})} ρ_S(U_μ)` of
  `eq:native-matter-links` (`spinLinkC`, equal to `NativeGauge.sLink` of the action:
  `spinLinkC_mulVec`), the frame gammas `γ^μ(e)` of the density (`gammaMuF_mulVec`) and the
  Yukawa blocks `𝓜_𝐘(H)` of `lem:SM-descent` (`yukawa_mulVec`); the kinetic part of the operator is
  `i γ^μ(e) ∇^h_μ` with `∇^h_μ` the action's covariant difference `NativeGauge.dDiff`
  (`incidence_kinetic_eq_dDiff`).
* **(I4)** the common action is **the native local action** `S_h^{loc}` (`eq:native-local-action`)
  in its link variables: `S_g = h⁴ Σ 𝓛_{g,h}`, `S_SM = h⁴ Σ (𝓛_{YM,h} + 𝓛_{H,h} + 𝓛_{D,h})`, `ν = 1`
  (`NativeGauge.linkAction` of the packet `smCovData θ`); on every native record `y` it is
  `NativeDensity.localAction` (`action_toLinks`).  It is `C^∞` on the admissible chart
  (`contDiffAt_linkActionC`, by the analytic logarithm, the exponential, the inverse on units and the
  smooth Cartan reader) and exactly invariant there under all site gauges `Grid → G_SM`
  (`NativeGauge.linkAction_gauge`), which preserve the chart.
* **(I5)** the cell-volume Gram `h⁴ ⟨·,·⟩` of a fixed coordinate basis of `𝒬_h`, positive definite.

`renewal_interface_general` records these identifications; `renewal_interface_general_nonempty`
is the nonemptiness of the family.  Disclosed renderings: the selected branch is the minimal one
(allowed: "on a selected Standard-Model branch"); the internal links range over the ambient
gauge algebra `End(ℂ²) × End(ℂ^{15})` (the group is not a vector space), the gauge group being the
image of `S(U(3)×U(2))`; the Gram form is coordinate (cell-volume) Euclidean.
-/

open Matrix NormedSpace Filter Topology
open scoped Kronecker ContDiff

noncomputable section

namespace RenewalGeometry
namespace RenewalNativeInterface

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat omegaLink)
open NativeDensity
open NativeGauge (LinkConfig plaq curv hLink sLink sLinkInv dDiff dDiffBar gravD ymD higgsD diracD
  linkAction)

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable {n : ℕ} [NeZero n]

/-! ### The link configuration space as a normed space -/

/-- **The link configuration space** `𝒬_h`: coframes, internal links, Higgs field, spinor and
co-spinor at every site. -/
abbrev LCfg (n : ℕ) (𝔄 𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] : Type _ :=
  (Grid n → Mat) × (Fin 4 → Grid n → 𝔄) × (Grid n → 𝓗) × (Grid n → 𝓢) × (Grid n → CoSpinor 𝓢)

/-- The link configuration of a point of `𝒬_h`. -/
def toLC (q : LCfg n 𝔄 𝓗 𝓢) : LinkConfig n 𝔄 𝓗 𝓢 := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2⟩

/-- The point of `𝒬_h` of a link configuration. -/
def ofLC (c : LinkConfig n 𝔄 𝓗 𝓢) : LCfg n 𝔄 𝓗 𝓢 := (c.e, c.U, c.H, c.Ψ, c.Ψb)

@[simp] theorem toLC_ofLC (c : LinkConfig n 𝔄 𝓗 𝓢) : toLC (ofLC c) = c := rfl

@[simp] theorem ofLC_toLC (q : LCfg n 𝔄 𝓗 𝓢) : ofLC (toLC q) = q := rfl

/-- A coframe-only record (the coframe sector of the native densities). -/
def recOf (q : LCfg n 𝔄 𝓗 𝓢) : Grid n → Field 𝔄 𝓗 𝓢 := fun x => (q.1 x, 0, 0, 0, 0)

theorem contDiff_recOf : ContDiff ℝ ∞ (recOf : LCfg n 𝔄 𝓗 𝓢 → Grid n → Field 𝔄 𝓗 𝓢) := by
  have : (recOf : LCfg n 𝔄 𝓗 𝓢 → Grid n → Field 𝔄 𝓗 𝓢) = fun q x =>
      (q.1 x, (0 : Fin 4 → 𝔄), (0 : 𝓗), (0 : 𝓢), (0 : CoSpinor 𝓢)) := rfl
  rw [this]
  fun_prop

theorem coframe_recOf (q : LCfg n 𝔄 𝓗 𝓢) : coframe (recOf q) = q.1 := rfl

/-! ### Smoothness of the link-level action on the admissible chart -/

section Smooth

variable (D : Data 𝔄 𝓗 𝓢) (h : ℝ) {q : LCfg n 𝔄 𝓗 𝓢}

theorem contDiffAt_coframeC (x : Grid n) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.1 x) q := by fun_prop

theorem contDiffAt_linkC (μ : Fin 4) (x : Grid n) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.1 μ x) q := by fun_prop

theorem contDiffAt_invLinkC {μ : Fin 4} {x : Grid n} (hu : IsUnit (q.2.1 μ x)) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => Ring.inverse (q.2.1 μ x)) q := by
  obtain ⟨u, hu⟩ := hu
  have h1 := contDiffAt_ringInverse ℝ (n := ∞) u
  rw [hu] at h1
  exact h1.comp q (contDiffAt_linkC μ x)

theorem contDiffAt_plaqC (hu : ∀ μ x, IsUnit (q.2.1 μ x)) (x : Grid n) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => plaq (toLC q) x μ ν) q := by
  have h1 := contDiffAt_linkC (q := q) μ x
  have h2 := contDiffAt_linkC (q := q) ν (x + unitVec n μ)
  have h3 := contDiffAt_invLinkC (q := q) (hu μ (x + unitVec n ν))
  have h4 := contDiffAt_invLinkC (q := q) (hu ν x)
  simp only [plaq, toLC]
  exact ((h1.mul h2).mul h3).mul h4

theorem contDiffAt_curvC (hu : ∀ μ x, IsUnit (q.2.1 μ x)) (x : Grid n) (μ ν : Fin 4)
    (hP : ‖plaq (toLC q) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => curv h (toLC q) x μ ν) q := by
  unfold curv
  exact (NativeFrechet.ContDiffAt.logOneAdd ((contDiffAt_plaqC hu x μ ν).sub contDiffAt_const)
    hP).const_smul _

theorem contDiffAt_volumeC {x : Grid n} (hdet : (q.1 x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => volume (q.1 x)) q :=
  ContDiffAt.comp (g := volume) q (contDiffAt_volume hdet) (contDiffAt_coframeC x)

theorem contDiffAt_ginvC {x : Grid n} (hdet : (q.1 x).det ≠ 0) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => ginv (q.1 x) μ ν) q :=
  ContDiffAt.comp (g := fun e => ginv e μ ν) q (contDiffAt_ginv μ ν hdet) (contDiffAt_coframeC x)

theorem contDiffAt_invEntryC {x : Grid n} (hdet : (q.1 x).det ≠ 0) (μ a : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => invEntry μ a (q.1 x)) q :=
  ContDiffAt.comp (g := invEntry μ a) q (contDiffAt_invEntry μ a hdet) (contDiffAt_coframeC x)

/-- The Yang–Mills density is smooth on the gauge chart. -/
theorem contDiffAt_ymDC (hu : ∀ μ x, IsUnit (q.2.1 μ x)) (x : Grid n)
    (hdet : (q.1 x).det ≠ 0) (hP : ∀ μ ν, μ < ν → ‖plaq (toLC q) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => ymD D h (toLC q) x) q := by
  have hA : ∀ μ ν, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => antisym (curv h (toLC q) x) μ ν) q :=
    fun μ ν => NativeFrechet.contDiffAt_antisym (P := fun q : LCfg n 𝔄 𝓗 𝓢 => curv h (toLC q) x)
      μ ν fun μ ν hμν => contDiffAt_curvC h hu x μ ν (hP μ ν hμν)
  have hv := contDiffAt_volumeC (q := q) hdet
  have hg := contDiffAt_ginvC (q := q) hdet
  have hip : ∀ μ ν ρ σ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 =>
      D.ipA (antisym (curv h (toLC q) x) μ ν) (antisym (curv h (toLC q) x) ρ σ)) q :=
    fun μ ν ρ σ => ((D.ipA.contDiff.contDiffAt.comp q (hA μ ν)).clm_apply (hA ρ σ))
  unfold ymD
  refine ContDiffAt.neg (ContDiffAt.mul (contDiffAt_const.mul (hv.congr_of_eventuallyEq ?_)) ?_)
  · exact Filter.Eventually.of_forall fun _ => rfl
  · refine ContDiffAt.sum fun μ _ => ContDiffAt.sum fun ν _ => ContDiffAt.sum fun ρ _ =>
      ContDiffAt.sum fun σ _ => ((hg μ ρ).mul (hg ν σ)).mul ?_
    exact hip μ ν ρ σ

/-- The Higgs density is smooth wherever the coframe is nondegenerate. -/
theorem contDiffAt_higgsDC (x : Grid n) (hdet : (q.1 x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => higgsD D h (toLC q) x) q := by
  have hK : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => hLink D h (toLC q) x μ) q := by
    intro μ
    have h1 : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => D.ρHL (q.2.1 μ x)) q :=
      D.ρHL.contDiff.contDiffAt.comp q (contDiffAt_linkC μ x)
    have h2 : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.1 (x + unitVec n μ)) q := by fun_prop
    have h3 : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.1 x) q := by fun_prop
    simp only [hLink, toLC, ← Data.ρHL_apply]
    exact ((h1.clm_apply h2).sub h3).const_smul _
  have hH : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.1 x) q := by fun_prop
  have hv := contDiffAt_volumeC (q := q) hdet
  have hg := contDiffAt_ginvC (q := q) hdet
  have hherm : ∀ μ ν, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 =>
      D.hermH (hLink D h (toLC q) x μ) (hLink D h (toLC q) x ν)) q :=
    fun μ ν => (D.hermH.contDiff.contDiffAt.comp q (hK μ)).clm_apply (hK ν)
  have hpot : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => potential D (q.2.2.1 x)) q := by
    unfold potential
    exact contDiffAt_const.mul (((D.hermH.contDiff.contDiffAt.comp q hH).clm_apply hH).sub
      contDiffAt_const |>.pow 2)
  unfold higgsD
  refine ContDiffAt.sub (ContDiffAt.neg (hv.mul (ContDiffAt.sum fun μ _ =>
    ContDiffAt.sum fun ν _ => (hg μ ν).mul (hherm μ ν)))) (hv.mul hpot)

/-- The coframe-derived connection is smooth where the coframe is nondegenerate. -/
theorem contDiffAt_omegaC {z : Grid n} (hdet : (q.1 z).det ≠ 0) (μ : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => omegaLink h q.1 z μ) q := by
  have h1 := NativeFrechet.contDiffAt_omegaLink (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) h z μ
    (y := recOf q) hdet
  exact h1.comp q contDiff_recOf.contDiffAt

/-- The Dirac–Yukawa density is smooth on the chart. -/
theorem contDiffAt_diracDC (hu : ∀ μ x, IsUnit (q.2.1 μ x)) (x : Grid n)
    (hdet : (q.1 x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => diracD D h (toLC q) x) q := by
  have hρ : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => D.ρS (q.2.1 μ x)) q := fun μ =>
    D.ρSL.contDiff.contDiffAt.comp q (contDiffAt_linkC μ x)
  have hρi : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => D.ρS (Ring.inverse (q.2.1 μ x))) q :=
    fun μ => D.ρSL.contDiff.contDiffAt.comp q (contDiffAt_invLinkC (hu μ x))
  have hσ : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => D.σ (omegaLink h q.1 x μ)) q := fun μ =>
    D.σ.contDiff.contDiffAt.comp q (contDiffAt_omegaC h hdet μ)
  have hV : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => sLink D h (toLC q) x μ) q := fun μ =>
    (NativeFrechet.ContDiffAt.nexp ((hσ μ).const_smul h)).mul (hρ μ)
  have hVi : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => sLinkInv D h (toLC q) x μ) q := fun μ =>
    (hρi μ).mul (NativeFrechet.ContDiffAt.nexp ((hσ μ).const_smul h).neg)
  have hΨ : ∀ z, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.2.1 z) q := fun z => by fun_prop
  have hΨb : ∀ z, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.2.2 z) q := fun z => by fun_prop
  have hH : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.2.1 x) q := by fun_prop
  have hdD : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => dDiff D h (toLC q) x μ) q := fun μ =>
    (((hV μ).clm_apply (hΨ _)).sub (hΨ x)).const_smul _
  have hdDb : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => dDiffBar D h (toLC q) x μ) q :=
    fun μ => (((hΨb _).clm_comp (hVi μ)).sub (hΨb x)).const_smul _
  have hγ : ∀ μ, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => gammaMu D μ (q.1 x)) q := fun μ => by
    unfold gammaMu
    exact ContDiffAt.sum fun a _ => (contDiffAt_invEntryC hdet μ a).smul contDiffAt_const
  have hv := contDiffAt_volumeC (q := q) hdet
  have hin : ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => Complex.I / 2 * ∑ μ,
      (q.2.2.2.2 x (gammaMu D μ (q.1 x) (dDiff D h (toLC q) x μ)) -
        dDiffBar D h (toLC q) x μ (gammaMu D μ (q.1 x) (q.2.2.2.1 x))) -
      q.2.2.2.2 x (D.yukawa (q.2.2.1 x) (q.2.2.2.1 x))) q := by
    refine (contDiffAt_const.mul (ContDiffAt.sum fun μ _ => ?_)).sub ?_
    · exact ((hΨb x).clm_apply ((hγ μ).clm_apply (hdD μ))).sub
        ((hdDb μ).clm_apply ((hγ μ).clm_apply (hΨ x)))
    · exact (hΨb x).clm_apply ((D.yukawa.contDiff.contDiffAt.comp q hH).clm_apply (hΨ x))
  unfold diracD
  exact hv.mul hin.complex_re

/-- The gravitational density is smooth on the Cartan chart. -/
theorem contDiffAt_gravDC (x : Grid n) (hdet : ∀ z, (q.1 z).det ≠ 0)
    (hC : ∀ μ ν, μ < ν → ‖cartanPlaquette h q.1 x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => gravD D h (toLC q) x) q := by
  have h1 := NativeFrechet.contDiffAt_gravityDensity D h (y := recOf q) x hdet hC
  exact h1.comp q contDiff_recOf.contDiffAt

/-- **The native link action is `C^∞` on the admissible chart.** -/
theorem contDiffAt_linkActionC (hdet : ∀ z, (q.1 z).det ≠ 0) (hu : ∀ μ x, IsUnit (q.2.1 μ x))
    (hP : ∀ x μ ν, μ < ν → ‖plaq (toLC q) x μ ν - 1‖ < 1)
    (hC : ∀ x μ ν, μ < ν → ‖cartanPlaquette h q.1 x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => linkAction D h (toLC q)) q := by
  unfold linkAction
  refine contDiffAt_const.mul (ContDiffAt.sum fun x _ => ?_)
  exact (((contDiffAt_gravDC D h x hdet (hC x)).add (contDiffAt_ymDC D h hu x (hdet x) (hP x))).add
    (contDiffAt_higgsDC D h x (hdet x))).add (contDiffAt_diracDC D h hu x (hdet x))

end Smooth


/-! ### The admissible chart -/

section Chart

variable (h : ℝ)

/-- **The admissible chart** of `𝒬_h`: oriented and time-oriented coframes, invertible links,
gauge and Cartan plaquettes in the logarithm chart. -/
def admChart : Set (LCfg n 𝔄 𝓗 𝓢) :=
  {q | (∀ x, 0 < (q.1 x).det) ∧ (∀ x, 0 < q.1 x 0 0) ∧ (∀ μ x, IsUnit (q.2.1 μ x)) ∧
    (∀ x μ ν, μ < ν → ‖plaq (toLC q) x μ ν - 1‖ < 1) ∧
    (∀ x μ ν, μ < ν → ‖cartanPlaquette h q.1 x μ ν - 1‖ < 1)}

theorem contDiffAt_cartanPlaqC {q : LCfg n 𝔄 𝓗 𝓢} (hdet : ∀ z, (q.1 z).det ≠ 0) (x : Grid n)
    (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => cartanPlaquette h q.1 x μ ν) q := by
  have hω : ∀ μ z, ContDiffAt ℝ ∞ (fun q : LCfg n 𝔄 𝓗 𝓢 => matToOp (omegaLink h q.1 z μ)) q :=
    fun μ z => by
      simp only [← matToOpL_apply]
      exact matToOpL.contDiff.contDiffAt.comp q (contDiffAt_omegaC h (hdet z) μ)
  unfold cartanPlaquette NativeScaling.gaugePlaquette
  have h1 := NativeFrechet.ContDiffAt.nexp ((hω μ x).const_smul h)
  have h2 := NativeFrechet.ContDiffAt.nexp ((hω ν (x + unitVec n μ)).const_smul h)
  have h3 := NativeFrechet.ContDiffAt.nexp ((hω μ (x + unitVec n ν)).const_smul h).neg
  have h4 := NativeFrechet.ContDiffAt.nexp ((hω ν x).const_smul h).neg
  exact ((h1.mul h2).mul h3).mul h4

theorem isOpen_admChart : IsOpen (admChart (n := n) (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) h) := by
  rw [isOpen_iff_mem_nhds]
  intro q ⟨h1, h2, h3, h4, h5⟩
  have hdet : ∀ z, (q.1 z).det ≠ 0 := fun z => (h1 z).ne'
  have hc : ∀ x, Continuous fun q : LCfg n 𝔄 𝓗 𝓢 => q.1 x := fun x => by fun_prop
  have e1 : ∀ᶠ q' in 𝓝 q, ∀ x, 0 < (q'.1 x).det := Filter.eventually_all.2 fun x =>
    (continuousAt_const.eventually_lt
      ((NativeDensity.contDiff_det (k := 0)).continuous.comp (hc x)).continuousAt (h1 x))
  have e2 : ∀ᶠ q' in 𝓝 q, ∀ x, 0 < q'.1 x 0 0 := Filter.eventually_all.2 fun x =>
    (continuousAt_const.eventually_lt
      ((continuous_apply_apply 0 0).comp (hc x)).continuousAt (h2 x))
  have e3 : ∀ᶠ q' in 𝓝 q, ∀ μ x, IsUnit (q'.2.1 μ x) := Filter.eventually_all.2 fun μ =>
    Filter.eventually_all.2 fun x =>
      ((by fun_prop : Continuous fun q : LCfg n 𝔄 𝓗 𝓢 => q.2.1 μ x).continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds (h3 μ x)))
  have e4 : ∀ᶠ q' in 𝓝 q, ∀ x μ ν, μ < ν → ‖plaq (toLC q') x μ ν - 1‖ < 1 :=
    Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun μ => Filter.eventually_all.2
      fun ν => by
        by_cases hμν : μ < ν
        · have hcont : ContinuousAt (fun q' : LCfg n 𝔄 𝓗 𝓢 => ‖plaq (toLC q') x μ ν - 1‖) q :=
            ((contDiffAt_plaqC h3 x μ ν).continuousAt.sub continuousAt_const).norm
          filter_upwards [hcont.eventually_lt continuousAt_const (h4 x μ ν hμν)] with q' hq' _
          exact hq'
        · exact Filter.Eventually.of_forall fun _ h' => absurd h' hμν
  have e5 : ∀ᶠ q' in 𝓝 q, ∀ x μ ν, μ < ν → ‖cartanPlaquette h q'.1 x μ ν - 1‖ < 1 :=
    Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun μ => Filter.eventually_all.2
      fun ν => by
        by_cases hμν : μ < ν
        · have hcont : ContinuousAt
              (fun q' : LCfg n 𝔄 𝓗 𝓢 => ‖cartanPlaquette h q'.1 x μ ν - 1‖) q :=
            ((contDiffAt_cartanPlaqC h hdet x μ ν).continuousAt.sub continuousAt_const).norm
          filter_upwards [hcont.eventually_lt continuousAt_const (h5 x μ ν hμν)] with q' hq' _
          exact hq'
        · exact Filter.Eventually.of_forall fun _ h' => absurd h' hμν
  filter_upwards [e1, e2, e3, e4, e5] with q' a1 a2 a3 a4 a5
  exact ⟨a1, a2, a3, a4, a5⟩

/-- The flat configuration: coframe `1`, links `1`, no matter. -/
def flatCfg : LCfg n 𝔄 𝓗 𝓢 := (fun _ => 1, fun _ _ => 1, 0, 0, 0)

theorem readerOmega_zero (e : Mat) (μ : Fin 4) : NativeScaling.readerOmega e 0 μ = 0 := by
  have := NativeScaling.readerOmega_smul e 0 0 μ
  rwa [zero_smul, zero_smul] at this

theorem omegaLink_const_one (x : Grid n) (μ : Fin 4) :
    omegaLink h (fun _ : Grid n => (1 : Mat)) x μ = 0 := by
  have hd : (fun lam => ShiftedJetAction.fwdDiff h lam (fun _ : Grid n => (1 : Mat)) x) = 0 := by
    funext lam; simp [ShiftedJetAction.fwdDiff]
  unfold omegaLink
  rw [hd, readerOmega_zero]

theorem flatCfg_mem : (flatCfg : LCfg n 𝔄 𝓗 𝓢) ∈ admChart h := by
  refine ⟨fun x => by simp [flatCfg], fun x => by simp [flatCfg], fun μ x => isUnit_one,
    fun x μ ν _ => ?_, fun x μ ν _ => ?_⟩
  · simp [plaq, toLC, flatCfg]
  · simp [cartanPlaquette, NativeScaling.gaugePlaquette, flatCfg, omegaLink_const_one]

end Chart

/-! ### The Standard-Model instance -/

open NativeSMPacket FiniteInterfaceGeneral FiniteInterfaceTable SMDescentYukawa

set_option synthInstance.maxHeartbeats 400000 in
instance instCompleteSpaceAlg : CompleteSpace Alg := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instNormOneClassAlg : NormOneClass Alg := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instNormedAlgebraAlg : NormedAlgebra ℝ Alg := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instFiniteDimensionalAlg : FiniteDimensional ℝ Alg := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instFiniteDimensionalCoSpinor : FiniteDimensional ℝ (CoSpinor SF) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instFiniteDimensionalSF : FiniteDimensional ℝ SF := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instFiniteDimensionalEH : FiniteDimensional ℝ EH := inferInstance

/-- Matrices as operators on Euclidean space. -/
local notation "toE" => Matrix.toEuclideanCLM (𝕜 := ℂ)

/-- The configuration space of the Standard-Model realization. -/
abbrev Cfg (n : ℕ) : Type := LCfg n Alg EH SF

set_option synthInstance.maxHeartbeats 400000 in
instance instNormedAddCommGroupCfg : NormedAddCommGroup (Cfg n) :=
  inferInstanceAs (NormedAddCommGroup (LCfg n Alg EH SF))

set_option synthInstance.maxHeartbeats 400000 in
instance instNormedSpaceCfg : NormedSpace ℝ (Cfg n) := inferInstanceAs (NormedSpace ℝ (LCfg n Alg EH SF))

set_option synthInstance.maxHeartbeats 400000 in
instance instFiniteDimensionalCfg : FiniteDimensional ℝ (Cfg n) :=
  inferInstanceAs (FiniteDimensional ℝ (LCfg n Alg EH SF))

variable (θ : CoefficientBank (Fin 3)) (h : ℝ)

/-- **The site-gauge action** of `γ : Grid → S(U(3)×U(2))` on `𝒬_h`, through `ι`. -/
def gaugeC (γ : Grid n → SMGaugeGroup) (q : Cfg n) : Cfg n :=
  ofLC (NativeGauge.gaugeAct (smCovData θ) (fun x => iota (γ x)) (toLC q))

theorem toLC_gaugeC (γ : Grid n → SMGaugeGroup) (q : Cfg n) :
    toLC (gaugeC θ γ q) = NativeGauge.gaugeAct (smCovData θ) (fun x => iota (γ x)) (toLC q) := rfl

theorem iota_mem (γ : Grid n → SMGaugeGroup) : ∀ x, iota (γ x) ∈ (smCovData θ).G :=
  fun x => ⟨γ x, rfl⟩

theorem gaugeC_mem {γ : Grid n → SMGaugeGroup} {q : Cfg n} (hq : q ∈ admChart h) :
    gaugeC θ γ q ∈ admChart h := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  refine ⟨h1, h2, fun μ x => ?_, fun x μ ν hμν => ?_, h5⟩
  · show IsUnit ((iota (γ x) : Alg) * q.2.1 μ x * ((iota (γ (x + unitVec n μ)))⁻¹ : Algˣ))
    exact ((Units.isUnit _).mul (h3 μ x)).mul (Units.isUnit _)
  · rw [toLC_gaugeC, NativeGauge.plaq_gauge]
    have e : (iota (γ x) : Alg) * plaq (toLC q) x μ ν * ((iota (γ x))⁻¹ : Algˣ) - 1 =
        (iota (γ x) : Alg) * (plaq (toLC q) x μ ν - 1) * ((iota (γ x))⁻¹ : Algˣ) := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e, (smCovData θ).norm_conj _ (iota_mem θ γ x)]
    exact h4 x μ ν hμν

/-- The gravitational sector `S_{g,h} = h⁴ Σ 𝓛_{g,h}`. -/
def gravC (q : Cfg n) : ℝ := NativeGauge.gravSector (smData θ) h (toLC q)

/-- The Standard-Model sector `S_{SM,h} = h⁴ Σ (𝓛_{YM,h} + 𝓛_{H,h} + 𝓛_{D,h})`. -/
def matterC (q : Cfg n) : ℝ :=
  NativeGauge.ymSector (smData θ) h (toLC q) + NativeGauge.higgsSector (smData θ) h (toLC q) +
    NativeGauge.diracSector (smData θ) h (toLC q)

theorem gravC_add_matterC (q : Cfg n) :
    gravC θ h q + 1 * matterC θ h q = linkAction (smData θ) h (toLC q) := by
  rw [NativeGauge.linkAction_eq_sectors, gravC, matterC]; ring

/-- The spin–gauge link `V_μ = e^{hσ(ω_{μ,h})} ρ_S(U_μ)` as a matrix on the fermion fibre. -/
def spinLinkC (q : Cfg n) (x : Grid n) (μ : Fin 4) : Matrix FibI FibI ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := FibI)).symm
    (exp (toE (spinOp .minimal (sigmaL (h • omegaLink h q.1 x μ)))) *
      toE (liftRow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm (q.2.1 μ x).2)))

theorem RF_spinLinkC (q : Cfg n) (x : Grid n) (μ : Fin 4) :
    RF (spinLinkC h q x μ) = sLink (smData θ) h (toLC q) x μ := by
  have hR : ∀ M, RF M = restrictR SF (toE M) := fun M => rfl
  rw [hR, spinLinkC, StarAlgEquiv.apply_symm_apply, map_mul,
    algHom_map_exp (restrictR SF) (LinearMap.continuous_of_finiteDimensional
      (restrictR SF).toLinearMap)]
  show exp (sigmaA (h • omegaLink h q.1 x μ)) * _ = _
  rw [map_smul]
  rfl

/-- **The incidence transport is the action's spin–gauge link**:
`V_μ v = NativeGauge.sLink(…) v` on the fermion fibre. -/
theorem spinLinkC_mulVec (q : Cfg n) (x : Grid n) (μ : Fin 4) (v : FibI → ℂ) :
    WithLp.toLp 2 (spinLinkC h q x μ *ᵥ v) =
      sLink (smData θ) h (toLC q) x μ (WithLp.toLp 2 v) := by
  rw [← RF_spinLinkC, RF_apply, Matrix.toEuclideanCLM_toLp]

theorem commute_exp_sigma (y : SMGaugeGroup) (om : Mat) :
    Commute (toE (fibreRep SpinI .minimal y)) (exp (toE (spinOp .minimal (sigmaL om)))) := by
  have hc : Commute (toE (fibreRep SpinI .minimal y)) (toE (spinOp .minimal (sigmaL om))) := by
    rw [fibreRep_apply]
    exact (show Commute (internalOp SpinI (internalRep .minimal y)) (spinOp .minimal (sigmaL om))
      from (spinOp_mul_internalOp _ _).symm).map _
  exact hc.exp_right

/-- Covariance of the spin–gauge links. -/
theorem spinLinkC_covariant (γ : Grid n → SMGaugeGroup) (q : Cfg n) (x : Grid n) (μ : Fin 4) :
    spinLinkC h (gaugeC θ γ q) x μ = fibreRep SpinI .minimal (γ x) * spinLinkC h q x μ *
      fibreRep SpinI .minimal (γ (x + unitVec n μ))⁻¹ := by
  have hU : ((gaugeC θ γ q).2.1 μ x).2 = toE (RenewalRealization.tableRepM (γ x)) * (q.2.1 μ x).2 *
      toE (RenewalRealization.tableRepM (γ (x + unitVec n μ))⁻¹) := by
    show ((iota (γ x) : Alg) * q.2.1 μ x * ((iota (γ (x + unitVec n μ)))⁻¹ : Algˣ)).2 = _
    rw [coe_iota, coe_iota_inv, Prod.snd_mul, Prod.snd_mul, iotaA_apply, iotaA_apply]
  have he : (gaugeC θ γ q).1 = q.1 := rfl
  set E := exp (toE (spinOp .minimal (sigmaL (h • omegaLink h q.1 x μ))))
  set L := toE (liftRow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm (q.2.1 μ x).2))
  have hL : toE (liftRow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm
      ((gaugeC θ γ q).2.1 μ x).2)) = toE (fibreRep SpinI .minimal (γ x)) * L *
        toE (fibreRep SpinI .minimal (γ (x + unitVec n μ))⁻¹) := by
    rw [hU]
    simp only [L, map_mul, StarAlgEquiv.symm_apply_apply, liftRow_tableRepM]
  have key : E * (toE (fibreRep SpinI .minimal (γ x)) * L *
      toE (fibreRep SpinI .minimal (γ (x + unitVec n μ))⁻¹)) =
      toE (fibreRep SpinI .minimal (γ x)) * (E * L) *
        toE (fibreRep SpinI .minimal (γ (x + unitVec n μ))⁻¹) := by
    rw [← mul_assoc, ← mul_assoc, ← (commute_exp_sigma (γ x) (h • omegaLink h q.1 x μ)).eq,
      mul_assoc (toE (fibreRep SpinI .minimal (γ x))) E L]
  show (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := FibI)).symm
      (exp (toE (spinOp .minimal (sigmaL (h • omegaLink h (gaugeC θ γ q).1 x μ)))) *
        toE (liftRow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm
          ((gaugeC θ γ q).2.1 μ x).2))) = _
  rw [he, hL, key, map_mul, map_mul, StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]
  rfl

/-- The Yukawa map of `lem:SM-descent` on generation × table rows, real-linear in `H`. -/
def yLin : (Fin 2 → ℂ) →ₗ[ℝ] Matrix (InternalIdx .minimal) (InternalIdx .minimal) ℂ where
  toFun H := internalCast (RenewalRealization.yM θ H)
  map_add' H H' := by rw [yM_add, map_add]
  map_smul' r H := by rw [yM_smul]; rfl

theorem yLin_covariant (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    yLin θ (higgsRep y H) = internalRep .minimal y * yLin θ H * internalRep .minimal y⁻¹ := by
  have hH : higgsRep y H = smU2 y *ᵥ H := rfl
  simp only [yLin, LinearMap.coe_mk, AddHom.coe_mk, hH, yM_covariant, map_mul]
  rfl

theorem RF_yukawa (H : EH) :
    RF (internalOp SpinI (yLin θ (WithLp.ofLp H))) = (smData θ).yukawa H := rfl

set_option synthInstance.maxHeartbeats 400000 in
instance instT2SpaceCfg : T2Space (Cfg n) := inferInstance

/-- Euclidean coordinates of `𝒬_h` (`toEuclidean`). -/
def eucl (n : ℕ) [NeZero n] : Cfg n →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (Cfg n))) :=
  (toEuclidean : Cfg n ≃L[ℝ] _).toLinearEquiv.toLinearMap

/-- The cell-volume coordinate Gram form `h⁴ ⟨c(u), c(v)⟩` of `𝒬_h`. -/
def gramC (n : ℕ) [NeZero n] : LinearMap.BilinForm ℝ (Cfg n) :=
  (h ^ 4) • (innerₗ (EuclideanSpace ℝ (Fin (Module.finrank ℝ (Cfg n))))).compl₁₂ (eucl n) (eucl n)

theorem gramC_apply (n : ℕ) [NeZero n] (u v : Cfg n) :
    gramC h n u v = h ^ 4 * inner ℝ (eucl n u) (eucl n v) := rfl

theorem gramC_symm (n : ℕ) [NeZero n] (u v : Cfg n) : gramC h n u v = gramC h n v u := by
  rw [gramC_apply, gramC_apply, real_inner_comm]

theorem gramC_nonneg (n : ℕ) [NeZero n] (v : Cfg n) : 0 ≤ gramC h n v v := by
  rw [gramC_apply]
  exact mul_nonneg (by positivity) real_inner_self_nonneg

theorem gramC_pos (n : ℕ) [NeZero n] (hh : 0 < h) {v : Cfg n} (hv : v ≠ 0) :
    0 < gramC h n v v := by
  rw [gramC_apply, real_inner_self_eq_norm_sq]
  have : eucl n v ≠ 0 := by
    intro h0
    exact hv ((toEuclidean : Cfg n ≃L[ℝ] _).map_eq_zero_iff.mp h0)
  exact mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr this) 2)

/-- The incidence operator of the realization. -/
def diracC (q : Cfg n) : FermionField (Grid n) SpinI .minimal →ₗ[ℂ] FermionField (Grid n) SpinI .minimal :=
  incidenceOp h (fun μ => Equiv.addRight (unitVec n μ)) gam (fun x => q.1 x)
    (spinLinkC h q) (fun x => yLin θ (WithLp.ofLp (q.2.2.1 x)))

theorem higgs_covariantC (γ : Grid n → SMGaugeGroup) (q : Cfg n) (x : Grid n) :
    WithLp.ofLp ((gaugeC θ γ q).2.2.1 x) = higgsRep (γ x) (WithLp.ofLp (q.2.2.1 x)) := by
  show WithLp.ofLp (rhoHA (iota (γ x)) (q.2.2.1 x)) = _
  rw [coe_iota, rhoHA_iota, Matrix.ofLp_toEuclideanCLM]
  rfl

theorem dirac_covariantC (γ : Grid n → SMGaugeGroup) (q : Cfg n)
    (ψ : FermionField (Grid n) SpinI .minimal) (x : Grid n) :
    diracC θ h (gaugeC θ γ q) (fun y => fibreRep SpinI .minimal (γ y) *ᵥ ψ y) x =
      fibreRep SpinI .minimal (γ x) *ᵥ diracC θ h q ψ x :=
  incidenceOp_covariant h (fun μ => Equiv.addRight (unitVec n μ)) gam (fun x => q.1 x)
    (spinLinkC h q) (spinLinkC h (gaugeC θ γ q)) (fun x => yLin θ (WithLp.ofLp (q.2.2.1 x)))
    (fun x => yLin θ (WithLp.ofLp ((gaugeC θ γ q).2.2.1 x))) γ
    (fun x μ => spinLinkC_covariant θ h γ q x μ)
    (fun x => by rw [higgs_covariantC]; exact yLin_covariant θ (γ x) _) ψ x

omit [NeZero n] in
theorem gaugeAct_one' (C : NativeGauge.CovData 𝔄 𝓗 𝓢) (c : LinkConfig n 𝔄 𝓗 𝓢) :
    NativeGauge.gaugeAct C (fun _ => 1) c = c := by
  cases c
  simp only [NativeGauge.gaugeAct, LinkConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext μ x; simp
  · funext x; simp
  · funext x; simp
  · funext x; ext v; simp

omit [NeZero n] in
theorem gaugeAct_mul' (C : NativeGauge.CovData 𝔄 𝓗 𝓢) (g g' : Grid n → 𝔄ˣ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    NativeGauge.gaugeAct C (fun x => g x * g' x) c =
      NativeGauge.gaugeAct C g (NativeGauge.gaugeAct C g' c) := by
  cases c
  simp only [NativeGauge.gaugeAct, LinkConfig.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext μ x
    simp only [Units.val_mul, _root_.mul_inv_rev, mul_assoc]
  · funext x
    rw [Units.val_mul, map_mul, ContinuousLinearMap.mul_apply]
  · funext x
    rw [Units.val_mul, map_mul, ContinuousLinearMap.mul_apply]
  · funext x
    ext v
    simp only [_root_.mul_inv_rev, Units.val_mul, map_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply]

theorem gaugeC_one (q : Cfg n) : gaugeC θ (1 : Grid n → SMGaugeGroup) q = q := by
  have : (fun x => iota ((1 : Grid n → SMGaugeGroup) x)) = fun _ => 1 := by
    funext x; exact map_one iota
  rw [gaugeC, this, gaugeAct_one']
  rfl

theorem gaugeC_mul (γ γ' : Grid n → SMGaugeGroup) (q : Cfg n) :
    gaugeC θ (γ * γ') q = gaugeC θ γ (gaugeC θ γ' q) := by
  have : (fun x => iota ((γ * γ') x)) = fun x => iota (γ x) * iota (γ' x) := by
    funext x; exact map_mul iota _ _
  rw [gaugeC, this, gaugeAct_mul']
  rfl

theorem differentiableOn_actionC :
    DifferentiableOn ℝ (fun q => gravC θ h q + 1 * matterC θ h q) (admChart (n := n) h) := by
  intro q hq
  have e : (fun q => gravC θ h q + 1 * matterC θ h q) =
      fun q : Cfg n => linkAction (smData θ) h (toLC q) := funext (gravC_add_matterC θ h)
  rw [e]
  obtain ⟨h1, -, h3, h4, h5⟩ := hq
  exact ((contDiffAt_linkActionC (smData θ) h (fun z => (h1 z).ne') h3 h4 h5).differentiableAt
    (by simp)).differentiableWithinAt

theorem action_gaugeC (γ : Grid n → SMGaugeGroup) {q : Cfg n} (hq : q ∈ admChart h) :
    gravC θ h (gaugeC θ γ q) + 1 * matterC θ h (gaugeC θ γ q) = gravC θ h q + 1 * matterC θ h q := by
  rw [gravC_add_matterC, gravC_add_matterC, toLC_gaugeC]
  exact NativeGauge.linkAction_gauge (smCovData θ) (iota_mem θ γ) h hq.2.2.2.1

set_option maxHeartbeats 1000000 in
/-- **The renewal realization of `def:finite-interface` by the native local action** at cutoff
`h > 0` on `(ℤ/n)⁴`, coefficient bank `θ`, minimal Standard-Model branch, with the spinor fibre. -/
def renewalSpinorInterface (n : ℕ) [NeZero n] (θ : CoefficientBank (Fin 3)) (h : ℝ) (hh : 0 < h) :
    SpinorFiniteInterface h where
  Site := Grid n
  Config := Cfg n
  chart := admChart h
  chart_isOpen := isOpen_admChart h
  chart_nonempty := ⟨flatCfg, flatCfg_mem h⟩
  coframe q x := q.1 x
  coframe_oriented q hq x := hq.1 x
  coframe_timeOriented q hq x := hq.2.1 x
  branch := .minimal
  higgs q x := WithLp.ofLp (q.2.2.1 x)
  SpinIdx := SpinI
  YukawaSector := Fin 3
  coefficients := θ
  dirac := diracC θ h
  gaugeAct := gaugeC θ
  higgs_covariant := higgs_covariantC θ
  dirac_covariant := dirac_covariantC θ h
  gravityAction := gravC θ h
  matterAction := matterC θ h
  relativeNormalization := 1
  relativeNormalization_pos := one_pos
  chart_gaugeAct γ q hq := gaugeC_mem θ h hq
  action_differentiableOn := differentiableOn_actionC θ h
  action_gauge_invariant γ q hq := action_gaugeC θ h γ hq
  retained := ⊤
  gram := gramC h n
  gram_symm u v := gramC_symm h n u v
  gram_nonneg v := gramC_nonneg h n v
  gram_pos_retained v _ hv := gramC_pos h n hh hv
  next μ := Equiv.addRight (unitVec n μ)
  spin_nonempty := ⟨Sum.inl 0⟩
  gamma := gam
  gamma_clifford := gam_clifford
  gamma5 := gam5
  gamma5_sq := gam5_sq
  gamma5_anticomm := gam5_anticomm
  gaugeAct_one := gaugeC_one θ
  gaugeAct_mul := gaugeC_mul θ
  coframe_gaugeAct γ q x := rfl
  spinLink := spinLinkC h
  spinLink_covariant γ q x μ := spinLinkC_covariant θ h γ q x μ
  yukawaMap := (yLin θ).toAffineMap
  yukawaMap_covariant y H := yLin_covariant θ y H
  dirac_eq q := rfl


/-! ### The realization statement -/

/-- Native records in their chart (`contDiffAt_localAction`) give configurations in the admissible
chart: their links `U = e^{hA}` are invertible and their gauge plaquettes are the native ones. -/
theorem toLinks_mem_admChart {y : Grid n → Field Alg EH SF} (hdet : ∀ x, 0 < (coframe y x).det)
    (ht : ∀ x, 0 < coframe y x 0 0)
    (hG : ∀ x μ ν, μ < ν → ‖NativeScaling.gaugePlaquette h (gauge y) x μ ν - 1‖ < 1)
    (hC : ∀ x μ ν, μ < ν → ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    ofLC (NativeGauge.toLinks h y) ∈ admChart h :=
  ⟨hdet, ht, fun μ x => NativeGauge.isUnit_toLinks h y μ x, fun x μ ν hμν => by
    rw [toLC_ofLC, ← NativeGauge.gaugePlaquette_eq_plaq]; exact hG x μ ν hμν, hC⟩

/-- The frame gammas of the incidence operator are those of the native Dirac density. -/
theorem RF_gammaMu (e : Mat) (μ : Fin 4) :
    RF (spinOp .minimal (FiniteInterfaceGeneral.gammaMu gam e μ)) =
      NativeDensity.gammaMu (smData θ) μ e := by
  simp only [FiniteInterfaceGeneral.gammaMu, NativeDensity.gammaMu, Complex.coe_smul]
  rw [show spinOp .minimal (∑ a, (e⁻¹ μ a) • gam a) = spinOpL (∑ a, (e⁻¹ μ a) • gam a) from rfl,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_smul]
  rfl

/-- The kinetic part of the incidence operator is the covariant Dirac difference `∇^h_μ` of the
native action (`NativeGauge.dDiff`). -/
theorem incidence_kinetic_eq_dDiff (q : Cfg n) (ψ : FermionField (Grid n) SpinI .minimal)
    (hψ : ∀ z, q.2.2.2.1 z = WithLp.toLp 2 (ψ z)) (x : Grid n) (μ : Fin 4) :
    WithLp.toLp 2 ((h⁻¹ : ℝ) • (spinLinkC h q x μ *ᵥ ψ (x + unitVec n μ) - ψ x)) =
      dDiff (smData θ) h (toLC q) x μ := by
  rw [WithLp.toLp_smul, WithLp.toLp_sub, spinLinkC_mulVec θ]
  simp only [dDiff, toLC, hψ]

/-- **`prop:renewal-interface`** (realization by the paper's native local action).  For every
lattice size `n ≥ 1`, coefficient bank `θ` and cutoff `h > 0`, `renewalSpinorInterface n θ h hh`
is a finite Einstein–Standard-Model interface in the chart encoding with spinor incidence
(`SpinorFiniteInterface`, `def:finite-interface`) on the minimal branch, whose data are the
paper's objects:

* the spinor fibre is the Dirac fibre `ℂ⁴` (Weyl basis), tensored with generations and the
  `15` table rows;
* (I4) the common action is the native local action: on every native record `y` it equals
  `NativeDensity.localAction` of the Standard-Model packet; in link variables it is
  `NativeGauge.linkAction`; it is `C^∞` on the admissible chart and gauge invariant there;
* (I3) the incidence operator is `Σ_μ i γ^μ(e) ∇^h_μ - 𝓜_𝐘(H)` with the action's spin–gauge links
  `V_μ = e^{hσ(ω)} ρ_S(U_μ)` and the Yukawa blocks `yukawaMin` of `lem:SM-descent` for `θ`;
* (I1) the flat configuration lies in the admissible chart; (I5) the Gram form is positive definite
  on all directions. -/
theorem renewal_interface_general (n : ℕ) [NeZero n] (θ : CoefficientBank (Fin 3)) (h : ℝ)
    (hh : 0 < h) :
    let I := renewalSpinorInterface n θ h hh
    I.branch = .minimal ∧ I.coefficients = θ ∧ I.relativeNormalization = 1 ∧
    Fintype.card I.SpinIdx = 4 ∧
    (∀ y : Grid n → Field Alg EH SF,
      I.action (ofLC (NativeGauge.toLinks h y)) = localAction (smData θ) h y) ∧
    (∀ q : Cfg n, I.action q = linkAction (smData θ) h (toLC q)) ∧
    (∀ q ∈ admChart (n := n) h, ContDiffAt ℝ ∞ (fun q : Cfg n => linkAction (smData θ) h (toLC q)) q) ∧
    (∀ (γ : Grid n → SMGaugeGroup) (q : Cfg n), q ∈ admChart h →
      linkAction (smData θ) h (toLC (gaugeC θ γ q)) = linkAction (smData θ) h (toLC q)) ∧
    (∀ (q : Cfg n) x μ (v : FibI → ℂ), WithLp.toLp 2 (spinLinkC h q x μ *ᵥ v) =
      sLink (smData θ) h (toLC q) x μ (WithLp.toLp 2 v)) ∧
    (∀ q : Cfg n, diracC θ h q = incidenceOp h (fun μ => Equiv.addRight (unitVec n μ)) gam
      (fun x => q.1 x) (spinLinkC h q) (fun x => yLin θ (WithLp.ofLp (q.2.2.1 x)))) ∧
    (∀ H : Fin 2 → ℂ, yLin θ H = internalCast (RenewalRealization.yM θ H)) ∧
    (flatCfg : Cfg n) ∈ admChart h ∧
    (∀ v : Cfg n, v ≠ 0 → 0 < gramC h n v v) := by
  intro I
  refine ⟨rfl, rfl, rfl, rfl, fun y => ?_, fun q => gravC_add_matterC θ h q, fun q hq => ?_,
    fun γ q hq => ?_, fun q x μ v => spinLinkC_mulVec θ h q x μ v, fun q => rfl, fun H => rfl,
    flatCfg_mem h, fun v hv => gramC_pos h n hh hv⟩
  · show gravC θ h _ + 1 * matterC θ h _ = _
    rw [gravC_add_matterC, toLC_ofLC, NativeGauge.localAction_eq_linkAction]
  · obtain ⟨h1, -, h3, h4, h5⟩ := hq
    exact contDiffAt_linkActionC (smData θ) h (fun z => (h1 z).ne') h3 h4 h5
  · rw [← gravC_add_matterC, ← gravC_add_matterC]
    exact action_gaugeC θ h γ hq

/-- The family of interfaces realized by the native local action is nonempty at every positive
cutoff. -/
theorem renewal_interface_general_nonempty (h : ℝ) (hh : 0 < h) :
    Nonempty (SpinorFiniteInterface h) :=
  ⟨renewalSpinorInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 0⟩ h hh⟩

/-- Non-vacuity of the chart: the flat configuration is admissible and the action is gauge
invariant there for every site gauge. -/
example (γ : Grid 1 → SMGaugeGroup) :
    let I := renewalSpinorInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 1⟩ 1 one_pos
    I.action (I.gaugeAct γ flatCfg) = I.action flatCfg :=
  (renewalSpinorInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 1⟩ 1 one_pos).action_gaugeAct γ
    (flatCfg_mem 1)

end RenewalNativeInterface
end RenewalGeometry
