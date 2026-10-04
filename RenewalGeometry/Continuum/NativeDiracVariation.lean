/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeDensitiesExact
import RenewalGeometry.Algebra.MatrixExpDerivative

/-!
# The finite Dirac–Yukawa sector of the native local action and its exact first variation
  (`prop:native-spinor-variation`, algebraic part; Einstein–SM action-closure manuscript)

The finite Dirac–Yukawa density of `eq:native-densities` is `NativeDensity.diracDensity`: spinor
and co-spinor fields on the nodes, the spin link `V_μ = e^{hσ(ω_{μ,h})} ρ_S(U_μ)` with the
coframe-derived connection `ω_{μ,h} = Ω_μ(e, δ⁺_h e)` of `eq:native-LC-reader` and the internal link
`U_μ = e^{hA_μ}`, the transported differences `eq:native-spin-differences` and the Yukawa map
`𝓜_𝐘(H)`.  (The fermionic data — `σ`, `γ^a`, `ρ_S`, `𝓜_𝐘` — are fields of
`NativeDensity.Data`, so no further encoding is needed.)  This file proves the exact algebra of its
first variation.

* `bForm c Φ w = Re(c Φ(w))` (real bilinear forms of a co-spinor and a spinor).
* `wL`, `wR`: the link quotients `W_μ = (V_μ - 1)/h`, `W'_μ = (V_μ⁻¹ - 1)/h`, with the exact splits
  `∇^h_μΨ = δ⁺_μΨ + W_μ T_μΨ` and `∇^{h,∨}_μΨ̄ = δ⁺_μΨ̄ + (T_μΨ̄) W'_μ` (`diracDiff_split`,
  `diracDiffBar_split`; the split `∇^h_μΨ_h = D⁺_{μ,h}Ψ_h + B_{μ,h}T_{μ,1}Ψ_h` of the paper's proof).
* `Coef`, `formDens`, `form`: the generalized finite Dirac form
  `Σ_μ [Re(i/2 Φ̄ Γ_μ δ⁺_μΦ) + Re(i/2 Φ̄ Ξ_μ T_μΦ) - Re(i/2 (δ⁺_μΦ̄) Γ'_μ Φ) - Re(i/2 (T_μΦ̄) Ξ'_μ Φ)]
  - Re(Φ̄ M Φ)` with operator coefficients, trilinear in (coefficients, co-spinor, spinor);
  `diracDensity_eq_formDens`: the Dirac density is the form with the **original coefficients**
  `Γ = Γ' = v γ^μ`, `Ξ = v γ^μ W_μ`, `Ξ' = v W'_μ γ^μ`, `M = v 𝓜_𝐘(H)` (`origCoef`).
* `hasDerivAt_dAct` (**the exact first variation**): along any record direction `δy`, on the
  nondegenerate chart, `d/dt S_{D,h}(y + t δy)|₀ = form(δc, Ψ̄, Ψ) + form(c, δΨ̄, Ψ) + form(c, Ψ̄, δΨ)`,
  where `δc = varCoef` is the explicit derivative of the original coefficients: the variations of
  `v(e)`, of `γ^μ(e)`, and of the link quotients through the **metric variation of the
  coframe-derived spin connection** `δω = DΩ(e, δ⁺e)[δe, δ⁺δe]` and the gauge variation, with the
  non-commutative exponential derivative `D exp`, and of the Yukawa term.
-/

open NormedSpace Finset Filter Topology
open scoped ContDiff

namespace RenewalGeometry
namespace NativeDirac

open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeDensity

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-! ### Real parts of co-spinor pairings -/

/-- `z ↦ Re(c z)` as a real-linear functional. -/
def reMul (c : ℂ) : ℂ →L[ℝ] ℝ := c.re • Complex.reCLM - c.im • Complex.imCLM

theorem reMul_apply (c z : ℂ) : reMul c z = (c * z).re := by
  simp [reMul, Complex.mul_re]

/-- The real bilinear form `(Φ̄, w) ↦ Re(c Φ̄(w))`. -/
def bForm (c : ℂ) : CoSpinor 𝓢 →L[ℝ] 𝓢 →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ 𝓢 ℂ ℝ (reMul c)

theorem bForm_apply (c : ℂ) (Φ : CoSpinor 𝓢) (w : 𝓢) : bForm c Φ w = (c * Φ w).re := by
  simp [bForm, reMul_apply]

/-! ### The link quotients and the exact splits -/

section Links

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) {n : ℕ} [NeZero n]

/-- The link quotient `W_μ = (V_μ - 1)/h`. -/
def wL (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  h⁻¹ • (spinLink D h y x μ - 1)

/-- The inverse link quotient `W'_μ = (V_μ⁻¹ - 1)/h`. -/
def wR (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  h⁻¹ • (spinLinkInv D h y x μ - 1)

/-- `∇^h_μ Ψ = δ⁺_μ Ψ + W_μ T_μ Ψ`. -/
theorem diracDiff_split (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    diracDiff D h y x μ = fwdDiff h μ (psi y) x + wL D h y x μ (psi y (x + unitVec n μ)) := by
  show h⁻¹ • (spinLink D h y x μ (psi y (x + unitVec n μ)) - psi y x) = _
  simp only [ShiftedJetAction.fwdDiff, wL, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [← smul_add]
  congr 1
  abel

/-- `∇^{h,∨}_μ Ψ̄ = δ⁺_μ Ψ̄ + (T_μ Ψ̄) W'_μ`. -/
theorem diracDiffBar_split (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    diracDiffBar D h y x μ =
      fwdDiff h μ (psiBar y) x + (psiBar y (x + unitVec n μ)).comp (wR D h y x μ) := by
  ext w
  simp only [diracDiffBar, ShiftedJetAction.fwdDiff, wR, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, map_smul, map_sub]
  rw [← smul_add]
  congr 1
  abel

end Links

/-! ### The generalized finite Dirac form -/

/-- Operator coefficients of the generalized finite Dirac form at the nodes. -/
structure Coef (n : ℕ) (𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] where
  /-- kinetic coefficient on `Φ̄ ⊗ δ⁺Φ` -/
  Γ : Grid n → Fin 4 → Spin 𝓢
  /-- kinetic coefficient on `δ⁺Φ̄ ⊗ Φ` -/
  Γ' : Grid n → Fin 4 → Spin 𝓢
  /-- link coefficient on `Φ̄ ⊗ T_μΦ` -/
  Ξ : Grid n → Fin 4 → Spin 𝓢
  /-- link coefficient on `T_μΦ̄ ⊗ Φ` -/
  Ξ' : Grid n → Fin 4 → Spin 𝓢
  /-- mass (Yukawa) coefficient on `Φ̄ ⊗ Φ` -/
  M : Grid n → Spin 𝓢

section Form

variable {n : ℕ} [NeZero n]

/-- The generalized finite Dirac density at a node. -/
def formDens (h : ℝ) (c : Coef n 𝓢) (Φb : Grid n → CoSpinor 𝓢) (Φ : Grid n → 𝓢) (x : Grid n) :
    ℝ :=
  (∑ μ, (bForm (Complex.I / 2) (Φb x) (c.Γ x μ (fwdDiff h μ Φ x)) +
      bForm (Complex.I / 2) (Φb x) (c.Ξ x μ (Φ (x + unitVec n μ))) -
      bForm (Complex.I / 2) (fwdDiff h μ Φb x) (c.Γ' x μ (Φ x)) -
      bForm (Complex.I / 2) (Φb (x + unitVec n μ)) (c.Ξ' x μ (Φ x)))) -
    bForm 1 (Φb x) (c.M x (Φ x))

/-- The generalized finite Dirac form `h⁴ Σ_x formDens`. -/
def form (h : ℝ) (c : Coef n 𝓢) (Φb : Grid n → CoSpinor 𝓢) (Φ : Grid n → 𝓢) : ℝ :=
  h ^ 4 * ∑ x, formDens h c Φb Φ x

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢)

/-- **The original coefficients** of the Dirac–Yukawa density:
`Γ = Γ' = v γ^μ`, `Ξ = v γ^μ W_μ`, `Ξ' = v W'_μ γ^μ`, `M = v 𝓜_𝐘(H)`. -/
def origCoef (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : Coef n 𝓢 where
  Γ x μ := volume (coframe y x) • gammaMu D μ (coframe y x)
  Γ' x μ := volume (coframe y x) • gammaMu D μ (coframe y x)
  Ξ x μ := volume (coframe y x) • (gammaMu D μ (coframe y x) * wL D h y x μ)
  Ξ' x μ := volume (coframe y x) • (wR D h y x μ * gammaMu D μ (coframe y x))
  M x := volume (coframe y x) • D.yukawa (higgs y x)

/-- Complex bookkeeping for `diracDensity_eq_formDens`. -/
theorem dirac_form_aux (v : ℝ) (a b c d : Fin 4 → ℂ) (m : ℂ) :
    v * (Complex.I / 2 * ∑ μ, (a μ + b μ - (c μ + d μ)) - m).re =
      (∑ μ, (v * (Complex.I / 2 * a μ).re + v * (Complex.I / 2 * b μ).re -
        v * (Complex.I / 2 * c μ).re - v * (Complex.I / 2 * d μ).re)) -
        v * (1 * m).re := by
  have k1 : ∀ w : ℂ, (Complex.I / 2 * w).re = -(w.im / 2) := fun w => by
    simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]; ring
  simp only [Complex.sub_re, k1, one_mul, Complex.add_im, Complex.sub_im, Complex.im_sum,
    Fin.sum_univ_four]
  ring

/-- **The Dirac density is the generalized form with the original coefficients.** -/
theorem diracDensity_eq_formDens (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    diracDensity D h y x = formDens h (origCoef D h y) (psiBar y) (psi y) x := by
  unfold diracDensity formDens origCoef
  simp only [diracDiff_split, diracDiffBar_split, bForm_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  exact dirac_form_aux _ _ _ _ _ _

/-- The finite Dirac–Yukawa action `S_{D,h} = h⁴ Σ_x 𝓛_{D,h}`. -/
def dAct (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, diracDensity D h y x

theorem dAct_eq_form (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    dAct D h y = form h (origCoef D h y) (psiBar y) (psi y) := by
  simp only [dAct, form, diracDensity_eq_formDens]

end Form
/-! ### The exact first variation along a record direction -/

section Variation

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) {n : ℕ} [NeZero n]

/-- The coframe-derived connection as a function of the first jet `(e, q)`. -/
def omegaJ (μ : Fin 4) (p : Mat × (Fin 4 → Mat)) : Mat := readerOmega p.1 p.2 μ

theorem contDiffAt_omegaJ (μ : Fin 4) {p : Mat × (Fin 4 → Mat)} (hp : p.1.det ≠ 0) :
    ContDiffAt ℝ ∞ (omegaJ μ) p :=
  contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => contDiffAt_readerOmega_entry μ a b hp

/-- The first jet `(e(x), δ⁺e(x))` of a coframe field. -/
def coJet (h : ℝ) (e : Grid n → Mat) (x : Grid n) : Mat × (Fin 4 → Mat) :=
  (e x, fun lam => fwdDiff h lam e x)

theorem omegaLink_eq_omegaJ (h : ℝ) (e : Grid n → Mat) (x : Grid n) (μ : Fin 4) :
    omegaLink h e x μ = omegaJ μ (coJet h e x) := rfl

theorem coframe_add_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    coframe (y + t • δy) = coframe y + t • coframe δy := rfl

theorem gauge_add_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) (μ : Fin 4) :
    gauge (y + t • δy) μ = gauge y μ + t • gauge δy μ := rfl

theorem higgs_add_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    higgs (y + t • δy) = higgs y + t • higgs δy := rfl

theorem psi_add_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    psi (y + t • δy) = psi y + t • psi δy := rfl

theorem psiBar_add_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) (t : ℝ) :
    psiBar (y + t • δy) = psiBar y + t • psiBar δy := rfl

theorem fwdDiff_add_smul {V : Type*} [AddCommGroup V] [Module ℝ V] (h : ℝ) (μ : Fin 4)
    (u v : Grid n → V) (t : ℝ) (x : Grid n) :
    fwdDiff h μ (u + t • v) x = fwdDiff h μ u x + t • fwdDiff h μ v x := by
  simp only [ShiftedJetAction.fwdDiff, Pi.add_apply, Pi.smul_apply]
  rw [smul_comm t h⁻¹, ← smul_add]
  congr 1
  rw [smul_sub]
  abel

theorem coJet_add_smul (h : ℝ) (e ε : Grid n → Mat) (t : ℝ) (x : Grid n) :
    coJet h (e + t • ε) x = coJet h e x + t • coJet h ε x := by
  simp only [coJet, Prod.ext_iff, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    Prod.snd_add, Prod.smul_snd, true_and]
  funext lam
  simp only [Pi.add_apply, Pi.smul_apply]
  exact fwdDiff_add_smul h lam e ε t x

/-- Derivative along a line. -/
theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun t : ℝ => a + t • b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a

theorem hasDerivAt_comp_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E} (hf : DifferentiableAt ℝ f a)
    (b : E) : HasDerivAt (fun t : ℝ => f (a + t • b)) (fderiv ℝ f a b) 0 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line a b) (by simp)
  exact h

theorem hasDerivAt_exp_comp {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅]
    {Z : ℝ → 𝔅} {Z' : 𝔅} (hZ : HasDerivAt Z Z' 0) :
    HasDerivAt (fun t : ℝ => exp (Z t)) (fderiv ℝ exp (Z 0) Z') 0 :=
  (exp_analytic (𝕂 := ℝ) (Z 0)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hZ

/-- The variation of the coframe-derived connection `δω_μ = DΩ_μ(e, δ⁺e)[δe, δ⁺δe]`. -/
def omegaVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Mat :=
  fderiv ℝ (omegaJ μ) (coJet h (coframe y) x) (coJet h (coframe δy) x)

theorem hasDerivAt_omegaLink (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => omegaLink h (coframe (y + t • δy)) x μ) (omegaVar h y δy x μ) 0 := by
  have hd : DifferentiableAt ℝ (omegaJ μ) (coJet h (coframe y) x) :=
    (contDiffAt_omegaJ μ hx).differentiableAt (by simp)
  have := hasDerivAt_comp_line hd (coJet h (coframe δy) x)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [omegaLink_eq_omegaJ, coframe_add_smul, coJet_add_smul]

/-- The variation of the spin link `δV_μ = D exp(hσω)[hσ(δω)] ρ_S(U) + e^{hσω} ρ_S(D exp(hA)[h a])`. -/
def spinLinkVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  fderiv ℝ exp (h • D.σ (omegaLink h (coframe y) x μ)) (h • D.σ (omegaVar h y δy x μ)) *
      D.ρS (exp (h • gauge y μ x)) +
    exp (h • D.σ (omegaLink h (coframe y) x μ)) *
      D.ρS (fderiv ℝ exp (h • gauge y μ x) (h • gauge δy μ x))

/-- The variation of the inverse spin link. -/
def spinLinkInvVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  D.ρS (fderiv ℝ exp (-(h • gauge y μ x)) (-(h • gauge δy μ x))) *
      exp (-(h • D.σ (omegaLink h (coframe y) x μ))) +
    D.ρS (exp (-(h • gauge y μ x))) *
      fderiv ℝ exp (-(h • D.σ (omegaLink h (coframe y) x μ))) (-(h • D.σ (omegaVar h y δy x μ)))

theorem hasDerivAt_spinLink (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => spinLink D h (y + t • δy) x μ) (spinLinkVar D h y δy x μ) 0 := by
  have hω := hasDerivAt_omegaLink h y δy x μ hx
  have h1 : HasDerivAt (fun t : ℝ => h • D.σ (omegaLink h (coframe (y + t • δy)) x μ))
      (h • D.σ (omegaVar h y δy x μ)) 0 := by
    have := (D.σ.hasFDerivAt.comp_hasDerivAt 0 hω).const_smul h
    exact this
  have h2 : HasDerivAt (fun t : ℝ => h • gauge (y + t • δy) μ x) (h • gauge δy μ x) 0 := by
    have := (hasDerivAt_line (gauge y μ x) (gauge δy μ x)).const_smul h
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [gauge_add_smul]
  have e1 := hasDerivAt_exp_comp h1
  have e2 := D.ρSL.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_exp_comp h2)
  have := e1.mul e2
  simp only [Function.comp_def, Data.ρSL_apply, coframe_add_smul, gauge_add_smul] at this
  simp only [zero_smul, add_zero] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · rw [spinLinkVar]

theorem hasDerivAt_spinLinkInv (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => spinLinkInv D h (y + t • δy) x μ) (spinLinkInvVar D h y δy x μ) 0 := by
  have hω := hasDerivAt_omegaLink h y δy x μ hx
  have h1 : HasDerivAt (fun t : ℝ => -(h • D.σ (omegaLink h (coframe (y + t • δy)) x μ)))
      (-(h • D.σ (omegaVar h y δy x μ))) 0 := by
    have := ((D.σ.hasFDerivAt.comp_hasDerivAt 0 hω).const_smul h).neg
    exact this
  have h2 : HasDerivAt (fun t : ℝ => -(h • gauge (y + t • δy) μ x)) (-(h • gauge δy μ x)) 0 := by
    have := ((hasDerivAt_line (gauge y μ x) (gauge δy μ x)).const_smul h).neg
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [gauge_add_smul]
  have e1 := D.ρSL.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_exp_comp h2)
  have e2 := hasDerivAt_exp_comp h1
  have := e1.mul e2
  simp only [Function.comp_def, Data.ρSL_apply, coframe_add_smul, gauge_add_smul] at this
  simp only [zero_smul, add_zero] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · rw [spinLinkInvVar]

/-- The variation of the link quotient `W_μ`. -/
def wLVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  h⁻¹ • spinLinkVar D h y δy x μ

/-- The variation of the link quotient `W'_μ`. -/
def wRVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  h⁻¹ • spinLinkInvVar D h y δy x μ

theorem hasDerivAt_wL (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => wL D h (y + t • δy) x μ) (wLVar D h y δy x μ) 0 := by
  have := ((hasDerivAt_spinLink D h y δy x μ hx).sub_const 1).const_smul h⁻¹
  exact this

theorem hasDerivAt_wR (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => wR D h (y + t • δy) x μ) (wRVar D h y δy x μ) 0 := by
  have := ((hasDerivAt_spinLinkInv D h y δy x μ hx).sub_const 1).const_smul h⁻¹
  exact this

/-- `dv = Dv(e)[δe]`. -/
def volVar (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  fderiv ℝ volume (coframe y x) (coframe δy x)

/-- `dγ^μ = Dγ^μ(e)[δe]`. -/
def gammaVar (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  fderiv ℝ (gammaMu D μ) (coframe y x) (coframe δy x)

theorem hasDerivAt_volume (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => volume (coframe (y + t • δy) x)) (volVar y δy x) 0 :=
  hasDerivAt_comp_line ((contDiffAt_volume (k := 1) hx).differentiableAt one_ne_zero) _

theorem hasDerivAt_gammaMu (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => gammaMu D μ (coframe (y + t • δy) x)) (gammaVar D y δy x μ) 0 :=
  hasDerivAt_comp_line ((contDiffAt_gammaMu D μ (k := 1) hx).differentiableAt one_ne_zero) _

/-- **The variation of the original coefficients** (`δc`). -/
def varCoef (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) : Coef n 𝓢 where
  Γ x μ := volVar y δy x • gammaMu D μ (coframe y x) +
    volume (coframe y x) • gammaVar D y δy x μ
  Γ' x μ := volVar y δy x • gammaMu D μ (coframe y x) +
    volume (coframe y x) • gammaVar D y δy x μ
  Ξ x μ := volVar y δy x • (gammaMu D μ (coframe y x) * wL D h y x μ) +
    volume (coframe y x) • (gammaVar D y δy x μ * wL D h y x μ +
      gammaMu D μ (coframe y x) * wLVar D h y δy x μ)
  Ξ' x μ := volVar y δy x • (wR D h y x μ * gammaMu D μ (coframe y x)) +
    volume (coframe y x) • (wRVar D h y δy x μ * gammaMu D μ (coframe y x) +
      wR D h y x μ * gammaVar D y δy x μ)
  M x := volVar y δy x • D.yukawa (higgs y x) + volume (coframe y x) • D.yukawa (higgs δy x)

/-- A trilinear derivative rule. -/
theorem hasDerivAt_tri {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F →L[ℝ] ℝ) {f : ℝ → E} {f' : E}
    {g : ℝ → F →L[ℝ] F} {g' : F →L[ℝ] F} {k : ℝ → F} {k' : F} (hf : HasDerivAt f f' 0)
    (hg : HasDerivAt g g' 0) (hk : HasDerivAt k k' 0) :
    HasDerivAt (fun t : ℝ => B (f t) (g t (k t)))
      (B f' (g 0 (k 0)) + B (f 0) (g' (k 0)) + B (f 0) (g 0 k')) 0 := by
  have hgk := hg.clm_apply hk
  have hB := (B.hasFDerivAt.comp_hasDerivAt 0 hf).clm_apply hgk
  simp only [Function.comp_def, ContinuousLinearMap.fderiv] at hB
  refine hB.congr_deriv ?_
  rw [map_add, add_assoc]

theorem zero_smul_coSpinor (g : CoSpinor 𝓢) : (0 : ℝ) • g = 0 := by ext w; simp

theorem zero_smul_coSpinor_fun (g : Grid n → CoSpinor 𝓢) : (0 : ℝ) • g = 0 := by
  funext i; exact zero_smul_coSpinor (g i)

theorem hasDerivAt_pi_line {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u v : Grid n → V) (z : Grid n) : HasDerivAt (fun t : ℝ => (u + t • v) z) (v z) 0 := by
  simpa using hasDerivAt_line (u z) (v z)

theorem hasDerivAt_fwdDiff_line {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ)
    (u v : Grid n → V) (μ : Fin 4) (x : Grid n) :
    HasDerivAt (fun t : ℝ => fwdDiff h μ (u + t • v) x) (fwdDiff h μ v x) 0 := by
  have := hasDerivAt_line (fwdDiff h μ u x) (fwdDiff h μ v x)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact fwdDiff_add_smul h μ u v t x

variable {D}

/-- **The derivative of the generalized form** along a curve of coefficients and two affine
spinor curves: trilinearity. -/
theorem hasDerivAt_formDens (h : ℝ) {c : ℝ → Coef n 𝓢} {c' : Coef n 𝓢}
    (Φb Φb' : Grid n → CoSpinor 𝓢) (Φ Φ' : Grid n → 𝓢) (x : Grid n)
    (hΓ : ∀ μ, HasDerivAt (fun t : ℝ => (c t).Γ x μ) (c'.Γ x μ) 0)
    (hΓ' : ∀ μ, HasDerivAt (fun t : ℝ => (c t).Γ' x μ) (c'.Γ' x μ) 0)
    (hΞ : ∀ μ, HasDerivAt (fun t : ℝ => (c t).Ξ x μ) (c'.Ξ x μ) 0)
    (hΞ' : ∀ μ, HasDerivAt (fun t : ℝ => (c t).Ξ' x μ) (c'.Ξ' x μ) 0)
    (hM : HasDerivAt (fun t : ℝ => (c t).M x) (c'.M x) 0) :
    HasDerivAt (fun t : ℝ => formDens h (c t) (Φb + t • Φb') (Φ + t • Φ') x)
      (formDens h c' Φb Φ x + formDens h (c 0) Φb' Φ x + formDens h (c 0) Φb Φ' x) 0 := by
  have T1 := fun μ => hasDerivAt_tri (bForm (Complex.I / 2)) (hasDerivAt_pi_line Φb Φb' x)
    (hΓ μ) (hasDerivAt_fwdDiff_line h Φ Φ' μ x)
  have T2 := fun μ => hasDerivAt_tri (bForm (Complex.I / 2)) (hasDerivAt_pi_line Φb Φb' x)
    (hΞ μ) (hasDerivAt_pi_line Φ Φ' (x + unitVec n μ))
  have T3 := fun μ => hasDerivAt_tri (bForm (Complex.I / 2))
    (hasDerivAt_fwdDiff_line h Φb Φb' μ x) (hΓ' μ) (hasDerivAt_pi_line Φ Φ' x)
  have T4 := fun μ => hasDerivAt_tri (bForm (Complex.I / 2))
    (hasDerivAt_pi_line Φb Φb' (x + unitVec n μ)) (hΞ' μ) (hasDerivAt_pi_line Φ Φ' x)
  have T5 := hasDerivAt_tri (bForm 1) (hasDerivAt_pi_line Φb Φb' x) hM
    (hasDerivAt_pi_line Φ Φ' x)
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    (((T1 μ).add (T2 μ)).sub (T3 μ)).sub (T4 μ)).sub T5
  refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [formDens]
    rfl
  · simp only [formDens, zero_smul_coSpinor_fun, zero_smul, add_zero, Pi.add_apply,
      Pi.zero_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring

end Variation

section MainVariation

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) {n : ℕ} [NeZero n]

theorem record_add_zero_smul (y δy : Grid n → Field 𝔄 𝓗 𝓢) : y + (0 : ℝ) • δy = y := by
  funext x
  simp only [Pi.add_apply, Pi.smul_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp
  · simp
  · simp
  · simp
  · show (y x).2.2.2.2 + (0 : ℝ) • (δy x).2.2.2.2 = (y x).2.2.2.2
    rw [zero_smul_coSpinor, add_zero]

theorem origCoef_zero (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) :
    origCoef D h (y + (0 : ℝ) • δy) = origCoef D h y := by
  rw [record_add_zero_smul]

theorem hasDerivAt_coefΓ (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (origCoef D h (y + t • δy)).Γ x μ) ((varCoef D h y δy).Γ x μ) 0 := by
  have := (hasDerivAt_volume y δy x hx).smul (hasDerivAt_gammaMu D y δy x μ hx)
  simp only [record_add_zero_smul] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · simp only [varCoef, Pi.mul_apply, record_add_zero_smul]
    abel

theorem hasDerivAt_coefΓ' (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (origCoef D h (y + t • δy)).Γ' x μ) ((varCoef D h y δy).Γ' x μ) 0 :=
  hasDerivAt_coefΓ D h y δy x μ hx

theorem hasDerivAt_coefΞ (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (origCoef D h (y + t • δy)).Ξ x μ) ((varCoef D h y δy).Ξ x μ) 0 := by
  have := (hasDerivAt_volume y δy x hx).smul
    ((hasDerivAt_gammaMu D y δy x μ hx).mul (hasDerivAt_wL D h y δy x μ hx))
  simp only [record_add_zero_smul] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · simp only [varCoef, Pi.mul_apply, record_add_zero_smul]
    abel

theorem hasDerivAt_coefΞ' (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (origCoef D h (y + t • δy)).Ξ' x μ) ((varCoef D h y δy).Ξ' x μ) 0 := by
  have := (hasDerivAt_volume y δy x hx).smul
    ((hasDerivAt_wR D h y δy x μ hx).mul (hasDerivAt_gammaMu D y δy x μ hx))
  simp only [record_add_zero_smul] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · simp only [varCoef, Pi.mul_apply, record_add_zero_smul]
    abel

theorem hasDerivAt_coefM (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n)
    (hx : (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (origCoef D h (y + t • δy)).M x) ((varCoef D h y δy).M x) 0 := by
  have hY : HasDerivAt (fun t : ℝ => D.yukawa (higgs (y + t • δy) x)) (D.yukawa (higgs δy x)) 0 := by
    have := D.yukawa.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line (higgs y x) (higgs δy x))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [higgs_add_smul]
  have := (hasDerivAt_volume y δy x hx).smul hY
  simp only [record_add_zero_smul] at this
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_) |>.congr_deriv ?_
  · rfl
  · simp only [varCoef, Pi.mul_apply, record_add_zero_smul]
    abel

/-- **The exact first variation of the finite Dirac–Yukawa action** along a record direction
`δy`, on the nondegenerate chart:
`d/dt S_{D,h}(y + t δy)|₀ = form(δc, Ψ̄, Ψ) + form(c, δΨ̄, Ψ) + form(c, Ψ̄, δΨ)`. -/
theorem hasDerivAt_dAct (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, (coframe y x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => dAct D h (y + t • δy))
      (form h (varCoef D h y δy) (psiBar y) (psi y) + form h (origCoef D h y) (psiBar δy) (psi y) +
        form h (origCoef D h y) (psiBar y) (psi δy)) 0 := by
  have hx : ∀ x, HasDerivAt (fun t : ℝ => formDens h (origCoef D h (y + t • δy))
      (psiBar y + t • psiBar δy) (psi y + t • psi δy) x)
      (formDens h (varCoef D h y δy) (psiBar y) (psi y) x +
        formDens h (origCoef D h y) (psiBar δy) (psi y) x +
        formDens h (origCoef D h y) (psiBar y) (psi δy) x) 0 := by
    intro x
    have := hasDerivAt_formDens h (c := fun t => origCoef D h (y + t • δy)) (psiBar y) (psiBar δy)
      (psi y) (psi δy) x (fun μ => hasDerivAt_coefΓ D h y δy x μ (hdet x))
      (fun μ => hasDerivAt_coefΓ' D h y δy x μ (hdet x))
      (fun μ => hasDerivAt_coefΞ D h y δy x μ (hdet x))
      (fun μ => hasDerivAt_coefΞ' D h y δy x μ (hdet x)) (hasDerivAt_coefM D h y δy x (hdet x))
    simp only [origCoef_zero] at this
    exact this
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hx x).const_mul (h ^ 4)
  refine (hs.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [dAct_eq_form, form, psi_add_smul, psiBar_add_smul]
  · simp only [form, Finset.sum_add_distrib]
    ring

/-- **The finite Dirac–Yukawa first variation** `D S_{D,h}(y)[δy]` (directional derivative). -/
def dVar (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  deriv (fun t : ℝ => dAct D h (y + t • δy)) 0

theorem dVar_eq (h : ℝ) (y δy : Grid n → Field 𝔄 𝓗 𝓢) (hdet : ∀ x, (coframe y x).det ≠ 0) :
    dVar D h y δy = form h (varCoef D h y δy) (psiBar y) (psi y) +
      form h (origCoef D h y) (psiBar δy) (psi y) + form h (origCoef D h y) (psiBar y) (psi δy) :=
  (hasDerivAt_dAct D h y δy hdet).deriv

end MainVariation


end

end NativeDirac
end RenewalGeometry
