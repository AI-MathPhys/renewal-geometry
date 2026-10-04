/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMFirstVariationContinuity

/-!
# Weak-`H¹` continuity of the complete fermionic first variation
  (`prop:weak-fermion`, and the Dirac–Yukawa sector of `prop:reduced-continuity`;
  Einstein–Standard-Model action-closure manuscript)

The Dirac–Yukawa density `eq:dirac-density` (`diracDensity`, including the Levi-Civita spin
connection `Ω_μ = ¼ ω_{μab}γ^aγ^b` and the gauge and Yukawa couplings) times the volume factor is
written on the nondegenerate chart as a jet density
`diracPt R = Φ_k(e)[(Ψ̄, Ψ), (∂Ψ, ∂Ψ̄)] + Φ_p(e)[(∂e, A, 𝓜_Y(H), 1), Ψ̄, Ψ]`
(`diracDensity_mul_vol`), with the kinetic coefficient `Φ_k` and the potential coefficient `Φ_p`
smooth on the chart (`contDiffOn_kinCoeff`, `contDiffOn_potCoeff`); the spin connection enters
through `ω = P(e)∂e` (`spinConn_eq_spinConnL`, `lem:products`).

* `addL`, `addBilinL`, `addTrilinL`: continuous multilinear maps from additive continuous maps
  (finite dimensions); `hasFDerivAt_coeff_trilin`: derivative of `R ↦ Φ(z R)(y₁ R + c, y₂ R, y₃ R)`.
* `diracDensity_eq`, `diracDensity_mul_vol`: the factorization `diracDensity · √|g| = diracPt(redJet)`;
  `hasFDerivAt_diracPt`, `fderiv_diracPt_redVar`: the covector `diracCov`, split into a strong part
  (`strongCoeff1`, `strongCoeff2`) and a weak part (`weakCoeff`) paired with the spinor gradients.
* `diracVariation_eq_cov`, `smVariation_eq_cov`: identification of the complete Dirac–Yukawa and
  Standard-Model first variations of smooth fields with covector integrals over the slab box.
* `diracStrong_tendsto` (`L¹`: coefficient–bilinear and critical `(2,4,4)` trilinear products),
  `diracWeak_tendsto` (`L²`); `spinor_chart_data` (Rellich strong `L²`, Sobolev uniform `L⁴`, weak
  `L²` gradient convergence from weak `H¹` convergence); `weakL2_complex`, `weakL2_pi`, `weakL2_prod`.
* `dual_tendsto_weak` (finite-net weak–strong pairing in the dual test norm), `dual_tendsto_split`.
* **`diracVariation_dual_tendsto`** (`prop:weak-fermion`, `L²` gauge/Higgs hypotheses, covering the
  weakened form) and **`diracVariation_dual_tendsto_L4`** (the paper's `L⁴` form).
* **`smVariation_dual_tendsto`** (`prop:reduced-continuity`, complete Standard-Model sector:
  Yang–Mills, Higgs and Dirac–Yukawa with the metric–spin-connection chain), with a non-vacuity
  example (the flat regulator).

Rendering: slab chart box `Q = (t₀,t₁) × (0,1)³ ⊇` time support of `K`; dual norm of `𝒱_K^r` as
the uniform estimate `|ℓ_h(v) - ℓ(v)| ≤ ε‖v‖_{C^r}`; the limit functional is the covector formula
evaluated on the limit jet (`diracLimitVariation`, `smLimitVariation`); the Yukawa map of the
carrier is an arbitrary function of the bank, so convergence of its linear part and constant is
assumed (`prop:weak-fermion`: "the finite Yukawa coefficients converge").
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### `fun_prop` support for complex coordinates -/

section FunProp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

@[fun_prop] theorem contDiffAt_re' {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => (f y).re) x :=
  Complex.reCLM.contDiff.contDiffAt.comp x hf

@[fun_prop] theorem contDiffAt_im' {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => (f y).im) x :=
  Complex.imCLM.contDiff.contDiffAt.comp x hf

@[fun_prop] theorem contDiffAt_ofReal' {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => ((f y : ℝ) : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

end FunProp

/-! ### Multilinear maps from additive maps -/

section Builders

variable {V₁ V₂ V₃ W : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]
  [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] [FiniteDimensional ℝ V₃]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An additive continuous map as a continuous `ℝ`-linear map. -/
def addL (f : V₁ → W) (h : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) : V₁ →L[ℝ] W :=
  (AddMonoidHom.mk' f h).toRealLinearMap hc

@[simp] theorem addL_apply (f : V₁ → W) (h hc) (x : V₁) : addL f h hc x = f x := rfl

/-- A biadditive jointly continuous map as a continuous bilinear map. -/
def addBilinL (f : V₁ → V₂ → W) (h₁ : ∀ x x' y, f (x + x') y = f x y + f x' y)
    (h₂ : ∀ x y y', f x (y + y') = f x y + f x y')
    (hc : Continuous fun p : V₁ × V₂ => f p.1 p.2) : V₁ →L[ℝ] V₂ →L[ℝ] W :=
  addL (fun x => addL (f x) (h₂ x) (hc.comp (continuous_const.prodMk continuous_id)))
    (fun x x' => ContinuousLinearMap.ext fun y => by simp [h₁])
    (continuous_clm_apply.mpr fun y => hc.comp (continuous_id.prodMk continuous_const))

@[simp] theorem addBilinL_apply (f : V₁ → V₂ → W) (h₁ h₂ hc) (x : V₁) (y : V₂) :
    addBilinL f h₁ h₂ hc x y = f x y := rfl

/-- A triadditive jointly continuous map as a continuous trilinear map. -/
def addTrilinL (f : V₁ → V₂ → V₃ → W) (h₁ : ∀ x x' y z, f (x + x') y z = f x y z + f x' y z)
    (h₂ : ∀ x y y' z, f x (y + y') z = f x y z + f x y' z)
    (h₃ : ∀ x y z z', f x y (z + z') = f x y z + f x y z')
    (hc : Continuous fun p : V₁ × V₂ × V₃ => f p.1 p.2.1 p.2.2) :
    V₁ →L[ℝ] V₂ →L[ℝ] V₃ →L[ℝ] W :=
  addL (fun x => addBilinL (f x) (h₂ x) (h₃ x) (hc.comp (continuous_const.prodMk continuous_id)))
    (fun x x' => ContinuousLinearMap.ext fun y => ContinuousLinearMap.ext fun z => by simp [h₁])
    (continuous_clm_apply.mpr fun y => continuous_clm_apply.mpr fun z =>
      hc.comp (continuous_id.prodMk (continuous_const (y := (y, z)))))

@[simp] theorem addTrilinL_apply (f : V₁ → V₂ → V₃ → W) (h₁ h₂ h₃ hc) (x : V₁) (y : V₂) (z : V₃) :
    addTrilinL f h₁ h₂ h₃ hc x y z = f x y z := rfl

/-- Derivative of a trilinear expression with a differentiable coefficient and an affine first
argument. -/
theorem hasFDerivAt_coeff_trilin {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {Φ : Z → V₁ →L[ℝ] V₂ →L[ℝ] V₃ →L[ℝ] ℝ}
    (pz : E →L[ℝ] Z) (p₁ : E →L[ℝ] V₁) (c₁ : V₁) (p₂ : E →L[ℝ] V₂) (p₃ : E →L[ℝ] V₃) {R : E}
    (hΦ : DifferentiableAt ℝ Φ (pz R)) :
    DifferentiableAt ℝ (fun R => Φ (pz R) (p₁ R + c₁) (p₂ R) (p₃ R)) R ∧ ∀ dR,
      fderiv ℝ (fun R => Φ (pz R) (p₁ R + c₁) (p₂ R) (p₃ R)) R dR =
        fderiv ℝ Φ (pz R) (pz dR) (p₁ R + c₁) (p₂ R) (p₃ R) + Φ (pz R) (p₁ dR) (p₂ R) (p₃ R) +
          Φ (pz R) (p₁ R + c₁) (p₂ dR) (p₃ R) + Φ (pz R) (p₁ R + c₁) (p₂ R) (p₃ dR) := by
  have h1 : HasFDerivAt (fun R => Φ (pz R)) ((fderiv ℝ Φ (pz R)).comp pz) R :=
    hΦ.hasFDerivAt.comp R pz.hasFDerivAt
  have h2 : HasFDerivAt (fun R => p₁ R + c₁) p₁ R := p₁.hasFDerivAt.add_const c₁
  have h4 := ((h1.clm_apply h2).clm_apply p₂.hasFDerivAt).clm_apply p₃.hasFDerivAt
  refine ⟨h4.differentiableAt, fun dR => ?_⟩
  rw [h4.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

end Builders

/-! ### The Dirac–Yukawa density as a jet density -/

section DiracForms

variable {C : Type} [Fintype C]

/-- Curved Clifford matrices `γ^μ = E^μ_a γ^a` at a coframe value. -/
def gammaE (e : CoframeFibre) : Fin 4 → Fin 4 → Fin 4 → ℂ :=
  fun μ s s' => ∑ a, (frameAt e μ a : ℂ) * gammaW a s s'

/-- Spinor connection `Ω_μ = ¼ ω_{μab}γ^aγ^b` at a coframe value and coframe jet, with
`ω = P(e)∂e = spinConnL e ∂e`. -/
def spinGenE (e : CoframeFibre) (de : CoframeJet) : Fin 4 → Fin 4 → Fin 4 → ℂ :=
  fun μ s s' => (1 / 4 : ℂ) * ∑ a, ∑ b,
    ((∑ c, minkowskiEta a c * spinConnL e de μ c b : ℝ) : ℂ) * mmul (gammaW a) (gammaW b) s s'

theorem spinGenE_add (e : CoframeFibre) (d d' : CoframeJet) :
    spinGenE e (d + d') = spinGenE e d + spinGenE e d' := by
  funext μ s s'
  simp only [spinGenE, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    Complex.ofReal_add, add_mul]

/-- The kinetic form `Re{(i/2)(Ψ̄γ^μ∂_μΨ - ∂_μΨ̄γ^μΨ)}` with given curved Clifford matrices. -/
def kinForm (γ : Fin 4 → Fin 4 → Fin 4 → ℂ) (U : SpinorFibre C × SpinorFibre C)
    (W : (Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)) : ℝ :=
  ((Complex.I / 2) * ∑ μ, ∑ s, ∑ s', ∑ c,
    (U.1 s c * γ μ s s' * W.1 μ s' c - W.2 μ s c * γ μ s s' * U.2 s' c)).re

end DiracForms

section DiracPoint

variable {Ysec : Type} (FC : FermionCarrier Ysec)

/-- The potential form: spin-connection, gauge and Yukawa couplings,
`Re{(i/2)(Ψ̄γ^μ(Ω_μ + ρ(A_μ))Ψ + Ψ̄(Ω_μ + ρ(A_μ))γ^μΨ) - Ψ̄𝓜Ψ}`. -/
def potForm (γ Ω : Fin 4 → Fin 4 → Fin 4 → ℂ) (A : ConnFibre) (M : FC.C → FC.C → ℂ)
    (Ψb Ψ : SpinorFibre FC.C) : ℝ :=
  ((Complex.I / 2) * ∑ μ, ∑ s, ∑ s', ∑ c,
      (Ψb s c * γ μ s s' * (∑ s'', Ω μ s' s'' * Ψ s'' c + ∑ c', FC.rho (A μ) c c' * Ψ s' c') +
        (∑ s'', Ψb s'' c * Ω μ s'' s + ∑ c', Ψb s c' * FC.rho (A μ) c' c) * γ μ s s' *
          Ψ s' c) -
    ∑ s, ∑ c, ∑ c', Ψb s c * M c c' * Ψ s c').re

/-- **Splitting of the Dirac–Yukawa density** into the kinetic and potential forms, with the spin
connection written as `ω = P(e)∂e` (needs the coframe differentiable and nondegenerate). -/
theorem diracDensity_eq (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4)
    (he : DifferentiableAt ℝ z.e x) (hx : z.e x ∈ coframeGL) :
    diracDensity FC θ z x =
      kinForm (gammaE (z.e x)) (z.Ψb x, z.Ψ x) (fun μ => pd z.Ψ μ x, fun μ => pd z.Ψb μ x) +
        potForm FC (gammaE (z.e x)) (spinGenE (z.e x) (fun i => pd z.e i x)) (z.A x)
          (FC.yukawa θ (z.H x)) (z.Ψb x) (z.Ψ x) := by
  have hg : spinGen z.e x = spinGenE (z.e x) (fun i => pd z.e i x) := by
    funext μ s s'
    simp only [spinGen, spinGenE, spinConn_eq_spinConnL he hx]
  simp only [diracDensity, kinForm, potForm, covDerivSpinor, covDerivCospinor, curvedGamma, hg,
    gammaE, ← Complex.add_re]
  congr 1
  rw [← add_sub_assoc, ← mul_add]
  simp only [← Finset.sum_add_distrib]
  refine congrArg (fun t => Complex.I / 2 * t - _) ?_
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end DiracPoint

section DiracCoeffs

variable {C : Type} [Fintype C]

/-- The kinetic form as a continuous bilinear map. -/
def kinBilin (γ : Fin 4 → Fin 4 → Fin 4 → ℂ) :
    (SpinorFibre C × SpinorFibre C) →L[ℝ] ((Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)) →L[ℝ]
      ℝ :=
  addBilinL (kinForm γ)
    (fun U U' W => by
      simp only [kinForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, Complex.add_re, Complex.sub_re]
      ring)
    (fun U W W' => by
      simp only [kinForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, Complex.add_re, Complex.sub_re]
      ring)
    (by unfold kinForm; fun_prop)

@[simp] theorem kinBilin_apply (γ : Fin 4 → Fin 4 → Fin 4 → ℂ) (U : SpinorFibre C × SpinorFibre C)
    (W : (Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)) : kinBilin γ U W = kinForm γ U W :=
  rfl

/-- **The kinetic coefficient** `Φ_k(e) = √|g| · kinForm(γ(e))`. -/
def kinCoeff (e : CoframeFibre) :
    (SpinorFibre C × SpinorFibre C) →L[ℝ] ((Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)) →L[ℝ]
      ℝ :=
  volFactor e • kinBilin (gammaE e)

theorem kinCoeff_apply (e : CoframeFibre) (U : SpinorFibre C × SpinorFibre C)
    (W : (Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)) :
    kinCoeff e U W = volFactor e * kinForm (gammaE e) U W := rfl

end DiracCoeffs

section DiracPot

variable {Ysec : Type} (FC : FermionCarrier Ysec)

/-- The potential field space `(∂e, A, 𝓜, s)`. -/
abbrev PotVar (FC : FermionCarrier Ysec) : Type :=
  CoframeJet × ConnFibre × (FC.C → FC.C → ℂ) × ℝ

theorem continuous_rho : Continuous FC.rho := LinearMap.continuous_of_finiteDimensional _

/-- The potential form as a continuous trilinear map at a coframe value. -/
def potTrilin (e : CoframeFibre) :
    PotVar FC →L[ℝ] SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C →L[ℝ] ℝ :=
  addTrilinL (fun Y Ψb Ψ => potForm FC (gammaE e) (spinGenE e Y.1) Y.2.1 Y.2.2.1 Ψb Ψ)
    (fun Y Y' Ψb Ψ => by
      simp only [potForm, Prod.fst_add, Prod.snd_add, spinGenE_add, Pi.add_apply, map_add,
        add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
        Complex.add_re, Complex.sub_re]
      ring)
    (fun Y Ψb Ψb' Ψ => by
      simp only [potForm, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_sub, Complex.add_re, Complex.sub_re]
      ring)
    (fun Y Ψb Ψ Ψ' => by
      simp only [potForm, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_sub, Complex.add_re, Complex.sub_re]
      ring)
    (by
      have hρ := continuous_rho FC
      have hω : Continuous (spinConnL e) := (spinConnL e).continuous
      unfold potForm spinGenE
      fun_prop)

@[simp] theorem potTrilin_apply (e : CoframeFibre) (Y : PotVar FC) (Ψb Ψ : SpinorFibre FC.C) :
    potTrilin FC e Y Ψb Ψ = potForm FC (gammaE e) (spinGenE e Y.1) Y.2.1 Y.2.2.1 Ψb Ψ := rfl

/-- **The potential coefficient** `Φ_p(e) = √|g| · potForm(γ(e), Ω(e,·))`. -/
def potCoeff (e : CoframeFibre) :
    PotVar FC →L[ℝ] SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C →L[ℝ] ℝ :=
  volFactor e • potTrilin FC e

theorem potCoeff_apply (e : CoframeFibre) (Y : PotVar FC) (Ψb Ψ : SpinorFibre FC.C) :
    potCoeff FC e Y Ψb Ψ =
      volFactor e * potForm FC (gammaE e) (spinGenE e Y.1) Y.2.1 Y.2.2.1 Ψb Ψ := rfl

/-- **The Dirac–Yukawa jet density**
`diracPt R = Φ_k(e)[(Ψ̄,Ψ),(∂Ψ,∂Ψ̄)] + Φ_p(e)[(∂e, A, 𝓜_Y(H), 1), Ψ̄, Ψ]`. -/
def diracPt (θ : CoefficientBank Ysec) (R : RJet FC.C) : ℝ :=
  kinCoeff R.e (R.Ψb, R.Ψ) (R.dΨ, R.dΨb) +
    potCoeff FC R.e (R.de, R.A, FC.yukawa θ R.H, 1) R.Ψb R.Ψ

/-- **`diracDensity · √|g| = diracPt (redJet)`** where the coframe is differentiable and
nondegenerate. -/
theorem diracDensity_mul_vol (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4)
    (he : DifferentiableAt ℝ z.e x) (hx : z.e x ∈ coframeGL) :
    diracDensity FC θ z x * volFactor (z.e x) = diracPt FC θ (redJet z x) := by
  rw [diracDensity_eq FC θ z x he hx]
  simp only [diracPt, kinCoeff_apply, potCoeff_apply, redJet, RJet.mk_e, RJet.mk_de, RJet.mk_A,
    RJet.mk_H, RJet.mk_Ψ, RJet.mk_dΨ, RJet.mk_Ψb, RJet.mk_dΨb]
  ring

end DiracPot

/-! ### Smoothness and the derivative of the Dirac jet density -/

section DiracSmooth

variable {Ysec : Type} (FC : FermionCarrier Ysec)

theorem contDiffOn_kinCoeff {C : Type} [Fintype C] {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (kinCoeff (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun U => contDiffOn_clm_apply.mpr fun W => ?_
  intro e he
  have hf : ∀ μ a, ContDiffAt ℝ n (fun e : CoframeFibre => frameAt e μ a) e := fun μ a =>
    contDiffAt_frameAt μ a he
  have hv : ContDiffAt ℝ n volFactor e := contDiffAt_volFactor he
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ n (fun e => volFactor e * kinForm (gammaE e) U W) e
  unfold kinForm gammaE
  fun_prop

theorem contDiffAt_spinConnL_apply {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL)
    (d : CoframeJet) (μ c b : Fin 4) :
    ContDiffAt ℝ n (fun e : CoframeFibre => spinConnL e d μ c b) e := by
  have h : ContDiffAt ℝ n (fun e : CoframeFibre => spinConnL e d) e :=
    ((contDiffOn_spinConnL (n := n)).contDiffAt (isOpen_coframeGL.mem_nhds he)).clm_apply
      contDiffAt_const
  exact contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_pi.mp h μ) c) b

theorem contDiffOn_potCoeff {n : WithTop ℕ∞} : ContDiffOn ℝ n (potCoeff FC) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun Y => contDiffOn_clm_apply.mpr fun Ψb =>
    contDiffOn_clm_apply.mpr fun Ψ => ?_
  intro e he
  have hf : ∀ μ a, ContDiffAt ℝ n (fun e : CoframeFibre => frameAt e μ a) e := fun μ a =>
    contDiffAt_frameAt μ a he
  have hv : ContDiffAt ℝ n volFactor e := contDiffAt_volFactor he
  have hω : ∀ μ c b, ContDiffAt ℝ n (fun e : CoframeFibre => spinConnL e Y.1 μ c b) e :=
    fun μ c b => contDiffAt_spinConnL_apply he Y.1 μ c b
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ n
    (fun e => volFactor e * potForm FC (gammaE e) (spinGenE e Y.1) Y.2.1 Y.2.2.1 Ψb Ψ) e
  unfold potForm gammaE spinGenE
  fun_prop

/-- The linear part of the Yukawa map as a continuous linear map. -/
def yukL (θ : CoefficientBank Ysec) : HiggsFibre →L[ℝ] (FC.C → FC.C → ℂ) :=
  LinearMap.toContinuousLinearMap (FC.yukawa θ).linear

theorem yukawa_eq (θ : CoefficientBank Ysec) (h : HiggsFibre) :
    FC.yukawa θ h = yukL FC θ h + FC.yukawa θ 0 := by
  have := (FC.yukawa θ).linearMap_vsub h 0
  simp only [vsub_eq_sub, sub_zero] at this
  simp only [yukL, LinearMap.coe_toContinuousLinearMap', this, sub_add_cancel]

/-- The potential variable `(∂e, A, 𝓜_Y(H), 1)` of a jet. -/
def potVar (θ : CoefficientBank Ysec) (R : RJet FC.C) : PotVar FC :=
  (R.de, R.A, FC.yukawa θ R.H, 1)

/-- Its linear part. -/
def potVarL (θ : CoefficientBank Ysec) : RJet FC.C →L[ℝ] PotVar FC :=
  πde.prod (πA.prod (((yukL FC θ).comp πH).prod 0))

theorem potVar_eq (θ : CoefficientBank Ysec) (R : RJet FC.C) :
    potVar FC θ R = potVarL FC θ R + (0, 0, FC.yukawa θ 0, 1) := by
  simp only [potVar, potVarL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, πde_apply, πA_apply, πH_apply, Prod.mk_add_mk, add_zero,
    zero_add, ← yukawa_eq]

/-- The spinor pair `(Ψ̄, Ψ)` and spinor-gradient pair `(∂Ψ, ∂Ψ̄)` of a jet. -/
def pU : RJet FC.C →L[ℝ] SpinorFibre FC.C × SpinorFibre FC.C := πΨb.prod πΨ
def pW : RJet FC.C →L[ℝ] (Fin 4 → SpinorFibre FC.C) × (Fin 4 → SpinorFibre FC.C) := πdΨ.prod πdΨb

/-- The explicit derivative of `diracPt`. -/
def diracDeriv (θ : CoefficientBank Ysec) (R dR : RJet FC.C) : ℝ :=
  fderiv ℝ kinCoeff R.e dR.e (R.Ψb, R.Ψ) (R.dΨ, R.dΨb) + kinCoeff R.e (dR.Ψb, dR.Ψ) (R.dΨ, R.dΨb) +
    kinCoeff R.e (R.Ψb, R.Ψ) (dR.dΨ, dR.dΨb) +
  (fderiv ℝ (potCoeff FC) R.e dR.e (potVar FC θ R) R.Ψb R.Ψ +
    potCoeff FC R.e (potVarL FC θ dR) R.Ψb R.Ψ + potCoeff FC R.e (potVar FC θ R) dR.Ψb R.Ψ +
    potCoeff FC R.e (potVar FC θ R) R.Ψb dR.Ψ)

theorem hasFDerivAt_diracPt (θ : CoefficientBank Ysec) {R : RJet FC.C} (hR : R ∈ jetGL FC.C) :
    DifferentiableAt ℝ (diracPt FC θ) R ∧
      ∀ dR, fderiv ℝ (diracPt FC θ) R dR = diracDeriv FC θ R dR := by
  have hk := hasFDerivAt_coeff_bilin (C := FC.C) πe (pU FC) (pW FC) (R := R)
    (((contDiffOn_kinCoeff (C := FC.C) (n := 1)).contDiffAt (isOpen_coframeGL.mem_nhds hR)).differentiableAt
      one_ne_zero)
  have hp := hasFDerivAt_coeff_trilin (Φ := potCoeff FC) πe (potVarL FC θ)
    ((0, 0, FC.yukawa θ 0, 1) : PotVar FC) πΨb πΨ (R := R)
    (((contDiffOn_potCoeff FC (n := 1)).contDiffAt (isOpen_coframeGL.mem_nhds hR)).differentiableAt
      one_ne_zero)
  have hfun : diracPt FC θ = fun R => kinCoeff (πe R) (pU FC R) (pW FC R) +
      potCoeff FC (πe R) (potVarL FC θ R + (0, 0, FC.yukawa θ 0, 1)) (πΨb R) (πΨ R) := by
    funext R
    rw [← potVar_eq]
    rfl
  have htot := hk.1.hasFDerivAt.fun_add hp.1.hasFDerivAt
  rw [hfun]
  refine ⟨htot.differentiableAt, fun dR => ?_⟩
  rw [htot.fderiv, ContinuousLinearMap.add_apply, hk.2, hp.2, ← potVar_eq]
  rfl

end DiracSmooth

/-! ### The fermionic covector: strong and weak parts -/

section DiracCov

variable {Ysec : Type} (FC : FermionCarrier Ysec)

/-- Test values `(k, η̄, η)` entering the weak (spinor-gradient) part of the covector. -/
abbrev TestVal (C : Type) [Fintype C] : Type := CoframeFibre × SpinorFibre C × SpinorFibre C

/-- Spinor-gradient values `(∂Ψ, ∂Ψ̄)`. -/
abbrev GradVal (C : Type) [Fintype C] : Type :=
  (Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)

/-- The extended potential variable `((∂e, A, 𝓜, s), 𝓜_Y^lin)`. -/
abbrev PotVar' : Type := PotVar FC × (HiggsFibre →L[ℝ] (FC.C → FC.C → ℂ))

/-- The test-value projection `T ↦ (k, η̄, η)`. -/
def πτ {C : Type} [Fintype C] : RJet C →L[ℝ] TestVal C := πe.prod (πΨb.prod πΨ)

/-- Embeddings into the potential variable. -/
def ιde : CoframeJet →L[ℝ] PotVar FC := ContinuousLinearMap.inl ℝ _ _
def ιA : ConnFibre →L[ℝ] PotVar FC :=
  (ContinuousLinearMap.inr ℝ CoframeJet _).comp (ContinuousLinearMap.inl ℝ _ _)
def ιM : (FC.C → FC.C → ℂ) →L[ℝ] PotVar FC :=
  (ContinuousLinearMap.inr ℝ CoframeJet _).comp
    ((ContinuousLinearMap.inr ℝ ConnFibre _).comp (ContinuousLinearMap.inl ℝ _ _))

/-- `∂k ↦ (ė(∂_μ k))_μ` at a coframe value. -/
def liftJetL (e : CoframeFibre) : CoframeJet →L[ℝ] CoframeJet :=
  ContinuousLinearMap.pi fun μ => (metricLiftL e).comp (ContinuousLinearMap.proj μ)

/-- `(∂e, k) ↦ (Dė(e)[∂_μ e] k)_μ` at a coframe value. -/
def dLiftL (e : CoframeFibre) : CoframeJet →L[ℝ] CoframeFibre →L[ℝ] CoframeJet :=
  addBilinL (fun d k μ => fderiv ℝ metricLiftL e (d μ) k)
    (fun d d' k => by funext μ; simp)
    (fun d k k' => by funext μ; simp)
    (continuous_pi fun μ => ((fderiv ℝ metricLiftL e).continuous.comp
      ((continuous_apply μ).comp continuous_fst)).clm_apply continuous_snd)

/-- **The weak coefficient**: `(s, U) ↦ [τ, W ↦ DΦ_k(e)[ė(k)](U, W) + s Φ_k(e)((η̄, η), W)]`;
paired with the weakly convergent spinor gradients `W = (∂Ψ, ∂Ψ̄)`. -/
def weakCoeff {C : Type} [Fintype C] (e : CoframeFibre) :
    (ℝ × (SpinorFibre C × SpinorFibre C)) →L[ℝ] TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ :=
  addTrilinL (fun sU τ W => fderiv ℝ kinCoeff e (metricLiftL e τ.1) sU.2 W +
      sU.1 * kinCoeff e (τ.2.1, τ.2.2) W)
    (fun sU sU' τ W => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply, add_mul]
      ring)
    (fun sU τ τ' W => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply,
        ← Prod.mk_add_mk, mul_add]
      ring)
    (fun sU τ W W' => by simp only [map_add, mul_add]; ring)
    (by fun_prop)

/-- **The first strong coefficient** (bilinear in the potential variable and the spinor pair):
`(Y', U) ↦ [T ↦ s Φ_k(e)(U, (∂η, ∂η̄)) + Φ_p(e)(Y, η̄, Ψ) + Φ_p(e)(Y, Ψ̄, η)]`. -/
def strongCoeff1 (e : CoframeFibre) :
    PotVar' FC →L[ℝ] (SpinorFibre FC.C × SpinorFibre FC.C) →L[ℝ] RJet FC.C →L[ℝ] ℝ :=
  addTrilinL (fun Y' U T => Y'.1.2.2.2 * kinCoeff e U (T.dΨ, T.dΨb) +
      potCoeff FC e Y'.1 T.Ψb U.2 + potCoeff FC e Y'.1 U.1 T.Ψ)
    (fun Y' Y'' U T => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply, add_mul]
      ring)
    (fun Y' U U' T => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply, mul_add]
      ring)
    (fun Y' U T T' => by
      simp only [RJet.add_dΨ, RJet.add_dΨb, RJet.add_Ψb, RJet.add_Ψ, ← Prod.mk_add_mk, map_add,
        ContinuousLinearMap.add_apply, mul_add]
      ring)
    (by
      have h1 : Continuous fun T : RJet FC.C => T.dΨ := (πdΨ (C := FC.C)).continuous
      have h2 : Continuous fun T : RJet FC.C => T.dΨb := (πdΨb (C := FC.C)).continuous
      have h3 : Continuous fun T : RJet FC.C => T.Ψb := (πΨb (C := FC.C)).continuous
      have h4 : Continuous fun T : RJet FC.C => T.Ψ := (πΨ (C := FC.C)).continuous
      fun_prop)

/-- The scalar formula of the second strong coefficient. -/
def strongForm2 (e : CoframeFibre) (Y' : PotVar' FC) (Ψb Ψ : SpinorFibre FC.C)
    (T : RJet FC.C) : ℝ :=
  fderiv ℝ (potCoeff FC) e (metricLiftL e T.e) Y'.1 Ψb Ψ +
    potCoeff FC e (ιde FC (dLiftL e Y'.1.1 T.e)) Ψb Ψ +
    Y'.1.2.2.2 * potCoeff FC e (ιde FC (liftJetL e T.de) + ιA FC T.A) Ψb Ψ +
    potCoeff FC e (ιM FC (Y'.2 T.H)) Ψb Ψ

theorem continuous_strongForm2 (e : CoframeFibre) (Y' : PotVar' FC) :
    Continuous fun p : SpinorFibre FC.C × SpinorFibre FC.C × RJet FC.C =>
      strongForm2 FC e Y' p.1 p.2.1 p.2.2 := by
  have h1 : Continuous fun T : RJet FC.C => T.e := (πe (C := FC.C)).continuous
  have h2 : Continuous fun T : RJet FC.C => T.de := (πde (C := FC.C)).continuous
  have h3 : Continuous fun T : RJet FC.C => T.A := (πA (C := FC.C)).continuous
  have h4 : Continuous fun T : RJet FC.C => T.H := (πH (C := FC.C)).continuous
  unfold strongForm2
  fun_prop

theorem continuous_strongForm2_left (e : CoframeFibre) (Ψb Ψ : SpinorFibre FC.C)
    (T : RJet FC.C) : Continuous fun Y' : PotVar' FC => strongForm2 FC e Y' Ψb Ψ T := by
  unfold strongForm2
  fun_prop

/-- **The second strong coefficient** (trilinear in the potential variable and the two spinors):
`(Y', Ψ̄, Ψ) ↦ [T ↦ DΦ_p(e)[ė(k)](Y, Ψ̄, Ψ) + Φ_p(e)(Ẏ, Ψ̄, Ψ)]`, with
`Ẏ = (Dė(e)[∂e]k + s ė(∂k), s a, 𝓜_Y^lin η_H, 0)`. -/
def strongCoeff2 (e : CoframeFibre) :
    PotVar' FC →L[ℝ] SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C →L[ℝ] RJet FC.C →L[ℝ] ℝ :=
  addL (fun Y' => addTrilinL (strongForm2 FC e Y')
      (fun Ψb Ψb' Ψ T => by
        simp only [strongForm2, map_add, ContinuousLinearMap.add_apply, mul_add]; ring)
      (fun Ψb Ψ Ψ' T => by
        simp only [strongForm2, map_add, ContinuousLinearMap.add_apply, mul_add]; ring)
      (fun Ψb Ψ T T' => by
        simp only [strongForm2, RJet.add_e, RJet.add_de, RJet.add_A, RJet.add_H, map_add,
          ContinuousLinearMap.add_apply, mul_add]
        ring)
      (continuous_strongForm2 FC e Y'))
    (fun Y' Y'' => ContinuousLinearMap.ext fun Ψb => ContinuousLinearMap.ext fun Ψ =>
      ContinuousLinearMap.ext fun T => by
        simp only [addTrilinL_apply, ContinuousLinearMap.add_apply, strongForm2, Prod.fst_add,
          Prod.snd_add, map_add, add_mul]
        ring)
    (continuous_clm_apply.mpr fun Ψb => continuous_clm_apply.mpr fun Ψ =>
      continuous_clm_apply.mpr fun T => continuous_strongForm2_left FC e Ψb Ψ T)

theorem strongCoeff2_apply (e : CoframeFibre) (Y' : PotVar' FC) (Ψb Ψ : SpinorFibre FC.C)
    (T : RJet FC.C) : strongCoeff2 FC e Y' Ψb Ψ T = strongForm2 FC e Y' Ψb Ψ T := rfl

/-- The extended potential variable of a jet. -/
def potVar' (θ : CoefficientBank Ysec) (R : RJet FC.C) : PotVar' FC :=
  (potVar FC θ R, yukL FC θ)

/-- **The fermionic covector** `T ↦ D(diracPt)(R)[redVar R T]`, split into the strong part and the
weak part paired with the spinor gradients. -/
def diracCov (θ : CoefficientBank Ysec) (R : RJet FC.C) : RJet FC.C →L[ℝ] ℝ :=
  strongCoeff1 FC R.e (potVar' FC θ R) (pU FC R) +
    strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ +
    ((weakCoeff R.e ((1 : ℝ), pU FC R)).flip (pW FC R)).comp πτ

theorem potVarL_redVar (θ : CoefficientBank Ysec) (R T : RJet FC.C) :
    potVarL FC θ (redVar R T) = ιde FC (dLiftL R.e R.de T.e) + ιde FC (liftJetL R.e T.de) +
      ιA FC T.A + ιM FC (yukL FC θ T.H) := by
  simp only [potVarL, redVar, ιde, ιA, ιM, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, πde_apply, πA_apply,
    πH_apply, RJet.mk_de, RJet.mk_A, RJet.mk_H, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rfl

/-- **The covector identity** `D(diracPt)(R)[redVar R T] = diracCov R T` on the chart. -/
theorem fderiv_diracPt_redVar (θ : CoefficientBank Ysec) {R : RJet FC.C} (hR : R ∈ jetGL FC.C)
    (T : RJet FC.C) : fderiv ℝ (diracPt FC θ) R (redVar R T) = diracCov FC θ R T := by
  rw [(hasFDerivAt_diracPt FC θ hR).2]
  simp only [diracDeriv]
  rw [potVarL_redVar]
  simp only [diracCov, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, strongCoeff1, addTrilinL_apply, strongCoeff2_apply,
    strongForm2, weakCoeff, πτ, ContinuousLinearMap.prod_apply, πe_apply, πΨb_apply, πΨ_apply,
    pU, pW, πdΨ_apply, πdΨb_apply, potVar', redVar, RJet.mk_e, RJet.mk_Ψb, RJet.mk_Ψ,
    RJet.mk_dΨ, RJet.mk_dΨb, map_add]
  simp only [potVar, one_mul]
  ring

end DiracCov

/-! ### Continuity of the fermionic coefficients on the chart -/

section CoeffCont

variable {Ysec : Type} (FC : FermionCarrier Ysec)

theorem continuousOn_weakCoeff {C : Type} [Fintype C] :
    ContinuousOn (weakCoeff (C := C)) coframeGL := by
  refine continuousOn_clm_apply.mpr fun sU => continuousOn_clm_apply.mpr fun τ =>
    continuousOn_clm_apply.mpr fun W => ?_
  have hfd : ContinuousOn (fderiv ℝ (kinCoeff (C := C))) coframeGL :=
    (contDiffOn_kinCoeff (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  have hk : ContinuousOn (kinCoeff (C := C)) coframeGL := (contDiffOn_kinCoeff (n := 0)).continuousOn
  show ContinuousOn (fun e => fderiv ℝ kinCoeff e (metricLiftL e τ.1) sU.2 W +
    sU.1 * kinCoeff e (τ.2.1, τ.2.2) W) coframeGL
  exact (((hfd.clm_apply (continuous_metricLiftL.continuousOn.clm_apply continuousOn_const)).clm_apply
    continuousOn_const).clm_apply continuousOn_const).add
    (continuousOn_const.mul ((hk.clm_apply continuousOn_const).clm_apply continuousOn_const))

theorem continuousOn_strongCoeff1 : ContinuousOn (strongCoeff1 FC) coframeGL := by
  refine continuousOn_clm_apply.mpr fun Y' => continuousOn_clm_apply.mpr fun U =>
    continuousOn_clm_apply.mpr fun T => ?_
  have hk : ContinuousOn (kinCoeff (C := FC.C)) coframeGL :=
    (contDiffOn_kinCoeff (n := 0)).continuousOn
  have hp : ContinuousOn (potCoeff FC) coframeGL := (contDiffOn_potCoeff FC (n := 0)).continuousOn
  show ContinuousOn (fun e => Y'.1.2.2.2 * kinCoeff e U (T.dΨ, T.dΨb) +
    potCoeff FC e Y'.1 T.Ψb U.2 + potCoeff FC e Y'.1 U.1 T.Ψ) coframeGL
  exact ((continuousOn_const.mul ((hk.clm_apply continuousOn_const).clm_apply continuousOn_const)).add
    (((hp.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply
      continuousOn_const)).add
    (((hp.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuous_dLiftL_apply (d : CoframeJet) (k : CoframeFibre) :
    Continuous fun e => dLiftL e d k :=
  continuous_pi fun μ => (continuous_fderiv_metricLiftL'.clm_apply continuous_const).clm_apply
    continuous_const

theorem continuous_liftJetL_apply (d : CoframeJet) : Continuous fun e => liftJetL e d :=
  continuous_pi fun μ => continuous_metricLiftL.clm_apply continuous_const

theorem continuousOn_strongCoeff2 : ContinuousOn (strongCoeff2 FC) coframeGL := by
  refine continuousOn_clm_apply.mpr fun Y' => continuousOn_clm_apply.mpr fun Ψb =>
    continuousOn_clm_apply.mpr fun Ψ => continuousOn_clm_apply.mpr fun T => ?_
  have hp : ContinuousOn (potCoeff FC) coframeGL := (contDiffOn_potCoeff FC (n := 0)).continuousOn
  have hfd : ContinuousOn (fderiv ℝ (potCoeff FC)) coframeGL :=
    (contDiffOn_potCoeff FC (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  have h1 : ContinuousOn (fun e => ιde FC (dLiftL e Y'.1.1 T.e)) coframeGL :=
    ((ιde FC).continuous.comp (continuous_dLiftL_apply Y'.1.1 T.e)).continuousOn
  have h2 : ContinuousOn (fun e => ιde FC (liftJetL e T.de) + ιA FC T.A) coframeGL :=
    (((ιde FC).continuous.comp (continuous_liftJetL_apply T.de)).add continuous_const).continuousOn
  show ContinuousOn (fun e => strongForm2 FC e Y' Ψb Ψ T) coframeGL
  unfold strongForm2
  exact (((((hfd.clm_apply (continuous_metricLiftL.continuousOn.clm_apply continuousOn_const)).clm_apply
    continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const).add
    (((hp.clm_apply h1).clm_apply continuousOn_const).clm_apply continuousOn_const)).add
    (continuousOn_const.mul (((hp.clm_apply h2).clm_apply continuousOn_const).clm_apply
      continuousOn_const)) |>.add
    (((hp.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const)

end CoeffCont

/-! ### Convergence of the fermionic covector pieces -/

section DiracConvergence

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem LpTendsto.prodMk' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {f : ℕ → X → E} {f₀ : X → E} {g : ℕ → X → F} {g₀ : X → F}
    (hf : RenewalGeometry.LpTendsto μ p f f₀) (hg : RenewalGeometry.LpTendsto μ p g g₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => (f n x, g n x)) (fun x => (f₀ x, g₀ x)) := by
  have h := (FirstVariationCalculus.LpTendsto.clm_comp hp (ContinuousLinearMap.inl ℝ E F) hf).add
    (FirstVariationCalculus.LpTendsto.clm_comp hp (ContinuousLinearMap.inr ℝ E F) hg)
  refine h.congr (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp
  · simp

theorem CoframeConv.trilin {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (h : CoframeConv μ Ke e e₀) {V₁ V₂ V₃ W : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] [FiniteDimensional ℝ V₃]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : CoframeFibre → V₁ →L[ℝ] V₂ →L[ℝ] V₃ →L[ℝ] W} (hΦ : ContinuousOn Φ coframeGL)
    {y₁ : ℕ → X → V₁} {y₁₀ : X → V₁} (hy₁ : RenewalGeometry.LpTendsto μ 2 y₁ y₁₀)
    {y₂ : ℕ → X → V₂} {y₂₀ : X → V₂} (hy₂ : RenewalGeometry.LpTendsto μ 2 y₂ y₂₀)
    {y₃ : ℕ → X → V₃} {y₃₀ : X → V₃} (hy₃ : RenewalGeometry.LpTendsto μ 2 y₃ y₃₀)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hy₂4 : ∀ n, eLpNorm (y₂ n) 4 μ ≤ M)
    (hy₃4 : ∀ n, eLpNorm (y₃ n) 4 μ ≤ M) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => Φ (e n x) (y₁ n x) (y₂ n x) (y₃ n x))
      (fun x => Φ (e₀ x) (y₁₀ x) (y₂₀ x) (y₃₀ x)) :=
  FirstVariationCalculus.tendsto_coeff_trilin_critical h.compact (hΦ.mono h.sub) h.mem h.mem₀
    h.tendsto (fun n => aesm_coeff hΦ (h.meas n) (h.memGL n)) hy₁ hy₂ hy₃ hM hy₂4 hy₃4

variable {Ysec : Type} (FC : FermionCarrier Ysec)

/-- **Strong part of the fermionic covector converges in `L¹`**: coframes converging in measure
inside a compact subset of the chart, the potential variable `(∂e, A, 𝓜, s, 𝓜^lin)` in `L²`, and
both spinors strongly in `L²` with uniform `L⁴` bounds. -/
theorem diracStrong_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {Y : ℕ → X → PotVar' FC}
    {Y₀ : X → PotVar' FC} (hY : RenewalGeometry.LpTendsto μ 2 Y Y₀)
    {Ψb Ψ : ℕ → X → SpinorFibre FC.C} {Ψb₀ Ψ₀ : X → SpinorFibre FC.C}
    (hΨb : RenewalGeometry.LpTendsto μ 2 Ψb Ψb₀) (hΨ : RenewalGeometry.LpTendsto μ 2 Ψ Ψ₀)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hΨb4 : ∀ n, eLpNorm (Ψb n) 4 μ ≤ M)
    (hΨ4 : ∀ n, eLpNorm (Ψ n) 4 μ ≤ M) :
    RenewalGeometry.LpTendsto μ 1
      (fun n x => strongCoeff1 FC (e n x) (Y n x) (Ψb n x, Ψ n x) +
        strongCoeff2 FC (e n x) (Y n x) (Ψb n x) (Ψ n x))
      (fun x => strongCoeff1 FC (e₀ x) (Y₀ x) (Ψb₀ x, Ψ₀ x) +
        strongCoeff2 FC (e₀ x) (Y₀ x) (Ψb₀ x) (Ψ₀ x)) :=
  (he.bilin (continuousOn_strongCoeff1 FC) hY (LpTendsto.prodMk' (by norm_num) hΨb hΨ)).add
    (he.trilin (continuousOn_strongCoeff2 FC) hY hΨb hΨ hM hΨb4 hΨ4)

/-- **Weak coefficient converges in `L²`**. -/
theorem diracWeak_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀)
    {Ψb Ψ : ℕ → X → SpinorFibre FC.C} {Ψb₀ Ψ₀ : X → SpinorFibre FC.C}
    (hΨb : RenewalGeometry.LpTendsto μ 2 Ψb Ψb₀) (hΨ : RenewalGeometry.LpTendsto μ 2 Ψ Ψ₀) :
    RenewalGeometry.LpTendsto μ 2 (fun n x => weakCoeff (e n x) ((1 : ℝ), (Ψb n x, Ψ n x)))
      (fun x => weakCoeff (e₀ x) ((1 : ℝ), (Ψb₀ x, Ψ₀ x))) :=
  he.apply continuousOn_weakCoeff (p := 2) (by norm_num)
    (LpTendsto.prodMk' (by norm_num) (FirstVariationCalculus.LpTendsto.const_seq
      (tendsto_const_nhds (x := (1 : ℝ)))) (LpTendsto.prodMk' (by norm_num) hΨb hΨ))

end DiracConvergence

/-! ### Identification of the Dirac and Standard-Model first variations -/

section DiracIdentification

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ} {left : FC.C → Bool}

theorem spinConn_congr {e e' : E4 → CoframeFibre} {x : E4} (he : e =ᶠ[𝓝 x] e') :
    spinConn e x = spinConn e' x := by
  have h1 : ∀ ν b μ, pd (fun y => frameAt (e y) ν b) μ x = pd (fun y => frameAt (e' y) ν b) μ x :=
    fun ν b μ => pd_congr (he.fun_comp fun f => frameAt f ν b) μ
  have h2 : ∀ μ ν i, pd (fun y => metricAt (e y) μ ν) i x = pd (fun y => metricAt (e' y) μ ν) i x :=
    fun μ ν i => pd_congr (he.fun_comp fun f => metricAt f μ ν) i
  have h3 : dMetric e x = dMetric e' x := by
    funext i μ ν; exact h2 μ ν i
  funext μ a b
  simp only [spinConn, christoffelF, h1, h3, he.eq_of_nhds]

/-- The Dirac–Yukawa density is local. -/
theorem diracDensity_congr (θ : CoefficientBank Ysec) {z z' : FieldTuple FC.C} {x : E4}
    (he : z.e =ᶠ[𝓝 x] z'.e) (hA : z.A =ᶠ[𝓝 x] z'.A) (hH : z.H =ᶠ[𝓝 x] z'.H)
    (hΨ : z.Ψ =ᶠ[𝓝 x] z'.Ψ) (hΨb : z.Ψb =ᶠ[𝓝 x] z'.Ψb) :
    diracDensity FC θ z x = diracDensity FC θ z' x := by
  have hs : spinGen z.e x = spinGen z'.e x := by
    funext μ s s'; simp only [spinGen, spinConn_congr he]
  simp only [diracDensity, covDerivSpinor, covDerivCospinor, curvedGamma, hs, he.eq_of_nhds,
    hA.eq_of_nhds, hH.eq_of_nhds, hΨ.eq_of_nhds, hΨb.eq_of_nhds, pd_congr hΨ, pd_congr hΨb]

/-- The Dirac–Yukawa sector density `𝓛_D dV_g`. -/
def diracSectorDensity (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4) : ℝ :=
  diracDensity FC θ z x * volFactor (z.e x)

theorem isLocalDensity_diracSector (θ : CoefficientBank Ysec) :
    IsLocalDensity (diracSectorDensity FC θ) := by
  intro z z' x he hA hH hΨ hΨb
  simp only [diracSectorDensity, diracDensity_congr FC θ he hA hH hΨ hΨb, he.eq_of_nhds]

theorem isLocalDensity_smDensity (θ : CoefficientBank Ysec) :
    IsLocalDensity (smDensity FC θ) := by
  intro z z' x he hA hH hΨ hΨb
  rw [smDensity_eq, smDensity_eq, isLocalDensity_bosonDensity θ z z' x he hA hH hΨ hΨb,
    diracDensity_congr FC θ he hA hH hΨ hΨb, he.eq_of_nhds]

theorem contDiffOn_diracPt (θ : CoefficientBank Ysec) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (diracPt FC θ) (jetGL FC.C) := by
  have hfun : diracPt FC θ = fun R => kinCoeff (πe R) (pU FC R) (pW FC R) +
      potCoeff FC (πe R) (potVarL FC θ R + (0, 0, FC.yukawa θ 0, 1)) (πΨb R) (πΨ R) := by
    funext R
    rw [← potVar_eq]
    rfl
  have hm : MapsTo (fun R : RJet FC.C => πe R) (jetGL FC.C) coframeGL := fun R hR => hR
  have hk := (contDiffOn_kinCoeff (C := FC.C) (n := n)).comp (πe (C := FC.C)).contDiff.contDiffOn hm
  have hp := (contDiffOn_potCoeff FC (n := n)).comp (πe (C := FC.C)).contDiff.contDiffOn hm
  rw [hfun]
  exact ((hk.clm_apply (pU FC).contDiff.contDiffOn).clm_apply (pW FC).contDiff.contDiffOn).add
    (((hp.clm_apply (((potVarL FC θ).contDiff.add contDiff_const).contDiffOn)).clm_apply
      (πΨb (C := FC.C)).contDiff.contDiffOn).clm_apply (πΨ (C := FC.C)).contDiff.contDiffOn)

/-- **First variation of the Dirac–Yukawa action of smooth fields** (complete: metric variation
through the symmetric coframe lift including the spin-connection chain, gauge, Higgs and spinor
variations): `D𝒮_D(z)[v] = ∫_Q diracCov(redJet z)(testJet v)`. -/
theorem diracVariation_eq_cov (θ : CoefficientBank Ysec) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁)
    {r : ℕ} (z : SmoothFields T left) (v : CrTest left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    actionVariation T (diracSectorDensity FC θ) z.z (variationDirection z.z v.val) =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
        diracCov FC θ (redJet z.z x) (testJet v.val x) :=
  actionVariation_eq_cov h0 h01 h1 hK z v hKe hKGL hzK (isLocalDensity_diracSector FC θ)
    (contDiffOn_diracPt FC θ)
    (fun z' x he _ _ _ _ hx => diracDensity_mul_vol FC θ z' x he hx)
    (fun R hR T' => fderiv_diracPt_redVar FC θ hR T')

/-- The Standard-Model jet density `bosonPt + diracPt`. -/
def smPt (θ : CoefficientBank Ysec) (R : RJet FC.C) : ℝ := bosonPt θ R + diracPt FC θ R

/-- **First variation of the complete Standard-Model sector of smooth fields**:
`D𝒮_{SM,θ}(z)[v] = ∫_Q (bosonCov + diracCov)(redJet z)(testJet v)`. -/
theorem smVariation_eq_cov (θ : CoefficientBank Ysec) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁)
    {r : ℕ} (z : SmoothFields T left) (v : CrTest left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    firstVariation T FC θ .standardModel z.z v.val =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
        (bosonCov θ (redJet z.z x) + diracCov FC θ (redJet z.z x)) (testJet v.val x) := by
  show actionVariation T (smDensity FC θ) z.z (variationDirection z.z v.val) = _
  refine actionVariation_eq_cov h0 h01 h1 hK z v hKe hKGL hzK (isLocalDensity_smDensity FC θ)
    (G := smPt FC θ) (Cov := fun R => bosonCov θ R + diracCov FC θ R) ((contDiffOn_bosonPt θ).add (contDiffOn_diracPt FC θ))
    (fun z' x he _ _ _ _ hx => ?_) (fun R hR T' => ?_)
  · rw [smDensity_eq, diracDensity_mul_vol FC θ z' x he hx]
    exact congrArg (· + _) (bosonDensity_eq_bosonPt θ z' x)
  · have hb := hasFDerivAt_bosonPt θ hR
    have hd := hasFDerivAt_diracPt FC θ hR
    rw [show smPt FC θ = fun R => bosonPt θ R + diracPt FC θ R from rfl,
      fderiv_fun_add hb.1 hd.1, ContinuousLinearMap.add_apply, hb.2, ← bosonCov_apply,
      fderiv_diracPt_redVar FC θ hR, ContinuousLinearMap.add_apply]

end DiracIdentification

/-! ### Weak `L²` convergence of vector fields -/

section WeakL2

open FirstVariationCalculus

variable {a b : E4}

theorem clm_complex_eq (ℓ : ℂ →L[ℝ] ℝ) (w : ℂ) : ℓ w = ℓ 1 * w.re + ℓ Complex.I * w.im := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Weak `L²` convergence of complex fields from convergence of the complex pairings. -/
theorem weakL2_complex {W : ℕ → E4 → ℂ} {W₀ : E4 → ℂ}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b)))
    (h : ∀ g : E4 → ℂ, MemLp g 2 (volume.restrict (box a b)) →
      Tendsto (fun n => ∫ x, g x * W n x ∂(volume.restrict (box a b))) atTop
        (𝓝 (∫ x, g x * W₀ x ∂(volume.restrict (box a b))))) :
    WeakL2Tendsto a b W W₀ := by
  intro ℓ g hg
  have hgc : MemLp (fun x => ((g x : ℝ) : ℂ)) 2 (volume.restrict (box a b)) := hg.ofReal
  have key : ∀ V : E4 → ℂ, MemLp V 2 (volume.restrict (box a b)) →
      ∫ x, g x * ℓ (V x) ∂(volume.restrict (box a b)) =
        ℓ 1 * (∫ x, ((g x : ℝ) : ℂ) * V x ∂(volume.restrict (box a b))).re +
          ℓ Complex.I * (∫ x, ((g x : ℝ) : ℂ) * V x ∂(volume.restrict (box a b))).im := by
    intro V hV
    have hint : Integrable (fun x => ((g x : ℝ) : ℂ) * V x) (volume.restrict (box a b)) :=
      hgc.integrable_mul hV
    have hre := integral_re hint
    have him := integral_im hint
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul] at hre him
    have hi1 : Integrable (fun x => g x * (V x).re) (volume.restrict (box a b)) :=
      hint.re.congr (Eventually.of_forall fun x => by simp [Complex.re_ofReal_mul])
    have hi2 : Integrable (fun x => g x * (V x).im) (volume.restrict (box a b)) :=
      hint.im.congr (Eventually.of_forall fun x => by simp [Complex.im_ofReal_mul])
    rw [← hre, ← him, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi1.const_mul _) (hi2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [clm_complex_eq ℓ (V x)]
    ring
  simp only [key _ (hW _), key _ hW₀]
  exact ((tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp (h _ hgc))).add
    (tendsto_const_nhds.mul ((Complex.continuous_im.tendsto _).comp (h _ hgc))))

/-- Weak `L²` convergence is preserved by continuous linear maps. -/
theorem WeakL2Tendsto.clm_comp {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] {W : ℕ → E4 → V} {W₀ : E4 → V}
    (h : WeakL2Tendsto a b W W₀) (L : V →L[ℝ] V') :
    WeakL2Tendsto a b (fun n x => L (W n x)) (fun x => L (W₀ x)) :=
  fun ℓ g hg => h (ℓ.comp L) g hg

theorem integrable_mul_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure E4} {g : E4 → ℝ} (hg : MemLp g 2 μ) (ℓ : V →L[ℝ] ℝ) {f : E4 → V}
    (hf : MemLp f 2 μ) : Integrable (fun x => g x * ℓ (f x)) μ :=
  hg.integrable_mul (ℓ.comp_memLp' hf)

/-- Weak `L²` convergence of `Π`-valued fields from that of the components. -/
theorem weakL2_pi {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {W : ℕ → E4 → ι → V} {W₀ : E4 → ι → V}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b)))
    (h : ∀ i, WeakL2Tendsto a b (fun n x => W n x i) (fun x => W₀ x i)) :
    WeakL2Tendsto a b W W₀ := by
  classical
  intro ℓ g hg
  have key : ∀ V' : E4 → ι → V, MemLp V' 2 (volume.restrict (box a b)) →
      ∫ x, g x * ℓ (V' x) ∂(volume.restrict (box a b)) =
        ∑ i, ∫ x, g x * (ℓ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => V) i)) (V' x i)
          ∂(volume.restrict (box a b)) := by
    intro V' hV'
    rw [← integral_finsetSum _ fun i _ => integrable_mul_clm hg
      (ℓ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => V) i)) (memLp_pi_iff.mp hV' i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [← Finset.mul_sum, ContinuousLinearMap.sum_comp_single]
  simp only [key _ (hW _), key _ hW₀]
  exact tendsto_finsetSum _ fun i _ => h i _ g hg

/-- Weak `L²` convergence of pairs from that of the components. -/
theorem weakL2_prod {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] {W : ℕ → E4 → V} {W₀ : E4 → V}
    {W' : ℕ → E4 → V'} {W'₀ : E4 → V'}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b)))
    (hW' : ∀ n, MemLp (W' n) 2 (volume.restrict (box a b)))
    (hW'₀ : MemLp W'₀ 2 (volume.restrict (box a b)))
    (h : WeakL2Tendsto a b W W₀) (h' : WeakL2Tendsto a b W' W'₀) :
    WeakL2Tendsto a b (fun n x => (W n x, W' n x)) (fun x => (W₀ x, W'₀ x)) := by
  intro ℓ g hg
  have key : ∀ (U : E4 → V) (U' : E4 → V'), MemLp U 2 (volume.restrict (box a b)) →
      MemLp U' 2 (volume.restrict (box a b)) →
      ∫ x, g x * ℓ (U x, U' x) ∂(volume.restrict (box a b)) =
        ∫ x, g x * (ℓ.comp (ContinuousLinearMap.inl ℝ V V')) (U x) ∂(volume.restrict (box a b)) +
          ∫ x, g x * (ℓ.comp (ContinuousLinearMap.inr ℝ V V')) (U' x)
            ∂(volume.restrict (box a b)) := by
    intro U U' hU hU'
    rw [← integral_add (integrable_mul_clm hg _ hU) (integrable_mul_clm hg _ hU')]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, ← mul_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simp only [key _ _ (hW _) (hW' _), key _ _ hW₀ hW'₀]
  exact (h _ g hg).add (h' _ g hg)

end WeakL2

/-! ### Spinor data on a chart box from weak `H¹` convergence -/

section SpinorChart

variable {T : ℝ} {C : Type} [Fintype C]

theorem norm_uncurry {α β F : Type*} [Fintype α] [Fintype β] [SeminormedAddCommGroup F]
    (f : α → β → F) : ‖(fun p : α × β => f p.1 p.2)‖ = ‖f‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun p =>
    (norm_le_pi_norm (f p.1) p.2).trans (norm_le_pi_norm f p.1)) ?_
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j =>
      norm_le_pi_norm (fun p : α × β => f p.1 p.2) (i, j)

/-- Currying `(Fin 4 × C → ℂ) → (Fin 4 → C → ℂ)`. -/
def curryL (C : Type) [Fintype C] : (Fin 4 × C → ℂ) →L[ℝ] SpinorFibre C :=
  ContinuousLinearMap.pi fun s => ContinuousLinearMap.pi fun c =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 × C => ℂ) (s, c)

/-- Currying of gradient packets. -/
def gradCurryL (C : Type) [Fintype C] :
    (Fin 4 → Fin 4 × C → ℂ) →L[ℝ] (Fin 4 → SpinorFibre C) :=
  ContinuousLinearMap.pi fun i => (curryL C).comp (ContinuousLinearMap.proj i)

theorem w12Norm_le_of_h1 (Q : ChartBox T) {u : E4 → Fin 4 × C → ℂ}
    {g : E4 → Fin 4 → Fin 4 × C → ℂ} (p : Fin 4 × C) :
    SobolevOpen.w12Norm Q.set (fun x => u x p) (fun i x => g x i p) ≤
      h1Norm Q u g + 4 * h1Norm Q u g := by
  unfold SobolevOpen.w12Norm h1Norm
  gcongr
  · exact (eLpNorm_apply_le u p 2).trans le_self_add
  · calc ∑ i, eLpNorm (fun x => g x i p) 2 Q.μ ≤ ∑ _i : Fin 4, (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) :=
          Finset.sum_le_sum fun i _ => ((eLpNorm_apply_le (fun x => g x i) p 2).trans
            (eLpNorm_apply_le g i 2)).trans le_add_self
      _ = 4 * (eLpNorm u 2 Q.μ + eLpNorm g 2 Q.μ) := by simp [mul_add]

/-- **Spinor data on a chart box** from weak `H¹(Q)` convergence `u_h ⇀ u`: strong `L²`
convergence (Rellich), uniform `L⁴` bounds (Sobolev), and weak `L²` convergence of the gradient
packets with uniform `L²` bounds. -/
theorem spinor_chart_data (Q : ChartBox T) {u : ℕ → E4 → SpinorFibre C}
    {g : ℕ → E4 → Fin 4 → Fin 4 × C → ℂ} {u₀ : E4 → SpinorFibre C}
    {g₀ : E4 → Fin 4 → Fin 4 × C → ℂ}
    (hw : WeakH1Tendsto Q (fun n => spinorC (u n)) g (spinorC u₀) g₀) :
    RenewalGeometry.LpTendsto Q.μ 2 u u₀ ∧
      (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, eLpNorm (u n) 4 Q.μ ≤ M) ∧
      (∀ n, MemLp (g n) 2 Q.μ) ∧ MemLp g₀ 2 Q.μ ∧
      (∃ B : ℝ, ∀ n, (eLpNorm (g n) 2 Q.μ).toReal ≤ B) ∧
      FirstVariationCalculus.WeakL2Tendsto Q.a Q.b g g₀ := by
  obtain ⟨hmem, hmem₀, ⟨B, hBt, hB⟩, hpair, hgpair⟩ := hw
  set B' := B + 4 * B with hB'
  have hB't : B' ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hBt, ENNReal.mul_ne_top (by simp) hBt⟩
  have hw12 : ∀ n p, SobolevOpen.w12Norm Q.set (fun x => u n x p.1 p.2) (fun i x => g n x i p) ≤
      B' := fun n p => (w12Norm_le_of_h1 Q (u := spinorC (u n)) p).trans
    (add_le_add (hB n) (by gcongr; exact hB n))
  -- Rellich, componentwise
  have hL2c : ∀ p : Fin 4 × C, Tendsto (fun n => eLpNorm (fun x => spinorC (u n) x p -
      spinorC u₀ x p) 2 Q.μ) atTop (𝓝 0) := fun p =>
    SobolevOpen.tendsto_L2_box_of_weak Q.lt (fun n x => u n x p.1 p.2)
      (fun n i x => g n x i p) (fun x => u₀ x p.1 p.2) (fun n => hmem n p) hB't
      (fun n => hw12 n p) (hmem₀ p).memLp (fun φ hφ => hpair φ hφ p)
  have hmemC : ∀ n, MemLp (spinorC (u n)) 2 Q.μ := fun n =>
    memLp_pi_iff.mpr fun p => (hmem n p).memLp
  have hmemC₀ : MemLp (spinorC u₀) 2 Q.μ := memLp_pi_iff.mpr fun p => (hmem₀ p).memLp
  have hLC : RenewalGeometry.LpTendsto Q.μ 2 (fun n => spinorC (u n)) (spinorC u₀) :=
    ⟨hmemC, hmemC₀, tendsto_eLpNorm_of_apply (by norm_num)
      (fun n p => ((hmem n p).memLp.1.sub (hmem₀ p).memLp.1)) hL2c⟩
  refine ⟨FirstVariationCalculus.LpTendsto.clm_comp (by norm_num) (curryL C) hLC, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- Sobolev `L⁴` bounds
    obtain ⟨Cs, hCs⟩ := SobolevOpen.exists_sobolev_L4_box (ι := Fin 4) (by simp) Q.lt
    refine ⟨∑ _p : Fin 4 × C, (Cs : ℝ≥0∞) * B', ENNReal.sum_ne_top.mpr fun _ _ =>
      ENNReal.mul_ne_top ENNReal.coe_ne_top hB't, fun n => ?_⟩
    have he : eLpNorm (u n) 4 Q.μ = eLpNorm (spinorC (u n)) 4 Q.μ :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_uncurry (u n x)).symm)
    rw [he]
    refine (eLpNorm_le_sum_apply (by norm_num) fun p => (hmem n p).memLp.1).trans
      (Finset.sum_le_sum fun p _ => ?_)
    exact (hCs _ _ (hmem n p)).trans (by gcongr; exact hw12 n p)
  · exact fun n => memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => (hmem n p).memLp_grad i
  · exact memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => (hmem₀ p).memLp_grad i
  · refine ⟨B.toReal, fun n => ENNReal.toReal_mono hBt ?_⟩
    exact le_add_self.trans (hB n)
  · -- weak `L²` convergence of the gradient packets
    have hgm : ∀ n i p, MemLp (fun x => g n x i p) 2 Q.μ := fun n i p => (hmem n p).memLp_grad i
    have hgm₀ : ∀ i p, MemLp (fun x => g₀ x i p) 2 Q.μ := fun i p => (hmem₀ p).memLp_grad i
    refine weakL2_pi (fun n => memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => hgm n i p)
      (memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun p => hgm₀ i p) fun i => ?_
    refine weakL2_pi (fun n => memLp_pi_iff.mpr fun p => hgm n i p)
      (memLp_pi_iff.mpr fun p => hgm₀ i p) fun p => ?_
    refine weakL2_complex (fun n => hgm n i p) (hgm₀ i p) fun φ hφ => ?_
    refine FirstVariationCalculus.tendsto_integral_of_weak (fun n => hgm n i p) (hgm₀ i p)
      (B := (B + 4 * B).toReal) (fun n => ENNReal.toReal_mono hB't
        (((eLpNorm_apply_le (fun x => g n x i) p 2).trans (eLpNorm_apply_le (g n) i 2)).trans
          (le_add_self.trans ((hB n).trans le_self_add)))) (fun ψ hψ => hgpair ψ hψ i p) hφ

end SpinorChart

/-! ### Assembly in the dual test norm -/

section DualAssembly

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}

theorem πτ_testJet (v : FieldTuple C) (x : E4) :
    πτ (testJet v x) = (v.e x, v.Ψb x, v.Ψ x) := rfl

theorem norm_πτ_testJet_le (v : CrTest left r K) (x : E4) : ‖πτ (testJet v.val x)‖ ≤ ‖v‖ := by
  rw [πτ_testJet]
  refine norm_prod_le_iff.mpr ⟨(norm_le_crNorm (isCylTest_e v) r x).trans (crNorm_e_le v),
    norm_prod_le_iff.mpr ⟨(norm_le_crNorm (isCylTest_Ψb v) r x).trans (crNorm_Ψb_le v),
      (norm_le_crNorm (isCylTest_Ψ v) r x).trans (crNorm_Ψ_le v)⟩⟩

theorem lipschitz_πτ_testJet (hr : 1 ≤ r) (v : CrTest left r K) (x y : E4) :
    ‖πτ (testJet v.val x) - πτ (testJet v.val y)‖ ≤ ‖v‖ * ‖x - y‖ := by
  rw [πτ_testJet, πτ_testJet, Prod.mk_sub_mk, Prod.mk_sub_mk]
  exact norm_prod_le_iff.mpr ⟨lipschitz_test_e hr v x y,
    norm_prod_le_iff.mpr ⟨lipschitz_test_Ψb hr v x y, lipschitz_test_Ψ hr v x y⟩⟩

theorem continuous_πτ_testJet (v : CrTest left r K) : Continuous fun x => πτ (testJet v.val x) :=
  (πτ (C := C)).continuous.comp (continuous_testJet v)

theorem integrable_clm_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure E4} {Λ : E4 → V →L[ℝ] ℝ} (hΛ : MemLp Λ 1 μ) {τ : E4 → V} (hτ : Continuous τ)
    {c : ℝ} (hc : ∀ x, ‖τ x‖ ≤ c) : Integrable (fun x => Λ x (τ x)) μ := by
  refine Integrable.mono' ((memLp_one_iff_integrable.mp hΛ).norm.mul_const c)
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : V →L[ℝ] ℝ) (t : V) => L t)
      (by fun_prop) hΛ.1 hτ.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  exact ((Λ x).le_opNorm (τ x)).trans (mul_le_mul_of_nonneg_left (hc x) (norm_nonneg _))

theorem integrable_bilin_apply {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] {μ : Measure E4}
    {Ω : E4 → V →L[ℝ] V' →L[ℝ] ℝ} (hΩ : MemLp Ω 2 μ) {τ : E4 → V} (hτ : Continuous τ)
    {c : ℝ} (hc : ∀ x, ‖τ x‖ ≤ c) {W : E4 → V'} (hW : MemLp W 2 μ) :
    Integrable (fun x => Ω x (τ x) (W x)) μ := by
  have h1 : AEStronglyMeasurable (fun x => Ω x (τ x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : V →L[ℝ] V' →L[ℝ] ℝ) (t : V) => L t)
      (by fun_prop) hΩ.1 hτ.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun x => Ω x (τ x) (W x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : V' →L[ℝ] ℝ) (t : V') => L t)
      (by fun_prop) h1 hW.1
  refine Integrable.mono' ((hΩ.norm.integrable_mul hW.norm).mul_const c) h2
    (Eventually.of_forall fun x => ?_)
  calc ‖Ω x (τ x) (W x)‖ ≤ ‖Ω x (τ x)‖ * ‖W x‖ := (Ω x (τ x)).le_opNorm (W x)
    _ ≤ ‖Ω x‖ * ‖τ x‖ * ‖W x‖ := by gcongr; exact (Ω x).le_opNorm (τ x)
    _ ≤ ‖Ω x‖ * c * ‖W x‖ := by gcongr; exact hc x
    _ = ‖Ω x‖ * ‖W x‖ * c := by ring

/-- **Dual-norm convergence of weak–strong pairings** (`r ≥ 1`): if `Ω_n → Ω` in `L²(Q)` and
`W_n ⇀ W` weakly in `L²(Q)` with uniform bounds, then
`v ↦ ∫_Q Ω_n(τ(v))(W_n)` converges in `(𝒱_K^r)^*`, where `τ(v) = (k, η̄, η)` are the test values
(finite-net argument on the `C¹` unit ball, `uniform_weak_strong_op`). -/
theorem dual_tendsto_weak (hr : 1 ≤ r) (Q : ChartBox T)
    {Ω : ℕ → E4 → TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ}
    {Ω₀ : E4 → TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ}
    (hΩ : RenewalGeometry.LpTendsto Q.μ 2 Ω Ω₀) {W : ℕ → E4 → GradVal C} {W₀ : E4 → GradVal C}
    (hW : ∀ n, MemLp (W n) 2 Q.μ) (hW₀ : MemLp W₀ 2 Q.μ) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 Q.μ).toReal ≤ B)
    (hweak : FirstVariationCalculus.WeakL2Tendsto Q.a Q.b W W₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |(∫ x in Q.set, Ω n x (πτ (testJet v.val x)) (W n x)) -
        ∫ x in Q.set, Ω₀ x (πτ (testJet v.val x)) (W₀ x)| ≤ ε * ‖v‖ := by
  filter_upwards [FirstVariationCalculus.uniform_weak_strong_op hΩ hW hW₀ hWB hweak 1 hε]
    with n hn v
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · have h' : ∀ x, πτ (testJet v.val x) = 0 := fun x =>
      norm_le_zero_iff.mp ((norm_πτ_testJet_le v x).trans h0.symm.le)
    simp [h', ← h0]
  · have hτc : Continuous fun x => ‖v‖⁻¹ • πτ (testJet v.val x) := by
      have := continuous_πτ_testJet v
      fun_prop
    have hτ1 : ∀ x, ‖‖v‖⁻¹ • πτ (testJet v.val x)‖ ≤ 1 := fun x => by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, mul_one]
      exact norm_πτ_testJet_le v x
    have hτL : ∀ x y, ‖‖v‖⁻¹ • πτ (testJet v.val x) - ‖v‖⁻¹ • πτ (testJet v.val y)‖ ≤
        1 * ‖x - y‖ := fun x y => by
      rw [← smul_sub, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, one_mul]
      exact lipschitz_πτ_testJet hr v x y
    have h2 := hn _ hτc hτ1 hτL
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, integral_const_mul,
      ← mul_sub, abs_mul, abs_inv, abs_norm] at h2
    rw [inv_mul_le_iff₀ hpos, mul_comm] at h2
    simpa only [ChartBox.set] using h2

/-- **Assembly**: a covector split into an `L¹`-convergent part and a weak–strong pairing
converges in the dual norm of `𝒱_K^r`. -/
theorem dual_tendsto_split (hr : 1 ≤ r) (Q : ChartBox T) {Λ : ℕ → E4 → RJet C →L[ℝ] ℝ}
    {Λ₀ : E4 → RJet C →L[ℝ] ℝ} (hΛ : RenewalGeometry.LpTendsto Q.μ 1 Λ Λ₀)
    {Ω : ℕ → E4 → TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ}
    {Ω₀ : E4 → TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ}
    (hΩ : RenewalGeometry.LpTendsto Q.μ 2 Ω Ω₀) {W : ℕ → E4 → GradVal C} {W₀ : E4 → GradVal C}
    (hW : ∀ n, MemLp (W n) 2 Q.μ) (hW₀ : MemLp W₀ 2 Q.μ) {B : ℝ}
    (hWB : ∀ n, (eLpNorm (W n) 2 Q.μ).toReal ≤ B)
    (hweak : FirstVariationCalculus.WeakL2Tendsto Q.a Q.b W W₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |(∫ x in Q.set, (Λ n x (testJet v.val x) + Ω n x (πτ (testJet v.val x)) (W n x))) -
        ∫ x in Q.set, (Λ₀ x (testJet v.val x) + Ω₀ x (πτ (testJet v.val x)) (W₀ x))| ≤
        ε * ‖v‖ := by
  filter_upwards [dual_tendsto_of_L1 (left := left) (K := K) hr hΛ (half_pos hε),
    dual_tendsto_weak (left := left) (K := K) hr Q hΩ hW hW₀ hWB hweak (half_pos hε)]
    with n h1 h2 v
  have hb := fun x => norm_testJet_le hr v x
  have hτb := norm_πτ_testJet_le v
  rw [integral_add (integrable_clm_apply (μ := volume.restrict Q.set) (hΛ.memLp n)
      (continuous_testJet v) hb)
      (integrable_bilin_apply (μ := volume.restrict Q.set) (hΩ.memLp n) (continuous_πτ_testJet v)
        hτb (hW n)),
    integral_add (integrable_clm_apply (μ := volume.restrict Q.set) hΛ.memLp_lim
      (continuous_testJet v) hb)
      (integrable_bilin_apply (μ := volume.restrict Q.set) hΩ.memLp_lim (continuous_πτ_testJet v)
        hτb hW₀)]
  have e : ∀ a b c d : ℝ, (a + c) - (b + d) = (a - b) + (c - d) := fun _ _ _ _ => by ring
  rw [e]
  exact (abs_add_le _ _).trans ((add_le_add (h1 v) (h2 v)).trans_eq (by ring))

end DualAssembly

/-! ### `prop:weak-fermion` and the Standard-Model sector of `prop:reduced-continuity` -/

section DiracMain

theorem LpTendsto.clm_seq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] {Lₙ : ℕ → V →L[ℝ] V'} {L₀ : V →L[ℝ] V'} (hL : Tendsto Lₙ atTop (𝓝 L₀))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {y : ℕ → X → V} {y₀ : X → V}
    (hy : RenewalGeometry.LpTendsto μ p y y₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => Lₙ n (y n x)) (fun x => L₀ (y₀ x)) :=
  FirstVariationCalculus.tendsto_coeff_apply (Φ := fun L : V →L[ℝ] V' => L)
    hL.isCompact_insert_range continuousOn_id (z := fun n _ => Lₙ n) (z₀ := fun _ => L₀)
    (fun n => ae_of_all _ fun _ => mem_insert_of_mem _ (mem_range_self n))
    (ae_of_all _ fun _ => mem_insert _ _)
    (tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => hL))
    (fun n => aestronglyMeasurable_const) hp hy

theorem memLp_prodMk {X : Type*} [MeasurableSpace X] {μ : Measure X} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : X → E} {g : X → F} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (fun x => (f x, g x)) p μ := by
  have h := ((ContinuousLinearMap.inl ℝ E F).comp_memLp' hf).add
    ((ContinuousLinearMap.inr ℝ E F).comp_memLp' hg)
  refine h.ae_eq (Eventually.of_forall fun x => ?_)
  simp

theorem norm_gradCurryL_le {C : Type} [Fintype C] (w : Fin 4 → Fin 4 × C → ℂ) :
    ‖gradCurryL C w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i => ?_
  have : gradCurryL C w i = fun s c => w i (s, c) := rfl
  rw [this, ← norm_uncurry (fun s c => w i (s, c))]
  exact norm_le_pi_norm w i

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ} {left : FC.C → Bool}

/-- The first variation of the Dirac–Yukawa action at limit fields, defined by the covector
formula of smooth fields (`diracVariation_eq_cov`). -/
def diracLimitVariation (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    {r : ℕ} {K : CylRegion T} (v : CrTest left r K) : ℝ :=
  ∫ x in Q.set, diracCov FC θ (limitJet L x) (testJet v.val x)

theorem diracCov_apply (θ : CoefficientBank Ysec) (R T' : RJet FC.C) :
    diracCov FC θ R T' =
      (strongCoeff1 FC R.e (potVar' FC θ R) (pU FC R) +
        strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ) T' +
      weakCoeff R.e ((1 : ℝ), pU FC R) (πτ T') (pW FC R) := rfl

/-- The strong part of the fermionic covector in terms of field values. -/
def diracStrongField (θ : CoefficientBank Ysec) (e : CoframeFibre) (de : CoframeJet)
    (A : ConnFibre) (H : HiggsFibre) (Ψb Ψ : SpinorFibre FC.C) : RJet FC.C →L[ℝ] ℝ :=
  strongCoeff1 FC e ((de, A, FC.yukawa θ H, 1), yukL FC θ) (Ψb, Ψ) +
    strongCoeff2 FC e ((de, A, FC.yukawa θ H, 1), yukL FC θ) Ψb Ψ

/-- The weak coefficient in terms of field values. -/
def diracWeakField (e : CoframeFibre) (Ψb Ψ : SpinorFibre FC.C) :
    TestVal FC.C →L[ℝ] GradVal FC.C →L[ℝ] ℝ :=
  weakCoeff e ((1 : ℝ), (Ψb, Ψ))

theorem gradCurryL_apply {C : Type} [Fintype C] (w : Fin 4 → Fin 4 × C → ℂ) :
    gradCurryL C w = fun i s c => w i (s, c) := rfl

theorem diracCov_eq (θ : CoefficientBank Ysec) (R T' : RJet FC.C) :
    diracCov FC θ R T' = diracStrongField FC θ R.e R.de R.A R.H R.Ψb R.Ψ T' +
      diracWeakField FC R.e R.Ψb R.Ψ (πτ T') (R.dΨ, R.dΨb) := by
  rw [diracCov_apply]
  simp only [pU, pW, ContinuousLinearMap.prod_apply, πΨb_apply, πΨ_apply, πdΨ_apply, πdΨb_apply]
  rfl

theorem diracCov_redJet (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4)
    (T' : RJet FC.C) :
    diracCov FC θ (redJet z x) T' =
      diracStrongField FC θ (z.e x) (fun i => pd z.e i x) (z.A x) (z.H x) (z.Ψb x) (z.Ψ x) T' +
      diracWeakField FC (z.e x) (z.Ψb x) (z.Ψ x) (πτ T')
        (gradCurryL FC.C (spinorGrad z.Ψ x), gradCurryL FC.C (spinorGrad z.Ψb x)) := by
  rw [diracCov_eq]
  rfl

theorem diracCov_limitJet (θ : CoefficientBank Ysec) (L : LimitFields FC.C) (x : E4)
    (T' : RJet FC.C) :
    diracCov FC θ (limitJet L x) T' =
      diracStrongField FC θ (L.e x) (toJet (reJet L.de x)) (L.A x) (L.H x) (L.Ψb x) (L.Ψ x) T' +
      diracWeakField FC (L.e x) (L.Ψb x) (L.Ψ x) (πτ T')
        (gradCurryL FC.C (L.dΨ x), gradCurryL FC.C (L.dΨb x)) := by
  rw [diracCov_eq]
  rfl

/-- **The fermionic covector data under the `prop:weak-fermion` hypotheses** on the slab box:
the strong part converges in `L¹`, the weak coefficient in `L²`, and the spinor gradients
converge weakly in `L²` with uniform bounds. -/
theorem dirac_data {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C} {Ke : Set CoframeFibre} (hKe : IsCompactCoframeSet Ke)
    (hzKe : ∀ n, ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, (z n).z.e x ∈ Ke)
    (hLKe : ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, L.e x ∈ Ke)
    (hemem : MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (coframeC L.e) L.de)
    (het : H1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => coframeC (z n).z.e)
      (fun n => coframeGrad (z n).z.e) (coframeC L.e) L.de)
    (hAmem : MemLp L.A 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hAt : LpTendsto 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.A) L.A)
    (hHmem : MemLp L.H 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hHt : LpTendsto 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.H) L.H)
    (hΨ : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψ)
      (fun n => spinorGrad (z n).z.Ψ) (spinorC L.Ψ) L.dΨ)
    (hΨb : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψb)
      (fun n => spinorGrad (z n).z.Ψb) (spinorC L.Ψb) L.dΨb)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0))) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
      (fun n x => diracStrongField FC (θ n) ((z n).z.e x) (fun i => pd (z n).z.e i x)
        ((z n).z.A x) ((z n).z.H x) ((z n).z.Ψb x) ((z n).z.Ψ x))
      (fun x => diracStrongField FC θ₀ (L.e x) (toJet (reJet L.de x)) (L.A x) (L.H x)
        (L.Ψb x) (L.Ψ x)) ∧
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2
      (fun n x => diracWeakField FC ((z n).z.e x) ((z n).z.Ψb x) ((z n).z.Ψ x))
      (fun x => diracWeakField FC (L.e x) (L.Ψb x) (L.Ψ x)) ∧
    (∀ n, MemLp (fun x => (gradCurryL FC.C (spinorGrad (z n).z.Ψ x),
      gradCurryL FC.C (spinorGrad (z n).z.Ψb x))) 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ) ∧
    MemLp (fun x => (gradCurryL FC.C (L.dΨ x), gradCurryL FC.C (L.dΨb x))) 2
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ ∧
    (∃ B : ℝ, ∀ n, (eLpNorm (fun x => (gradCurryL FC.C (spinorGrad (z n).z.Ψ x),
      gradCurryL FC.C (spinorGrad (z n).z.Ψb x))) 2
        (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ).toReal ≤ B) ∧
    FirstVariationCalculus.WeakL2Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).a
      (slabChart t₀ t₁ h0 h01 h1 (T := T)).b
      (fun n x => (gradCurryL FC.C (spinorGrad (z n).z.Ψ x),
        gradCurryL FC.C (spinorGrad (z n).z.Ψb x)))
      (fun x => (gradCurryL FC.C (L.dΨ x), gradCurryL FC.C (L.dΨb x))) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  obtain ⟨-, hmem, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hemem het
  have he' : CoframeConv Q.μ Ke (fun n x => (z n).z.e x) (fun x => L.e x) := he
  have hmemLp : ∀ {F : Type} [NormedAddCommGroup F] {f : E4 → F} (p : ℝ≥0∞),
      ContinuousOn f (cylSlab T) → MemLp f p Q.μ := fun p hf =>
    memLp_of_continuousOn_closure hO hc (hf.mono hclS) p
  -- the potential variable `(∂e, A, 𝓜_Y(H), 1, 𝓜_Y^lin)`
  have hde : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => fun i => pd (z n).z.e i x)
      (fun x => toJet (reJet L.de x)) :=
    (coframeJet_L2_tendsto hmem hemem het).congr
      (fun n => Eventually.of_forall fun x => toJet_reJet_coframeGrad x)
      (Eventually.of_forall fun x => rfl)
  have hA2 : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (z n).z.A x) L.A :=
    ⟨fun n => hmemLp 2 (z n).smooth_A.continuousOn, hAmem, hAt⟩
  have hH2 : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (z n).z.H x) L.H :=
    ⟨fun n => hmemLp 2 (z n).smooth_H.continuousOn, hHmem, hHt⟩
  have hM : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => FC.yukawa (θ n) ((z n).z.H x))
      (fun x => FC.yukawa θ₀ (L.H x)) := by
    have h := (LpTendsto.clm_seq hyL (by norm_num) hH2).add
      (FirstVariationCalculus.LpTendsto.const_seq (μ := Q.μ) (p := 2) hy0)
    refine h.congr (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (yukawa_eq FC (θ n) _).symm
    · exact (yukawa_eq FC θ₀ _).symm
  have hY : RenewalGeometry.LpTendsto Q.μ 2
      (fun n x => (((fun i => pd (z n).z.e i x, (z n).z.A x, FC.yukawa (θ n) ((z n).z.H x),
        (1 : ℝ)), yukL FC (θ n)) : PotVar' FC))
      (fun x => (((toJet (reJet L.de x), L.A x, FC.yukawa θ₀ (L.H x), (1 : ℝ)), yukL FC θ₀) :
        PotVar' FC)) :=
    LpTendsto.prodMk' (by norm_num) (LpTendsto.prodMk' (by norm_num) hde
      (LpTendsto.prodMk' (by norm_num) hA2 (LpTendsto.prodMk' (by norm_num) hM
        (FirstVariationCalculus.LpTendsto.const_seq (tendsto_const_nhds (x := (1 : ℝ)))))))
      (FirstVariationCalculus.LpTendsto.const_seq hyL)
  -- the spinors
  obtain ⟨hΨ2, ⟨MΨ, hMΨt, hMΨ⟩, hgΨ, hgΨ₀, ⟨BΨ, hBΨ⟩, hwΨ⟩ := spinor_chart_data Q hΨ
  obtain ⟨hΨb2, ⟨MΨb, hMΨbt, hMΨb⟩, hgΨb, hgΨb₀, ⟨BΨb, hBΨb⟩, hwΨb⟩ := spinor_chart_data Q hΨb
  have hΨ2' : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (z n).z.Ψ x) L.Ψ := hΨ2
  have hΨb2' : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (z n).z.Ψb x) L.Ψb := hΨb2
  have hstrong := diracStrong_tendsto FC he' hY hΨb2' hΨ2' (M := MΨ + MΨb)
    (ENNReal.add_ne_top.mpr ⟨hMΨt, hMΨbt⟩) (fun n => (hMΨb n).trans le_add_self)
    (fun n => (hMΨ n).trans le_self_add)
  have hweak := diracWeak_tendsto FC he' hΨb2' hΨ2'
  -- the spinor gradients
  have hW1 : ∀ n, MemLp (fun x => gradCurryL FC.C (spinorGrad (z n).z.Ψ x)) 2 Q.μ := fun n =>
    (gradCurryL FC.C).comp_memLp' (hgΨ n)
  have hW2 : ∀ n, MemLp (fun x => gradCurryL FC.C (spinorGrad (z n).z.Ψb x)) 2 Q.μ := fun n =>
    (gradCurryL FC.C).comp_memLp' (hgΨb n)
  have hW1₀ : MemLp (fun x => gradCurryL FC.C (L.dΨ x)) 2 Q.μ :=
    (gradCurryL FC.C).comp_memLp' hgΨ₀
  have hW2₀ : MemLp (fun x => gradCurryL FC.C (L.dΨb x)) 2 Q.μ :=
    (gradCurryL FC.C).comp_memLp' hgΨb₀
  refine ⟨hstrong, hweak, fun n => memLp_prodMk (hW1 n) (hW2 n), memLp_prodMk hW1₀ hW2₀,
    ⟨BΨ + BΨb, fun n => ?_⟩,
    weakL2_prod hW1 hW1₀ hW2 hW2₀ (WeakL2Tendsto.clm_comp hwΨ (gradCurryL FC.C))
      (WeakL2Tendsto.clm_comp hwΨb (gradCurryL FC.C))⟩
  have hle : eLpNorm (fun x => (gradCurryL FC.C (spinorGrad (z n).z.Ψ x),
      gradCurryL FC.C (spinorGrad (z n).z.Ψb x))) 2 Q.μ ≤
      eLpNorm (spinorGrad (z n).z.Ψ) 2 Q.μ + eLpNorm (spinorGrad (z n).z.Ψb) 2 Q.μ := by
    calc _ ≤ eLpNorm (fun x => ‖spinorGrad (z n).z.Ψ x‖ + ‖spinorGrad (z n).z.Ψb x‖) 2 Q.μ := by
          refine eLpNorm_mono_real fun x => ?_
          refine norm_prod_le_iff.mpr ⟨(norm_gradCurryL_le _).trans ?_,
            (norm_gradCurryL_le _).trans ?_⟩
          · exact le_add_of_nonneg_right (norm_nonneg _)
          · exact le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ eLpNorm (fun x => ‖spinorGrad (z n).z.Ψ x‖) 2 Q.μ +
          eLpNorm (fun x => ‖spinorGrad (z n).z.Ψb x‖) 2 Q.μ :=
          eLpNorm_add_le (hgΨ n).1.norm (hgΨb n).1.norm (by norm_num)
      _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]
  calc _ ≤ (eLpNorm (spinorGrad (z n).z.Ψ) 2 Q.μ +
        eLpNorm (spinorGrad (z n).z.Ψb) 2 Q.μ).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hgΨ n).2.ne, (hgΨb n).2.ne⟩) hle
    _ = (eLpNorm (spinorGrad (z n).z.Ψ) 2 Q.μ).toReal +
        (eLpNorm (spinorGrad (z n).z.Ψb) 2 Q.μ).toReal :=
        ENNReal.toReal_add (hgΨ n).2.ne (hgΨb n).2.ne
    _ ≤ BΨ + BΨb := add_le_add (hBΨ n) (hBΨb n)

/-- **`prop:weak-fermion`** (slab-box rendering).  On the slab box `Q ⊇` time support of `K`,
suppose the coframes take values a.e. in one compact subset of the coframe chart and converge
strongly in `H¹(Q)`, the connections and Higgs fields converge strongly in `L²(Q)` (this covers
both the `L⁴` hypotheses and their weakening to `L²` with uniform `L⁴` bounds), the spinors and
cospinors converge weakly in `H¹(Q)`, and the Yukawa coefficients converge.  Then the complete
first variation of the Dirac–Yukawa action (metric variation including the spin-connection chain,
gauge, Higgs and spinor variations) converges in the dual norm of `𝒱_K^r` for every `r ≥ 1`. -/
theorem diracVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hchart : ∃ Ke, IsCompactCoframeSet Ke ∧
      (∀ n, ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, (z n).z.e x ∈ Ke) ∧
      ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, L.e x ∈ Ke)
    (hemem : MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (coframeC L.e) L.de)
    (het : H1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => coframeC (z n).z.e)
      (fun n => coframeGrad (z n).z.e) (coframeC L.e) L.de)
    (hAmem : MemLp L.A 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hAt : LpTendsto 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.A) L.A)
    (hHmem : MemLp L.H 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hHt : LpTendsto 2 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.H) L.H)
    (hΨ : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψ)
      (fun n => spinorGrad (z n).z.Ψ) (spinorC L.Ψ) L.dΨ)
    (hΨb : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψb)
      (fun n => spinorGrad (z n).z.Ψb) (spinorC L.Ψb) L.dΨb)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |actionVariation T (diracSectorDensity FC (θ n)) (z n).z (variationDirection (z n).z v.val) -
        diracLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hchart
  obtain ⟨hcl, -, -⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hemem het
  obtain ⟨hS, hΩ, hW, hW₀, ⟨B, hB⟩, hwk⟩ := dirac_data FC h0 h01 h1 hKe hzKe hLKe hemem het
    hAmem hAt hHmem hHt hΨ hΨb hyL hy0
  filter_upwards [dual_tendsto_split (left := left) (K := K) hr _ hS hΩ hW hW₀ hB hwk hε]
    with n hn v
  rw [diracVariation_eq_cov FC (θ n) h0 h01 h1 hK (z n) v hKe.1
    (hKe.2.trans coframeChart_subset_GL) (hcl n)]
  unfold diracLimitVariation
  simp only [diracCov_redJet, diracCov_limitJet]
  exact hn v

/-- **`prop:weak-fermion` in the paper's form**: `A_h → A` and `H_h → H` in `L⁴(Q)`. -/
theorem diracVariation_dual_tendsto_L4 {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hchart : ∃ Ke, IsCompactCoframeSet Ke ∧
      (∀ n, ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, (z n).z.e x ∈ Ke) ∧
      ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, L.e x ∈ Ke)
    (hemem : MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (coframeC L.e) L.de)
    (het : H1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => coframeC (z n).z.e)
      (fun n => coframeGrad (z n).z.e) (coframeC L.e) L.de)
    (hAmem : MemLp L.A 4 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hAt : LpTendsto 4 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.A) L.A)
    (hHmem : MemLp L.H 4 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ)
    (hHt : LpTendsto 4 (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ (fun n => (z n).z.H) L.H)
    (hΨ : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψ)
      (fun n => spinorGrad (z n).z.Ψ) (spinorC L.Ψ) L.dΨ)
    (hΨb : WeakH1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => spinorC (z n).z.Ψb)
      (fun n => spinorGrad (z n).z.Ψb) (spinorC L.Ψb) L.dΨb)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |actionVariation T (diracSectorDensity FC (θ n)) (z n).z (variationDirection (z n).z v.val) -
        diracLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  have hA2 := RenewalGeometry.LpTendsto.mono (ν := Q.μ) (p := 2) (q := 4) (by norm_num)
    (by norm_num) ⟨fun n => memLp_of_continuousOn_closure hO hc
      ((z n).smooth_A.continuousOn.mono hclS) 4, hAmem, hAt⟩
  have hH2 := RenewalGeometry.LpTendsto.mono (ν := Q.μ) (p := 2) (q := 4) (by norm_num)
    (by norm_num) ⟨fun n => memLp_of_continuousOn_closure hO hc
      ((z n).smooth_H.continuousOn.mono hclS) 4, hHmem, hHt⟩
  exact diracVariation_dual_tendsto FC h0 h01 h1 hK hr hchart hemem het hA2.memLp_lim hA2.tendsto
    hH2.memLp_lim hH2.tendsto hΨ hΨb hyL hy0 hε

/-- The first variation of the complete Standard-Model action at limit fields. -/
def smLimitVariation (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    {r : ℕ} {K : CylRegion T} (v : CrTest left r K) : ℝ :=
  ∫ x in Q.set, (bosonCov θ (limitJet L x) + diracCov FC θ (limitJet L x)) (testJet v.val x)

/-- **`prop:reduced-continuity`, complete Standard-Model sector** (Yang–Mills, Higgs and the
complete Dirac–Yukawa contribution including the metric–spin-connection chain).  Under the reduced
convergence on the slab box and convergence of the Yukawa coefficients, the Standard-Model first
variations `D𝒮_{SM,θ_h}(z_h) = firstVariation T FC θ_h .standardModel` converge in the dual norm
of `𝒱_K^r` (`r ≥ 1`) to the first variation of the limit fields. -/
theorem smVariation_dual_tendsto [Fintype Ysec] {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ}
    (hr : 1 ≤ r) {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    {θ₀ : CoefficientBank Ysec} {L : LimitFields FC.C}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |firstVariation T FC (θ n) .standardModel (z n).z v.val -
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨hcl, -, -⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  have hA2 := RenewalGeometry.LpTendsto.mono (ν := Q.μ) (p := 2) (q := 4) (by norm_num)
    (by norm_num) ⟨fun n => memLp_of_continuousOn_closure (SobolevOpen.isOpen_box Q.a Q.b)
      (isCompact_closure_slabChart h0 h01 h1)
      ((z n).smooth_A.continuousOn.mono ((closure_slabChart_subset h0 h01 h1).trans
        (slabTime_subset_cylSlab h0 h1))) 4, hRC.conn_mem, hRC.conn_tendsto⟩
  obtain ⟨hS, hΩ, hW, hW₀, ⟨B, hB⟩, hwk⟩ := dirac_data FC h0 h01 h1 hKe hzKe hLKe
    hRC.coframe_mem hRC.coframe_tendsto hA2.memLp_lim hA2.tendsto hRC.higgs_mem
    hRC.higgs_tendsto hRC.spinor_weak hRC.cospinor_weak hyL hy0
  have hΛ := (bosonCov_reduced_tendsto h0 h01 h1 hRC).add hS
  filter_upwards [dual_tendsto_split (left := left) (K := K) hr _ hΛ hΩ hW hW₀ hB hwk hε]
    with n hn v
  rw [smVariation_eq_cov FC (θ n) h0 h01 h1 hK (z n) v hKe.1
    (hKe.2.trans coframeChart_subset_GL) (hcl n)]
  unfold smLimitVariation
  simp only [ContinuousLinearMap.add_apply, diracCov_redJet, diracCov_limitJet, ← add_assoc]
  exact hn v

end DiracMain

/-! ### Non-vacuity -/

section NonVacuity

/-- **Non-vacuity of `smVariation_dual_tendsto`** (and hence of the Dirac sector): the flat
regulator, which converges to the flat limit in the reduced action topology, satisfies all the
hypotheses, with the trivial carrier and the constant physical bank. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest (trivialCarrier Unit).left r K,
      |firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
          ((flatRegulator T).fields n).z v.val -
        smLimitVariation (trivialCarrier Unit) physicalBank
          (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v| ≤ ε * ‖v‖ :=
  smVariation_dual_tendsto (trivialCarrier Unit) h0 h01 h1 hK hr
    (flatRegulator_reducedActionConvergence T _) tendsto_const_nhds tendsto_const_nhds hε

end NonVacuity

end EinsteinSM
end RenewalGeometry
