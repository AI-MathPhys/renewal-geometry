/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.RenewalLatticeCarrier

/-!
# The common gravity–matter finite action of the renewal realization
  (`prop:renewal-interface`, item (I4); Einstein–Standard-Model action-closure manuscript)

On the lattice carrier of `RenewalLatticeCarrier.lean` this file defines the finite common action
`S_h = S_{g,h} + ν S_{SM,h}` with `ν = 1` and the coefficient normalization of `eq:total-action`,
proves its exact finite gauge invariance under every site gauge `γ : Grid → G_SM`, and its
differentiability on the whole configuration space.

* **Gravity** (`gravityActionR`): the Palatini–Cartan density of `eq:native-densities`,
  `v(e)/(2κ) e_a^μ e^{bν} (R_{μν})^a_b - (Λ/κ) v(e)`, with the *same* coframe-derived Cartan links
  `exp(h ω_{μ,h})` (`NativeScaling.omegaLink`) and the *same* plaquette
  (`NativeScaling.gaugePlaquette`) as the native local action, taken in Wilson form
  `R^W = h⁻²(P - 1)` (`cartanW`).  The native curvature is the logarithm of the same plaquette,
  `R^h = h⁻² Log(1 + h² R^W)` (`cartanCurvature_eq_log`).
* **Matter** (`matterActionR`): the Lorentzian Yang–Mills density
  `-¼ v(e) g^{μρ}g^{νσ}⟨F_{μν}, F_{ρσ}⟩` with Wilson field strengths `F = h⁻²(P - 1)` of the colour,
  weak and hypercharge (`det`) plaquettes and the invariant metric with coefficients `g_j^{-2}`;
  the Higgs density `-v(e) g^{μν} Re⟨K_μ, K_ν⟩ - v(e) λ_H(|H|² - v_H²)²` with the covariant Higgs
  link `K_μ = h⁻¹(L₂,μ H(x + e_μ) - H(x))`; and the Dirac/Yukawa density
  `v(e) Re Σ_g Ψ̄_g · (D_q Ψ)_g` of the incidence operator of (I3).

Why Wilson form: the native local action takes its logarithms "on the declared admissible chart"
(`subsec:local-action-conventions`), so it is defined and differentiable only on that chart and
link-variable gauge transformations leave the logarithmic coordinates; the Lean encoding of
(I4) (`FiniteInterface.action_differentiable`, `action_gauge_invariant`) requires a globally
differentiable and globally gauge-invariant action on a vector-space configuration chart.  The
Wilson form of the same plaquettes satisfies both exactly.
-/

open Matrix
open scoped Kronecker ContDiff

noncomputable section

namespace RenewalGeometry
namespace RenewalRealization

open NativeScaling (Mat omegaLink gaugePlaquette)
open NativeDensity (pal volume ginv opEntry antisym matToOp matToOpL Op)
open ShiftedJetAction (Grid unitVec)
open FiniteInterfaceTable SMDescentYukawa

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} [NeZero n]

/-! ### The gravitational sector -/

/-- The Cartan links `ω_{μ,h}(y)` of a coframe field, as operators on `ℝ⁴`. -/
def cartanLink (h : ℝ) (E : Grid n → Mat) : Fin 4 → Grid n → Op :=
  fun μ y => matToOp (omegaLink h E y μ)

/-- **The Wilson-form Cartan curvature** `R^W_{μν} = h⁻²(P_{μν} - 1)` of the native Cartan
plaquette `P_{μν} = e^{hω_μ(x)} e^{hω_ν(x+e_μ)} e^{-hω_μ(x+e_ν)} e^{-hω_ν(x)}`. -/
def cartanW (h : ℝ) (E : Grid n → Mat) (x : Grid n) (μ ν : Fin 4) : Op :=
  (h ^ 2)⁻¹ • (gaugePlaquette h (cartanLink h E) x μ ν - 1)

/-- The native Cartan curvature is the logarithm of the same plaquette:
`R^h = h⁻² Log(1 + h² R^W)`. -/
theorem cartanCurvature_eq_log {h : ℝ} (hh : h ≠ 0) (E : Grid n → Mat) (x : Grid n)
    (μ ν : Fin 4) :
    NativeDensity.cartanCurvature h E x μ ν =
      (h ^ 2)⁻¹ • ShiftedPlaquette.logOneAdd (h ^ 2 • cartanW h E x μ ν) := by
  rw [cartanW, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hh), one_smul]
  rfl

/-- **The gravitational density** `v(e)/(2κ) e_a^μ e^{bν}(R^W_{μν})^a_b - (Λ/κ) v(e)`
(`eq:native-densities`, Wilson form). -/
def gravDensityW (κ Λ h : ℝ) (E : Grid n → Mat) (x : Grid n) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (E x) μ ν a b *
      opEntry (antisym (cartanW h E x) μ ν) a b) - Λ / κ * volume (E x)

/-- **The finite gravitational action** `S_{g,h} = h⁴ Σ_x 𝓛_{g,h}(x)` of the coframe field of a
configuration, with the coefficients `κ, Λ` of the bank. -/
def gravityActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) : ℝ :=
  h ^ 4 * ∑ x, gravDensityW θ.kappa θ.Lambda h (frameE q) x

/-- The gravitational action is internal-gauge invariant (the coframe is gauge neutral). -/
theorem gravityActionR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) : gravityActionR θ h (gaugeAct γ q) = gravityActionR θ h q := by
  have : frameE (gaugeAct γ q) = frameE q := funext fun x => frameE_gaugeAct γ q x
  simp only [gravityActionR, this]

/-! ### Smoothness of the gravitational sector -/

@[fun_prop]
theorem ContDiffAt.nexp {E 𝔄 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔄]
    [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] {k : WithTop ℕ∞} {f : E → 𝔄} {z : E}
    (hf : ContDiffAt ℝ k f z) : ContDiffAt ℝ k (fun z => NormedSpace.exp (f z)) z :=
  ((NormedSpace.exp_analytic (𝕂 := ℝ) (f z)).contDiffAt).comp z hf

/-- The chart coframe field of a chart-variable field. -/
def chartField (P : Grid n → Mat) : Grid n → Mat := fun y => chartCoframe (P y)

theorem contDiff_chartField_apply (y : Grid n) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun P : Grid n → Mat => chartField P y) := by
  refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_
  exact (contDiff_chartCoframe_entry a b).comp (contDiff_apply ℝ Mat y)

theorem det_chartField_ne_zero (P : Grid n → Mat) (y : Grid n) : (chartField P y).det ≠ 0 :=
  det_chartCoframe_ne_zero (P y)

/-- The Cartan connection of a chart coframe field is smooth in the chart variables. -/
theorem contDiffAt_omegaLink_chart (h : ℝ) (y : Grid n) (μ : Fin 4) (P : Grid n → Mat) :
    ContDiffAt ℝ ∞ (fun P : Grid n → Mat => omegaLink h (chartField P) y μ) P := by
  have h1 : ContDiffAt ℝ ∞ (fun P : Grid n → Mat =>
      (chartField P y, fun lam => ShiftedJetAction.fwdDiff h lam (chartField P) y)) P := by
    refine ContDiffAt.prodMk (contDiff_chartField_apply y).contDiffAt ?_
    refine contDiffAt_pi.mpr fun lam => ?_
    simp only [ShiftedJetAction.fwdDiff]
    exact (((contDiff_chartField_apply _).sub (contDiff_chartField_apply y)).const_smul
      h⁻¹).contDiffAt
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (NativeDensity.contDiffAt_readerOmega_entry μ a b
    (q := (chartField P y, fun lam => ShiftedJetAction.fwdDiff h lam (chartField P) y))
    (det_chartField_ne_zero P y)).comp P h1

theorem contDiffAt_cartanLink_chart (h : ℝ) (μ : Fin 4) (y : Grid n) (P : Grid n → Mat) :
    ContDiffAt ℝ ∞ (fun P : Grid n → Mat => cartanLink h (chartField P) μ y) P := by
  simp only [cartanLink, ← NativeDensity.matToOpL_apply]
  exact matToOpL.contDiff.contDiffAt.comp P (contDiffAt_omegaLink_chart h y μ P)

theorem contDiffAt_cartanW_chart (h : ℝ) (x : Grid n) (μ ν : Fin 4) (P : Grid n → Mat) :
    ContDiffAt ℝ ∞ (fun P : Grid n → Mat => cartanW h (chartField P) x μ ν) P := by
  have h1 := contDiffAt_cartanLink_chart h μ x P
  have h2 := contDiffAt_cartanLink_chart h ν (x + unitVec n μ) P
  have h3 := contDiffAt_cartanLink_chart h μ (x + unitVec n ν) P
  have h4 := contDiffAt_cartanLink_chart h ν x P
  simp only [cartanW, gaugePlaquette]
  refine ContDiffAt.const_smul _ (ContDiffAt.sub ?_ contDiffAt_const)
  refine ContDiffAt.mul (ContDiffAt.mul (ContDiffAt.mul ?_ ?_) ?_) ?_
  · exact ContDiffAt.nexp (h1.const_smul h)
  · exact ContDiffAt.nexp (h2.const_smul h)
  · exact ContDiffAt.nexp (h3.const_smul h).neg
  · exact ContDiffAt.nexp (h4.const_smul h).neg

theorem contDiffAt_gravDensityW_chart (κ Λ h : ℝ) (x : Grid n) (P : Grid n → Mat) :
    ContDiffAt ℝ ∞ (fun P : Grid n → Mat => gravDensityW κ Λ h (chartField P) x) P := by
  have hR : ∀ μ ν, ContDiffAt ℝ ∞ (fun P : Grid n → Mat => cartanW h (chartField P) x μ ν) P :=
    fun μ ν => contDiffAt_cartanW_chart h x μ ν P
  have he := det_chartField_ne_zero P x
  have hE : ContDiffAt ℝ ∞ (fun P : Grid n → Mat => chartField P x) P :=
    (contDiff_chartField_apply x).contDiffAt
  have hpal : ∀ μ ν a b, ContDiffAt ℝ ∞ (fun P : Grid n → Mat => pal κ (chartField P x) μ ν a b)
      P := fun μ ν a b =>
    ContDiffAt.comp (g := fun e => pal κ e μ ν a b) P (NativeDensity.contDiffAt_pal κ μ ν a b he) hE
  have hvol : ContDiffAt ℝ ∞ (fun P : Grid n → Mat => volume (chartField P x)) P :=
    ContDiffAt.comp (g := volume) P (NativeDensity.contDiffAt_volume he) hE
  simp only [gravDensityW]
  fun_prop

/-- The chart variables of a configuration, as a continuous linear map. -/
def prmL : Config n →L[ℝ] (Grid n → Mat) :=
  ContinuousLinearMap.pi fun x => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
    EuclideanSpace.proj (x, Coord.frame a b)

theorem prmL_apply (q : Config n) : prmL q = fun x => prm q x := rfl

theorem frameE_eq_chartField (q : Config n) : frameE q = chartField (prmL q) := rfl

/-- **(I4) The gravitational action is differentiable on all of `𝒬_h`.** -/
theorem differentiable_gravityActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) :
    Differentiable ℝ (gravityActionR θ h (n := n)) := by
  intro q
  have : gravityActionR θ h (n := n) =
      fun q => h ^ 4 * ∑ x, gravDensityW θ.kappa θ.Lambda h (chartField (prmL q)) x := rfl
  rw [this]
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun x _ => ?_) _
  exact ((contDiffAt_gravDensityW_chart θ.kappa θ.Lambda h x (prmL q)).differentiableAt
    (by simp)).comp q prmL.differentiableAt

/-! ### The Standard-Model sector -/

/-- The colour plaquette `L₃,μ(x) L₃,ν(x+e_μ) L₃,μ(x+e_ν)^* L₃,ν(x)^*`. -/
def plaq3 (q : Config n) (x : Grid n) (μ ν : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  lk3 q μ x * lk3 q ν (x + unitVec n μ) * star (lk3 q μ (x + unitVec n ν)) * star (lk3 q ν x)

/-- The weak plaquette. -/
def plaq2 (q : Config n) (x : Grid n) (μ ν : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  lk2 q μ x * lk2 q ν (x + unitVec n μ) * star (lk2 q μ (x + unitVec n ν)) * star (lk2 q ν x)

/-- Colour field strength `F₃ = h⁻²(P₃ - 1)`. -/
def fs3 (h : ℝ) (q : Config n) (x : Grid n) (μ ν : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  (h ^ 2)⁻¹ • (plaq3 q x μ ν - 1)

/-- Weak field strength `F₂ = h⁻²(P₂ - 1)`. -/
def fs2 (h : ℝ) (q : Config n) (x : Grid n) (μ ν : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (h ^ 2)⁻¹ • (plaq2 q x μ ν - 1)

/-- Hypercharge field strength `F₁ = h⁻²(det P₂ - 1)` (the `U(1)` phase of `S(U(3)×U(2))`). -/
def fs1 (h : ℝ) (q : Config n) (x : Grid n) (μ ν : Fin 4) : ℂ :=
  (h ^ 2)⁻¹ • ((plaq2 q x μ ν).det - 1)

/-- The Hilbert–Schmidt pairing `2 Re tr(A^* B)`. -/
def hsIp {m : Type*} [Fintype m] (A B : Matrix m m ℂ) : ℝ := 2 * (Matrix.trace (Aᴴ * B)).re

/-- The positive invariant metric on the field strengths, with coefficients `g_j^{-2}`. -/
def ymIp (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) (x : Grid n) (μ ν ρ σ : Fin 4) :
    ℝ :=
  (θ.g3 ^ 2)⁻¹ * hsIp (fs3 h q x μ ν) (fs3 h q x ρ σ) +
    (θ.g2 ^ 2)⁻¹ * hsIp (fs2 h q x μ ν) (fs2 h q x ρ σ) +
    (θ.g1 ^ 2)⁻¹ * (2 * (star (fs1 h q x μ ν) * fs1 h q x ρ σ).re)

/-- **Yang–Mills density** `-¼ v(e) g^{μρ} g^{νσ} ⟨F_{μν}, F_{ρσ}⟩`. -/
def ymDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) (x : Grid n) : ℝ :=
  -(4⁻¹ * volume (frameE q x) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
    ginv (frameE q x) μ ρ * ginv (frameE q x) ν σ * ymIp θ h q x μ ν ρ σ)

/-- The covariant Higgs link `K_μ = h⁻¹(L₂,μ(x) H(x + e_μ) - H(x))`. -/
def higgsLinkR (h : ℝ) (q : Config n) (x : Grid n) (μ : Fin 4) : Fin 2 → ℂ :=
  h⁻¹ • (lk2 q μ x *ᵥ hig q (x + unitVec n μ) - hig q x)

/-- The Hermitian product `Re⟨u, v⟩`. -/
def hipR (u v : Fin 2 → ℂ) : ℝ := (star u ⬝ᵥ v).re

/-- **Higgs density** `-v(e) g^{μν} Re⟨K_μ, K_ν⟩ - v(e) λ_H(|H|² - v_H²)²`. -/
def higgsDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) (x : Grid n) : ℝ :=
  -(volume (frameE q x) * ∑ μ, ∑ ν, ginv (frameE q x) μ ν *
      hipR (higgsLinkR h q x μ) (higgsLinkR h q x ν)) -
    volume (frameE q x) * (θ.lambdaH * (hipR (hig q x) (hig q x) - θ.vH ^ 2) ^ 2)

/-- **Dirac/Yukawa density** `v(e) Re Σ_g Ψ̄_g · (D_q Ψ)_g` with the incidence operator of (I3). -/
def diracDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) (x : Grid n) : ℝ :=
  volume (frameE q x) * (∑ g, psibF q x g ⬝ᵥ diracFun θ h q (psiF q) x g).re

/-- **The finite Standard-Model action** `S_{SM,h} = h⁴ Σ_x (𝓛_YM + 𝓛_H + 𝓛_D)`. -/
def matterActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) : ℝ :=
  h ^ 4 * ∑ x, (ymDensityR θ h q x + higgsDensityR θ h q x + diracDensityR θ h q x)

/-! ### Exact gauge invariance of the Standard-Model sector -/

theorem smU3_cancel (y : SMGaugeGroup) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    star (smU3 y) * (smU3 y * M) = M := by
  rw [← Matrix.mul_assoc, smU3_star_mul, Matrix.one_mul]

theorem smU2_cancel (y : SMGaugeGroup) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (smU2 y) * (smU2 y * M) = M := by
  rw [← Matrix.mul_assoc, smU2_star_mul, Matrix.one_mul]

theorem plaq3_gauge (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) (μ ν : Fin 4) :
    plaq3 (gaugeAct γ q) x μ ν = smU3 (γ x) * plaq3 q x μ ν * star (smU3 (γ x)) := by
  simp only [plaq3, lk3_gaugeAct, star_gauge_link]
  simp only [show x + unitVec n ν + unitVec n μ = x + unitVec n μ + unitVec n ν from
    add_right_comm _ _ _, Matrix.mul_assoc, smU3_cancel]

theorem plaq2_gauge (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) (μ ν : Fin 4) :
    plaq2 (gaugeAct γ q) x μ ν = smU2 (γ x) * plaq2 q x μ ν * star (smU2 (γ x)) := by
  simp only [plaq2, lk2_gaugeAct, star_gauge_link]
  simp only [show x + unitVec n ν + unitVec n μ = x + unitVec n μ + unitVec n ν from
    add_right_comm _ _ _, Matrix.mul_assoc, smU2_cancel]

theorem conj_sub_one {m : Type*} [Fintype m] [DecidableEq m] (u P : Matrix m m ℂ)
    (hu : u * star u = 1) (c : ℝ) : c • (u * P * star u - 1) = u * (c • (P - 1)) * star u := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]

theorem hsIp_conj {m : Type*} [Fintype m] [DecidableEq m] (u A B : Matrix m m ℂ)
    (hu : star u * u = 1) : hsIp (u * A * star u) (u * B * star u) = hsIp A B := by
  unfold hsIp
  congr 2
  rw [Matrix.star_eq_conjTranspose] at hu ⊢
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  have e : u * (Aᴴ * uᴴ) * (u * B * uᴴ) = u * (Aᴴ * B) * uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc uᴴ u, hu, Matrix.one_mul]
  rw [e, trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem det_conj_unitary {m : Type*} [Fintype m] [DecidableEq m] (u P : Matrix m m ℂ)
    (hu : star u * u = 1) : (u * P * star u).det = P.det := by
  rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hu, det_one, one_mul]

theorem ymIp_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) (x : Grid n) (μ ν ρ σ : Fin 4) :
    ymIp θ h (gaugeAct γ q) x μ ν ρ σ = ymIp θ h q x μ ν ρ σ := by
  simp only [ymIp, fs3, fs2, fs1, plaq3_gauge, plaq2_gauge,
    conj_sub_one _ _ (smU3_mul_star _), conj_sub_one _ _ (smU2_mul_star _),
    hsIp_conj _ _ _ (smU3_star_mul _), hsIp_conj _ _ _ (smU2_star_mul _),
    det_conj_unitary _ _ (smU2_star_mul _)]

theorem ymDensityR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) (x : Grid n) : ymDensityR θ h (gaugeAct γ q) x = ymDensityR θ h q x := by
  simp only [ymDensityR, frameE_gaugeAct, ymIp_gauge]

theorem higgsLinkR_gauge (h : ℝ) (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n)
    (μ : Fin 4) : higgsLinkR h (gaugeAct γ q) x μ = smU2 (γ x) *ᵥ higgsLinkR h q x μ := by
  simp only [higgsLinkR, lk2_gaugeAct, hig_gaugeAct, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    smU2_star_mul, Matrix.mul_one, Matrix.mulVec_smul, Matrix.mulVec_sub]

theorem hipR_unitary (u : Matrix (Fin 2) (Fin 2) ℂ) (hu : star u * u = 1) (v w : Fin 2 → ℂ) :
    hipR (u *ᵥ v) (u *ᵥ w) = hipR v w := by
  unfold hipR
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hu' : uᴴ * u = 1 := hu
  rw [hu', Matrix.one_mulVec]

theorem higgsDensityR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) (x : Grid n) : higgsDensityR θ h (gaugeAct γ q) x = higgsDensityR θ h q x := by
  simp only [higgsDensityR, frameE_gaugeAct, higgsLinkR_gauge, hig_gaugeAct,
    hipR_unitary _ (smU2_star_mul _)]

theorem psiF_gaugeAct' (γ : Grid n → SMGaugeGroup) (q : Config n) :
    psiF (gaugeAct γ q) = fun y m => tableRepM (γ y) *ᵥ psiF q y m :=
  funext fun y => psiF_gaugeAct γ q y

theorem diracDensityR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) (x : Grid n) :
    diracDensityR θ h (gaugeAct γ q) x = diracDensityR θ h q x := by
  simp only [diracDensityR, frameE_gaugeAct, psibF_gaugeAct, psiF_gaugeAct',
    diracFun_covariant, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, tableRep_inv_mul,
    Matrix.one_mulVec]

/-- **Exact gauge invariance of the Standard-Model action** under every site gauge. -/
theorem matterActionR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) : matterActionR θ h (gaugeAct γ q) = matterActionR θ h q := by
  simp only [matterActionR, ymDensityR_gauge, higgsDensityR_gauge, diracDensityR_gauge]

/-! ### Differentiability of the Standard-Model sector -/

section EntrywiseCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Entrywise real differentiability of a complex-matrix-valued map. -/
def MDiff {m k : Type*} (A : E → Matrix m k ℂ) : Prop := ∀ i j, Differentiable ℝ fun q => A q i j

/-- Entrywise real differentiability of a complex-vector-valued map. -/
def VDiff {m : Type*} (v : E → m → ℂ) : Prop := ∀ i, Differentiable ℝ fun q => v q i

theorem differentiable_star_comp {f : E → ℂ} (hf : Differentiable ℝ f) :
    Differentiable ℝ fun q => star (f q) :=
  Complex.conjCLE.toContinuousLinearMap.differentiable.comp hf

theorem differentiable_re_comp {f : E → ℂ} (hf : Differentiable ℝ f) :
    Differentiable ℝ fun q => (f q).re :=
  Complex.reCLM.differentiable.comp hf

theorem differentiable_ofReal_comp {f : E → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ fun q => (f q : ℂ) :=
  Complex.ofRealCLM.differentiable.comp hf

theorem MDiff.mul {m k l : Type*} [Fintype k] {A : E → Matrix m k ℂ} {B : E → Matrix k l ℂ}
    (hA : MDiff A) (hB : MDiff B) : MDiff fun q => A q * B q := fun i j => by
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum fun c _ => (hA i c).mul (hB c j)

theorem MDiff.add {m k : Type*} {A B : E → Matrix m k ℂ} (hA : MDiff A) (hB : MDiff B) :
    MDiff fun q => A q + B q := fun i j => (hA i j).add (hB i j)

theorem MDiff.sub {m k : Type*} {A B : E → Matrix m k ℂ} (hA : MDiff A) (hB : MDiff B) :
    MDiff fun q => A q - B q := fun i j => (hA i j).sub (hB i j)

theorem MDiff.const {m k : Type*} (A : Matrix m k ℂ) : MDiff fun _ : E => A :=
  fun _ _ => differentiable_const _

theorem MDiff.rsmul {m k : Type*} (c : ℝ) {A : E → Matrix m k ℂ} (hA : MDiff A) :
    MDiff fun q => c • A q := fun i j => by
  simp only [Matrix.smul_apply]
  exact (hA i j).const_smul c

theorem MDiff.fsmul {m k : Type*} {c : E → ℂ} (hc : Differentiable ℝ c) {A : E → Matrix m k ℂ}
    (hA : MDiff A) : MDiff fun q => c q • A q := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul (hA i j)

theorem MDiff.star {m : Type*} {A : E → Matrix m m ℂ} (hA : MDiff A) :
    MDiff fun q => star (A q) := fun i j => by
  simp only [Matrix.star_apply]
  exact differentiable_star_comp (hA j i)

theorem differentiable_finset_prod_c {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    (hf : ∀ i, Differentiable ℝ (f i)) : Differentiable ℝ fun q => ∏ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiable_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

theorem MDiff.det {m : Type*} [Fintype m] [DecidableEq m] {A : E → Matrix m m ℂ}
    (hA : MDiff A) : Differentiable ℝ fun q => (A q).det := by
  simp only [Matrix.det_apply]
  refine Differentiable.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiable_const _).mul (differentiable_finset_prod_c _ fun i => hA _ _)

theorem MDiff.kron {m k m' k' : Type*} {A : E → Matrix m k ℂ} {B : E → Matrix m' k' ℂ}
    (hA : MDiff A) (hB : MDiff B) : MDiff fun q => A q ⊗ₖ B q := fun i j => by
  simp only [kroneckerMap_apply]
  exact (hA i.1 j.1).mul (hB i.2 j.2)

theorem MDiff.fromBlocks {l m k o : Type*} {A : E → Matrix l k ℂ} {B : E → Matrix l o ℂ}
    {C : E → Matrix m k ℂ} {D : E → Matrix m o ℂ} (hA : MDiff A) (hB : MDiff B) (hC : MDiff C)
    (hD : MDiff D) : MDiff fun q => Matrix.fromBlocks (A q) (B q) (C q) (D q) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem MDiff.mulVec {m k : Type*} [Fintype k] {A : E → Matrix m k ℂ} {v : E → k → ℂ}
    (hA : MDiff A) (hv : VDiff v) : VDiff fun q => A q *ᵥ v q := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Differentiable.fun_sum fun c _ => (hA i c).mul (hv c)

theorem VDiff.dotProduct {m : Type*} [Fintype m] {v w : E → m → ℂ} (hv : VDiff v)
    (hw : VDiff w) : Differentiable ℝ fun q => v q ⬝ᵥ w q := by
  show Differentiable ℝ fun q => ∑ i, v q i * w q i
  exact Differentiable.fun_sum fun c _ => (hv c).mul (hw c)

theorem VDiff.star {m : Type*} {v : E → m → ℂ} (hv : VDiff v) : VDiff fun q => star (v q) :=
  fun i => differentiable_star_comp (hv i)

theorem VDiff.add {m : Type*} {v w : E → m → ℂ} (hv : VDiff v) (hw : VDiff w) :
    VDiff fun q => v q + w q := fun i => (hv i).add (hw i)

theorem VDiff.sub {m : Type*} {v w : E → m → ℂ} (hv : VDiff v) (hw : VDiff w) :
    VDiff fun q => v q - w q := fun i => (hv i).sub (hw i)

theorem VDiff.rsmul {m : Type*} (c : ℝ) {v : E → m → ℂ} (hv : VDiff v) :
    VDiff fun q => c • v q := fun i => by
  simp only [Pi.smul_apply]
  exact (hv i).const_smul c

theorem VDiff.sum {m ι : Type*} [Fintype ι] {v : ι → E → m → ℂ} (hv : ∀ i, VDiff (v i)) :
    VDiff fun q => ∑ i, v i q := fun j => by
  simp only [Finset.sum_apply]
  exact Differentiable.fun_sum fun i _ => hv i j

end EntrywiseCalculus

theorem differentiable_coord (p : Grid n × Coord) : Differentiable ℝ fun q : Config n => q p :=
  (EuclideanSpace.proj p : Config n →L[ℝ] ℝ).differentiable

theorem differentiable_cpx (p p' : Grid n × Coord) :
    Differentiable ℝ fun q : Config n => cpx (q p) (q p') := by
  simp only [cpx_eq]
  exact (differentiable_ofReal_comp (differentiable_coord p)).add
    ((differentiable_ofReal_comp (differentiable_coord p')).mul_const _)

theorem mdiff_lk3 (μ : Fin 4) (x : Grid n) : MDiff fun q : Config n => lk3 q μ x :=
  fun _ _ => differentiable_cpx _ _

theorem mdiff_lk2 (μ : Fin 4) (x : Grid n) : MDiff fun q : Config n => lk2 q μ x :=
  fun _ _ => differentiable_cpx _ _

theorem vdiff_hig (x : Grid n) : VDiff fun q : Config n => hig q x :=
  fun _ => differentiable_cpx _ _

theorem vdiff_psiF (x : Grid n) (g : Fin 3) : VDiff fun q : Config n => psiF q x g :=
  fun _ => differentiable_cpx _ _

theorem vdiff_psibF (x : Grid n) (g : Fin 3) : VDiff fun q : Config n => psibF q x g :=
  fun _ => differentiable_cpx _ _

theorem mdiff_extRep {A3 : Config n → Matrix (Fin 3) (Fin 3) ℂ}
    {A2 : Config n → Matrix (Fin 2) (Fin 2) ℂ} (h3 : MDiff A3) (h2 : MDiff A2) :
    MDiff fun q => extRep (A3 q) (A2 q) := by
  have hd : Differentiable ℝ fun q => (A2 q).det := h2.det
  have hsd : Differentiable ℝ fun q => star (A2 q).det := differentiable_star_comp hd
  unfold extRep
  exact MDiff.fromBlocks (MDiff.fromBlocks (h3.kron h2) (MDiff.const 0) (MDiff.const 0)
    (h2.fsmul hsd)) (MDiff.const 0) (MDiff.const 0)
    (MDiff.fromBlocks (MDiff.fromBlocks (h3.fsmul hd) (MDiff.const 0) (MDiff.const 0) h3)
      (MDiff.const 0) (MDiff.const 0) ((MDiff.const 1).fsmul hsd))

/-- The Yukawa matrix entries are real-linear in the Higgs field. -/
theorem differentiable_yM_entry (θ : CoefficientBank (Fin 3)) (i j : Fin 3 × Row) :
    Differentiable ℝ fun H : Fin 2 → ℂ => yM θ H i j := by
  let L : (Fin 2 → ℂ) →ₗ[ℝ] ℂ :=
    (Matrix.entryLinearMap ℝ ℂ (genEquiv i) (genEquiv j)).comp (yukawaMinLinear (ybank θ))
  exact (LinearMap.toContinuousLinearMap L).differentiable

theorem mdiff_yM (θ : CoefficientBank (Fin 3)) (x : Grid n) :
    MDiff fun q : Config n => yM θ (hig q x) := fun i j =>
  (differentiable_yM_entry θ i j).comp (differentiable_pi.mpr (vdiff_hig x))

theorem vdiff_yukOp (θ : CoefficientBank (Fin 3)) (x : Grid n) (g : Fin 3) :
    VDiff fun q : Config n => yukOp θ (hig q x) (psiF q x) g := fun r => by
  have := (mdiff_yM θ x).mulVec (v := fun q => flat (psiF q x)) (fun p => vdiff_psiF x p.1 p.2)
  exact this (g, r)

theorem vdiff_diracFun (θ : CoefficientBank (Fin 3)) (h : ℝ) (x : Grid n) (g : Fin 3) :
    VDiff fun q : Config n => diracFun θ h q (psiF q) x g := by
  unfold diracFun
  refine VDiff.add (VDiff.sum fun μ => VDiff.rsmul _ (VDiff.sub ?_ ?_)) (vdiff_yukOp θ x g)
  · exact (mdiff_extRep (mdiff_lk3 μ x) (mdiff_lk2 μ x)).mulVec (vdiff_psiF _ g)
  · exact (mdiff_extRep (mdiff_lk3 μ _).star (mdiff_lk2 μ _).star).mulVec (vdiff_psiF _ g)

theorem contDiff_prm (x : Grid n) {k : WithTop ℕ∞} : ContDiff ℝ k fun q : Config n => prm q x :=
  contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
    (EuclideanSpace.proj (x, Coord.frame a b) : Config n →L[ℝ] ℝ).contDiff

theorem contDiff_frameE (x : Grid n) {k : WithTop ℕ∞} :
    ContDiff ℝ k fun q : Config n => frameE q x := by
  unfold frameE
  exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
    (contDiff_chartCoframe_entry a b).comp (contDiff_prm x)

theorem differentiable_volume_frameE (x : Grid n) :
    Differentiable ℝ fun q : Config n => volume (frameE q x) := fun q =>
  (ContDiffAt.comp (g := volume) q
    (NativeDensity.contDiffAt_volume (k := 1) (det_chartCoframe_ne_zero (prm q x)))
    (contDiff_frameE x).contDiffAt).differentiableAt (by norm_num)

theorem differentiable_ginv_frameE (x : Grid n) (μ ν : Fin 4) :
    Differentiable ℝ fun q : Config n => ginv (frameE q x) μ ν := fun q =>
  (ContDiffAt.comp (g := fun e => ginv e μ ν) q
    (NativeDensity.contDiffAt_ginv μ ν (k := 1) (det_chartCoframe_ne_zero (prm q x)))
    (contDiff_frameE x).contDiffAt).differentiableAt (by norm_num)

theorem mdiff_plaq3 (x : Grid n) (μ ν : Fin 4) : MDiff fun q : Config n => plaq3 q x μ ν :=
  (((mdiff_lk3 μ x).mul (mdiff_lk3 ν _)).mul (mdiff_lk3 μ _).star).mul (mdiff_lk3 ν x).star

theorem mdiff_plaq2 (x : Grid n) (μ ν : Fin 4) : MDiff fun q : Config n => plaq2 q x μ ν :=
  (((mdiff_lk2 μ x).mul (mdiff_lk2 ν _)).mul (mdiff_lk2 μ _).star).mul (mdiff_lk2 ν x).star

theorem differentiable_hsIp {m : Type*} [Fintype m] {A B : Config n → Matrix m m ℂ}
    (hA : MDiff A) (hB : MDiff B) : Differentiable ℝ fun q => hsIp (A q) (B q) := by
  unfold hsIp
  refine (differentiable_re_comp ?_).const_mul _
  simp only [Matrix.trace]
  refine Differentiable.fun_sum fun i _ => ?_
  have : MDiff fun q => (A q)ᴴ * B q := (MDiff.star hA).mul hB
  exact this i i

theorem differentiable_ymIp (θ : CoefficientBank (Fin 3)) (h : ℝ) (x : Grid n)
    (μ ν ρ σ : Fin 4) : Differentiable ℝ fun q : Config n => ymIp θ h q x μ ν ρ σ := by
  have h3 : ∀ μ ν, MDiff fun q : Config n => fs3 h q x μ ν := fun μ ν =>
    ((mdiff_plaq3 x μ ν).sub (MDiff.const 1)).rsmul _
  have h2 : ∀ μ ν, MDiff fun q : Config n => fs2 h q x μ ν := fun μ ν =>
    ((mdiff_plaq2 x μ ν).sub (MDiff.const 1)).rsmul _
  have h1 : ∀ μ ν, Differentiable ℝ fun q : Config n => fs1 h q x μ ν := fun μ ν => by
    simp only [fs1]
    exact ((mdiff_plaq2 x μ ν).det.sub (differentiable_const _)).const_smul ((h ^ 2)⁻¹ : ℝ)
  unfold ymIp
  refine (((differentiable_hsIp (h3 μ ν) (h3 ρ σ)).const_mul _).add
    ((differentiable_hsIp (h2 μ ν) (h2 ρ σ)).const_mul _)).add ?_
  exact ((differentiable_re_comp ((differentiable_star_comp (h1 μ ν)).mul (h1 ρ σ))).const_mul
    _).const_mul _

theorem differentiable_ymDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (x : Grid n) :
    Differentiable ℝ fun q : Config n => ymDensityR θ h q x := by
  unfold ymDensityR
  refine (((differentiable_volume_frameE x).const_mul _).mul ?_).neg
  refine Differentiable.fun_sum fun μ _ => Differentiable.fun_sum fun ν _ =>
    Differentiable.fun_sum fun ρ _ => Differentiable.fun_sum fun σ _ => ?_
  exact ((differentiable_ginv_frameE x μ ρ).mul (differentiable_ginv_frameE x ν σ)).mul
    (differentiable_ymIp θ h x μ ν ρ σ)

theorem differentiable_hipR {v w : Config n → Fin 2 → ℂ} (hv : VDiff v) (hw : VDiff w) :
    Differentiable ℝ fun q => hipR (v q) (w q) :=
  differentiable_re_comp (hv.star.dotProduct hw)

theorem vdiff_higgsLinkR (h : ℝ) (x : Grid n) (μ : Fin 4) :
    VDiff fun q : Config n => higgsLinkR h q x μ :=
  (((mdiff_lk2 μ x).mulVec (vdiff_hig _)).sub (vdiff_hig x)).rsmul _

theorem differentiable_higgsDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (x : Grid n) :
    Differentiable ℝ fun q : Config n => higgsDensityR θ h q x := by
  unfold higgsDensityR
  refine ((differentiable_volume_frameE x).mul ?_).neg.sub
    ((differentiable_volume_frameE x).mul ?_)
  · exact Differentiable.fun_sum fun μ _ => Differentiable.fun_sum fun ν _ =>
      (differentiable_ginv_frameE x μ ν).mul
        (differentiable_hipR (vdiff_higgsLinkR h x μ) (vdiff_higgsLinkR h x ν))
  · exact (((differentiable_hipR (vdiff_hig x) (vdiff_hig x)).sub
      (differentiable_const _)).pow 2).const_mul _

theorem differentiable_diracDensityR (θ : CoefficientBank (Fin 3)) (h : ℝ) (x : Grid n) :
    Differentiable ℝ fun q : Config n => diracDensityR θ h q x := by
  unfold diracDensityR
  refine (differentiable_volume_frameE x).mul (differentiable_re_comp ?_)
  exact Differentiable.fun_sum fun g _ =>
    (vdiff_psibF x g).dotProduct (vdiff_diracFun θ h x g)

/-- **(I4) The Standard-Model action is differentiable on all of `𝒬_h`.** -/
theorem differentiable_matterActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) :
    Differentiable ℝ (matterActionR θ h (n := n)) := by
  unfold matterActionR
  refine Differentiable.const_mul (Differentiable.fun_sum fun x _ => ?_) _
  exact ((differentiable_ymDensityR θ h x).add (differentiable_higgsDensityR θ h x)).add
    (differentiable_diracDensityR θ h x)

/-! ### The common action -/

/-- **(I4) The common finite action** `S_h = S_{g,h} + ν S_{SM,h}` with the physical relative
normalization `ν = 1` of `eq:total-action` (the gravitational coefficients `1/(2κ)`, `Λ/κ` are
inside `S_{g,h}`, as in `S_θ = S_{g,θ} + S_{SM,θ}`). -/
def commonActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) : ℝ :=
  gravityActionR θ h q + 1 * matterActionR θ h q

theorem differentiable_commonActionR (θ : CoefficientBank (Fin 3)) (h : ℝ) :
    Differentiable ℝ (commonActionR θ h (n := n)) :=
  Differentiable.add (differentiable_gravityActionR θ h)
    (Differentiable.const_mul (differentiable_matterActionR θ h) (1 : ℝ))

/-- **(I4) Exact finite gauge invariance of the common action** under every site gauge. -/
theorem commonActionR_gauge (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) : commonActionR θ h (gaugeAct γ q) = commonActionR θ h q := by
  simp only [commonActionR, gravityActionR_gauge, matterActionR_gauge]

end RenewalRealization
end RenewalGeometry
