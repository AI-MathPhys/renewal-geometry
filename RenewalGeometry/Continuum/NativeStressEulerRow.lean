/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressDirac

/-!
# The coframe (Einstein) row of the native Lagrangian with the complete Standard-Model stress

Bridge step **P3-stress** of `thm:native-closure` (Einstein–Standard-Model action-closure
manuscript): the coframe row of the native continuum Lagrangian
`L₀ = limDensity (firstJetDensity D) = L_g + L_YM + L_H + L_D` on metric directions is the
Einstein residual with the complete minimally coupled Standard-Model stress.

## Main result

**`coframe_row`** — for a smooth native field `Y = (e, A, H, Ψ, Ψ̄)` on `ℝ⁴` whose coframe is
`L`-periodic (`L > 0`, e.g. the `2π` box of `thm:native-source`) with `det e > 0`, Clifford
relations and `σ(ω) = ¼ω_{ab}γ^aγ^b`, and every `S` with `ηS` symmetric (the metric directions
`δe = Se`, `δg = (Se)ᵀηe + eᵀη(Se) = 2eᵀ(ηS)e`, which exhaust all symmetric `δg`):
```
𝓔₀(Y)(z)[(Se, 0, 0, 0, 0)]
  = -(v/(2κ)) (G^{ab} + Λg^{ab}) δg_{ab} + (v/2) T_{SM}^{ab} δg_{ab},
```
with `T_{SM}^{ab} = T_{YM}^{ab} + T_H^{ab} + T_D^{ab}` (`smStressUp`): the Yang–Mills and Higgs
stresses of `ActualJetRecon.ymStressB`/`higgsStressB` with raised indices and the Dirac stress
`T_D^{ab} = g^{ab}ℓ_D - g^{aμ}Θ_μ{}^b` (`NativeStressEuler.diracStressUp`), and `G` the Einstein
tensor of `g = eᵀηe` (`HarmonicDefect.einstein`, the slab-model Einstein tensor).  The proof:
* gravitational sector: `PalatiniEuler.palatini_euler_period` (bridge step P3, f1);
* the Euler row of the matter part `R = L_YM + L_H + L_D` in the direction `Se` is the
  derivative along the frozen metric direction `((Se, 0), μ ↦ (S∂_μe, 0))`, because a symmetric
  coframe-jet direction does not move `R` (`hasDerivAt_LDc_jetSym`, which kills the
  `∂_μ[∂R/∂(∂_μe)]` term up to the product rule);
* `hasDerivAt_LYMc_coframe`, `hasDerivAt_LHc_coframe`, `hasDerivAt_LDc_frozen` (the spin
  connection does not move: `spin_anticomm_frozen`).

Corollaries: `coframe_row_einstein` (`κ ≠ 0`:
`𝓔₀(Y)[(Se, 0)] = -(v/(2κ))(G^{ab} + Λg^{ab} - κT_{SM}^{ab})δg_{ab}`), `metricDir` /
`metricVarM_metricDir` (every symmetric `k` is a `δg`), and **`einstein_equation_iff`**: the
coframe row vanishes on all metric directions iff the symmetric part of the Einstein residual
`G^{ab} + Λg^{ab} - κT_{SM}^{ab}` vanishes.

Disclosed: the antisymmetric (local Lorentz) coframe directions are not treated here (they carry
no Einstein information); the identification is in the native frame `e` (bridge step P2 relates
it to the slab frame `frU(g⁻¹)`).
-/

namespace RenewalGeometry

namespace NativeStressEuler

open Finset HarmonicDefect PalatiniEuler NativeDiracEuler NativeBosonicEuler EHFieldVariation
  EHJetVariation
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open SobolevOpen (pd)
open Filter Topology
open scoped Matrix ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-! ### Splitting off the gravitational sector -/

/-- The projection of a first jet onto the coframe jet `(e, ∂e)`. -/
def projG : FJ 𝔄 𝓗 𝓢 →L[ℝ] Mat × (Fin 4 → Mat) :=
  ContEulerAlg.jetMap (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))

theorem projG_apply (wp : FJ 𝔄 𝓗 𝓢) : projG wp = (wp.1.1, fun μ => (wp.2 μ).1) := rfl

/-- The matter part `R = L_YM + L_H + L_D` of the native Lagrangian. -/
def Rr (wp : FJ 𝔄 𝓗 𝓢) : ℝ := LYMc D wp + LHc D wp + LDc D wp

theorem L0_split (wp : FJ 𝔄 𝓗 𝓢) : L0 D wp = Lg D.κ D.Λ (projG wp) + Rr D wp := by
  rw [L0_eq]
  unfold Rr
  show Lgc D wp + LYMc D wp + LHc D wp + LDc D wp = Lgc D wp + (LYMc D wp + LHc D wp + LDc D wp)
  ring

theorem contDiffOn_LgP :
    ContDiffOn ℝ ∞ (fun wp : FJ 𝔄 𝓗 𝓢 => Lg D.κ D.Λ (projG wp)) chartF :=
  (contDiffOn_Lg D.κ D.Λ).comp (projG : FJ 𝔄 𝓗 𝓢 →L[ℝ] _).contDiff.contDiffOn
    (fun _ hwp => hwp)

theorem contDiffOn_Rr : ContDiffOn ℝ ∞ (Rr D) (chartF : Set (FJ 𝔄 𝓗 𝓢)) := by
  refine ((contDiffOn_L0 D).sub (contDiffOn_LgP D)).congr fun wp _ => ?_
  rw [L0_split]
  ring

theorem differentiableAt_Rr {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) :
    DifferentiableAt ℝ (Rr D) wp :=
  ((contDiffOn_Rr D).contDiffAt (isOpen_chartF.mem_nhds h)).differentiableAt (by simp)

theorem contDiff_eF {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) : ContDiff ℝ ∞ (eF Y) :=
  (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)).contDiff.comp hY

/-- **The Euler row of `L₀` splits** into the Euler row of the Palatini density of the coframe
and the Euler row of the matter part. -/
theorem contEuler_L0_split {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) (δ : Mat) :
    contEuler (L0 D) Y z (coframeDir δ) =
      contEuler (Lg D.κ D.Λ) (eF Y) z δ + contEuler (Rr D) Y z (coframeDir δ) := by
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  have hfun : L0 D = fun wp => Lg D.κ D.Λ (projG wp) + Rr D wp := funext (L0_split D)
  rw [hfun, ContEulerAlg.contEuler_add (V := Field 𝔄 𝓗 𝓢) isOpen_chartF (contDiffOn_LgP D) (contDiffOn_Rr D) hY hJU z,
    ContinuousLinearMap.add_apply]
  congr 1
  have h := ContEulerAlg.contEuler_comp_jetMap (V := Field 𝔄 𝓗 𝓢) (W := Mat)
    (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)) isOpen_chartJ
    (contDiffOn_Lg D.κ D.Λ) hY (fun y => (hdet y).ne') z
  exact congrArg (fun A => A (coframeDir δ)) h

/-! ### The matter row along the frozen metric direction -/

/-- **The symmetric coframe-jet directions are null for `R`**. -/
theorem fderiv_Rr_jetSym (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {wp : FJ 𝔄 𝓗 𝓢} (hE : wp.1.1.det ≠ 0) (μ : Fin 4)
    {T : Mat} (hT : (eta * T)ᵀ = eta * T) :
    fderiv ℝ (Rr D) wp (jetDir μ (T * wp.1.1)) = 0 := by
  refine fderiv_apply_of_line (differentiableAt_Rr D hE) ?_
  have hYM : ∀ t : ℝ, LYMc D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢)) = LYMc D wp := by
    intro t
    have hF : ∀ α β, FA (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢)) α β = FA wp α β := by
      intro α β
      unfold FA
      rw [jd_1, jd_pA, jd_pA]
    unfold LYMc
    simp only [hF, jd_1]
  have hH : ∀ t : ℝ, LHc D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢)) = LHc D wp := by
    intro t
    have hK : ∀ α, KH D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢)) α = KH D wp α := by
      intro α
      unfold KH
      rw [jd_1, jd_pH]
    unfold LHc
    simp only [hK, jd_1]
  have hfun : (fun t : ℝ => Rr D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢))) =
      fun t => (LYMc D wp + LHc D wp) + LDc D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢)) := by
    funext t
    unfold Rr
    rw [hYM, hH]
  rw [hfun]
  simpa using (hasDerivAt_LDc_jetSym D wp μ hcl hσ hE hT).const_add (LYMc D wp + LHc D wp)

/-- The complete Standard-Model stress with raised indices,
`T_{SM}^{ab} = g^{aμ}g^{bν}(T^{YM}_{μν} + T^H_{μν}) + T_D^{ab}`. -/
def smStressUp (wp : FJ 𝔄 𝓗 𝓢) (a b : Fin 4) : ℝ :=
  raise wp.1.1 (fun μ ν => ymStressN D wp μ ν + higgsStressN D wp μ ν) a b +
    diracStressUp D wp a b

/-- **The matter row along the frozen metric direction**: `DR[frozenDir S] = (v/2)T_{SM}^{ab}δg_{ab}`. -/
theorem fderiv_Rr_frozen (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {wp : FJ 𝔄 𝓗 𝓢} (hE : wp.1.1.det ≠ 0) {S : Mat}
    (hS : (eta * S)ᵀ = eta * S) :
    fderiv ℝ (Rr D) wp (frozenDir S wp) =
      volume wp.1.1 / 2 * ∑ a, ∑ b, smStressUp D wp a b * metricVarM wp.1.1 (S * wp.1.1) a b := by
  refine fderiv_apply_of_line (differentiableAt_Rr D hE) ?_
  have hYM := hasDerivAt_LYMc_coframe D wp (frozenDir S wp) hE (S * wp.1.1) (fz_e S wp)
    (fz_FA S wp)
  have hH := hasDerivAt_LHc_coframe D wp (frozenDir S wp) hE (S * wp.1.1) (fz_e S wp)
    (fun t μ => fz_KH S wp t D μ) (fz_H S wp)
  have hDir := hasDerivAt_LDc_frozen D wp hcl hσ hE hS
  refine ((hYM.fun_add hH).fun_add hDir).congr_deriv ?_
  have hR := raise_contract wp.1.1 (S * wp.1.1)
    (fun μ ν => ymStressN D wp μ ν + higgsStressN D wp μ ν)
  have hsum : ∑ μ, ∑ ν, (ymStressN D wp μ ν + higgsStressN D wp μ ν) *
      dgi wp.1.1 (S * wp.1.1) μ ν =
      ∑ μ, ∑ ν, ymStressN D wp μ ν * dgi wp.1.1 (S * wp.1.1) μ ν +
        ∑ μ, ∑ ν, higgsStressN D wp μ ν * dgi wp.1.1 (S * wp.1.1) μ ν := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ν _ => add_mul _ _ _
  have hsm : ∑ a, ∑ b, smStressUp D wp a b * metricVarM wp.1.1 (S * wp.1.1) a b =
      ∑ a, ∑ b, raise wp.1.1 (fun μ ν => ymStressN D wp μ ν + higgsStressN D wp μ ν) a b *
          metricVarM wp.1.1 (S * wp.1.1) a b +
        ∑ a, ∑ b, diracStressUp D wp a b * metricVarM wp.1.1 (S * wp.1.1) a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => add_mul _ _ _
  rw [hsm, ← hR, hsum]
  ring

/-- Left multiplication by a fixed matrix as a continuous linear map. -/
def mulLeftL (S : Mat) : Mat →L[ℝ] Mat :=
  ⟨LinearMap.mulLeft ℝ S, LinearMap.continuous_of_finiteDimensional _⟩

theorem mulLeftL_apply (S m : Mat) : mulLeftL S m = S * m := rfl

/-- The coframe direction as a continuous linear map. -/
def cfL : Mat →L[ℝ] Field 𝔄 𝓗 𝓢 :=
  ContinuousLinearMap.inl ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)

theorem cfL_apply (m : Mat) : (cfL m : Field 𝔄 𝓗 𝓢) = coframeDir m := rfl

/-- **The matter row on a metric direction is the derivative along the frozen metric direction**
(null-direction trick with the symmetric coframe-jet directions, `fderiv_Rr_jetSym`). -/
theorem contEuler_Rr_frozen (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) {S : Mat} (hS : (eta * S)ᵀ = eta * S) :
    contEuler (Rr D) Y z (coframeDir (S * (Y z).1)) =
      fderiv ℝ (Rr D) (jet1 Y z) (frozenDir S (jet1 Y z)) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  set f : R4 → Field 𝔄 𝓗 𝓢 := fun y => cfL (mulLeftL S (eF Y y)) with hf_def
  have hf : ContDiff ℝ ∞ f :=
    ((cfL : Mat →L[ℝ] Field 𝔄 𝓗 𝓢).contDiff.comp ((mulLeftL S).contDiff.comp (contDiff_eF hY)))
  have hnull : ∀ μ y, fderiv ℝ (Rr D) (jet1 Y y) (ContEulerAlg.slot (Field 𝔄 𝓗 𝓢) μ (f y)) = 0 :=
    fun μ y => fderiv_Rr_jetSym D hcl hσ (wp := jet1 Y y) (hdet y).ne' μ hS
  have h := ContEulerAlg.contEuler_of_null (V := Field 𝔄 𝓗 𝓢) isOpen_chartF (contDiffOn_Rr D) hY hJU hf hnull z
  have hfz : f z = coframeDir (S * (Y z).1) := rfl
  rw [hfz] at h
  rw [h]
  congr 1
  refine Prod.ext rfl (funext fun μ => ?_)
  show fderiv ℝ f z (evec μ) = coframeDir (S * ((jet1 Y z).2 μ).1)
  rw [jet1_e hYd z μ]
  have hd : fderiv ℝ f z = (cfL.comp (mulLeftL S)).comp (fderiv ℝ (eF Y) z) := by
    have h1 := (((cfL : Mat →L[ℝ] Field 𝔄 𝓗 𝓢).comp (mulLeftL S)).hasFDerivAt.comp z
      (((contDiff_eF hY).differentiable (by simp)) z).hasFDerivAt).fderiv
    exact h1
  rw [hd]
  rfl

/-- **The coframe row of the native Lagrangian on metric directions** (bridge step P3-stress of
`thm:native-closure`; see the module docstring). -/
theorem coframe_row (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    {L : ℝ} (hL : 0 < L) (hper : IsLPeriodic L (eF Y)) (hdet : ∀ z, 0 < ((Y z).1).det)
    (z : R4) {S : Mat} (hS : (eta * S)ᵀ = eta * S) :
    contEuler (L0 D) Y z (coframeDir (S * (Y z).1)) =
      einsteinCov D.κ D.Λ (eF Y) z (S * (Y z).1) +
        volume (Y z).1 / 2 * ∑ a, ∑ b, smStressUp D (jet1 Y z) a b *
          metricVarM (Y z).1 (S * (Y z).1) a b := by
  rw [contEuler_L0_split D hY hdet z, contEuler_Rr_frozen D hcl hσ hY hdet z hS,
    fderiv_Rr_frozen D hcl hσ (wp := jet1 Y z) (hdet z).ne' hS,
    palatini_euler_period D.κ D.Λ hL (contDiff_eF hY) hper hdet]
  rfl

/-! ### Metric directions and the Einstein equation -/

/-- The metric direction of a symmetric `k`: `S = ½ η e⁻ᵀ k e⁻¹`, so that `δe = Se` has
`δg = (Se)ᵀηe + eᵀη(Se) = k`. -/
def metricS (E k : Mat) : Mat := (1 / 2 : ℝ) • (eta * (E⁻¹)ᵀ * k * E⁻¹)

theorem metricS_symm (E : Mat) {k : Mat} (hk : kᵀ = k) :
    (eta * metricS E k)ᵀ = eta * metricS E k := by
  have h : eta * metricS E k = (1 / 2 : ℝ) • ((E⁻¹)ᵀ * k * E⁻¹) := by
    unfold metricS
    rw [Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, PalatiniEuler.eta_mul_eta,
      Matrix.one_mul, Matrix.mul_assoc]
  rw [h, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, hk,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem metricVarM_metricS {E : Mat} (hE : E.det ≠ 0) {k : Mat} (hk : kᵀ = k) :
    metricVarM E (metricS E k * E) = k := by
  have hS := metricS_symm E hk
  set S := metricS E k
  have h1 : Sᵀ * eta = eta * S := by
    rw [← hS, Matrix.transpose_mul, PalatiniEuler.eta_transpose]
  have hηS : eta * S = (1 / 2 : ℝ) • ((E⁻¹)ᵀ * k * E⁻¹) := by
    simp only [S, metricS]
    rw [Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, PalatiniEuler.eta_mul_eta,
      Matrix.one_mul, Matrix.mul_assoc]
  have hEt : Eᵀ * (E⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul E hE.isUnit, Matrix.transpose_one]
  have hEi : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hE.isUnit
  unfold metricVarM
  rw [Matrix.transpose_mul]
  calc Eᵀ * Sᵀ * eta * E + Eᵀ * eta * (S * E) = Eᵀ * (Sᵀ * eta) * E + Eᵀ * (eta * S) * E := by
        noncomm_ring
    _ = (2 : ℝ) • (Eᵀ * (eta * S) * E) := by rw [h1, two_smul]
    _ = Eᵀ * (E⁻¹)ᵀ * k * (E⁻¹ * E) := by
        rw [hηS, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        norm_num
        noncomm_ring
    _ = k := by rw [hEt, hEi, Matrix.one_mul, Matrix.mul_one]

/-- The Einstein residual with the complete Standard-Model stress,
`G^{ab} + Λg^{ab} - κT_{SM}^{ab}` (raised indices), of a native field. -/
def einsteinRes (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) (a b : Fin 4) : ℝ :=
  einsteinUp (gF (eF Y) z) (ActualJetSystem.ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) (ddF (gF (eF Y)) z) a b +
    D.Λ * ginv (Y z).1 a b - D.κ * smStressUp D (jet1 Y z) a b

/-- **The coframe row is the Einstein residual** (`κ ≠ 0`):
`𝓔₀(Y)(z)[(Se, 0)] = -(v/(2κ)) (G^{ab} + Λg^{ab} - κT_{SM}^{ab}) δg_{ab}`. -/
theorem coframe_row_einstein (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hκ : D.κ ≠ 0) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hY : ContDiff ℝ ∞ Y) {L : ℝ} (hL : 0 < L) (hper : IsLPeriodic L (eF Y))
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) {S : Mat} (hS : (eta * S)ᵀ = eta * S) :
    contEuler (L0 D) Y z (coframeDir (S * (Y z).1)) =
      -(volume (Y z).1 / (2 * D.κ)) * ∑ a, ∑ b, einsteinRes D Y z a b *
        metricVarM (Y z).1 (S * (Y z).1) a b := by
  rw [coframe_row D hcl hσ hY hL hper hdet z hS, einsteinCov_apply,
    show eF Y z = (Y z).1 from rfl]
  have hsplit : ∑ a, ∑ b, einsteinRes D Y z a b * metricVarM (Y z).1 (S * (Y z).1) a b =
      ∑ a, ∑ b, (einsteinUp (gF (eF Y) z) (ActualJetSystem.ginvOf (gF (eF Y) z))
          (dF (gF (eF Y)) z) (ddF (gF (eF Y)) z) a b +
          D.Λ * ActualJetSystem.ginvOf (gF (eF Y) z) a b) * metricVarM (Y z).1 (S * (Y z).1) a b -
        D.κ * ∑ a, ∑ b, smStressUp D (jet1 Y z) a b * metricVarM (Y z).1 (S * (Y z).1) a b := by
    unfold einsteinRes
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ginv (Y z).1 a b = ActualJetSystem.ginvOf (gF (eF Y) z) a b := rfl
    rw [this]
    ring
  rw [hsplit]
  field_simp
  ring

/-- A symmetric test tensor `k = E_{ab} + E_{ba}`. -/
def symTest (a b : Fin 4) : Mat :=
  Matrix.of fun c d => (if c = a ∧ d = b then 1 else 0) + (if c = b ∧ d = a then 1 else 0)

theorem symTest_transpose (a b : Fin 4) : (symTest a b)ᵀ = symTest a b := by
  ext c d
  simp only [symTest, Matrix.transpose_apply, Matrix.of_apply]
  have h1 : (d = a ∧ c = b) ↔ (c = b ∧ d = a) := and_comm
  have h2 : (d = b ∧ c = a) ↔ (c = a ∧ d = b) := and_comm
  simp only [h1, h2]
  ring

theorem sum_symTest (R : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    ∑ c, ∑ d, R c d * symTest a b c d = R a b + R b a := by
  simp only [symTest, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
    mul_zero]
  congr 1
  · rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
    simp
  · rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp)]
    simp

/-- **The native Einstein equation**: the coframe row of the native Lagrangian vanishes on all
metric directions iff the symmetric part of the Einstein residual vanishes,
`G^{ab} + Λg^{ab} = κ T_{SM}^{(ab)}`. -/
theorem einstein_equation_iff (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hκ : D.κ ≠ 0) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hY : ContDiff ℝ ∞ Y) {L : ℝ} (hL : 0 < L) (hper : IsLPeriodic L (eF Y))
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) :
    (∀ S : Mat, (eta * S)ᵀ = eta * S → contEuler (L0 D) Y z (coframeDir (S * (Y z).1)) = 0) ↔
      ∀ a b, einsteinRes D Y z a b + einsteinRes D Y z b a = 0 := by
  have hE : ((Y z).1).det ≠ 0 := (hdet z).ne'
  have hv : volume (Y z).1 ≠ 0 := by
    rw [volume_of_det_pos (hdet z)]; exact hE
  have hc : -(volume (Y z).1 / (2 * D.κ)) ≠ 0 := by
    have : volume (Y z).1 / (2 * D.κ) ≠ 0 := div_ne_zero hv (mul_ne_zero two_ne_zero hκ)
    exact neg_ne_zero.2 this
  constructor
  · intro h a b
    have hk := symTest_transpose a b
    have h0 := h (metricS (Y z).1 (symTest a b)) (metricS_symm _ hk)
    rw [coframe_row_einstein D hcl hσ hκ hY hL hper hdet z (metricS_symm _ hk),
      metricVarM_metricS hE hk, sum_symTest] at h0
    exact (mul_eq_zero.1 h0).resolve_left hc
  · intro h S hS
    rw [coframe_row_einstein D hcl hσ hκ hY hL hper hdet z hS]
    have hsym : ∀ a b, metricVarM (Y z).1 (S * (Y z).1) a b =
        metricVarM (Y z).1 (S * (Y z).1) b a := fun a b => metricVarM_symm _ _ a b
    have h2 : ∑ a, ∑ b, einsteinRes D Y z a b * metricVarM (Y z).1 (S * (Y z).1) a b =
        -∑ a, ∑ b, einsteinRes D Y z a b * metricVarM (Y z).1 (S * (Y z).1) a b := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      have := h b a
      rw [hsym b a, show einsteinRes D Y z b a = -einsteinRes D Y z a b by linarith]
      ring
    have h3 : ∑ a, ∑ b, einsteinRes D Y z a b * metricVarM (Y z).1 (S * (Y z).1) a b = 0 := by
      linarith
    rw [h3, mul_zero]

end

end NativeStressEuler

end RenewalGeometry
