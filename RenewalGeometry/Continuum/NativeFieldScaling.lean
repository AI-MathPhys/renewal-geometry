/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeBosonicEulerRows
import RenewalGeometry.Continuum.NativeDiracEulerRows
import RenewalGeometry.Continuum.NativeTailTransfer

/-!
# Covariance of the native Euler rows under the dilation of the slab coordinates

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`: the native records of
`thm:native-source` live on the auxiliary box of period `2π`, the actual-tuple slab model of
`prop:coupled-bootstrap` on the unit torus.  The coordinate change `ξ = λx + c` (`λ = 2π`, `c` a
time shift) pulls the native fields back to `Ỹ(x) = Φ_λ(Y(λx + c))`, where
`Φ_λ(e, A, H, Ψ, Ψ̄) = (λe, λA, H, Ψ, Ψ̄)` is the tensorial transformation of the coframe and the
gauge potential.  The native Lagrangian is a scalar density of weight one:
`L₀(Φ_λ w, λΦ_λ p) = λ⁴ L₀(w, p)` (`L0_scale`), so its Euler covector transforms by
`𝓔₀(Ỹ)(x) = λ⁴ 𝓔₀(Y)(λx + c) ∘ Φ_λ⁻¹` (`Rfull_dilate`), and the bosonic / Dirac residual maps by
`𝓡_B(Ỹ)(x) = λ⁴ 𝓡_B(Y)(λx + c) ∘ Φ_{B,λ}⁻¹`, `𝓡_D(Ỹ)(x) = λ⁴ 𝓡_D(Y)(λx + c)`.

## Main results

* `contEuler_dilate` (generic): if `L(Ψ_λ wp) = λ⁴ L(wp)` on an open set of jets containing the
  jets of `Y`, with `Ψ_λ(w, p) = (Φw, λΦp)` for a linear equivalence `Φ`, then
  `contEuler L (x ↦ Φ(Y(λx + c))) x = λ⁴ (contEuler L Y (λx + c)) ∘ Φ⁻¹` (no differentiability
  hypotheses: the rescalings are linear equivalences).
* `L0_scale` — the weight-one homogeneity of `L₀` on the oriented chart `det e > 0`, sector by
  sector (`Lgc_scale` through the explicit Palatini representative `palatiniFirstOrder_eq`,
  `LYMc_scale`, `LHc_scale`, `LDc_scale`).
* **`RB_dilate`**, **`RD_dilate`** — the transformation of the residual maps.
-/

open Finset
open scoped ContDiff

namespace RenewalGeometry.FieldScaling

open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity NativeBosonicEuler NativeDiracEuler NativeTail

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic: the Euler expression under an affine dilation and a linear field map -/

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The dilated field `x ↦ Φ(Y(λx + c))`. -/
def dilateF (Φ : V ≃L[ℝ] V) (lam : ℝ) (c : R4) (Y : R4 → V) : R4 → V :=
  fun x => Φ (Y (lam • x + c))

/-- The jet map `(w, p) ↦ (Φw, λΦp)`. -/
def jetL (Φ : V ≃L[ℝ] V) (lam : ℝ) : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V) :=
  ((Φ : V →L[ℝ] V).comp (ContinuousLinearMap.fst ℝ V (Fin 4 → V))).prod
    (lam • ContinuousLinearMap.pi fun μ => (Φ : V →L[ℝ] V).comp
      ((ContinuousLinearMap.proj μ).comp (ContinuousLinearMap.snd ℝ V (Fin 4 → V))))

theorem jetL_apply (Φ : V ≃L[ℝ] V) (lam : ℝ) (wp : V × (Fin 4 → V)) :
    jetL Φ lam wp = (Φ wp.1, fun μ => lam • Φ (wp.2 μ)) := rfl

/-- The jet map as a linear equivalence (`λ ≠ 0`). -/
def jetE (Φ : V ≃L[ℝ] V) {lam : ℝ} (hlam : lam ≠ 0) :
    (V × (Fin 4 → V)) ≃L[ℝ] (V × (Fin 4 → V)) :=
  ContinuousLinearEquiv.equivOfInverse (jetL Φ lam) (jetL Φ.symm lam⁻¹)
    (fun wp => by
      simp only [jetL_apply, map_smul, ContinuousLinearEquiv.symm_apply_apply, smul_smul,
        inv_mul_cancel₀ hlam, one_smul])
    (fun wp => by
      simp only [jetL_apply, map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ hlam, one_smul])

theorem jetE_apply (Φ : V ≃L[ℝ] V) {lam : ℝ} (hlam : lam ≠ 0) (wp : V × (Fin 4 → V)) :
    jetE Φ hlam wp = (Φ wp.1, fun μ => lam • Φ (wp.2 μ)) := rfl

theorem jetE_symm_apply (Φ : V ≃L[ℝ] V) {lam : ℝ} (hlam : lam ≠ 0) (wp : V × (Fin 4 → V)) :
    (jetE Φ hlam).symm wp = (Φ.symm wp.1, fun μ => lam⁻¹ • Φ.symm (wp.2 μ)) := rfl

theorem fderiv_dilateF (Φ : V ≃L[ℝ] V) (lam : ℝ) (c : R4) (Y : R4 → V) (x : R4) :
    fderiv ℝ (dilateF Φ lam c Y) x = lam • (Φ : V →L[ℝ] V).comp (fderiv ℝ Y (lam • x + c)) := by
  have h1 : dilateF Φ lam c Y = Φ ∘ (fun x => (fun u => Y (u + c)) (lam • x)) := rfl
  rw [h1, Φ.comp_fderiv, fderiv_comp_smul (f := fun u => Y (u + c)) lam, fderiv_comp_add_right,
    ContinuousLinearMap.comp_smul]

theorem jet1_dilateF (Φ : V ≃L[ℝ] V) {lam : ℝ} (hlam : lam ≠ 0) (c : R4) (Y : R4 → V) (x : R4) :
    jet1 (dilateF Φ lam c Y) x = jetE Φ hlam (jet1 Y (lam • x + c)) := by
  rw [jetE_apply]
  simp only [jet1, fderiv_dilateF, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **The Euler expression under an affine dilation of the coordinates and a linear field
map.**  If `L(Φw, λΦp) = λ⁴L(w, p)` on an open set `U` of jets containing every jet of `Y`, then
`𝓔₀[L](x ↦ Φ(Y(λx + c)))(x) = λ⁴ 𝓔₀[L](Y)(λx + c) ∘ Φ⁻¹`. -/
theorem contEuler_dilate {L : V × (Fin 4 → V) → ℝ} (Φ : V ≃L[ℝ] V) {lam : ℝ} (hlam : lam ≠ 0)
    (c : R4) {U : Set (V × (Fin 4 → V))} (hU : IsOpen U)
    (hL : ∀ wp ∈ U, L (jetE Φ hlam wp) = lam ^ 4 * L wp) {Y : R4 → V} (hJ : ∀ z, jet1 Y z ∈ U)
    (x : R4) :
    contEuler L (dilateF Φ lam c Y) x =
      lam ^ 4 • (contEuler L Y (lam • x + c)).comp (Φ.symm : V →L[ℝ] V) := by
  haveI : Invertible (lam ^ 4) := invertibleOfNonzero (pow_ne_zero 4 hlam)
  haveI : Invertible lam := invertibleOfNonzero hlam
  set E := jetE Φ hlam with hE
  -- the derivative of `L` at transformed jets
  have hfd : ∀ j ∈ U, fderiv ℝ L (E j) =
      lam ^ 4 • (fderiv ℝ L j).comp (E.symm : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)) := by
    intro j hj
    have hev : (L ∘ E) =ᶠ[nhds j] fun wp => lam ^ 4 • L wp :=
      Filter.eventually_of_mem (hU.mem_nhds hj) fun wp hwp => hL wp hwp
    have h1 : fderiv ℝ (L ∘ E) j = (fderiv ℝ L (E j)).comp
        (E : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)) := E.comp_right_fderiv
    have h2 : fderiv ℝ (L ∘ E) j = lam ^ 4 • fderiv ℝ L j := by
      rw [hev.fderiv_eq]
      exact fderiv_const_smul_of_invertible (𝕜 := ℝ) (lam ^ 4)
    have h3 := congrArg (fun T : V × (Fin 4 → V) →L[ℝ] ℝ =>
      T.comp (E.symm : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V))) (h1.symm.trans h2)
    simp only [ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_comp_coe_symm,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.smul_comp] at h3
    exact h3
  have hjet : ∀ x', jet1 (dilateF Φ lam c Y) x' = E (jet1 Y (lam • x' + c)) :=
    fun x' => jet1_dilateF Φ hlam c Y x'
  have hinl : (E.symm : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)).comp
      (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) =
      (ContinuousLinearMap.inl ℝ V (Fin 4 → V)).comp (Φ.symm : V →L[ℝ] V) := by
    ext w
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearEquiv.coe_coe, hE, jetE_symm_apply, map_zero]
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearEquiv.coe_coe, hE, jetE_symm_apply, map_zero, smul_zero]
      simp
  have hinr : ∀ μ, (E.symm : V × (Fin 4 → V) →L[ℝ] V × (Fin 4 → V)).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) =
      lam⁻¹ • ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)).comp (Φ.symm : V →L[ℝ] V) := by
    intro μ
    ext w : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hE,
      ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe, jetE_symm_apply]
    refine Prod.ext (by simp) ?_
    funext ν
    by_cases h : ν = μ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  -- the right composition with `Φ⁻¹` as a linear equivalence of covectors
  set R : (V →L[ℝ] ℝ) ≃L[ℝ] (V →L[ℝ] ℝ) := Φ.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
    with hR
  have hRapp : ∀ T : V →L[ℝ] ℝ, R T = T.comp (Φ.symm : V →L[ℝ] V) := fun T => by
    ext v; simp [hR]
  set G : Fin 4 → R4 → (V →L[ℝ] ℝ) := fun μ ξ => (fderiv ℝ L (jet1 Y ξ)).comp
    ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) with hG
  have hterm : ∀ μ, (fun x' => (fderiv ℝ L (jet1 (dilateF Φ lam c Y) x')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) =
      fun x' => (lam ^ 4 * lam⁻¹) • R (G μ (lam • x' + c)) := by
    intro μ
    funext x'
    rw [hjet, hfd _ (hJ _), ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hinr,
      ContinuousLinearMap.comp_smul, smul_smul, hRapp, hG]
    simp only [ContinuousLinearMap.comp_assoc]
  have hderiv : ∀ μ, fderiv ℝ (fun x' => (lam ^ 4 * lam⁻¹) • R (G μ (lam • x' + c))) x =
      (lam ^ 4 * lam⁻¹) • (lam • (R : (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ)).comp
        (fderiv ℝ (G μ) (lam • x + c))) := by
    intro μ
    haveI : Invertible (lam ^ 4 * lam⁻¹) :=
      invertibleOfNonzero (mul_ne_zero (pow_ne_zero 4 hlam) (inv_ne_zero hlam))
    rw [show (fun x' => (lam ^ 4 * lam⁻¹) • R (G μ (lam • x' + c))) =
        (lam ^ 4 * lam⁻¹) • (R ∘ fun x' => (fun u => G μ (u + c)) (lam • x')) from rfl,
      fderiv_const_smul_of_invertible (𝕜 := ℝ)
        (f := R ∘ fun x' => (fun u => G μ (u + c)) (lam • x')) (lam ^ 4 * lam⁻¹), R.comp_fderiv,
      fderiv_comp_smul (f := fun u => G μ (u + c)) lam, fderiv_comp_add_right,
      ContinuousLinearMap.comp_smul]
  unfold contEuler
  simp only [hterm, hderiv]
  rw [hjet, hfd _ (hJ _), ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hinl,
    ← ContinuousLinearMap.comp_assoc]
  rw [ContinuousLinearMap.sub_comp, smul_sub]
  congr 1
  ext v
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hRapp, smul_eq_mul,
    Finset.mul_sum, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hG]
  field_simp

/-- A linear equivalence from a pair of mutually inverse maps (instances of the normed space `V`). -/
def equivOf (f g : V →L[ℝ] V) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse f g h1 h2

theorem equivOf_apply (f g : V →L[ℝ] V) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) (x : V) :
    equivOf f g h1 h2 x = f x := rfl

theorem equivOf_symm_apply (f g : V →L[ℝ] V) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x)
    (x : V) : (equivOf f g h1 h2).symm x = g x := rfl

end Generic

/-! ### The tensorial field scaling of native fields -/

section Native

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The tensorial scaling `(e, A, H, Ψ, Ψ̄) ↦ (λe, λA, H, Ψ, Ψ̄)`. -/
def fieldScaleL (lam : ℝ) : Field 𝔄 𝓗 𝓢 →L[ℝ] Field 𝔄 𝓗 𝓢 :=
  (lam • ContinuousLinearMap.id ℝ Mat).prodMap
    ((lam • ContinuousLinearMap.id ℝ (Fin 4 → 𝔄)).prodMap
      (ContinuousLinearMap.id ℝ (𝓗 × 𝓢 × CoSpinor 𝓢)))

theorem fieldScaleL_apply (lam : ℝ) (w : Field 𝔄 𝓗 𝓢) :
    fieldScaleL lam w = (lam • w.1, lam • w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2) := rfl

/-- The tensorial scaling as a linear equivalence (`λ ≠ 0`). -/
def fieldScale {lam : ℝ} (hlam : lam ≠ 0) : Field 𝔄 𝓗 𝓢 ≃L[ℝ] Field 𝔄 𝓗 𝓢 :=
  ContinuousLinearEquiv.equivOfInverse (fieldScaleL lam) (fieldScaleL lam⁻¹)
    (fun w => by
      simp only [fieldScaleL_apply, smul_smul, inv_mul_cancel₀ hlam, one_smul])
    (fun w => by
      simp only [fieldScaleL_apply, smul_smul, mul_inv_cancel₀ hlam, one_smul])

theorem fieldScale_apply {lam : ℝ} (hlam : lam ≠ 0) (w : Field 𝔄 𝓗 𝓢) :
    fieldScale hlam w = (lam • w.1, lam • w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2) := rfl

theorem fieldScale_symm_apply {lam : ℝ} (hlam : lam ≠ 0) (w : Field 𝔄 𝓗 𝓢) :
    (fieldScale hlam).symm w =
      (lam⁻¹ • w.1, lam⁻¹ • w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2) := rfl

/-! #### Homogeneity of the geometric building blocks -/

theorem det_smul_mat (lam : ℝ) (e : Mat) : (lam • e).det = lam ^ 4 * e.det := by
  rw [Matrix.det_smul, Fintype.card_fin]

theorem inv_smul_mat {lam : ℝ} (hlam : lam ≠ 0) (e : Mat) : (lam • e)⁻¹ = lam⁻¹ • e⁻¹ := by
  by_cases he : e.det ≠ 0
  · refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul e (isUnit_iff_ne_zero.2 he),
      smul_smul, inv_mul_cancel₀ hlam, one_smul]
  · have he' : ¬IsUnit e.det := by rwa [isUnit_iff_ne_zero]
    have h2 : ¬IsUnit (lam • e).det := by
      rw [det_smul_mat, isUnit_iff_ne_zero]
      rw [not_not] at he
      simp [he]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ he', Matrix.nonsing_inv_apply_not_isUnit _ h2,
      smul_zero]

theorem volume_smul (lam : ℝ) (e : Mat) : volume (lam • e) = lam ^ 4 * volume e := by
  rw [volume_eq_abs_det, volume_eq_abs_det, det_smul_mat, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ 4)]

theorem metric_smul (lam : ℝ) (e : Mat) : metric (lam • e) = lam ^ 2 • metric e := by
  unfold metric
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

theorem invEntry_smul {lam : ℝ} (hlam : lam ≠ 0) (i j : Fin 4) (e : Mat) :
    invEntry i j (lam • e) = lam⁻¹ * invEntry i j e := by
  simp [invEntry, inv_smul_mat hlam]

theorem ginv_smul {lam : ℝ} (hlam : lam ≠ 0) (e : Mat) (μ ν : Fin 4) :
    ginv (lam • e) μ ν = (lam ^ 2)⁻¹ * ginv e μ ν := by
  unfold ginv
  rw [metric_smul, invEntry_smul (pow_ne_zero 2 hlam)]

theorem gammaMu_smul {lam : ℝ} (hlam : lam ≠ 0) (μ : Fin 4) (e : Mat) :
    gammaMu D μ (lam • e) = lam⁻¹ • gammaMu D μ e := by
  simp only [gammaMu_eq, inv_smul_mat hlam, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]

theorem readerG_smul2 (lam : ℝ) (e : Mat) (q : Fin 4 → Mat) (l : Fin 4) :
    readerG (lam • e) (fun μ => lam ^ 2 • q μ) l = lam ^ 3 • readerG e q l := by
  unfold readerG
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  congr 1 <;> congr 1 <;> ring

theorem readerGamma_smul2 {lam : ℝ} (hlam : lam ≠ 0) (e : Mat) (q : Fin 4 → Mat)
    (ρ μ ν : Fin 4) :
    readerGamma (lam • e) (fun μ => lam ^ 2 • q μ) ρ μ ν = lam * readerGamma e q ρ μ ν := by
  unfold readerGamma
  simp only [readerG_smul2, metric_smul, inv_smul_mat (pow_ne_zero 2 hlam), Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  field_simp

theorem readerOmega_smul2 {lam : ℝ} (hlam : lam ≠ 0) (e : Mat) (q : Fin 4 → Mat) (μ : Fin 4) :
    readerOmega (lam • e) (fun μ => lam ^ 2 • q μ) μ = lam • readerOmega e q μ := by
  ext a b
  simp only [readerOmega, Matrix.smul_apply, smul_eq_mul, readerGamma_smul2 hlam,
    inv_smul_mat hlam]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    field_simp
  · refine Finset.sum_congr rfl fun ν _ => ?_
    field_simp

/-! #### The scaled first jet -/

variable {lam : ℝ} (hlam : lam ≠ 0)

theorem jetE_fieldScale (wp : FJ 𝔄 𝓗 𝓢) :
    jetE (fieldScale hlam) hlam wp =
      ((lam • wp.1.1, lam • wp.1.2.1, wp.1.2.2.1, wp.1.2.2.2.1, wp.1.2.2.2.2),
        fun μ => (lam • lam • (wp.2 μ).1, lam • lam • (wp.2 μ).2.1, lam • (wp.2 μ).2.2.1,
          lam • (wp.2 μ).2.2.2.1, lam • (wp.2 μ).2.2.2.2)) := rfl

theorem jetE_fieldScale' (wp : FJ 𝔄 𝓗 𝓢) :
    jetE (fieldScale hlam) hlam wp =
      ((lam • wp.1.1, lam • wp.1.2.1, wp.1.2.2.1, wp.1.2.2.2.1, wp.1.2.2.2.2),
        fun μ => (lam ^ 2 • (wp.2 μ).1, lam ^ 2 • (wp.2 μ).2.1, lam • (wp.2 μ).2.2.1,
          lam • (wp.2 μ).2.2.2.1, lam • (wp.2 μ).2.2.2.2)) := by
  rw [jetE_fieldScale]
  simp only [smul_smul, sq]

theorem FA_scale (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) :
    FA (jetE (fieldScale hlam) hlam wp) μ ν = lam ^ 2 • FA wp μ ν := by
  rw [jetE_fieldScale']
  unfold FA
  simp only [Pi.smul_apply, smul_mul_smul_comm, smul_sub, smul_add, sq]

theorem KH_scale (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) :
    KH D (jetE (fieldScale hlam) hlam wp) μ = lam • KH D wp μ := by
  rw [jetE_fieldScale']
  unfold KH
  simp only [Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem omC_scale (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) :
    omC (jetE (fieldScale hlam) hlam wp) μ = lam • omC wp μ := by
  rw [jetE_fieldScale']
  unfold omC
  exact readerOmega_smul2 hlam _ _ μ

theorem DPsi_scale (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) :
    DPsi D (jetE (fieldScale hlam) hlam wp) μ = lam • DPsi D wp μ := by
  have hω := omC_scale hlam wp μ
  rw [jetE_fieldScale'] at hω ⊢
  unfold DPsi
  rw [hω]
  simp only [Pi.smul_apply, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_add]

theorem DPsiBar_scale (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) :
    DPsiBar D (jetE (fieldScale hlam) hlam wp) μ = lam • DPsiBar D wp μ := by
  have hω := omC_scale hlam wp μ
  rw [jetE_fieldScale'] at hω ⊢
  unfold DPsiBar
  rw [hω]
  ext x
  simp only [Pi.smul_apply, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_sub, map_neg, map_smul, smul_add, smul_sub, smul_neg]

/-! #### The four sectors -/

theorem fst_jetE_fieldScale (wp : FJ 𝔄 𝓗 𝓢) :
    (jetE (fieldScale hlam) hlam wp).1 =
      (lam • wp.1.1, lam • wp.1.2.1, wp.1.2.2.1, wp.1.2.2.2.1, wp.1.2.2.2.2) := rfl

theorem LYMc_scale (wp : FJ 𝔄 𝓗 𝓢) :
    LYMc D (jetE (fieldScale hlam) hlam wp) = lam ^ 4 * LYMc D wp := by
  have hFA := FA_scale hlam wp
  have hsum : ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv (lam • wp.1.1) μ ρ * ginv (lam • wp.1.1) ν σ *
      D.ipA (FA (jetE (fieldScale hlam) hlam wp) μ ν) (FA (jetE (fieldScale hlam) hlam wp) ρ σ) =
      ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ * D.ipA (FA wp μ ν) (FA wp ρ σ) := by
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [hFA, ginv_smul hlam, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  unfold LYMc
  rw [fst_jetE_fieldScale, volume_smul]
  simp only [] at hsum ⊢
  rw [hsum]
  ring

theorem LHc_scale (wp : FJ 𝔄 𝓗 𝓢) :
    LHc D (jetE (fieldScale hlam) hlam wp) = lam ^ 4 * LHc D wp := by
  have hK := KH_scale D hlam wp
  have hsum : ∑ μ, ∑ ν, ginv (lam • wp.1.1) μ ν *
      D.hermH (KH D (jetE (fieldScale hlam) hlam wp) μ) (KH D (jetE (fieldScale hlam) hlam wp) ν) =
      ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH (KH D wp μ) (KH D wp ν) := by
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [hK, ginv_smul hlam, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  unfold LHc
  rw [fst_jetE_fieldScale, volume_smul]
  simp only [] at hsum ⊢
  rw [hsum]
  ring

theorem LDc_scale (wp : FJ 𝔄 𝓗 𝓢) :
    LDc D (jetE (fieldScale hlam) hlam wp) = lam ^ 4 * LDc D wp := by
  have hΨ := DPsi_scale D hlam wp
  have hΨb := DPsiBar_scale D hlam wp
  have hsum : ∀ μ, wp.1.2.2.2.2 (gammaMu D μ (lam • wp.1.1)
        (DPsi D (jetE (fieldScale hlam) hlam wp) μ)) -
      DPsiBar D (jetE (fieldScale hlam) hlam wp) μ (gammaMu D μ (lam • wp.1.1) wp.1.2.2.2.1) =
      wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DPsi D wp μ)) -
        DPsiBar D wp μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1) := by
    intro μ
    simp only [hΨ, hΨb, gammaMu_smul D hlam, ContinuousLinearMap.smul_apply, map_smul,
      smul_smul, inv_mul_cancel₀ hlam, mul_inv_cancel₀ hlam, one_smul]
  unfold LDc
  rw [fst_jetE_fieldScale, volume_smul]
  simp only [] at hsum ⊢
  simp only [hsum]
  ring

theorem pal_smul {lam : ℝ} (hlam : lam ≠ 0) (κ : ℝ) (M : Mat) (μ ν a b : Fin 4) :
    pal κ (lam • M) μ ν a b = lam ^ 2 * pal κ M μ ν a b := by
  unfold pal
  simp only [volume_smul, invEntry_smul hlam, Finset.mul_sum]
  field_simp

theorem palA_smul {lam : ℝ} (hlam : lam ≠ 0) (κ : ℝ) (M : Mat) (μ ν a b : Fin 4) :
    NativeDensity.palA κ (lam • M) μ ν a b = lam ^ 2 * NativeDensity.palA κ M μ ν a b := by
  unfold NativeDensity.palA
  rw [pal_smul hlam, pal_smul hlam]
  ring

theorem deriv_palA_scale {lam : ℝ} (hlam : lam ≠ 0) (κ : ℝ) (e p : Mat) (μ ν a b : Fin 4) :
    deriv (fun t : ℝ => NativeDensity.palA κ (lam • e + t • (lam ^ 2 • p)) μ ν a b) 0 =
      lam ^ 3 * deriv (fun t : ℝ => NativeDensity.palA κ (e + t • p) μ ν a b) 0 := by
  have h : (fun t : ℝ => NativeDensity.palA κ (lam • e + t • (lam ^ 2 • p)) μ ν a b) =
      fun t => lam ^ 2 * (fun s : ℝ => NativeDensity.palA κ (e + s • p) μ ν a b) (lam * t) := by
    funext t
    rw [show lam • e + t • (lam ^ 2 • p) = lam • (e + (lam * t) • p) by
      rw [smul_add, smul_smul, smul_smul]; congr 1; ring_nf, palA_smul hlam]
  rw [h, deriv_const_mul_field']
  show lam ^ 2 * deriv (fun t => (fun s : ℝ => NativeDensity.palA κ (e + s • p) μ ν a b)
    (lam * t)) 0 = _
  have hd := deriv_comp_mul_left (f := fun s : ℝ => NativeDensity.palA κ (e + s • p) μ ν a b)
    (c := lam) (x := 0)
  rw [mul_zero, smul_eq_mul] at hd
  erw [hd]
  ring

/-- **Weight-one homogeneity of the Palatini sector** on the oriented chart. -/
theorem Lgc_scale (hlam0 : 0 < lam) (wp : FJ 𝔄 𝓗 𝓢) (hdet : 0 < wp.1.1.det) :
    Lgc D (jetE (fieldScale hlam) hlam wp) = lam ^ 4 * Lgc D wp := by
  have hdet' : 0 < (lam • wp.1.1).det := by rw [det_smul_mat]; positivity
  unfold Lgc
  rw [jetE_fieldScale']
  simp only []
  rw [NativeGravityJet.palatiniFirstOrder_eq D.κ D.Λ hdet',
    NativeGravityJet.palatiniFirstOrder_eq D.κ D.Λ hdet]
  have hΩ : ∀ μ, readerOmega (lam • wp.1.1) (fun μ => lam ^ 2 • (wp.2 μ).1) μ =
      lam • readerOmega wp.1.1 (fun μ => (wp.2 μ).1) μ :=
    fun μ => readerOmega_smul2 hlam _ _ μ
  simp only [hΩ, pal_smul hlam, deriv_palA_scale hlam, volume_smul, smul_mul_smul_comm,
    ← smul_sub, Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, mul_sub]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  · ring

/-- **Weight-one homogeneity of the native Lagrangian**:
`L₀(Φ_λw, λΦ_λp) = λ⁴L₀(w, p)` on the oriented chart (`λ > 0`). -/
theorem L0_scale (hlam0 : 0 < lam) (wp : FJ 𝔄 𝓗 𝓢) (hdet : 0 < wp.1.1.det) :
    L0 D (jetE (fieldScale hlam) hlam wp) = lam ^ 4 * L0 D wp := by
  rw [L0_eq, L0_eq, Lgc_scale D hlam hlam0 wp hdet, LYMc_scale D hlam, LHc_scale D hlam,
    LDc_scale D hlam]
  ring

/-- The oriented chart of first jets. -/
def posChart : Set (FJ 𝔄 𝓗 𝓢) := {wp | 0 < wp.1.1.det}

theorem isOpen_posChart : IsOpen (posChart : Set (FJ 𝔄 𝓗 𝓢)) :=
  isOpen_lt continuous_const (Continuous.matrix_det (continuous_fst.comp continuous_fst))

/-- **The native Euler covector under the dilation of the slab coordinates**:
`𝓔₀(Φ_λ ∘ Y ∘ (λ · + c))(x) = λ⁴ 𝓔₀(Y)(λx + c) ∘ Φ_λ⁻¹` (`λ > 0`, `det e > 0`). -/
theorem Rfull_dilate (hlam0 : 0 < lam) (c : R4) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ z, 0 < (Y z).1.det) (x : R4) :
    Rfull D (dilateF (fieldScale hlam) lam c Y) x =
      lam ^ 4 • (Rfull D Y (lam • x + c)).comp
        ((fieldScale (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) hlam).symm :
          Field 𝔄 𝓗 𝓢 →L[ℝ] Field 𝔄 𝓗 𝓢) :=
  contEuler_dilate (L := L0 D) (fieldScale hlam) hlam c isOpen_posChart
    (fun wp hwp => L0_scale D hlam hlam0 wp hwp) (fun z => hdet z) x

/-- The bosonic scaling `(δe, δA, δH) ↦ (λ⁻¹δe, λ⁻¹δA, δH)`. -/
def bosScaleInv (lam : ℝ) : (Mat × (Fin 4 → 𝔄) × 𝓗) →L[ℝ] (Mat × (Fin 4 → 𝔄) × 𝓗) :=
  (lam⁻¹ • ContinuousLinearMap.id ℝ Mat).prodMap
    ((lam⁻¹ • ContinuousLinearMap.id ℝ (Fin 4 → 𝔄)).prodMap (ContinuousLinearMap.id ℝ 𝓗))

theorem bosScaleInv_apply (lam : ℝ) (v : Mat × (Fin 4 → 𝔄) × 𝓗) :
    bosScaleInv lam v = (lam⁻¹ • v.1, lam⁻¹ • v.2.1, v.2.2) := rfl

/-- **The bosonic residual map under the dilation**:
`𝓡_B(Ỹ)(x) = λ⁴ 𝓡_B(Y)(λx + c) ∘ Φ_{B,λ}⁻¹`. -/
theorem RB_dilate (hlam0 : 0 < lam) (c : R4) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ z, 0 < (Y z).1.det) (x : R4) :
    RB D (dilateF (fieldScale hlam) lam c Y) x =
      lam ^ 4 • (RB D Y (lam • x + c)).comp (bosScaleInv lam) := by
  unfold RB
  rw [Rfull_dilate D hlam hlam0 c hdet x]
  ext v <;> rfl

/-- **The Dirac residual map under the dilation**: `𝓡_D(Ỹ)(x) = λ⁴ 𝓡_D(Y)(λx + c)`. -/
theorem RD_dilate (hlam0 : 0 < lam) (c : R4) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ z, 0 < (Y z).1.det) (x : R4) :
    RD D (dilateF (fieldScale hlam) lam c Y) x = lam ^ 4 • RD D Y (lam • x + c) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h := congrArg (fun T : Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ => T (ιS v)) (Rfull_dilate D hlam hlam0 c hdet x)
  have hs : (fieldScale (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) hlam).symm (ιS v) = ιS v := by
    rw [fieldScale_symm_apply, ιS_apply]
    simp
  refine h.trans ?_
  show lam ^ 4 • Rfull D Y (lam • x + c) ((fieldScale hlam).symm (ιS v)) =
    lam ^ 4 • Rfull D Y (lam • x + c) (ιS v)
  rw [hs]

end Native

end

end RenewalGeometry.FieldScaling
