/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordDilate
import RenewalGeometry.Continuum.NativeSourceCompareGeneric

/-!
# The extraction maps as smooth continuous-linear-map fields of the coframe

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (source-budget
comparison, first part).  The bosonic and Dirac extraction maps `RecordTuple.MBf`,
`RecordTuple.MDf` (slab residuals of the actual tuple as linear images of the native Euler rows)
are linear in the row and smooth in the coframe value on the nondegenerate chart:

* `MBl`, `MDl` (linear), `MBc` — the extraction maps as (continuous) linear maps;
* `coordB`, `coordD` — their coordinate functionals `ρ ↦ P(MB(E)ρ)`, `ρ ↦ P(MD(E)ρ)`;
  **`contDiffOn_coordB`**, **`contDiffOn_coordD`** — smooth on `detU = {det E ≠ 0}`;
* `gB`, `gD` — the composition with the dilation of the slab coordinates (`E ↦ 2πE`, the row
  rescaling `𝓡 ↦ (2π)⁴𝓡 ∘ Φ⁻¹` of `FieldScaling.RB_dilate`); **`bosF_dil`**, **`dirF_dil`** — the
  slab residual coordinates of the actual tuple of a dilated record are `gB(e(ξ))𝓡_B(ξ)`,
  `gD(e(ξ))𝓡_D(ξ)` at `ξ = 2πx + t₀e₀`.
-/

open Finset Set
open scoped Matrix ContDiff Real

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect NativeStressEuler NativeTail ActualJetState ActualJetCompleteForcing
open FieldScaling
open ContEulerBounds (NCLM)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Smoothness of matrix-valued maps -/

section MatSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_mat {f : E → Mat} {x : E} (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => f y i j) x) :
    ContDiffAt ℝ ∞ f x :=
  contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => h i j

theorem contDiffAt_mat_entry {f : E → Mat} {x : E} (h : ContDiffAt ℝ ∞ f x) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => f y i j) x :=
  contDiffAt_pi.1 (contDiffAt_pi.1 h i) j

theorem contDiffAt_matMul {f g : E → Mat} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) : ContDiffAt ℝ ∞ (fun y => f y * g y) x := by
  refine contDiffAt_mat fun i j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (contDiffAt_mat_entry hf i k).mul (contDiffAt_mat_entry hg k j)

theorem contDiffAt_matTranspose {f : E → Mat} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => (f y)ᵀ) x :=
  contDiffAt_mat fun i j => by simpa using contDiffAt_mat_entry hf j i

theorem contDiffAt_matInv {e : Mat} (he : e.det ≠ 0) : ContDiffAt ℝ ∞ (fun E : Mat => E⁻¹) e :=
  contDiffAt_mat fun i j => contDiffAt_invEntry i j he

theorem contDiffAt_metricS {e : Mat} (he : e.det ≠ 0) (k : Mat) :
    ContDiffAt ℝ ∞ (fun E : Mat => metricS E k * E) e := by
  unfold metricS
  have hi := contDiffAt_matInv he
  refine contDiffAt_matMul ?_ contDiffAt_id
  refine (contDiffAt_matMul (contDiffAt_matMul (contDiffAt_matMul contDiffAt_const
    (contDiffAt_matTranspose hi)) contDiffAt_const) hi).const_smul (1 / 2 : ℝ)

theorem contDiffAt_metric_entry {e : Mat} (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun E : Mat => metric E a b) e :=
  contDiffAt_mat_entry contDiff_metric.contDiffAt a b

theorem contDiffAt_metricInv_entry {e : Mat} (he : e.det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun E : Mat => (metric E)⁻¹ a b) e :=
  (contDiffAt_invEntry a b (det_metric_ne_zero he)).comp e contDiff_metric.contDiffAt

theorem contDiffAt_volume_inv {e : Mat} (he : e.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun E : Mat => (volume E)⁻¹) e := by
  refine (contDiffAt_volume he).inv ?_
  rw [volume_eq_abs_det]; exact abs_ne_zero.2 he

end MatSmooth

/-! ### The extraction maps are linear in the row -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

theorem EtrOf_add (E : Mat) (ρ ρ' : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    EtrOf M E (ρ + ρ') = EtrOf M E ρ + EtrOf M E ρ' := by
  funext a b
  simp only [EtrOf, traceRev, trG, lowerE, ContinuousLinearMap.add_apply, Pi.add_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem trG_smul' (gi X : Fin 4 → Fin 4 → ℝ) (r : ℝ) :
    trG gi (fun a b => r * X a b) = r * trG gi X := by
  unfold trG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem EtrOf_smul (E : Mat) (r : ℝ) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    EtrOf M E (r • ρ) = r • EtrOf M E ρ := by
  have hT : (lowerE E fun c d => -(M.κ / volume E) * (r • ρ) (metricS E (symTest c d) * E, 0, 0))
      = fun a b => r * lowerE E (fun c d => -(M.κ / volume E) *
        ρ (metricS E (symTest c d) * E, 0, 0)) a b := by
    funext a b
    rw [← lowerE_smul]
    congr 1
    funext c d
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  funext a b
  simp only [EtrOf, hT, traceRev, trG_smul', Pi.smul_apply, smul_eq_mul]
  ring

theorem rAOf_add (E : Mat) (ρ ρ' : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    rAOf M E (ρ + ρ') = rAOf M E ρ + rAOf M E ρ' := by
  funext σ
  simp only [rAOf, ContinuousLinearMap.add_apply, Pi.add_apply]
  rw [← map_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [rieszVec_add _ (fun y => ρ (0, Pi.single ν y, 0)) (fun y => ρ' (0, Pi.single ν y, 0)),
    smul_add, smul_add]

theorem rAOf_smul (E : Mat) (r : ℝ) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    rAOf M E (r • ρ) = r • rAOf M E ρ := by
  funext σ
  simp only [rAOf, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← map_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [rieszVec_smul _ r (fun y => ρ (0, Pi.single ν y, 0)), smul_comm r, smul_comm r]

theorem rHOf_add (E : Mat) (ρ ρ' : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    rHOf M E (ρ + ρ') = rHOf M E ρ + rHOf M E ρ' := by
  simp only [rHOf, ContinuousLinearMap.add_apply]
  rw [rieszVec_add, smul_add]

theorem rHOf_smul (E : Mat) (r : ℝ) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    rHOf M E (r • ρ) = r • rHOf M E ρ := by
  simp only [rHOf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [rieszVec_smul, smul_comm]

/-- The bosonic extraction as a linear map. -/
def MBl (E : Mat) : (Bos 𝔄 𝓗 →L[ℝ] ℝ) →ₗ[ℝ] BosP m (HSp M) where
  toFun := MBf M E
  map_add' ρ ρ' := by
    simp only [MBf, EtrOf_add, rAOf_add, rHOf_add]; rfl
  map_smul' r ρ := by
    simp only [MBf, EtrOf_smul, rAOf_smul, rHOf_smul]; rfl

/-- **The bosonic extraction** `MB(e)` as a continuous linear map. -/
def MBc (E : Mat) : (Bos 𝔄 𝓗 →L[ℝ] ℝ) →L[ℝ] BosP m (HSp M) :=
  LinearMap.toContinuousLinearMap (MBl M E)

theorem MBc_apply (E : Mat) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) : MBc M E ρ = MBf M E ρ := rfl

theorem rDOf_add (E : Mat) (ρ ρ' : Dir 𝓢 →L[ℝ] ℝ) :
    rDOf M E (ρ + ρ') = rDOf M E ρ + rDOf M E ρ' := by
  simp only [rDOf, ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

theorem rDOf_smul (E : Mat) (r : ℝ) (ρ : Dir 𝓢 →L[ℝ] ℝ) :
    rDOf M E (r • ρ) = r • rDOf M E ρ := by
  simp only [rDOf, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
  rw [smul_comm]

theorem rDbOf_add (E : Mat) (ρ ρ' : Dir 𝓢 →L[ℝ] ℝ) :
    rDbOf M E (ρ + ρ') = rDbOf M E ρ + rDbOf M E ρ' := by
  ext w
  simp only [rDbOf, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, smul_add, smul_sub]
  ring

theorem rDbOf_smul (E : Mat) (r : ℝ) (ρ : Dir 𝓢 →L[ℝ] ℝ) :
    rDbOf M E (r • ρ) = r • rDbOf M E ρ := by
  ext w
  simp only [rDbOf, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- The Dirac extraction as a linear map. -/
def MDl (E : Mat) : (Dir 𝓢 →L[ℝ] ℝ) →ₗ[ℝ] 𝓢 × CoSpinor 𝓢 where
  toFun := MDf M E
  map_add' ρ ρ' := by simp only [MDf, rDOf_add, rDbOf_add]; rfl
  map_smul' r ρ := by simp only [MDf, rDOf_smul, rDbOf_smul]; rfl

/-! ### Smoothness of the extraction maps in the coframe -/

section Smooth

variable {e : Mat}

theorem contDiffAt_lowerE_row (he : e.det ≠ 0) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun E : Mat => lowerE E (fun c d => -(M.κ / volume E) *
      ρ (metricS E (symTest c d) * E, 0, 0)) a b) e := by
  unfold lowerE
  have hv : volume e ≠ 0 := by rw [volume_eq_abs_det]; exact abs_ne_zero.2 he
  refine ContDiffAt.sum fun c _ => ContDiffAt.sum fun d _ => ?_
  refine ((contDiffAt_metric_entry a c).mul (contDiffAt_metric_entry b d)).mul ?_
  refine (contDiffAt_const.div (contDiffAt_volume he) hv).neg.mul ?_
  exact ρ.contDiff.contDiffAt.comp e ((contDiffAt_metricS he _).prodMk contDiffAt_const)

theorem contDiffAt_EtrOf (he : e.det ≠ 0) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (fun E : Mat => EtrOf M E ρ) e := by
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  simp only [EtrOf, traceRev, trG]
  refine (contDiffAt_lowerE_row M he ρ a b).sub ?_
  refine (contDiffAt_const.mul (contDiffAt_metric_entry a b)).mul ?_
  exact ContDiffAt.sum fun μ _ => ContDiffAt.sum fun ν _ =>
    (contDiffAt_metricInv_entry he μ ν).mul (contDiffAt_lowerE_row M he ρ μ ν)

theorem contDiffAt_rAOf (he : e.det ≠ 0) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (fun E : Mat => rAOf M E ρ) e := by
  refine contDiffAt_pi.mpr fun σ => ?_
  simp only [rAOf]
  refine (contDiff_phi M).contDiffAt.comp e ?_
  exact ContDiffAt.sum fun ν _ =>
    (contDiffAt_metric_entry σ ν).smul ((contDiffAt_volume_inv he).smul contDiffAt_const)

theorem contDiffAt_rHOf (he : e.det ≠ 0) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (fun E : Mat => rHOf M E ρ) e := by
  have hv : volume e ≠ 0 := by rw [volume_eq_abs_det]; exact abs_ne_zero.2 he
  simp only [rHOf]
  exact ((contDiffAt_const.mul (contDiffAt_volume he)).inv (mul_ne_zero two_ne_zero hv)).smul
    contDiffAt_const

theorem contDiffAt_MBf (he : e.det ≠ 0) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (fun E : Mat => MBf M E ρ) e :=
  (contDiffAt_EtrOf M he ρ).prodMk ((contDiffAt_rAOf M he ρ).prodMk (contDiffAt_rHOf M he ρ))

theorem contDiffAt_MDf (he : e.det ≠ 0) (ρ : Dir 𝓢 →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (fun E : Mat => MDf M E ρ) e := by
  refine ContDiffAt.prodMk ?_ ?_
  · simp only [rDOf]
    exact (contDiffAt_volume_inv he).smul contDiffAt_const
  · simp only [rDbOf]
    exact (contDiffAt_volume_inv he).neg.smul contDiffAt_const

end Smooth

/-! ### Coordinate functionals of the extractions -/

/-- The nondegenerate coframe chart. -/
def detU : Set Mat := {E | E.det ≠ 0}

theorem isOpen_detU : IsOpen detU :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

/-- A coordinate functional of the bosonic extraction, `ρ ↦ P(MB(E)ρ)`. -/
def coordB (P : BosP m (HSp M) →L[ℝ] ℝ) (E : Mat) :
    NCLM (NCLM (Bos 𝔄 𝓗) ℝ) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => P (MBf M E ρ)
      map_add' := fun ρ ρ' => by
        have h := (MBl M E).map_add ρ ρ'
        simp only [MBl, LinearMap.coe_mk, AddHom.coe_mk] at h
        exact (congrArg P h).trans (P.map_add _ _)
      map_smul' := fun r ρ => by
        have h := (MBl M E).map_smul r ρ
        simp only [MBl, LinearMap.coe_mk, AddHom.coe_mk] at h
        exact (congrArg P h).trans (P.map_smul _ _) }

theorem coordB_apply (P : BosP m (HSp M) →L[ℝ] ℝ) (E : Mat) (ρ : NCLM (Bos 𝔄 𝓗) ℝ) :
    coordB M P E ρ = P (MBf M E ρ) := rfl

/-- A coordinate functional of the Dirac extraction, `ρ ↦ P(MD(E)ρ)`. -/
def coordD (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) (E : Mat) :
    NCLM (NCLM (Dir 𝓢) ℝ) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => P (MDf M E ρ)
      map_add' := fun ρ ρ' => by
        have h := (MDl M E).map_add ρ ρ'
        simp only [MDl, LinearMap.coe_mk, AddHom.coe_mk] at h
        exact (congrArg P h).trans (P.map_add _ _)
      map_smul' := fun r ρ => by
        have h := (MDl M E).map_smul r ρ
        simp only [MDl, LinearMap.coe_mk, AddHom.coe_mk] at h
        exact (congrArg P h).trans (P.map_smul _ _) }

theorem coordD_apply (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) (E : Mat) (ρ : NCLM (Dir 𝓢) ℝ) :
    coordD M P E ρ = P (MDf M E ρ) := rfl

theorem contDiffOn_coordB (P : BosP m (HSp M) →L[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (coordB M P) detU := by
  refine contDiffOn_clm_apply.2 fun ρ => ?_
  intro E hE
  exact (P.contDiff.contDiffAt.comp E (contDiffAt_MBf M hE ρ)).contDiffWithinAt

theorem contDiffOn_coordD (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (coordD M P) detU := by
  refine contDiffOn_clm_apply.2 fun ρ => ?_
  intro E hE
  exact (P.contDiff.contDiffAt.comp E (contDiffAt_MDf M hE ρ)).contDiffWithinAt

/-! ### The dilated slab residuals -/

/-- The bosonic row rescaling `𝓡 ↦ (2π)⁴ 𝓡 ∘ Φ_{B,2π}⁻¹`. -/
def scaleB : NCLM (NCLM (Bos 𝔄 𝓗) ℝ) (NCLM (Bos 𝔄 𝓗) ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => (2 * π) ^ 4 • ρ.comp (bosScaleInv (2 * π))
      map_add' := fun ρ ρ' => ContinuousLinearMap.ext fun v => by
        show (2 * π) ^ 4 * (ρ (bosScaleInv (2 * π) v) + ρ' (bosScaleInv (2 * π) v)) =
          (2 * π) ^ 4 * ρ (bosScaleInv (2 * π) v) + (2 * π) ^ 4 * ρ' (bosScaleInv (2 * π) v)
        ring
      map_smul' := fun r ρ => ContinuousLinearMap.ext fun v => by
        show (2 * π) ^ 4 * (r * ρ (bosScaleInv (2 * π) v)) =
          r * ((2 * π) ^ 4 * ρ (bosScaleInv (2 * π) v))
        ring }

theorem scaleB_apply (ρ : NCLM (Bos 𝔄 𝓗) ℝ) :
    scaleB ρ = (2 * π) ^ 4 • ρ.comp (bosScaleInv (2 * π)) := rfl

/-- **The dilated bosonic coordinate coefficient** `E ↦ (ρ ↦ P(MB(2πE)((2π)⁴ρ∘Φ⁻¹)))`. -/
def gB (P : BosP m (HSp M) →L[ℝ] ℝ) (E : Mat) : NCLM (NCLM (Bos 𝔄 𝓗) ℝ) ℝ :=
  (coordB M P ((2 * π) • E)).comp scaleB

/-- **The dilated Dirac coordinate coefficient** `E ↦ (2π)⁴ P(MD(2πE)·)`. -/
def gD (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) (E : Mat) : NCLM (NCLM (Dir 𝓢) ℝ) ℝ :=
  (2 * π) ^ 4 • coordD M P ((2 * π) • E)

theorem smul_mem_detU {E : Mat} (hE : E ∈ detU) : (2 * π) • E ∈ detU := by
  show ((2 * π) • E).det ≠ 0
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ two_pi_ne) hE

theorem contDiffOn_gB (P : BosP m (HSp M) →L[ℝ] ℝ) : ContDiffOn ℝ ∞ (gB M P) detU := by
  have h1 : ContDiffOn ℝ ∞ (fun E : Mat => coordB M P ((2 * π) • E)) detU :=
    (contDiffOn_coordB M P).comp (contDiff_const_smul _).contDiffOn fun E hE => smul_mem_detU hE
  exact h1.clm_comp contDiffOn_const

theorem contDiffOn_gD (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) : ContDiffOn ℝ ∞ (gD M P) detU := by
  have h1 : ContDiffOn ℝ ∞ (fun E : Mat => coordD M P ((2 * π) • E)) detU :=
    (contDiffOn_coordD M P).comp (contDiff_const_smul _).contDiffOn fun E hE => smul_mem_detU hE
  exact h1.const_smul _

variable {M}

/-- **The bosonic slab residual of the actual tuple of a dilated native field**:
`bosF(z)(x) = MB(2πe(ξ)) ((2π)⁴ 𝓡_B^𝔤(Y)(ξ) ∘ Φ⁻¹)`, `ξ = 2πx + t₀e₀`, with the physical bosonic
rows `𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB πg` (gauge rows in the gauge Lie algebra). -/
theorem bosF_dil {δ : ℝ} (hδ : 0 < δ) {t₀ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ z, 0 < (Y z).1.det) (h : TupleHyp M δ (dilField t₀ Y))
    (P : BosP m (HSp M) →L[ℝ] ℝ) (x : R4) :
    P (bosF (toSMData M δ) (toTuple hδ h) x) =
      gB M P (Y ((2 * π) • x + Pi.single 0 t₀)).1
        (RBP M.toData M.πg Y ((2 * π) • x + Pi.single 0 t₀)) := by
  rw [bosF_toTuple hδ h x]
  have h1 := RBP_dilate M.toData M.πg (two_pi_ne) two_pi_pos (Pi.single 0 t₀) hdet x
  have h2 : (dilField t₀ Y x).1 = (2 * π) • (Y ((2 * π) • x + Pi.single 0 t₀)).1 := rfl
  rw [h2]
  show P (MBf M _ (RBP M.toData M.πg (dilField t₀ Y) x)) = _
  unfold dilField
  rw [h1]
  rfl

/-- **The Dirac slab residual of the actual tuple of a dilated native field**:
`dirF(z)(x) = (2π)⁴ MD(2πe(ξ)) 𝓡_D(Y)(ξ)`. -/
theorem dirF_dil {δ : ℝ} (hδ : 0 < δ) {t₀ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ z, 0 < (Y z).1.det) (h : TupleHyp M δ (dilField t₀ Y))
    (P : 𝓢 × CoSpinor 𝓢 →L[ℝ] ℝ) (x : R4) :
    P (dirF (toSMData M δ) (toTuple hδ h) x) =
      gD M P (Y ((2 * π) • x + Pi.single 0 t₀)).1
        (RD M.toData Y ((2 * π) • x + Pi.single 0 t₀)) := by
  rw [dirF_toTuple hδ h x]
  have h1 := RD_dilate M.toData (two_pi_ne) two_pi_pos (Pi.single 0 t₀) hdet x
  have h2 : (dilField t₀ Y x).1 = (2 * π) • (Y ((2 * π) • x + Pi.single 0 t₀)).1 := rfl
  rw [h2]
  show P (MDf M _ (RD M.toData (dilField t₀ Y) x)) = _
  unfold dilField
  rw [h1]
  show P (MDf M _ ((2 * π) ^ 4 • _)) = (2 * π) ^ 4 • P (MDf M _ _)
  rw [← P.map_smul]
  congr 1
  exact (MDl M _).map_smul _ _

end

end RenewalGeometry.RecordTuple
