/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeEulerConsistency
import RenewalGeometry.Continuum.ContEulerDerivativeBounds

/-!
# Structure of the continuum Einstein–Standard-Model Euler rows under the native scaling

Einstein–Standard-Model action-closure manuscript, `lem:native-scaling` and the physical residual
maps `𝓡_B`, `𝓡_D` of `thm:native-source` / `lem:native-tail-transfer`.

The continuum Lagrangian of the unchanged local action is `L₀ = limDensity (firstJetDensity D)`
(`NativeEulerConsistency`, identified sector by sector there).  Its Euler–Lagrange covector
`𝓔₀(y)(z) = contEuler L₀ y z ∈ (e, A, H, Ψ, Ψ̄)^*` has the **bosonic rows** (components dual to
the coframe, gauge and Higgs fields: Einstein, Yang–Mills and Higgs rows) and the **Dirac rows**
(components dual to `Ψ` and `Ψ̄`: Dirac and dual-Dirac rows):
`𝓡_B(y) = 𝓔₀(y) ∘ ι_B`, `𝓡_D(y) = 𝓔₀(y) ∘ ι_S` (`RB`, `RD`).

## Main results

* `Ldens` — the normalised continuum density `𝓛(ν; w, p) = 𝒢(ν, 0, (w; p))` of `lem:native-scaling`
  (`L₀(w, K p) = K² 𝓛(K⁻¹; w, p)`), smooth on the chart `det e ≠ 0` (`contDiffOn_Ldens`), with
  gradient `Gd(ν; w, p) = ∂_{(w,p)}𝓛` (`contDiffOn_Gd`).
* **`contEuler_native_scale`**: for `y(z) = ỹ(Kz)`,
  `𝓔₀(y)(z) = K² E_ν(ỹ)(Kz)` with the Euler operator `E_ν = eulerOp Gd ν` of the normalised density,
  `ν = 1/K` (`eq:native-density-scaling` on Euler rows).
* Bosonic/Dirac splitting `𝓛 = 𝓛^B + ν 𝓛^D` (`Ldens_eq`): the bosonic density does not depend on
  the spinor components of the jet (`Bdens_PB`); the Dirac density is affine in the spinor first
  differences with a coefficient depending only on the values (`Ddens_decomp`).
* **`eulerOp_comp_ιS`**: the Dirac rows of the normalised Euler operator are
  `E_ν(ỹ)(ξ) ∘ ι_S = ν Φ_D(ν; J¹ỹ(ξ))`, a smooth function `Φ_D` of the **first** jet
  (`contDiffOn_PhiD`): the Dirac rows have differential order one and carry one factor `K`
  (`𝓡_D(y)(z) = K Φ_D(ν; J¹ỹ(Kz))`, `RD_native_scale`).
-/

open Finset Filter Topology Metric Set NormedSpace
open scoped ContDiff

namespace RenewalGeometry.NativeTail

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency
open ContEulerBounds (JS jetP eulerOp contEuler_eq_eulerOp inlJ slotJ inrP)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

local notation "FJ" => JS (Field 𝔄 𝓗 𝓢)

/-! The covector spaces carry the operator norm; the instances are given explicitly because the
topology of the matrix factor found by instance search is only definitionally equal to the one
induced by the (local) matrix norm. -/

local instance instNACGdualFJ : NormedAddCommGroup (FJ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNSdualFJ : NormedSpace ℝ (FJ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNACGdualField : NormedAddCommGroup (Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNSdualField : NormedSpace ℝ (Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance instNACGdualBos : NormedAddCommGroup (Mat × (Fin 4 → 𝔄) × 𝓗 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNSdualBos : NormedSpace ℝ (Mat × (Fin 4 → 𝔄) × 𝓗 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-! ### The normalised continuum density -/

/-- The normalised continuum density `𝓛(ν; w, p) = 𝒢(ν, 0, (w; p))` (`lem:native-scaling` at
`ρ = 0`). -/
def Ldens (q : ℝ × FJ) : ℝ :=
  scaledDensity D (q.1, ((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))))

/-- The chart `det e ≠ 0`. -/
def chartU : Set (ℝ × FJ) := {q | q.2.1.1.det ≠ 0}

theorem isOpen_chartU : IsOpen (chartU : Set (ℝ × FJ)) :=
  isOpen_ne_fun (Continuous.matrix_det (continuous_fst.comp (continuous_fst.comp continuous_snd)))
    continuous_const

theorem jetChart_cmap {wp : FJ} (h : wp.1.1.det ≠ 0) :
    JetChart (cmap wp : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) := fun _ => h

theorem contDiffAt_Ldens {q : ℝ × FJ} (hq : q ∈ chartU) : ContDiffAt ℝ ∞ (Ldens D) q := by
  have hin : ContDiffAt ℝ ∞ (fun q : ℝ × FJ =>
      ((q.1, ((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) :
        ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) q := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × FJ => q.1) := contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × FJ =>
        (((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :
          ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :=
      contDiff_const.prodMk ((cmap : FJ →L[ℝ] NativeDensity.Jet (Field 𝔄 𝓗 𝓢)).contDiff.comp
        contDiff_snd)
    exact (h1.prodMk h2).contDiffAt
  exact (contDiffAt_scaledDensity D (ν := q.1) (jetChart_cmap hq)).comp q hin

theorem contDiffOn_Ldens : ContDiffOn ℝ ∞ (Ldens D) chartU :=
  fun q hq => (contDiffAt_Ldens D hq).contDiffWithinAt

/-- The gradient `Gd(ν; w, p) = ∂_{(w,p)}𝓛(ν; w, p)`. -/
def Gd (q : ℝ × FJ) : ContEulerBounds.Cov (Field 𝔄 𝓗 𝓢) :=
  (fderiv ℝ (Ldens D) q).comp (inrP ℝ FJ)

theorem contDiffOn_Gd : ContDiffOn ℝ ∞ (Gd D) chartU := by
  have h := (contDiffOn_Ldens D).fderiv_of_isOpen isOpen_chartU (m := ∞) (by simp)
  exact ((ContEulerBounds.preL (inrP ℝ FJ)).contDiff.comp_contDiffOn h)

theorem fderiv_slice_Ldens {q : ℝ × FJ} (hq : q ∈ chartU) :
    fderiv ℝ (fun wp => Ldens D (q.1, wp)) q.2 = Gd D q := by
  have hd : DifferentiableAt ℝ (Ldens D) q :=
    (contDiffAt_Ldens D hq).differentiableAt (by simp)
  have hin : HasFDerivAt (fun wp : FJ => ((q.1, wp) : ℝ × FJ))
      (inrP ℝ FJ) q.2 := by
    have := ((inrP ℝ FJ).hasFDerivAt (x := q.2)).const_add
      ((q.1, 0) : ℝ × FJ)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun wp => ?_)
    show ((q.1, wp) : ℝ × FJ) = (q.1, 0) + inrP ℝ FJ wp
    rw [ContEulerBounds.inrP_apply]
    simp
  have hd' : HasFDerivAt (Ldens D) (fderiv ℝ (Ldens D) q) (q.1, q.2) := by
    simpa using hd.hasFDerivAt
  exact (hd'.comp q.2 hin).fderiv

/-- **The native scaling of the continuum Euler rows**: for `y(z) = ỹ(K z)` with the first jets of
`ỹ` in the chart, `𝓔₀(y)(z) = K² E_ν(ỹ)(K z)`, `ν = 1/K`, where `E_ν = eulerOp Gd ν` is the Euler
operator of the normalised density. -/
theorem contEuler_native_scale {K : ℝ} (hK : K ≠ 0) (Yt : R4 → Field 𝔄 𝓗 𝓢)
    (hYt : ∀ ξ, ((K⁻¹, jet1 Yt ξ) : ℝ × FJ) ∈ chartU) (z : R4) :
    contEuler (limDensity (ι := Shift) (firstJetDensity D)) (fun z => Yt (K • z)) z =
      K ^ 2 • eulerOp (Gd D) K⁻¹ Yt (K • z) := by
  have h := contEuler_scale hK (limDensity_eq_scaled D hK) Yt z
  rw [h]
  congr 1
  have hL : limDensity (ι := Shift) (fun q => scaledDensity D (K⁻¹, q)) =
      fun wp => Ldens D (K⁻¹, wp) := rfl
  rw [hL, contEuler_eq_eulerOp (fun q => Ldens D q) (Gd D) K⁻¹ Yt
    (fun ξ => (fderiv_slice_Ldens D (hYt ξ)).symm)]


/-! ### Lines and directional derivatives -/

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_line (q d : E) : HasDerivAt (fun t : ℝ => q + t • d) d 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add q

/-- The directional derivative along a line on which `f` is affine. -/
theorem fderiv_apply_of_affine_line {f : E → ℝ} {q d : E} {c : ℝ} (hf : DifferentiableAt ℝ f q)
    (h : ∀ t : ℝ, f (q + t • d) = f q + t * c) : fderiv ℝ f q d = c := by
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line q d) (by simp)
  have h2 : HasDerivAt (fun t : ℝ => f (q + t • d)) c 0 := by
    have : (fun t : ℝ => f (q + t • d)) = fun t => f q + t * c := funext h
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (f q)
  exact h1.unique h2

end Lines

/-! ### Bosonic / Dirac splitting of the normalised density -/

/-- Zero the spinor components: `(e, A, H, Ψ, Ψ̄) ↦ (e, A, H, 0, 0)`. -/
def PB (w : Field 𝔄 𝓗 𝓢) : Field 𝔄 𝓗 𝓢 := (w.1, w.2.1, w.2.2.1, 0, 0)

theorem PB_add (w v : Field 𝔄 𝓗 𝓢) : PB (w + v) = PB w + PB v := by
  simp [PB, Prod.ext_iff]

/-- The spinor inclusion `(Ψ, Ψ̄) ↦ (0, 0, 0, Ψ, Ψ̄)`. -/
def ιS : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) (Field 𝔄 𝓗 𝓢) :=
  (ContinuousLinearMap.inr ℝ Mat _).comp ((ContinuousLinearMap.inr ℝ (Fin 4 → 𝔄) _).comp
    (ContinuousLinearMap.inr ℝ 𝓗 (𝓢 × CoSpinor 𝓢)))

theorem ιS_apply (s : 𝓢 × CoSpinor 𝓢) : (ιS s : Field 𝔄 𝓗 𝓢) = (0, 0, 0, s.1, s.2) := rfl

theorem PB_ιS (s : 𝓢 × CoSpinor 𝓢) : PB (ιS s : Field 𝔄 𝓗 𝓢) = 0 := rfl

theorem PB_smul_ιS (t : ℝ) (s : 𝓢 × CoSpinor 𝓢) : PB (t • (ιS s : Field 𝔄 𝓗 𝓢)) = 0 := by
  rw [← map_smul]; exact PB_ιS _

/-- The bosonic inclusion `(e, A, H) ↦ (e, A, H, 0, 0)`. -/
def ιB : ContEulerBounds.NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) (Field 𝔄 𝓗 𝓢) :=
  (ContinuousLinearMap.fst ℝ Mat _).prod
    (((ContinuousLinearMap.fst ℝ (Fin 4 → 𝔄) 𝓗).comp (ContinuousLinearMap.snd ℝ Mat _)).prod
      (((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) 𝓗).comp (ContinuousLinearMap.snd ℝ Mat _)).prod 0))

theorem norm_ιS_apply_le (s : 𝓢 × CoSpinor 𝓢) : ‖(ιS s : Field 𝔄 𝓗 𝓢)‖ ≤ ‖s‖ := by
  rw [ιS_apply]
  simp [Prod.norm_def]

theorem ιB_apply (x : Mat × (Fin 4 → 𝔄) × 𝓗) :
    (ιB x : Field 𝔄 𝓗 𝓢) = (x.1, x.2.1, x.2.2, 0) := rfl

theorem norm_ιB_apply_le (x : Mat × (Fin 4 → 𝔄) × 𝓗) : ‖(ιB x : Field 𝔄 𝓗 𝓢)‖ ≤ ‖x‖ := by
  rw [ιB_apply]
  simp only [Prod.norm_def, norm_zero]
  refine max_le (le_max_left _ _) (max_le ((le_max_left _ _).trans (le_max_right _ _))
    (max_le ((le_max_right _ _).trans (le_max_right _ _)) ?_))
  exact (norm_nonneg _).trans (le_max_left _ _)

/-- Precomposition of a covector with `ι_S` does not increase its norm. -/
theorem norm_comp_ιS_le (T : Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ) : ‖T.comp (ιS (𝔄 := 𝔄) (𝓗 := 𝓗))‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_ιS_apply_le s) (norm_nonneg _))

/-- Precomposition of a covector with `ι_B` does not increase its norm. -/
theorem norm_comp_ιB_le (T : Field 𝔄 𝓗 𝓢 →L[ℝ] ℝ) : ‖T.comp (ιB (𝓢 := 𝓢))‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_ιB_apply_le x) (norm_nonneg _))

/-- The bosonic part `𝓛^B` of the normalised density (Cartan/Palatini, cosmological, Yang–Mills
and Higgs sectors). -/
def Bdens (q : ℝ × FJ) : ℝ :=
  gravFirstJet D ((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) +
    (1 - q.1 ^ 2) * (D.Λ / D.κ) * volume q.2.1.1 +
    normYM D ((0 : ℝ), q.1, (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) +
    normHiggs D ((0 : ℝ), q.1, (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))

/-- The Dirac part `𝓛^D` of the normalised density. -/
def Ddens (q : ℝ × FJ) : ℝ :=
  normD D ((0 : ℝ), q.1, (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))

/-- `𝓛 = 𝓛^B + ν 𝓛^D` (`eq:native-density-scaling`). -/
theorem Ldens_eq (q : ℝ × FJ) : Ldens D q = Bdens D q + q.1 * Ddens D q := rfl

/-- The bosonic density does not see the spinor components of the jet. -/
theorem Bdens_PB (ν : ℝ) (w : Field 𝔄 𝓗 𝓢) (p : Fin 4 → Field 𝔄 𝓗 𝓢) :
    Bdens D (ν, (PB w, fun μ => PB (p μ))) = Bdens D (ν, (w, p)) := rfl

/-- The spinor-derivative coefficient of the Dirac density:
`s ↦ v(e) Re(i/2 (Ψ̄ γ^μ s_Ψ - s_Ψ̄ γ^μ Ψ))`. -/
def dlin (w : Field 𝔄 𝓗 𝓢) (μ : Fin 4) : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ :=
  volume w.1 • (Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ (Complex.I / 2)).comp
    ((w.2.2.2.2.comp (gammaMu D μ w.1)).comp (ContinuousLinearMap.fst ℝ 𝓢 (CoSpinor 𝓢)) -
      (ContinuousLinearMap.apply ℝ ℂ (gammaMu D μ w.1 w.2.2.2.1)).comp
        (ContinuousLinearMap.snd ℝ 𝓢 (CoSpinor 𝓢)))))

theorem dlin_apply (w : Field 𝔄 𝓗 𝓢) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) :
    dlin D w μ s = volume w.1 *
      (Complex.I / 2 * (w.2.2.2.2 (gammaMu D μ w.1 s.1) - s.2 (gammaMu D μ w.1 w.2.2.2.1))).re := by
  simp [dlin]
  ring

/-- **The Dirac density is affine in the spinor first differences**, with a coefficient depending
only on the values. -/
theorem Ddens_decomp (ν : ℝ) (w : Field 𝔄 𝓗 𝓢) (p : Fin 4 → Field 𝔄 𝓗 𝓢) :
    Ddens D (ν, (w, p)) = Ddens D (ν, (w, fun μ => PB (p μ))) +
      ∑ μ, dlin D w μ ((p μ).2.2.2.1, (p μ).2.2.2.2) := by
  simp only [Ddens, normD, nuDiracDiffJet, nuDiracDiffBarJet, nuDiracDiff, nuDiracDiffBar,
    cmap_apply, PB, jetOmega, dlin_apply]
  simp only [map_add, ContinuousLinearMap.add_apply, map_zero, add_zero,
    ContinuousLinearMap.zero_apply]
  have key : ∀ (f g k l : Fin 4 → ℂ) (e : ℂ),
      Complex.I / 2 * ∑ x, (f x + g x - (k x + l x)) - e =
        (Complex.I / 2 * ∑ x, (f x - k x) - e) + ∑ x, Complex.I / 2 * (g x - l x) := by
    intro f g k l e
    rw [← Finset.mul_sum]
    have : ∀ x, f x + g x - (k x + l x) = (f x - k x) + (g x - l x) := fun x => by ring
    simp_rw [this, Finset.sum_add_distrib]
    ring
  rw [key, Complex.add_re, Complex.re_sum, mul_add]
  congr 1
  rw [Finset.mul_sum]

/-- The Dirac density's gradient `G_D = ∂_{(w,p)}𝓛^D`. -/
def GD (q : ℝ × FJ) : ContEulerBounds.Cov (Field 𝔄 𝓗 𝓢) :=
  (fderiv ℝ (Ddens D) q).comp (inrP ℝ FJ)

theorem contDiffAt_Ddens {q : ℝ × FJ} (hq : q ∈ chartU) : ContDiffAt ℝ ∞ (Ddens D) q := by
  have hin : ContDiffAt ℝ ∞ (fun q : ℝ × FJ =>
      (((0 : ℝ), q.1, (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :
        ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) q :=
    (contDiff_const.prodMk (contDiff_fst.prodMk
      ((cmap : FJ →L[ℝ] NativeDensity.Jet (Field 𝔄 𝓗 𝓢)).contDiff.comp contDiff_snd))).contDiffAt
  exact (contDiffAt_normD D (p := ((0 : ℝ), q.1, cmap q.2)) hq).comp q hin

theorem contDiffOn_Ddens : ContDiffOn ℝ ∞ (Ddens D) chartU :=
  fun _ hq => (contDiffAt_Ddens D hq).contDiffWithinAt

theorem contDiffOn_GD : ContDiffOn ℝ ∞ (GD D) chartU := by
  have h := (contDiffOn_Ddens D).fderiv_of_isOpen isOpen_chartU (m := ∞) (by simp)
  exact ((ContEulerBounds.preL (inrP ℝ FJ)).contDiff.comp_contDiffOn h)

/-- The value-spinor line `t ↦ (ν, (w + ι_S(t s), p))`. -/
def lineS (q : ℝ × FJ) (s : 𝓢 × CoSpinor 𝓢) (t : ℝ) : ℝ × FJ :=
  (q.1, (q.2.1 + (ιS (t • s) : Field 𝔄 𝓗 𝓢), q.2.2))

theorem hasDerivAt_lineS (q : ℝ × FJ) (s : 𝓢 × CoSpinor 𝓢) :
    HasDerivAt (lineS q s) ((0 : ℝ), ((ιS s : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))) 0 := by
  unfold lineS
  have h1 : HasDerivAt (fun t : ℝ => (ιS (t • s) : Field 𝔄 𝓗 𝓢)) (ιS s) 0 := by
    have := (ιS (𝔄 := 𝔄) (𝓗 := 𝓗)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const s)
    exact this.congr_deriv (congrArg _ (one_smul ℝ s))
  exact (hasDerivAt_const _ _).prodMk ((h1.const_add q.2.1).prodMk (hasDerivAt_const _ _))

theorem lineS_zero (q : ℝ × FJ) (s : 𝓢 × CoSpinor 𝓢) : lineS q s 0 = q := by
  have h0 : (ιS ((0 : ℝ) • s) : Field 𝔄 𝓗 𝓢) = 0 :=
    (congrArg _ (zero_smul ℝ s)).trans (map_zero _)
  simp only [lineS]
  rw [h0, add_zero]

theorem Bdens_lineS (q : ℝ × FJ) (s : 𝓢 × CoSpinor 𝓢) (t : ℝ) :
    Bdens D (lineS q s t) = Bdens D q := by
  obtain ⟨ν, w, p⟩ := q
  simp only [lineS]
  rw [← Bdens_PB D, ← Bdens_PB D ν w p, PB_add, PB_ιS, add_zero]

/-- **Gradient of `𝓛` in a value-spinor direction**: `Gd(q)(ι_S s, 0) = ν G_D(q)(ι_S s, 0)`. -/
theorem Gd_inl_ιS {q : ℝ × FJ} (hq : q ∈ chartU) (s : 𝓢 × CoSpinor 𝓢) :
    Gd D q (inlJ (Field 𝔄 𝓗 𝓢) (ιS s)) =
      q.1 * GD D q (inlJ (Field 𝔄 𝓗 𝓢) (ιS s)) := by
  have hDd : DifferentiableAt ℝ (Ddens D) q := (contDiffAt_Ddens D hq).differentiableAt (by simp)
  have hLd : DifferentiableAt ℝ (Ldens D) q := (contDiffAt_Ldens D hq).differentiableAt (by simp)
  have hlineD := hDd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineS q s)
    (lineS_zero q s).symm
  have hlineL := hLd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineS q s)
    (lineS_zero q s).symm
  have hfun : (Ldens D ∘ lineS q s) = fun t => Bdens D q + q.1 * Ddens D (lineS q s t) := by
    funext t
    simp only [Function.comp_apply]
    rw [Ldens_eq, Bdens_lineS]
    rfl
  have h2 : HasDerivAt (fun t : ℝ => Bdens D q + q.1 * Ddens D (lineS q s t))
      (q.1 * fderiv ℝ (Ddens D) q ((0 : ℝ), ((ιS s : Field 𝔄 𝓗 𝓢),
        (0 : Fin 4 → Field 𝔄 𝓗 𝓢)))) 0 :=
    (hlineD.const_mul q.1).const_add (Bdens D q)
  rw [hfun] at hlineL
  have hval := hlineL.unique h2
  simp only [Gd, GD, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  exact hval


/-! ### The spinor first-difference direction -/

section Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative along a curve on which `f` is affine. -/
theorem fderiv_apply_of_affine_curve {f : E → ℝ} {q d : E} {γ : ℝ → E} {c : ℝ}
    (hf : DifferentiableAt ℝ f q) (hγ : HasDerivAt γ d 0) (hγ0 : γ 0 = q)
    (h : ∀ t : ℝ, f (γ t) = f q + t * c) : fderiv ℝ f q d = c := by
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have h2 : HasDerivAt (fun t : ℝ => f (γ t)) c 0 := by
    have : (fun t : ℝ => f (γ t)) = fun t => f q + t * c := funext h
    rw [this]
    exact ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (f q) |>.congr_deriv (by simp)
  exact h1.unique h2

end Curves

/-- The spinor components `x ↦ (Ψ, Ψ̄)`. -/
def spin (x : Field 𝔄 𝓗 𝓢) : 𝓢 × CoSpinor 𝓢 := (x.2.2.2.1, x.2.2.2.2)

theorem spin_add (x y : Field 𝔄 𝓗 𝓢) : spin (x + y) = spin x + spin y := rfl

theorem spin_ιS (s : 𝓢 × CoSpinor 𝓢) : spin (ιS s : Field 𝔄 𝓗 𝓢) = s := rfl

theorem PB_zero : PB (0 : Field 𝔄 𝓗 𝓢) = 0 := rfl

theorem spin_zero : spin (0 : Field 𝔄 𝓗 𝓢) = 0 := rfl

/-- The derivative-spinor line `t ↦ (ν, (w, p + e_μ ⊗ ι_S(t s)))`. -/
def lineP (q : ℝ × FJ) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) (t : ℝ) : ℝ × FJ :=
  (q.1, (q.2.1, q.2.2 + Pi.single μ (ιS (t • s) : Field 𝔄 𝓗 𝓢)))

/-- The direction of `lineP`. -/
def dirP (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) : ℝ × FJ :=
  ((0 : ℝ), ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (ιS s : Field 𝔄 𝓗 𝓢)))

theorem hasDerivAt_lineP (q : ℝ × FJ) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) :
    HasDerivAt (lineP q μ s) (dirP μ s) 0 := by
  unfold lineP dirP
  have h1 : HasDerivAt (fun t : ℝ => (ιS (t • s) : Field 𝔄 𝓗 𝓢)) (ιS s) 0 := by
    have := (ιS (𝔄 := 𝔄) (𝓗 := 𝓗)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const s)
    exact this.congr_deriv (congrArg _ (one_smul ℝ s))
  have h2 : HasDerivAt (fun t : ℝ => (Pi.single μ (ιS (t • s) : Field 𝔄 𝓗 𝓢) :
      Fin 4 → Field 𝔄 𝓗 𝓢)) (Pi.single μ (ιS s)) 0 :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Field 𝔄 𝓗 𝓢) μ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
  exact (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (h2.const_add q.2.2))

theorem lineP_zero (q : ℝ × FJ) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) : lineP q μ s 0 = q := by
  have h0 : (ιS ((0 : ℝ) • s) : Field 𝔄 𝓗 𝓢) = 0 :=
    (congrArg _ (zero_smul ℝ s)).trans (map_zero _)
  simp only [lineP]
  rw [h0, Pi.single_zero, add_zero]

theorem Bdens_lineP (q : ℝ × FJ) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) (t : ℝ) :
    Bdens D (lineP q μ s t) = Bdens D q := by
  obtain ⟨ν, w, p⟩ := q
  simp only [lineP]
  rw [← Bdens_PB D, ← Bdens_PB D ν w p]
  congr 3
  funext μ'
  rw [Pi.add_apply, PB_add]
  by_cases h : μ' = μ
  · subst h; rw [Pi.single_eq_same, PB_ιS, add_zero]
  · rw [Pi.single_eq_of_ne h, PB_zero, add_zero]

theorem Ddens_lineP (q : ℝ × FJ) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) (t : ℝ) :
    Ddens D (lineP q μ s t) = Ddens D q + t * dlin D q.2.1 μ s := by
  obtain ⟨ν, w, p⟩ := q
  simp only [lineP]
  rw [Ddens_decomp D ν w, Ddens_decomp D ν w p]
  have hPB : (fun μ' => PB ((p + (Pi.single μ (ιS (t • s)) : Fin 4 → Field 𝔄 𝓗 𝓢)) μ')) =
      fun μ' => PB (p μ') := by
    funext μ'
    rw [Pi.add_apply, PB_add]
    by_cases h : μ' = μ
    · subst h; rw [Pi.single_eq_same, PB_ιS, add_zero]
    · rw [Pi.single_eq_of_ne h, PB_zero, add_zero]
  rw [hPB, add_assoc]
  congr 1
  have hsp : ∀ μ', (((p + (Pi.single μ (ιS (t • s)) : Fin 4 → Field 𝔄 𝓗 𝓢)) μ').2.2.2.1,
      ((p + (Pi.single μ (ιS (t • s)) : Fin 4 → Field 𝔄 𝓗 𝓢)) μ').2.2.2.2) =
        spin (p μ') + spin ((Pi.single μ (ιS (t • s)) : Fin 4 → Field 𝔄 𝓗 𝓢) μ') := by
    intro μ'; rfl
  simp only [hsp, map_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single μ]
  · rw [Pi.single_eq_same, spin_ιS]
    exact (dlin D w μ).map_smul t s |>.trans (smul_eq_mul _ _)
  · intro μ' _ h; rw [Pi.single_eq_of_ne h, spin_zero, map_zero]
  · simp

/-- **Gradient of `𝓛^D` in a spinor-difference direction**: `G_D(q)(0, e_μ ⊗ ι_S s) = d_μ(w)(s)`,
independent of `ν` and of the first differences. -/
theorem GD_dirP {q : ℝ × FJ} (hq : q ∈ chartU) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) :
    GD D q (slotJ (Field 𝔄 𝓗 𝓢) μ (ιS s)) = dlin D q.2.1 μ s := by
  have hDd : DifferentiableAt ℝ (Ddens D) q := (contDiffAt_Ddens D hq).differentiableAt (by simp)
  simp only [GD, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.inr_apply]
  exact fderiv_apply_of_affine_curve hDd (hasDerivAt_lineP q μ s) (lineP_zero q μ s)
    (Ddens_lineP D q μ s)

/-- **Gradient of `𝓛` in a spinor-difference direction**: `Gd(q)(0, e_μ ⊗ ι_S s) = ν d_μ(w)(s)`. -/
theorem Gd_dirP {q : ℝ × FJ} (hq : q ∈ chartU) (μ : Fin 4) (s : 𝓢 × CoSpinor 𝓢) :
    Gd D q (slotJ (Field 𝔄 𝓗 𝓢) μ (ιS s)) = q.1 * dlin D q.2.1 μ s := by
  have hLd : DifferentiableAt ℝ (Ldens D) q := (contDiffAt_Ldens D hq).differentiableAt (by simp)
  simp only [Gd, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.inr_apply]
  refine fderiv_apply_of_affine_curve hLd (hasDerivAt_lineP q μ s) (lineP_zero q μ s) fun t => ?_
  rw [Ldens_eq, Ldens_eq, Bdens_lineP, Ddens_lineP]
  simp only [lineP]
  ring

/-! ### The Dirac rows as a first-order operator -/

/-- The chart of values `det e ≠ 0`. -/
def chartW : Set (ℝ × Field 𝔄 𝓗 𝓢) := {r | r.2.1.det ≠ 0}

theorem isOpen_chartW : IsOpen (chartW : Set (ℝ × Field 𝔄 𝓗 𝓢)) :=
  isOpen_ne_fun (Continuous.matrix_det (continuous_fst.comp continuous_snd)) continuous_const

/-- The spinor-difference coefficient `ℓ_μ(ν, w) = G_D(ν; w, 0)(0, e_μ ⊗ ι_S ·)` (equal to
`d_μ(w)`, `ellD_eq`). -/
def ellD (μ : Fin 4) (r : ℝ × Field 𝔄 𝓗 𝓢) : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ :=
  (GD D (r.1, (r.2, 0))).comp ((slotJ (Field 𝔄 𝓗 𝓢) μ).comp ιS)

theorem ellD_eq {r : ℝ × Field 𝔄 𝓗 𝓢} (hr : r ∈ chartW) (μ : Fin 4) :
    ellD D μ r = dlin D r.2 μ := by
  refine ContinuousLinearMap.ext fun s => ?_
  simp only [ellD, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.single_apply]
  exact GD_dirP D (q := (r.1, (r.2, 0))) hr μ s

theorem GD_comp_dirP {q : ℝ × FJ} (hq : q ∈ chartU) (μ : Fin 4) :
    (GD D q).comp ((slotJ (Field 𝔄 𝓗 𝓢) μ).comp ιS) = ellD D μ (q.1, q.2.1) := by
  rw [ellD_eq D (r := (q.1, q.2.1)) hq]
  refine ContinuousLinearMap.ext fun s => ?_
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply]
  exact GD_dirP D hq μ s

theorem contDiffOn_ellD (μ : Fin 4) : ContDiffOn ℝ ∞ (ellD D μ) chartW := by
  have hmap : ContDiff ℝ ∞ (fun r : ℝ × Field 𝔄 𝓗 𝓢 => ((r.1, (r.2, 0)) : ℝ × FJ)) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have h := (contDiffOn_GD D).comp hmap.contDiffOn (fun r hr => hr)
  exact (ContEulerBounds.preL ((slotJ (Field 𝔄 𝓗 𝓢) μ).comp ιS)).contDiff.comp_contDiffOn h

/-- **The Dirac rows of the normalised Euler operator** in first-order form:
`E^D_ν(ỹ)(ξ) = G_D(ν; J¹ỹ(ξ))(ι_S ·, 0) - Σ_μ ∂_μ[ℓ_μ(ν, ỹ)](ξ)` — the coefficients `G_D` and
`ℓ_μ` are smooth, the second term differentiates only the values of `ỹ`. -/
def dirOp (ν : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) (ξ : R4) : ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ :=
  (GD D (ν, jet1 Y ξ)).comp ((inlJ (Field 𝔄 𝓗 𝓢)).comp ιS) -
    ∑ μ, fderiv ℝ (fun z' => ellD D μ (ν, Y z')) ξ (evec μ)

/-- **The Dirac rows of the normalised Euler operator are first order**:
`E_ν(ỹ)(ξ) ∘ ι_S = ν E^D_ν(ỹ)(ξ)` (`dirOp`). -/
theorem eulerOp_comp_ιS {ν : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hch : ∀ ξ, ((ν, jet1 Y ξ) : ℝ × FJ) ∈ chartU) (ξ : R4) :
    (eulerOp (Gd D) ν Y ξ).comp (ιS (𝔄 := 𝔄) (𝓗 := 𝓗)) = ν • dirOp D ν Y ξ := by
  have hJ : ContDiff ℝ 1 (jetP ν Y) :=
    ContEulerBounds.contDiff_jetP ν (n := 1) (hY.of_le (ContEulerBounds.natCast_le_infty _))
  have hGJ : ContDiff ℝ 1 (Gd D ∘ jetP ν Y) :=
    ((contDiffOn_Gd D).of_le (by simp)).comp_contDiff hJ hch
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  refine ContinuousLinearMap.ext fun s => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContEulerBounds.eulerOp_slot,
    dirOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  · exact Gd_inl_ιS D (hch ξ) s
  · refine Finset.sum_congr rfl fun μ _ => ?_
    have hdiff : DifferentiableAt ℝ (fun z' => (Gd D (jetP ν Y z')).comp
        (slotJ (Field 𝔄 𝓗 𝓢) μ)) ξ :=
      ((ContEulerBounds.preL (slotJ (Field 𝔄 𝓗 𝓢) μ)).differentiable.comp
        (hGJ.differentiable (by simp))) ξ
    have heval : fderiv ℝ (fun z' => (Gd D (jetP ν Y z')).comp (slotJ (Field 𝔄 𝓗 𝓢) μ)) ξ
        (evec μ) (ιS s) =
        fderiv ℝ (fun z' => (Gd D (jetP ν Y z')).comp (slotJ (Field 𝔄 𝓗 𝓢) μ) (ιS s)) ξ
          (evec μ) := by
      have := ((ContinuousLinearMap.apply ℝ ℝ (ιS s : Field 𝔄 𝓗 𝓢)).hasFDerivAt.comp ξ
        hdiff.hasFDerivAt).fderiv
      rw [show (fun z' => (Gd D (jetP ν Y z')).comp (slotJ (Field 𝔄 𝓗 𝓢) μ) (ιS s)) =
          ⇑(ContinuousLinearMap.apply ℝ ℝ (ιS s : Field 𝔄 𝓗 𝓢)) ∘ (fun z' =>
            (Gd D (jetP ν Y z')).comp (slotJ (Field 𝔄 𝓗 𝓢) μ)) from rfl, this]
      rfl
    have hfun : (fun z' => (Gd D (jetP ν Y z')).comp (slotJ (Field 𝔄 𝓗 𝓢) μ) (ιS s)) =
        fun z' => ν * ellD D μ (ν, Y z') s := by
      funext z'
      rw [ContinuousLinearMap.comp_apply, jetP, Gd_dirP D (hch z') μ s,
        ellD_eq D (r := (ν, Y z')) (hch z') μ]
      rfl
    rw [heval, hfun]
    have hmap : ContDiff ℝ ∞ (fun z' : R4 => ((ν, Y z') : ℝ × Field 𝔄 𝓗 𝓢)) :=
      contDiff_const.prodMk hY
    have hEY : ContDiff ℝ ∞ (fun z' => ellD D μ (ν, Y z')) :=
      (contDiffOn_ellD D μ).comp_contDiff hmap (fun z' => hch z')
    have hd : DifferentiableAt ℝ (fun z' => ellD D μ (ν, Y z')) ξ :=
      hEY.differentiable (by simp) ξ
    have hcomp := ((ν • ContinuousLinearMap.apply ℝ ℝ s).hasFDerivAt.comp ξ hd.hasFDerivAt).fderiv
    rw [show (fun z' => ν * ellD D μ (ν, Y z') s) =
      ⇑(ν • ContinuousLinearMap.apply ℝ ℝ s) ∘ (fun z' => ellD D μ (ν, Y z')) from by
        funext z'; simp, hcomp]
    simp

end

end RenewalGeometry.NativeTail
