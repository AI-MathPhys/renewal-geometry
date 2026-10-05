/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeTailTransferBounds

/-!
# Real-analyticity of the normalised Einstein–Standard-Model density on the chart

Einstein–Standard-Model action-closure manuscript, proof of `thm:native-source` ("taking its
width `a/K` with `a` small relative to the declared field-value and inverse-metric margins
preserves the analytic branches of every algebraic coefficient").

The normalised density `𝒢(ν, ρ, ξ)` of `lem:native-scaling` (`NativeEulerConsistency.scaledDensity`)
is built from determinants, matrix inverses, the volume `|det e|`, the Palatini coefficients, the
torsion-free reader connection, the removable plaquette quotients and the logarithm series, and
the representation/coefficient data (continuous linear and bilinear maps).  The library proves
`C^∞` regularity at `ρ = 0`; every building block is in fact proved `C^k` for **every**
`k : WithTop ℕ∞`, so the same proofs give `C^ω`, i.e. real-analyticity
(`ContDiffAt.analyticAt`).

## Main results

* `contDiffAt_omega_scaledDensity`: `𝒢` is `C^ω` at every `(ν, 0, ξ)` with `ξ` in the
  nondegenerate chart.
* **`analyticAt_Ldens`**, `analyticAt_Ddens`: the continuum normalised density
  `𝓛(ν; w, p)` and its Dirac part are real-analytic on the chart `det e ≠ 0`.
* **`analyticAt_Gd`**, `analyticAt_GD`, `analyticAt_G1D`, `analyticAt_ellD`: the gradient maps
  entering the Euler rows are real-analytic on the chart.
-/

open Finset Filter Topology Metric Set NormedSpace
open scoped ContDiff

namespace RenewalGeometry.NativeAnalytic

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency NativeTail
open ContEulerBounds (JS jetP jetQ eulerOp inlJ slotJ inrP)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### `C^ω` regularity of the building blocks -/

theorem contDiffAt_omega_readerOmega_entry (μ a b : Fin 4) {q : Mat × (Fin 4 → Mat)}
    (hq : q.1.det ≠ 0) :
    ContDiffAt ℝ ω (fun q : Mat × (Fin 4 → Mat) => readerOmega q.1 q.2 μ a b) q := by
  have hm : (metric q.1).det ≠ 0 := det_metric_ne_zero hq
  simp only [readerOmega, NativeScaling.readerGamma, NativeScaling.readerG, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, ← invEntry_apply]
  fun_prop (disch := assumption)

theorem contDiffAt_omega_dqPal (κ : ℝ) (μ ν a b : Fin 4) {q : ℝ × Mat × Mat}
    (h0 : q.2.1.det ≠ 0) (h1 : (q.2.1 + q.1 • q.2.2).det ≠ 0) :
    ContDiffAt ℝ ω (fun q : ℝ × Mat × Mat => dqPal κ q.1 q.2.1 q.2.2 μ ν a b) q := by
  unfold dqPal palBil
  simp only [Matrix.neg_apply, Matrix.mul_apply, ← invEntry_apply]
  fun_prop (disch := assumption)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

theorem contDiffAt_omega_jetOmega (μ : Fin 4) {ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (he : (ξ.1 none).1.det ≠ 0) : ContDiffAt ℝ ω (jetOmega μ) ξ := by
  unfold jetOmega
  have h1 : ContDiffAt ℝ ω (fun ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢) =>
      ((ξ.1 none).1, fun lam => (ξ.2 (none, lam)).1)) ξ := by fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_omega_readerOmega_entry μ a b
    (q := ((ξ.1 none).1, fun lam => (ξ.2 (none, lam)).1)) he).comp ξ h1

theorem contDiffAt_omega_jetOmegaShift (ν μ : Fin 4) {ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (he : (ξ.1 (some (true, μ))).1.det ≠ 0) : ContDiffAt ℝ ω (jetOmegaShift ν μ) ξ := by
  unfold jetOmegaShift
  have h1 : ContDiffAt ℝ ω (fun ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢) =>
      ((ξ.1 (some (true, μ))).1, fun lam => (ξ.2 (some (true, μ), lam)).1)) ξ := by fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_omega_readerOmega_entry ν a b
    (q := ((ξ.1 (some (true, μ))).1, fun lam => (ξ.2 (some (true, μ), lam)).1)) he).comp ξ h1

theorem contDiffAt_omega_remPlaquette_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] [NormOneClass 𝔅]
    {g : E → ℝ × 𝔅 × 𝔅 × 𝔅 × 𝔅} {z : E} (hg : ContDiffAt ℝ ω g z) (h0 : (g z).1 = 0) :
    ContDiffAt ℝ ω (fun z => remPlaquette (g z)) z := by
  refine ContDiffAt.comp z (analyticAt_remPlaquette ?_).contDiffAt hg
  simp [h0]

theorem contDiffAt_omega_remCartan (μ ν : Fin 4) {q : ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (hq : q.1 = 0) (hc : JetChart q.2) : ContDiffAt ℝ ω (remCartan μ ν) q := by
  have hΩ : ∀ μ, ContDiffAt ℝ ω (jetOmega μ) q.2 := fun μ =>
    contDiffAt_omega_jetOmega μ (hc none)
  have hΩs : ∀ ν μ, ContDiffAt ℝ ω (jetOmegaShift ν μ) q.2 := fun ν μ =>
    contDiffAt_omega_jetOmegaShift ν μ (hc _)
  unfold remCartan
  refine contDiffAt_omega_remPlaquette_comp ?_ hq
  simp only [← matToOpL_apply]
  fun_prop

/-- Composition form of the `C^ω` regularity of `dqPal`. -/
@[fun_prop]
theorem ContDiffAt.dqPal_omega {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : ℝ)
    (μ ν a b : Fin 4) {f : E → ℝ} {g l : E → Mat} {x : E} (hf : ContDiffAt ℝ ω f x)
    (hg : ContDiffAt ℝ ω g x) (hl : ContDiffAt ℝ ω l x) (h0 : (g x).det ≠ 0)
    (h1 : (g x + f x • l x).det ≠ 0) :
    ContDiffAt ℝ ω (fun x => NativeDensity.dqPal κ (f x) (g x) (l x) μ ν a b) x := by
  have h := ContDiffAt.comp
    (g := fun q : ℝ × Mat × Mat => NativeDensity.dqPal κ q.1 q.2.1 q.2.2 μ ν a b)
    (f := fun x => (f x, g x, l x)) x
    (contDiffAt_omega_dqPal κ μ ν a b (q := (f x, g x, l x)) h0 h1) (hf.prodMk (hg.prodMk hl))
  simp only [Function.comp_def] at h
  exact h

theorem contDiffAt_omega_gravFirstJet {q : ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (hq : q.1 = 0)
    (hc : JetChart q.2) : ContDiffAt ℝ ω (gravFirstJet D) q := by
  have hR : ∀ μ ν, ContDiffAt ℝ ω (remCartan μ ν) q := fun μ ν =>
    contDiffAt_omega_remCartan μ ν hq hc
  have hΩ : ∀ ν, ContDiffAt ℝ ω (jetOmega ν) q.2 := fun ν => contDiffAt_omega_jetOmega ν (hc none)
  have he0 : (q.2.1 none).1.det ≠ 0 := hc none
  have hEm : ∀ μ, (jetEm μ q.2).det ≠ 0 := fun μ => hc _
  have hseg : ∀ μ, (jetEm μ q.2 + q.1 • jetPm μ q.2).det ≠ 0 := by
    intro μ
    rw [hq, zero_smul, add_zero]
    exact hEm μ
  unfold gravFirstJet
  fun_prop (disch := solve_by_elim)

theorem contDiffAt_omega_jointNuLogPlaquette_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅]
    [NormOneClass 𝔅] {g : E → ℝ × ℝ × 𝔅 × 𝔅 × 𝔅 × 𝔅} {z : E} (hg : ContDiffAt ℝ ω g z)
    (h0 : (g z).1 = 0) : ContDiffAt ℝ ω (fun z => jointNuLogPlaquette (g z)) z := by
  refine ContDiffAt.comp z (analyticAt_jointNuLogPlaquette ?_).contDiffAt hg
  simp [h0]

theorem contDiffAt_omega_nuFieldStrength (μ ν : Fin 4)
    {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (hp : p.1 = 0) :
    ContDiffAt ℝ ω (nuFieldStrength μ ν) p := by
  unfold nuFieldStrength
  refine contDiffAt_omega_jointNuLogPlaquette_comp ?_ hp
  fun_prop

theorem contDiffAt_omega_nuDiracDiffJet (μ : Fin 4)
    {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (he : (p.2.2.1 none).1.det ≠ 0) :
    ContDiffAt ℝ ω (nuDiracDiffJet D μ) p := by
  have hΩ : ContDiffAt ℝ ω (jetOmega μ) p.2.2 := contDiffAt_omega_jetOmega μ he
  unfold nuDiracDiffJet nuDiracDiff nuSpinQuot
  fun_prop

theorem contDiffAt_omega_nuDiracDiffBarJet (μ : Fin 4)
    {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (he : (p.2.2.1 none).1.det ≠ 0) :
    ContDiffAt ℝ ω (nuDiracDiffBarJet D μ) p := by
  have hΩ : ContDiffAt ℝ ω (jetOmega μ) p.2.2 := contDiffAt_omega_jetOmega μ he
  unfold nuDiracDiffBarJet nuDiracDiffBar nuSpinQuotInv
  fun_prop

theorem contDiffAt_omega_normYM {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (hp : p.1 = 0)
    (he : (p.2.2.1 none).1.det ≠ 0) : ContDiffAt ℝ ω (normYM D) p := by
  have hF : ∀ μ ν, ContDiffAt ℝ ω (nuFieldStrength μ ν) p := fun μ ν =>
    contDiffAt_omega_nuFieldStrength μ ν hp
  unfold normYM
  fun_prop (disch := assumption)

theorem contDiffAt_omega_normHiggs {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (he : (p.2.2.1 none).1.det ≠ 0) : ContDiffAt ℝ ω (normHiggs D) p := by
  unfold normHiggs
  fun_prop (disch := assumption)

theorem contDiffAt_omega_normD {p : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (he : (p.2.2.1 none).1.det ≠ 0) : ContDiffAt ℝ ω (normD D) p := by
  have h1 : ∀ μ, ContDiffAt ℝ ω (nuDiracDiffJet D μ) p := fun μ =>
    contDiffAt_omega_nuDiracDiffJet D μ he
  have h2 : ∀ μ, ContDiffAt ℝ ω (nuDiracDiffBarJet D μ) p := fun μ =>
    contDiffAt_omega_nuDiracDiffBarJet D μ he
  have hγ : ∀ μ, ContDiffAt ℝ ω (gammaMu D μ) (p.2.2.1 none).1 := fun μ =>
    contDiffAt_gammaMu D μ he
  unfold normD
  fun_prop (disch := assumption)

/-- **`C^ω` regularity of the normalised density** at the mesh origin, for every `ν`. -/
theorem contDiffAt_omega_scaledDensity {ν : ℝ} {ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)}
    (hc : JetChart ξ) : ContDiffAt ℝ ω (scaledDensity D) (ν, ((0 : ℝ), ξ)) := by
  have hg : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      gravFirstJet D (p.2.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := gravFirstJet D)
      (f := fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) => (p.2.1, p.2.2))
      (contDiffAt_omega_gravFirstJet D (q := ((0 : ℝ), ξ)) rfl hc) (by fun_prop)
  have hv : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      NativeDensity.volume (p.2.2.1 none).1) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := NativeDensity.volume)
      (f := fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) => (p.2.2.1 none).1)
      (contDiffAt_volume (k := ω) (hc none)) (by fun_prop)
  have hproj : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      ((p.2.1, p.1, p.2.2) : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) (ν, ((0 : ℝ), ξ)) := by
    fun_prop
  have hy : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normYM D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normYM D)
      (contDiffAt_omega_normYM D (p := ((0 : ℝ), ν, ξ)) rfl (hc none)) hproj
  have hH : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normHiggs D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normHiggs D)
      (contDiffAt_omega_normHiggs D (p := ((0 : ℝ), ν, ξ)) (hc none)) hproj
  have hD : ContDiffAt ℝ ω (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normD D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normD D)
      (contDiffAt_omega_normD D (p := ((0 : ℝ), ν, ξ)) (hc none)) hproj
  unfold scaledDensity
  refine (((hg.add ?_).add hy).add hH).add ?_
  · exact ((contDiffAt_const.sub (contDiffAt_fst.pow 2)).mul contDiffAt_const).mul hv
  · exact contDiffAt_fst.mul hD

/-! ### Real-analyticity of the continuum density and its gradients -/

local notation "FJ" => JS (Field 𝔄 𝓗 𝓢)

local instance instNACGdualFJ' : NormedAddCommGroup (FJ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNSdualFJ' : NormedSpace ℝ (FJ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNACGdualRFJ' : NormedAddCommGroup (ℝ × FJ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNSdualRFJ' : NormedSpace ℝ (ℝ × FJ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem contDiffAt_omega_Ldens {q : ℝ × FJ} (hq : q ∈ chartU) : ContDiffAt ℝ ω (Ldens D) q := by
  have hin : ContDiffAt ℝ ω (fun q : ℝ × FJ =>
      ((q.1, ((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) :
        ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) q := by
    have h1 : ContDiff ℝ ω (fun q : ℝ × FJ => q.1) := contDiff_fst
    have h2 : ContDiff ℝ ω (fun q : ℝ × FJ =>
        (((0 : ℝ), (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :
          ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :=
      contDiff_const.prodMk ((cmap : FJ →L[ℝ] NativeDensity.Jet (Field 𝔄 𝓗 𝓢)).contDiff.comp
        contDiff_snd)
    exact (h1.prodMk h2).contDiffAt
  exact (contDiffAt_omega_scaledDensity D (ν := q.1) (jetChart_cmap hq)).comp q hin

/-- **The continuum normalised density is real-analytic on the chart** `det e ≠ 0`. -/
theorem analyticAt_Ldens {q : ℝ × FJ} (hq : q ∈ chartU) : AnalyticAt ℝ (Ldens D) q :=
  (contDiffAt_omega_Ldens D hq).analyticAt

theorem analyticAt_Ddens {q : ℝ × FJ} (hq : q ∈ chartU) : AnalyticAt ℝ (Ddens D) q := by
  have hin : ContDiffAt ℝ ω (fun q : ℝ × FJ =>
      (((0 : ℝ), q.1, (cmap q.2 : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) :
        ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) q :=
    (contDiff_const.prodMk (contDiff_fst.prodMk
      ((cmap : FJ →L[ℝ] NativeDensity.Jet (Field 𝔄 𝓗 𝓢)).contDiff.comp contDiff_snd))).contDiffAt
  exact ((contDiffAt_omega_normD D (p := ((0 : ℝ), q.1, cmap q.2)) hq).comp q hin).analyticAt

theorem analyticOnNhd_Ldens : AnalyticOnNhd ℝ (Ldens D) chartU := fun _ hq => analyticAt_Ldens D hq

theorem analyticOnNhd_Ddens : AnalyticOnNhd ℝ (Ddens D) chartU := fun _ hq => analyticAt_Ddens D hq

variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **The gradient `Gd = ∂_{(w,p)}𝓛` is real-analytic on the chart.** -/
theorem analyticAt_Gd {q : ℝ × FJ} (hq : q ∈ chartU) : AnalyticAt ℝ (Gd D) q := by
  have h : AnalyticAt ℝ (fderiv ℝ (Ldens D)) q :=
    ((analyticOnNhd_Ldens D).fderiv_of_isOpen isOpen_chartU) q hq
  exact (ContEulerBounds.preL (inrP ℝ FJ)).analyticAt _ |>.comp h

theorem analyticAt_GD {q : ℝ × FJ} (hq : q ∈ chartU) : AnalyticAt ℝ (GD D) q := by
  have h : AnalyticAt ℝ (fderiv ℝ (Ddens D)) q :=
    ((analyticOnNhd_Ddens D).fderiv_of_isOpen isOpen_chartU) q hq
  exact (ContEulerBounds.preL (inrP ℝ FJ)).analyticAt _ |>.comp h

theorem analyticAt_G1D {q : ℝ × FJ} (hq : q ∈ chartU) : AnalyticAt ℝ (G1D D) q :=
  (ContEulerBounds.preL ((inlJ (Field 𝔄 𝓗 𝓢)).comp ιS)).analyticAt _ |>.comp (analyticAt_GD D hq)

theorem analyticAt_ellD (μ : Fin 4) {r : ℝ × Field 𝔄 𝓗 𝓢} (hr : r ∈ chartW) :
    AnalyticAt ℝ (ellD D μ) r := by
  have hmap : AnalyticAt ℝ (fun r : ℝ × Field 𝔄 𝓗 𝓢 => ((r.1, (r.2, 0)) : ℝ × FJ)) r := by
    have : (fun r : ℝ × Field 𝔄 𝓗 𝓢 => ((r.1, (r.2, 0)) : ℝ × FJ)) =
        fun r => ((ContinuousLinearMap.fst ℝ ℝ (Field 𝔄 𝓗 𝓢)).prod
          ((ContinuousLinearMap.inl ℝ (Field 𝔄 𝓗 𝓢) (Fin 4 → Field 𝔄 𝓗 𝓢)).comp
            (ContinuousLinearMap.snd ℝ ℝ (Field 𝔄 𝓗 𝓢)))) r := by
      funext r; rfl
    rw [this]
    exact ContinuousLinearMap.analyticAt _ _
  have hG : AnalyticAt ℝ (GD D) ((r.1, (r.2, 0)) : ℝ × FJ) := analyticAt_GD D hr
  exact (ContEulerBounds.preL ((slotJ (Field 𝔄 𝓗 𝓢) μ).comp ιS)).analyticAt _ |>.comp
    (AnalyticAt.comp (g := GD D) hG hmap)

end

end RenewalGeometry.NativeAnalytic
