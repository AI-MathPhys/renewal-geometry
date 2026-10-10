/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeLocalCalibrationClosed
import RenewalGeometry.Continuum.NativeDiracEulerRows
import RenewalGeometry.Continuum.NativeGravityJetDensity
import RenewalGeometry.Continuum.NativeStressDirac

/-!
# Non-vacuity of `cor:local-calibration-nonempty`: constant vacua solve the native Euler equations

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty` ("Let `z_*` be
a smooth solution on a compact slab, with compatible fixed gauges and a smooth periodic extension
to the buffered comparison box that remains in the chosen field-value chart …").

The hypothesis packet of `LocalCalibrationClosed.local_calibration_nonempty` (smooth `2π`-periodic
native field, fixed gauges, compact coframe chart, Lorentzian chart, harmonic gauge of the dilated
metric, and the **physical native Euler equations** `𝓔₀(Y) ∘ physF πg = 0` on the buffered slab —
gauge rows in the gauge Lie algebra `𝔤` only, corrected encoding g11) is satisfiable.  The
witnesses below prove more: the whole covector on `Field = Mat × (Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢`
vanishes (coframe directions including the antisymmetric local Lorentz ones, and every direction of
`𝔄`), hence in particular its physical part.

* **`contEuler_const`** (generic) — the Euler covector of a constant field is the value partial
  `∂_w L(y₀, 0)`.
* **`fderiv_L0_vac`** — at a constant background `(e₀, A = 0, H₀, Ψ = 0, Ψ̄ = 0)` with
  `det e₀ ≠ 0`, the value partial of the native Lagrangian `L₀ = limDensity (firstJetDensity D)`
  vanishes in every direction, provided the cosmological balance `Λ/κ + V(H₀) = 0` holds and `H₀` is
  a critical point of the Higgs potential (`DV(H₀) = 0`).  Each of the five sectors is handled:
  coframe directions (all of `Mat`) because `L₀` vanishes identically along the coframe line
  (`palatiniFirstOrder κ Λ e 0 = -(Λ/κ) v(e)`, `gravCurv_constJet_zero`), gauge, Higgs, spinor and
  co-spinor directions by the line derivatives `hasDerivAt_L0_gaugeLine`, `hasDerivAt_L0_hLine`,
  `fderiv_L0_psi`, `fderiv_L0_psiBar` evaluated at the background.
* **`native_euler_vac`** — hence `𝓔₀(Y) = 0` everywhere for the constant field.
* **`local_calibration_nonempty_vac`** — `cor:local-calibration-nonempty` for the constant vacuum
  `Y ≡ (1, 0, H₀, 0, 0)` of any slab model with `Λ + κλ_H(⟨H₀,H₀⟩ - v_H²)² = 0` and
  `λ_H(⟨H₀,H₀⟩ - v_H²) = 0 ∨ H₀ = 0`: every field hypothesis of `local_calibration_nonempty`
  is discharged (only the corollary's own parameters remain: `k`, the slab, the cutoff family).
* **`local_calibration_nonempty_flat`** — the flat (Minkowski) vacuum of the concrete slab model
  `SlabData.diracSlab` (= `NativeModelExample.diracModel`, `Λ = λ_H = v_H = 0`), and
  `local_calibration_nonempty_flat_example`: a fully instantiated instance (`k = 4`,
  `[t₀, t₁] = [2, 3]`, `b = 1`, `β = 1/16`, `K_h = h^{-β}`).
-/

open Filter Topology Set Metric Finset
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.CalibrationWitness

open SobolevOpen (pd)
open NativeDensity NativeBosonicEuler NativeDiracEuler NativeStressEuler NativeGravityJet
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The Euler covector of a constant field -/

section Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem jet1_const (y₀ : V) (z : R4) : jet1 (fun _ : R4 => y₀) z = (y₀, 0) := by
  unfold jet1
  ext <;> simp

/-- **The Euler covector of a constant field** is the value partial `∂_w L(y₀, 0)`. -/
theorem contEuler_const (L : V × (Fin 4 → V) → ℝ) (y₀ : V) (z : R4) :
    contEuler L (fun _ : R4 => y₀) z =
      (fderiv ℝ L (y₀, 0)).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) := by
  unfold contEuler
  simp only [jet1_const]
  simp

end Const

/-! ### The native Lagrangian at a constant background -/

section Vacuum

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The constant background `(e₀, A = 0, H₀, Ψ = 0, Ψ̄ = 0)`. -/
def vacField (e₀ : Mat) (H₀ : 𝓗) : Field 𝔄 𝓗 𝓢 := (e₀, 0, H₀, 0, 0)

/-- Its first jet (vanishing derivatives). -/
def vacJet (e₀ : Mat) (H₀ : 𝓗) : FJ 𝔄 𝓗 𝓢 := (vacField e₀ H₀, 0)

theorem readerG_zero (e : Mat) (lam : Fin 4) : readerG e (fun _ => 0) lam = 0 := by
  simp [readerG]

theorem readerGamma_zero (e : Mat) (ρ μ ν : Fin 4) : readerGamma e (fun _ => 0) ρ μ ν = 0 := by
  simp [readerGamma, readerG_zero]

/-- The reader connection of a coframe jet with vanishing derivatives vanishes. -/
theorem readerOmega_zero (e : Mat) (μ : Fin 4) : readerOmega e (fun _ => 0) μ = 0 := by
  funext a b
  simp [readerOmega, readerGamma_zero]

/-- The curvature part of the first-order Palatini density vanishes on jets with `∂e = 0`. -/
theorem gravCurv_constJet_zero (κ : ℝ) (e : Mat) : gravCurv κ (0, constJet e (fun _ => 0)) = 0 := by
  have hom : ∀ ν, omegaM ν (constJet e (fun _ => 0)) = 0 := fun ν => readerOmega_zero e ν
  have hrem : ∀ μ ν, remM μ ν (0, constJet e (fun _ => 0)) = 0 := by
    intro μ ν
    rw [remM_constJet]
    simp [readerOmega_zero]
  unfold gravCurv
  have ha : ∀ μ ν, antisym (fun μ ν => remM μ ν ((0 : ℝ), constJet e (fun _ => 0))) μ ν = 0 := by
    intro μ ν
    simp only [hrem]
    unfold antisym
    split_ifs <;> simp
  simp only [ha, hom]
  simp [opEntry]

/-- **The first-order Palatini density at `∂e = 0`** is the cosmological term. -/
theorem palatiniFirstOrder_zero (κ Λ : ℝ) (e : Mat) :
    palatiniFirstOrder κ Λ e (fun _ => 0) = -(Λ / κ * volume e) := by
  unfold palatiniFirstOrder
  rw [gravCurv_constJet_zero]
  ring

/-- **The native Lagrangian along a coframe line through a constant background** (`A = 0`,
`Ψ = Ψ̄ = 0`, `∂ = 0`): `L₀ = -v(e)(Λ/κ + V(H₀))`. -/
theorem L0_coframe_line (e₀ δ : Mat) (H₀ : 𝓗) (t : ℝ) :
    L0 D (vacJet e₀ H₀ + t • ((coframeDir δ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))) =
      -(volume (e₀ + t • δ) * (D.Λ / D.κ + potential D H₀)) := by
  rw [L0_eq]
  have hw : (vacJet e₀ H₀ + t • ((coframeDir δ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))) =
      (((e₀ + t • δ : Mat), (0 : Fin 4 → 𝔄), H₀, (0 : 𝓢), (0 : CoSpinor 𝓢)),
        (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) := by
    simp [vacJet, vacField, coframeDir]
    all_goals (funext μ; exact smul_zero (A := Field 𝔄 𝓗 𝓢) t)
  rw [hw]
  have hg : Lgc D ((((e₀ + t • δ : Mat), (0 : Fin 4 → 𝔄), H₀, (0 : 𝓢), (0 : CoSpinor 𝓢)),
      (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) : FJ 𝔄 𝓗 𝓢) = -(D.Λ / D.κ * volume (e₀ + t • δ)) := by
    unfold Lgc
    exact palatiniFirstOrder_zero D.κ D.Λ _
  rw [hg]
  simp [LYMc, LHc, LDc, FA, KH, DPsiBar]
  ring

variable {D}

/-- **The value partial of `L₀` at a constant background vanishes** in every direction, under the
cosmological balance and the criticality of `H₀`. -/
theorem fderiv_L0_vac {e₀ : Mat} (he : e₀.det ≠ 0) {H₀ : 𝓗}
    (hbal : D.Λ / D.κ + potential D H₀ = 0) (hcrit : ∀ η, potGrad D H₀ η = 0)
    (v : Field 𝔄 𝓗 𝓢) :
    fderiv ℝ (L0 D) (vacJet e₀ H₀) (v, 0) = 0 := by
  have hJ : (vacJet e₀ H₀ : FJ 𝔄 𝓗 𝓢).1.1.det ≠ 0 := he
  have hdiff := differentiableAt_L0 D hJ
  -- the decomposition of `v` into the five sectors
  have hv : ((v, 0) : FJ 𝔄 𝓗 𝓢) =
      ((coframeDir v.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) +
      ((gaugeDir v.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) +
      ((higgsDir v.2.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) +
      ((psiDir v.2.2.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) +
      ((psiBarDir v.2.2.2.2 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) := by
    obtain ⟨E, X, η, χ, φ⟩ := v
    simp [coframeDir, gaugeDir, higgsDir, psiDir, psiBarDir]
  rw [hv, map_add, map_add, map_add, map_add]
  -- coframe directions: `L₀` vanishes identically along the line
  have h1 : fderiv ℝ (L0 D) (vacJet e₀ H₀)
      ((coframeDir v.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) = 0 := by
    refine fderiv_apply_of_line hdiff ?_
    have : (fun t : ℝ => L0 D (vacJet e₀ H₀ +
        t • ((coframeDir v.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)))) = fun _ => 0 := by
      funext t
      rw [L0_coframe_line, hbal, mul_zero, neg_zero]
    rw [this]
    exact hasDerivAt_const _ _
  -- gauge directions
  have h2 : fderiv ℝ (L0 D) (vacJet e₀ H₀)
      ((gaugeDir v.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) = 0 := by
    refine (fderiv_apply_of_line hdiff (hasDerivAt_L0_gaugeLine D (vacJet e₀ H₀) v.2.1)).trans ?_
    simp [vacJet, vacField, BA, FA, gaugeCur, KH]
  -- Higgs directions
  have h3 : fderiv ℝ (L0 D) (vacJet e₀ H₀)
      ((higgsDir v.2.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) = 0 := by
    refine (fderiv_apply_of_line hdiff (hasDerivAt_L0_hLine D (vacJet e₀ H₀) v.2.2.1)).trans ?_
    have hc := hcrit v.2.2.1
    simp [vacJet, vacField, KH] at hc ⊢
    simp [hc]
  -- spinor directions
  have h4 : fderiv ℝ (L0 D) (vacJet e₀ H₀)
      ((psiDir v.2.2.2.1 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) = 0 := by
    rw [fderiv_L0_psi D hJ]
    simp [vacJet, vacField, DPsiBar]
  -- co-spinor directions
  have h5 : fderiv ℝ (L0 D) (vacJet e₀ H₀)
      ((psiBarDir v.2.2.2.2 : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) = 0 := by
    rw [fderiv_L0_psiBar D hJ]
    simp [vacJet, vacField, DPsi]
  rw [h1, h2, h3, h4, h5]
  simp

/-- **A constant background solves the complete native Euler equations** `𝓔₀(Y) = 0` (the whole
covector on `Field`, every coframe direction included), under the cosmological balance
`Λ/κ + V(H₀) = 0` and `DV(H₀) = 0`. -/
theorem native_euler_vac {e₀ : Mat} (he : e₀.det ≠ 0) {H₀ : 𝓗}
    (hbal : D.Λ / D.κ + potential D H₀ = 0) (hcrit : ∀ η, potGrad D H₀ η = 0) (z : R4) :
    contEuler (limDensity (ι := Shift) (firstJetDensity D))
      (fun _ : R4 => (vacField e₀ H₀ : Field 𝔄 𝓗 𝓢)) z = 0 := by
  rw [contEuler_const]
  refine ContinuousLinearMap.ext fun v => ?_
  exact fderiv_L0_vac he hbal hcrit v

end Vacuum

/-! ### The Lorentzian chart and the harmonic gauge of the flat coframe -/

section Chart

open ActualJetSystem ActualJetFrame ActualJetWriter

theorem eta_eq_minkInv (i j : Fin 4) : eta i j = minkInv i j := by
  fin_cases i <;> fin_cases j <;> simp [eta, minkInv]

theorem metric_smul_one (c : ℝ) :
    (fun i j : Fin 4 => metric (c • (1 : Mat)) i j) = (c ^ 2) • minkInv := by
  funext i j
  have : metric (c • (1 : Mat)) = (c ^ 2) • eta := by
    simp only [metric, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, sq]
  rw [this, Matrix.smul_apply, eta_eq_minkInv]
  rfl

theorem ginvOf_smul_minkInv {r : ℝ} (hr : r ≠ 0) : ginvOf (r • minkInv) = r⁻¹ • minkInv := by
  have h : Matrix.of (r • minkInv) * Matrix.of (r⁻¹ • minkInv) = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    have := minkInv_sq a c
    calc ∑ b, r * minkInv a b * (r⁻¹ * minkInv b c) = (r * r⁻¹) * ∑ b, minkInv a b * minkInv b c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      _ = _ := by rw [mul_inv_cancel₀ hr, one_mul, this]
  funext i j
  unfold ginvOf
  rw [Matrix.inv_eq_right_inv h]
  rfl

theorem isLorChart_smul_minkInv {s : ℝ} (hs : 0 < s) : IsLorChart (s • minkInv) := by
  refine ⟨by simp [minkInv]; linarith, ?_, ?_, ?_⟩ <;>
    simp [hInv, minkInv, L10, L20, L21, L11, L00, hs]

/-- **The flat coframe `e = 1` is in the Lorentzian chart** (`ginvS 1 = (2π)⁻²η⁻¹`). -/
theorem isLorChart_ginvS_one : IsLorChart (CalibrationSampling.ginvS (1 : Mat)) := by
  unfold CalibrationSampling.ginvS
  rw [metric_smul_one, ginvOf_smul_minkInv (by positivity)]
  exact isLorChart_smul_minkInv (by positivity)

theorem isAdaptedCoframe_one : NativeFrameBridge.IsAdaptedCoframe (1 : Mat) :=
  ⟨fun a μ h => by simp [h.ne], fun a => by simp⟩

end Chart

/-! ### All hypotheses of `local_calibration_nonempty` for constant vacua -/

section Slab

open SlabData NativeModel CalibrationSampling RecordTuple NativeFrameBridge ActualJetWriter
  PalatiniEuler ActualJetSystem

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The constant vacuum field `Y ≡ (1, 0, H₀, 0, 0)` (flat coframe, Higgs value `H₀`). -/
def vacY (H₀ : 𝓗) : R4 → Field 𝔄 𝓗 𝓢 := fun _ => vacField (1 : Mat) H₀

variable {M}

theorem vacY_smooth (H₀ : 𝓗) : ContDiff ℝ ∞ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀) := contDiff_const

theorem vacY_periodic (H₀ : 𝓗) : IsPeriodic (2 * π) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀) :=
  fun _ _ => rfl

theorem vacY_gauge (H₀ : 𝓗) : FieldGauge M (vacY H₀) where
  adapted _ := isAdaptedCoframe_one
  temporal _ := rfl
  gauge _ _ := M.gSub.zero_mem
  clin _ := fun x => by simp [vacY, vacField]

/-- The constant vacuum solves the complete native Euler equations of a slab model, under the
cosmological balance `Λ + κλ_H(⟨H₀,H₀⟩ - v_H²)² = 0` and the Higgs criticality
`λ_H(⟨H₀,H₀⟩ - v_H²) = 0 ∨ H₀ = 0`. -/
theorem vacY_native_euler {H₀ : 𝓗} (hbal : M.Λ + M.κ * (M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) ^ 2) = 0)
    (hH : M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) = 0 ∨ H₀ = 0) (z : R4) :
    contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) (vacY H₀) z = 0 := by
  refine native_euler_vac (by simp) ?_ ?_ z
  · show M.Λ / M.κ + M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) ^ 2 = 0
    have hκ := M.κ_ne
    field_simp
    linear_combination hbal
  · intro η
    show M.lamH * (2 * (M.hermH H₀ H₀ - M.vH ^ 2) * (M.hermH η H₀ + M.hermH H₀ η)) = 0
    rcases hH with hH | rfl
    · linear_combination (2 * (M.hermH η H₀ + M.hermH H₀ η)) * hH
    · simp

/-- The dilated metric of the constant vacuum is in harmonic gauge (its metric is constant). -/
theorem vacY_harm (H₀ : 𝓗) (t₀ : ℝ) (x : R4) (l : Fin 4) :
    C (ginvOf (gF (eF (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))) x))
      (fun α => pd (gF (eF (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)))) α x) l = 0 := by
  have hc : gF (eF (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))) =
      fun _ => gF (eF (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))) 0 := rfl
  have hpd : ∀ α, pd (gF (eF (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)))) α x = 0 := by
    intro α
    rw [hc]
    simp [SobolevOpen.pd]
  simp only [hpd]
  simp [C, HarmonicDefect.cUp, HarmonicDefect.chr]

end Slab

/-! ### `cor:local-calibration-nonempty` for constant vacua -/

section Corollary

open SobolevOpen (pd)
open CNConv StateConv RecordTuple SlabData NativeDensity NativeModel NativeFrameBridge
  ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState CoupledBootstrap FieldScaling
  PalatiniEuler NativeBosonicEuler ActualJetFrame CalibrationSampling SlabSymmetric
  ClosureUnconditional ActualJetCompleteForcing LocalCalibrationClosed
open DiscreteEulerConsistency (R4 pos samp IsPeriodic realVec contEuler limDensity eulerRow)
open ShiftedPlaquette
open ShiftedJetAction (Grid)
open NativeScaling (Mat metric)
open TrigInterp (recon reconLow tau)
open NativeRate (forcingBudget)
open LocalCalibration (oddN meshOdd tendsto_meshOdd)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

set_option maxHeartbeats 1600000 in
/-- **`cor:local-calibration-nonempty` for a constant vacuum**: for every slab model and every
Higgs value `H₀` with the cosmological balance `Λ + κλ_H(⟨H₀,H₀⟩ - v_H²)² = 0` and
`λ_H(⟨H₀,H₀⟩ - v_H²) = 0 ∨ H₀ = 0`, the constant field `Y ≡ (1, 0, H₀, 0, 0)` satisfies every
field hypothesis of `LocalCalibrationClosed.local_calibration_nonempty` (smooth, `2π`-periodic,
fixed gauges, compact coframe chart `{1}`, Lorentzian chart, physical (indeed complete) native Euler equations,
harmonic gauge), so its sampled records realise the corollary for every admissible `k`, slab and
cutoff family. -/
theorem local_calibration_nonempty_vac {H₀ : 𝓗}
    (hbal : M.Λ + M.κ * (M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) ^ 2) = 0)
    (hH : M.lamH * (M.hermH H₀ H₀ - M.vH ^ 2) = 0 ∨ H₀ = 0)
    {k : ℕ} (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀) (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁)
    {β c₁ c₂ : ℝ} (hβ : 0 < β) (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
    (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β))
    {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp M δ (dilField t₀ (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))) (Ke : Set Mat) (A Cσ C : ℝ)
      (Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)) (R₁ : ℝ),
      IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ 0 ≤ Cσ ∧ 0 ≤ C ∧
      IsCompact Kr ∧ Kr ⊆ chartC (slabX M) ∧ 0 ≤ R₁ ∧
      ExactOn (toSMData M δ) (slabT t₀ t₁) (toTuple hδ hT) ∧
      toTuple hδ hT ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁ ∧
      (∀ᶠ m in atTop, RecordHyp M δ Ke A t₀ t₁ b (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))
        (Kh m) (Cσ * meshOdd m)) ∧
      Tendsto (fun m => meshOdd m * Kh m) atTop (𝓝 0) ∧ Tendsto Kh atTop atTop ∧
      Tendsto (fun m => tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))) atTop
        (𝓝 0) ∧
      Tendsto (fun m => ‖(slabMod M hδ eY eYD k h01).init
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)) -
          (slabMod M hδ eY eYD k h01).init (toTuple hδ hT)‖) atTop (𝓝 0) ∧
      Tendsto (fun m => (slabMod M hδ eY eYD k h01).harm
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)))
        atTop (𝓝 0) ∧
      Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)))) atTop (𝓝 0) ∧
      (∀ᶠ m in atTop, dist ((slabMod M hδ eY eYD k h01).obs
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)))
          ((slabMod M hδ eY eYD k h01).obs (toTuple hδ hT)) ≤
        C * (‖(slabMod M hδ eY eYD k h01).init
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)) -
          (slabMod M hδ eY eYD k h01).init (toTuple hδ hT)‖ +
          (slabMod M hδ eY eYD k h01).harm
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)) +
          forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
            (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)))
            (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀))))) ∧
      Tendsto (fun m => dist ((slabMod M hδ eY eYD k h01).obs
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := 𝔄) (𝓢 := 𝓢) H₀)) (toTuple hδ hT)))
          ((slabMod M hδ eY eYD k h01).obs (toTuple hδ hT))) atTop (𝓝 0) :=
  local_calibration_nonempty M (vacY_smooth H₀) (vacY_periodic H₀) (vacY_gauge H₀)
    (isCompact_singleton (x := (1 : Mat))) (fun e he => by rw [Set.mem_singleton_iff.1 he]; simp)
    (fun _ => rfl) (fun _ => isLorChart_ginvS_one) hk hCk hb h0 h1 h01
    (fun z _ => by rw [vacY_native_euler hbal hH z, ContinuousLinearMap.zero_comp])
    (fun x _ l => vacY_harm H₀ t₀ x l) hβ hβk hc₁ Kh hKh
    eY eYD

end Corollary

section Flat

open SobolevOpen (pd)
open CNConv StateConv RecordTuple SlabData NativeDensity NativeModel NativeFrameBridge
  ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState CoupledBootstrap FieldScaling
  PalatiniEuler NativeBosonicEuler ActualJetFrame CalibrationSampling SlabSymmetric
  ClosureUnconditional ActualJetCompleteForcing LocalCalibrationClosed NativeModelExample
open DiscreteEulerConsistency (R4 pos samp IsPeriodic realVec contEuler limDensity eulerRow)
open ShiftedPlaquette
open ShiftedJetAction (Grid)
open NativeScaling (Mat metric)
open TrigInterp (recon reconLow tau)
open NativeRate (forcingBudget)
open LocalCalibration (oddN meshOdd tendsto_meshOdd)

/-- The flat vacuum `flat` of `NativeModelExample` is the constant vacuum `vacY 0`. -/
theorem vacY_zero_eq_flat : vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ) = flat := rfl

/-- **The flat vacuum solves the complete native Euler equations of `diracModel`** (every
direction of the native field space, coframe directions included). -/
theorem flat_native_euler (z : R4) :
    contEuler (limDensity (ι := Shift) (firstJetDensity diracModel.toData)) flat z = 0 :=
  vacY_native_euler (M := diracSlab) (H₀ := (0 : ℝ)) (by simp [diracSlab, diracModel])
    (Or.inr rfl) z

set_option maxHeartbeats 1600000 in
/-- **`cor:local-calibration-nonempty`, non-vacuity: the flat (Minkowski) vacuum** `e = 1`,
`A = H = Ψ = Ψ̄ = 0` of the concrete slab model `diracSlab` (`diracModel`: Dirac matrices with
the Clifford relations, `κ = 1`, `Λ = λ_H = v_H = 0`) satisfies every hypothesis of
`local_calibration_nonempty`; only the corollary's own parameters remain. -/
theorem local_calibration_nonempty_flat
    {k : ℕ} (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀) (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁)
    {β c₁ c₂ : ℝ} (hβ : 0 < β) (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
    (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β))
    {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP 1 (HSp diracSlab))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] Sp × CoSpinor Sp) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp diracSlab δ (dilField t₀ (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))) (Ke : Set Mat) (A Cσ C : ℝ)
      (Kr : Set (Fin (ActualJetKato.dimS 1 (HSp diracSlab) Sp (CoSpinor Sp)) → ℝ)) (R₁ : ℝ),
      IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ 0 ≤ Cσ ∧ 0 ≤ C ∧
      IsCompact Kr ∧ Kr ⊆ chartC (slabX diracSlab) ∧ 0 ≤ R₁ ∧
      ExactOn (toSMData diracSlab δ) (slabT t₀ t₁) (toTuple hδ hT) ∧
      toTuple hδ hT ∈ refSet (toSMData diracSlab δ) (slabX diracSlab) k (slabT t₀ t₁) Kr R₁ ∧
      (∀ᶠ m in atTop, RecordHyp diracSlab δ Ke A t₀ t₁ b (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))
        (Kh m) (Cσ * meshOdd m)) ∧
      Tendsto (fun m => meshOdd m * Kh m) atTop (𝓝 0) ∧ Tendsto Kh atTop atTop ∧
      Tendsto (fun m => tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))) atTop
        (𝓝 0) ∧
      Tendsto (fun m => ‖(slabMod diracSlab hδ eY eYD k h01).init
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) -
          (slabMod diracSlab hδ eY eYD k h01).init (toTuple hδ hT)‖) atTop (𝓝 0) ∧
      Tendsto (fun m => (slabMod diracSlab hδ eY eYD k h01).harm
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
        atTop (𝓝 0) ∧
      Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))) atTop (𝓝 0) ∧
      (∀ᶠ m in atTop, dist ((slabMod diracSlab hδ eY eYD k h01).obs
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
          ((slabMod diracSlab hδ eY eYD k h01).obs (toTuple hδ hT)) ≤
        C * (‖(slabMod diracSlab hδ eY eYD k h01).init
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) -
          (slabMod diracSlab hδ eY eYD k h01).init (toTuple hδ hT)‖ +
          (slabMod diracSlab hδ eY eYD k h01).harm
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) +
          forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
            (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))
            (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))))) ∧
      Tendsto (fun m => dist ((slabMod diracSlab hδ eY eYD k h01).obs
            (recTuple diracSlab hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
          ((slabMod diracSlab hδ eY eYD k h01).obs (toTuple hδ hT))) atTop (𝓝 0) :=
  local_calibration_nonempty_vac diracSlab (H₀ := (0 : ℝ)) (by simp [diracSlab, diracModel])
    (Or.inr rfl) hk hCk hb h0 h1 h01 hβ hβk hc₁ Kh hKh eY eYD

set_option maxHeartbeats 1600000 in
/-- **A fully instantiated instance** of `cor:local-calibration-nonempty`: the flat vacuum of
`diracSlab`, `k = 4`, `C_k = 1`, slab `[t₀, t₁] = [2, 3]` with buffer `b = 1`, `β = 1/16`,
`K_h = h^{-1/16}` (`rpow_cutoff_admissible`); the state coordinates `eY`, `eYD` are arbitrary
(they exist: `exists_coords`). -/
theorem local_calibration_nonempty_flat_example
    {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP 1 (HSp diracSlab))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] Sp × CoSpinor Sp) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp diracSlab δ (dilField 2 (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))) (Ke : Set Mat) (A Cσ C : ℝ)
      (Kr : Set (Fin (ActualJetKato.dimS 1 (HSp diracSlab) Sp (CoSpinor Sp)) → ℝ)) (R₁ : ℝ),
      IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ 0 ≤ Cσ ∧ 0 ≤ C ∧
      IsCompact Kr ∧ Kr ⊆ chartC (slabX diracSlab) ∧ 0 ≤ R₁ ∧
      ExactOn (toSMData diracSlab δ) (slabT 2 3) (toTuple hδ hT) ∧
      toTuple hδ hT ∈ refSet (toSMData diracSlab δ) (slabX diracSlab) 4 (slabT 2 3) Kr R₁ ∧
      (∀ᶠ m in atTop, RecordHyp diracSlab δ Ke A 2 3 1 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))
        (meshOdd m ^ (-(1 / 16 : ℝ))) (Cσ * meshOdd m)) ∧
      Tendsto (fun m => meshOdd m * meshOdd m ^ (-(1 / 16 : ℝ))) atTop (𝓝 0) ∧ Tendsto (fun m => meshOdd m ^ (-(1 / 16 : ℝ))) atTop atTop ∧
      Tendsto (fun m => tau (oddN m) (meshOdd m ^ (-(1 / 16 : ℝ))) (4 + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))) atTop
        (𝓝 0) ∧
      Tendsto (fun m => ‖(slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).init
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) -
          (slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).init (toTuple hδ hT)‖) atTop (𝓝 0) ∧
      Tendsto (fun m => (slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).harm
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
        atTop (𝓝 0) ∧
      Tendsto (fun m => forcingBudget 4 1 (Cσ * meshOdd m) (meshOdd m) (meshOdd m ^ (-(1 / 16 : ℝ)))
          (tau (oddN m) (meshOdd m ^ (-(1 / 16 : ℝ))) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))
          (tau (oddN m) (meshOdd m ^ (-(1 / 16 : ℝ))) (4 + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))) atTop (𝓝 0) ∧
      (∀ᶠ m in atTop, dist ((slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).obs
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
          ((slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).obs (toTuple hδ hT)) ≤
        C * (‖(slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).init
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) -
          (slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).init (toTuple hδ hT)‖ +
          (slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).harm
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)) +
          forcingBudget 4 1 (Cσ * meshOdd m) (meshOdd m) (meshOdd m ^ (-(1 / 16 : ℝ)))
            (tau (oddN m) (meshOdd m ^ (-(1 / 16 : ℝ))) 2 (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))))
            (tau (oddN m) (meshOdd m ^ (-(1 / 16 : ℝ))) (4 + 2) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ)))))) ∧
      Tendsto (fun m => dist ((slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).obs
            (recTuple diracSlab hδ 2 (oddN m) (samp (n := oddN m) (meshOdd m) (vacY (𝔄 := ℝ) (𝓢 := Sp) (0 : ℝ))) (toTuple hδ hT)))
          ((slabMod diracSlab hδ eY eYD 4 (by norm_num : (2 : ℝ) < 3)).obs (toTuple hδ hT))) atTop (𝓝 0) := by
  have hpi : (4 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  obtain ⟨hK, -⟩ := rpow_cutoff_admissible (β := 1 / 16) (by norm_num)
  exact local_calibration_nonempty_flat (k := 4) le_rfl one_pos (t₀ := 2) (t₁ := 3) (b := 1)
    one_pos (by norm_num) (by linarith) (by norm_num) (β := 1 / 16) (c₁ := 1) (c₂ := 1)
    (by norm_num) (by norm_num) one_pos _ hK eY eYD

/-- State coordinates exist for every finite-dimensional state space. -/
theorem exists_coords (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Nonempty ((Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E) :=
  ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩

end Flat

end RenewalGeometry.CalibrationWitness

end
