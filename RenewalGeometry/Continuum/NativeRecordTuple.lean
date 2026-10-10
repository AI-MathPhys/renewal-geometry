/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSlabData
import RenewalGeometry.Continuum.NativeFieldScaling
import RenewalGeometry.Continuum.NativePhysRows
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel

/-!
# The actual field tuple of a native field (bridge step P2 of `thm:native-closure`)

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` ("the state `𝒰_h` is
built from the actual derivatives and curvatures of `z_h`").

A native field `Y = (e, A, H, Ψ, Ψ̄)` on `ℝ⁴` (unit spatial period, in the adapted Lorentz gauge,
temporal internal gauge, physical co-spinors, gauge potential in the gauge Lie subspace, inverse
metric in a margin of the Lorentzian chart — `TupleHyp`) determines the smooth actual field
tuple `toTuple` of the slab model of `prop:coupled-bootstrap`: metric `g = eᵀηe`, gauge potential
`φ ∘ A` in `gl(m)`, Higgs field, spinor and co-spinor.

## Main results

* `toTuple` — the actual field tuple, with values in the slab data `SlabData.toSMData`.
* the identification of its actual jets with the native jets: metric jets (`dg_toTuple`:
  `∂g = readerG(e, ∂e)`), the slab frame is the native frame (`e_toTuple`: `e_A{}^μ = (e⁻¹)^μ_A`,
  from `NativeFrameBridge.frU_eq_of_adapted`), its jets (`de_toTuple`:
  `∂_γe_A{}^μ = -(e⁻¹∂_γe e⁻¹)^μ_A`), gauge, Higgs and spinor jets.
* `hasDerivAt_inv_curve` (generic) — the derivative of the inverse of a matrix curve.
-/

open Finset Set
open scoped ContDiff Matrix

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic: the derivative of the inverse of a matrix curve -/

/-- `d/dt c(t)⁻¹ = -c⁻¹ c' c⁻¹` at an invertible point of a differentiable matrix curve. -/
theorem hasDerivAt_inv_curve {c : ℝ → Mat} {q : Mat} {t : ℝ} (hc : HasDerivAt c q t)
    (hdet : (c t).det ≠ 0) :
    HasDerivAt (fun s => (c s)⁻¹) (-((c t)⁻¹ * q * (c t)⁻¹)) t := by
  have hcont : ContinuousAt c t := hc.continuousAt
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun s => (c s)⁻¹ i j) t := by
    intro i j
    have h1 : DifferentiableAt ℝ (invEntry i j) (c t) :=
      (contDiffAt_invEntry (k := 1) i j hdet).differentiableAt (by norm_num)
    exact h1.comp t hc.differentiableAt
  set Dm : Mat := fun i j => deriv (fun s => (c s)⁻¹ i j) t
  have hDi : HasDerivAt (fun s => (c s)⁻¹) Dm t :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hdiff i j).hasDerivAt
  have hprod : ∀ a b, HasDerivAt (fun s => ∑ k, (c s)⁻¹ a k * c s k b)
      (∑ k, (Dm a k * c t k b + (c t)⁻¹ a k * q k b)) t := by
    intro a b
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hDi a) k
    have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hc k) b
    exact h1.fun_mul h2
  have hcd : ContinuousAt (fun s => (c s).det) t :=
    ((Continuous.matrix_det continuous_id).continuousAt).comp hcont
  have hevdet : ∀ᶠ s in nhds t, (c s).det ≠ 0 := hcd.eventually_ne hdet
  have hzero : Dm * c t + (c t)⁻¹ * q = 0 := by
    ext a b
    have h := hprod a b
    have hev : (fun s => ∑ k, (c s)⁻¹ a k * c s k b) =ᶠ[nhds t] fun _ => (1 : Mat) a b := by
      filter_upwards [hevdet] with s hs
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hs.isUnit]
    have h0 := h.unique ((hasDerivAt_const t ((1 : Mat) a b)).congr_of_eventuallyEq hev)
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simpa using h0
  have hD : Dm = -((c t)⁻¹ * q * (c t)⁻¹) := by
    have hEEi : c t * (c t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet.isUnit
    calc Dm = (Dm * c t + (c t)⁻¹ * q) * (c t)⁻¹ - (c t)⁻¹ * q * (c t)⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_assoc Dm, hEEi, Matrix.mul_one]; abel
      _ = -((c t)⁻¹ * q * (c t)⁻¹) := by rw [hzero, Matrix.zero_mul, zero_sub]
  rw [hD] at hDi
  exact hDi

/-! ### Native fields satisfying the slab hypotheses -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **The hypotheses on a unit-scale native field** under which it is an actual field tuple of the
slab model: smoothness, unit spatial periodicity (and `ℤ⁴`-periodicity of the coframe, the
setting of the coframe row `NativeStressEuler.coframe_row`), the adapted Lorentz gauge, a margin
`δ` of the Lorentzian chart for the inverse metric, temporal internal gauge `A₀ = 0`, gauge
potential in the gauge Lie subspace and physical (`ℂ`-linear) co-spinors. -/
structure TupleHyp (δ : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) : Prop where
  smooth : ContDiff ℝ ∞ Y
  per : ∀ (k : Fin 3 → ℤ) (x : R4), Y (x + SymHypEnergy.sshift k) = Y x
  perL : IsLPeriodic 1 (eF Y)
  adapted : ∀ x, IsAdaptedCoframe (Y x).1
  margin : ∀ x, Margin δ (ginvOf (gF (eF Y) x))
  temporal : ∀ x, (Y x).2.1 0 = 0
  gauge : ∀ x μ, (Y x).2.1 μ ∈ M.gLie
  clin : ∀ x, IsCLin M.toModel (Y x).2.2.2.2

variable {M}
variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢}

theorem TupleHyp.det_pos (h : TupleHyp M δ Y) (x : R4) : 0 < (Y x).1.det := by
  have ha := h.adapted x
  have hl : Matrix.BlockTriangular (Y x).1 OrderDual.toDual := fun i j hij => ha.1 i j hij
  rw [Matrix.det_of_lowerTriangular _ hl]
  exact Finset.prod_pos fun i _ => ha.2 i

theorem TupleHyp.det_ne (h : TupleHyp M δ Y) (x : R4) : (Y x).1.det ≠ 0 := (h.det_pos x).ne'

theorem metric_det_ne {E : Mat} (hE : E.det ≠ 0) : (Matrix.of fun i j => metric E i j).det ≠ 0 :=
  det_metric_ne_zero hE

theorem TupleHyp.chart (hδ : 0 < δ) (h : TupleHyp M δ Y) (x : R4) :
    IsLorChart (ginvOf (gF (eF Y) x)) := (h.margin x).isLorChart hδ

/-- The inverse metric of a coframe as `ginvOf`. -/
theorem ginvOf_gF (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) :
    ginvOf (gF (eF Y) x) = fun a b => (metric (Y x).1)⁻¹ a b := rfl

theorem contDiff_eF' (h : ContDiff ℝ ∞ Y) : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp h

/-- The projections of a native field. -/
def projAμ (μ : Fin 4) : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝔄 :=
  (ContinuousLinearMap.proj μ).comp ((ContinuousLinearMap.fst ℝ (Fin 4 → 𝔄) _).comp
    (ContinuousLinearMap.snd ℝ Mat _))

def projH : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝓗 :=
  (ContinuousLinearMap.fst ℝ 𝓗 _).comp ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp
    (ContinuousLinearMap.snd ℝ Mat _))

def projψ : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝓢 :=
  (ContinuousLinearMap.fst ℝ 𝓢 _).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

def projψb : Field 𝔄 𝓗 𝓢 →L[ℝ] CoSpinor 𝓢 :=
  (ContinuousLinearMap.snd ℝ 𝓢 _).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

/-- **The actual field tuple of a native field** (`TupleHyp`): metric `g = eᵀηe`, gauge
potential `φ ∘ A ∈ gl(m)`, Higgs field, spinor, co-spinor. -/
def toTuple (hδ : 0 < δ) (h : TupleHyp M δ Y) : Tuple m (HSp M) 𝓢 (CoSpinor 𝓢) where
  g := gF (eF Y)
  A := fun x μ => M.φ ((Y x).2.1 μ)
  H := fun x => (show HSp M from (Y x).2.2.1)
  ψ := fun x => (Y x).2.2.2.1
  ψb := fun x => (Y x).2.2.2.2
  g_smooth := contDiff_gF (contDiff_eF' h.smooth)
  A_smooth := contDiff_pi.2 fun μ => (contDiff_phi M).comp
    ((projAμ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ).contDiff.comp h.smooth)
  H_smooth := (projH (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).contDiff.comp h.smooth
  ψ_smooth := (projψ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).contDiff.comp h.smooth
  ψb_smooth := (projψb (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).contDiff.comp h.smooth
  g_per k x := by
    show gF (eF Y) (x + SymHypEnergy.sshift k) = gF (eF Y) x
    unfold gF eF
    rw [h.per k x]
  A_per k x := by
    show (fun μ => M.φ ((Y (x + SymHypEnergy.sshift k)).2.1 μ)) = fun μ => M.φ ((Y x).2.1 μ)
    rw [h.per k x]
  H_per k x := by
    show (Y (x + SymHypEnergy.sshift k)).2.2.1 = (Y x).2.2.1
    rw [h.per k x]
  ψ_per k x := by
    show (Y (x + SymHypEnergy.sshift k)).2.2.2.1 = (Y x).2.2.2.1
    rw [h.per k x]
  ψb_per k x := by
    show (Y (x + SymHypEnergy.sshift k)).2.2.2.2 = (Y x).2.2.2.2
    rw [h.per k x]
  g_symm x μ ν := metric_symm _ μ ν
  temporal x := by
    show M.φ ((Y x).2.1 0) = 0
    rw [h.temporal x, map_zero]
  det_ne x := det_metric_ne_zero (h.det_ne x)
  lor x := h.chart hδ x

variable (hδ : 0 < δ) (h : TupleHyp M δ Y)

theorem toTuple_g (x : R4) : (toTuple hδ h).g x = gF (eF Y) x := rfl

theorem toTuple_gi (x : R4) : (toTuple hδ h).gi x = fun a b => (metric (Y x).1)⁻¹ a b := rfl

theorem toTuple_A (x : R4) (μ : Fin 4) : (toTuple hδ h).A x μ = M.φ ((Y x).2.1 μ) := rfl

/-- **The slab frame is the native frame**: `e_A{}^μ = (e⁻¹)^μ_A`. -/
theorem e_toTuple (x : R4) (A μ : Fin 4) : (toTuple hδ h).e x A μ = ((Y x).1)⁻¹ μ A :=
  frU_eq_of_adapted (h.adapted x) (h.det_ne x) (h.chart hδ x) A μ

/-- The coordinate derivative jets of the coframe, `q_γ = ∂_γe`. -/
def qJ (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) (γ : Fin 4) : Mat := fderiv ℝ (eF Y) x (evec γ)

theorem pd_eF (x : R4) (γ : Fin 4) : pd (eF Y) γ x = qJ Y x γ := rfl

/-- **The metric first jet is the reader jet**: `∂_αg = readerG(e, ∂e)`. -/
theorem dg_toTuple (x : R4) :
    (toTuple hδ h).dg x = fun α i j => readerG (Y x).1 (qJ Y x) α i j := by
  funext α i j
  exact dF_gF ((contDiff_eF' h.smooth).differentiable (by simp)) x α i j

/-- **The frame jets**: `∂_γe_A{}^μ = -(e⁻¹∂_γe e⁻¹)^μ_A`. -/
theorem de_toTuple (x : R4) (γ A μ : Fin 4) :
    (toTuple hδ h).de x γ A μ = (-(((Y x).1)⁻¹ * qJ Y x γ * ((Y x).1)⁻¹)) μ A := by
  set z := toTuple hδ h
  have he : (fun y => z.e y A μ) = fun y => ((Y y).1)⁻¹ μ A := funext fun y => e_toTuple hδ h y A μ
  rw [← z.pd_e x γ A μ, he]
  have hY : DifferentiableAt ℝ (eF Y) x := (contDiff_eF' h.smooth).differentiable (by simp) x
  have hline : HasDerivAt (fun s : ℝ => eF Y (x + s • PeriodicCube.ev γ)) (qJ Y x γ) 0 := by
    exact ActualJetBridge.hasDerivAt_line0 (d := 3) hY γ
  have hinv := hasDerivAt_inv_curve hline (by simpa [eF] using h.det_ne x)
  have hd : DifferentiableAt ℝ (fun y => ((Y y).1)⁻¹ μ A) x := by
    have h1 : DifferentiableAt ℝ (invEntry μ A) ((Y x).1) :=
      (contDiffAt_invEntry (k := 1) μ A (h.det_ne x)).differentiableAt (by norm_num)
    exact h1.comp x hY
  refine ActualJetBridge.pd_eq_of_line hd ?_
  have := hasDerivAt_pi.1 (hasDerivAt_pi.1 hinv μ) A
  simpa [eF] using this

/-! ### The physical directions -/

/-- **The physical Euler equations are the Euler equations in the gauge Lie algebra**: a covector
`E` on the native field space vanishes on `physF πg` iff it vanishes on every direction whose gauge
components lie in the gauge Lie algebra `𝔤 = gSub` (coframe, Higgs, spinor and co-spinor
directions unrestricted). -/
theorem comp_physF_eq_zero_iff (M : SlabModel 𝔄 𝓗 𝓢 m) (E : ContEulerBounds.CovV (Field 𝔄 𝓗 𝓢)) :
    E.comp (NativeTail.physF M.πg) = 0 ↔
      ∀ w : Field 𝔄 𝓗 𝓢, (∀ μ, w.2.1 μ ∈ M.gSub) → E w = 0 := by
  constructor
  · intro h w hw
    have hP : NativeTail.physF M.πg w = w := by
      rw [NativeTail.physF_apply]
      have : NativeTail.gaugeSlots M.πg w.2.1 = w.2.1 := by
        funext μ
        rw [NativeTail.gaugeSlots_apply, M.πg_of_mem (hw μ)]
      rw [this]
    rw [← hP]
    exact congrArg (fun T : ContEulerBounds.CovV (Field 𝔄 𝓗 𝓢) => T w) h
  · intro h
    refine ContinuousLinearMap.ext fun w => ?_
    show E (NativeTail.physF M.πg w) = 0
    refine h _ fun μ => ?_
    exact M.πg_mem _

end

end RenewalGeometry.RecordTuple
