/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordStressDirac

/-!
# The Einstein residual of the actual tuple of a native field and the native coframe row

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`, bridge step P2
(gravitational row).  For a native field satisfying `RecordTuple.TupleHyp`:

* `Fm_toTuple`, `ymStress_toTuple`, `higgsStress_toTuple` — the Yang–Mills and Higgs stresses of
  the tuple are the native ones;
* **`Tact_toTuple`** — the complete off-shell stress of the tuple is the lowered symmetric part of
  the native stress `NativeStressEuler.smStressUp`;
* **`Etr_toTuple`** — the trace-reversed Einstein residual of the tuple is
  `traceRev(g, g⁻¹, lower(sym 𝓔))` with the native Einstein residual `𝓔 = einsteinRes`;
* **`einsteinRes_sym_row`** — `sym 𝓔^{cd} = -(κ/v) 𝓔₀(Y)(x)[(S_{cd}e, 0, 0, 0, 0)]` with
  `S_{cd} = metricS e (symTest c d)` (the native coframe row on metric directions,
  `NativeStressEuler.coframe_row_einstein`).
-/

open Finset
open scoped Matrix

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect NativeStressEuler

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} {M : SlabModel 𝔄 𝓗 𝓢 m}
variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hδ : 0 < δ) (h : TupleHyp M δ Y)

attribute [local instance 100] LieRing.ofAssociativeRing

include hδ h in
/-- The field strength of the tuple is `φ` of the native field strength. -/
theorem Fm_toTuple (x : R4) (μ ν : Fin 4) :
    ActualJetGauge.Fm ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).dA μ ν =
      M.φ (FA (jet1 Y x) μ ν) := by
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  rw [FA_jet1, Ff_eq hYd]
  unfold ActualJetGauge.Fm ActualJetWriter.fieldStrength
  have hl : M.φ ⁅Af Y x μ, Af Y x ν⁆ = ⁅M.φ (Af Y x μ), M.φ (Af Y x ν)⁆ :=
    LieHom.map_lie (phiLie M) _ _
  rw [dA_toTuple hδ h x, dA_toTuple hδ h x, map_add, map_sub, hl]
  rfl

include hδ h in
theorem ymStress_toTuple (x : R4) (a b : Fin 4) :
    ActualJetRecon.ymStressB (toSMData M δ).ipG ((toTuple hδ h).jet x).FJ.g
        ((toTuple hδ h).jet x).FJ.gi
        (ActualJetGauge.Fm ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).dA) a b =
      ymStressN M.toData (jet1 Y x) a b := by
  have hF : ActualJetGauge.Fm ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).dA =
      fun μ ν => M.φ (FA (jet1 Y x) μ ν) := funext fun μ => funext fun ν => Fm_toTuple hδ h x μ ν
  rw [hF]
  unfold ActualJetRecon.ymStressB ymStressN
  have hip : ∀ u v : 𝔄, (toSMData M δ).ipG (M.φ u) (M.φ v) = M.ipA u v := fun u v => by
    show M.ipA (M.φ.symm (M.φ u)) (M.φ.symm (M.φ v)) = _
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  simp only [hip]
  rfl

include hδ h in
theorem higgsStress_toTuple (x : R4) (a b : Fin 4) :
    ActualJetRecon.higgsStressB (toSMData M δ).ipV (toSMData M δ).lamH (toSMData M δ).vH
        ((toTuple hδ h).jet x).FJ.g ((toTuple hδ h).jet x).FJ.gi ((toTuple hδ h).jet x).H
        (ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
          ((toTuple hδ h).jet x).dH) a b =
      higgsStressN M.toData (jet1 Y x) a b := by
  have hDH : ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
      ((toTuple hδ h).jet x).dH = Kf M.toData Y x := funext fun μ => DH_toTuple hδ h x μ
  rw [hDH]
  rfl

theorem ymStressN_symm (D : Data 𝔄 𝓗 𝓢) (hsym : ∀ x y, D.ipA x y = D.ipA y x) (wp : FJ 𝔄 𝓗 𝓢)
    (a b : Fin 4) : ymStressN D wp a b = ymStressN D wp b a := by
  unfold ymStressN
  rw [PalatiniEuler.metric_symm wp.1.1 a b]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [ginv_symm wp.1.1 β α, hsym]

theorem higgsStressN_symm (D : Data 𝔄 𝓗 𝓢) (hsym : ∀ x y, D.hermH x y = D.hermH y x)
    (wp : FJ 𝔄 𝓗 𝓢) (a b : Fin 4) : higgsStressN D wp a b = higgsStressN D wp b a := by
  unfold higgsStressN
  rw [PalatiniEuler.metric_symm wp.1.1 a b, hsym]

theorem raise_symm {E : Mat} {T : Fin 4 → Fin 4 → ℝ} (hT : ∀ a b, T a b = T b a) (a b : Fin 4) :
    raise E T a b = raise E T b a := by
  unfold raise
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [hT]; ring

include hδ h in
/-- **The complete off-shell stress of the tuple is the lowered symmetric native stress.** -/
theorem Tact_toTuple (x : R4) (a b : Fin 4) :
    ((toTuple hδ h).jet x).Tact (toSMData M δ) a b =
      lowerE (Y x).1 (fun c d => (1 / 2 : ℝ) * (smStressUp M.toData (jet1 Y x) c d +
        smStressUp M.toData (jet1 Y x) d c)) a b := by
  have hE := h.det_ne x
  set T : Fin 4 → Fin 4 → ℝ := fun μ ν => ymStressN M.toData (jet1 Y x) μ ν +
    higgsStressN M.toData (jet1 Y x) μ ν with hT
  have hTs : ∀ a b, T a b = T b a := fun a b => by
    simp only [hT, ymStressN_symm M.toData M.ipA_symm, higgsStressN_symm M.toData M.hermH_symm]
  have hsym : (fun c d => (1 / 2 : ℝ) * (smStressUp M.toData (jet1 Y x) c d +
      smStressUp M.toData (jet1 Y x) d c)) = fun c d => raise (Y x).1 T c d +
        (1 / 2 : ℝ) * (diracStressUp M.toData (jet1 Y x) c d +
          diracStressUp M.toData (jet1 Y x) d c) := by
    funext c d
    unfold smStressUp
    rw [show (jet1 Y x).1.1 = (Y x).1 from rfl, raise_symm hTs d c]
    ring
  rw [hsym, lowerE_add, lowerE_raise hE, ← coordTD_toTuple hδ h x a b]
  unfold ActualJet.Tact
  rw [ymStress_toTuple hδ h x a b, higgsStress_toTuple hδ h x a b]
  rfl

theorem lowerE_ginv {E : Mat} (hE : E.det ≠ 0) (a b : Fin 4) :
    lowerE E (fun c d => ginv E c d) a b = metric E a b := by
  unfold lowerE
  calc ∑ c, ∑ d, metric E a c * metric E b d * ginv E c d
      = ∑ c, metric E a c * ∑ d, metric E b d * ginv E d c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [ginv_symm E c d]; ring
    _ = metric E a b := by simp [sum_metric_ginv hE, PalatiniEuler.metric_symm E a b]

include hδ h in
/-- **The trace-reversed Einstein residual of the tuple** is the trace reversal of the lowered
symmetric native Einstein residual `𝓔^{ab} = G^{ab} + Λg^{ab} - κT_{SM}^{ab}`. -/
theorem Etr_toTuple (x : R4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).Etr =
      traceRev ((toTuple hδ h).jet x).FJ.g ((toTuple hδ h).jet x).FJ.gi
        (lowerE (Y x).1 (fun c d => (1 / 2 : ℝ) * (einsteinRes M.toData Y x c d +
          einsteinRes M.toData Y x d c))) := by
  have hE := h.det_ne x
  set J := (toTuple hδ h).jet x
  set E := (Y x).1
  have hG : ∀ a b, einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg a b =
      einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg b a :=
    einstein_symm J.FJ.g_symm J.FJ.gi_symm J.FJ.dg_symm J.FJ.ddg_symm1 J.FJ.ddg_symm2
  have hup : (fun c d => EHJetVariation.einsteinUp (gF (eF Y) x) (ginvOf (gF (eF Y) x))
      (EHFieldVariation.dF (gF (eF Y)) x) (EHFieldVariation.ddF (gF (eF Y)) x) c d) =
      raise E (einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg) := by
    funext c d
    unfold EHJetVariation.einsteinUp raise
    rfl
  have hsym : (fun c d => (1 / 2 : ℝ) * (einsteinRes M.toData Y x c d +
      einsteinRes M.toData Y x d c)) = fun c d =>
        (raise E (einstein J.FJ.g J.FJ.gi J.FJ.dg J.FJ.ddg) c d + M.Λ * ginv E c d) +
          (-M.κ) * ((1 / 2 : ℝ) * (smStressUp M.toData (jet1 Y x) c d +
            smStressUp M.toData (jet1 Y x) d c)) := by
    funext c d
    have h1 := congrFun (congrFun hup c) d
    have h2 := congrFun (congrFun hup d) c
    unfold einsteinRes
    rw [h1, h2, raise_symm hG d c, ginv_symm E d c]
    ring
  have hTact : ∀ a b, J.Tact (toSMData M δ) a b = lowerE E (fun c d => (1 / 2 : ℝ) *
      (smStressUp M.toData (jet1 Y x) c d + smStressUp M.toData (jet1 Y x) d c)) a b :=
    Tact_toTuple hδ h x
  unfold ActualJet.res
  simp only []
  congr 1
  funext a b
  rw [hsym, lowerE_add, lowerE_smul, lowerE_add, lowerE_raise hE, lowerE_smul, lowerE_ginv hE,
    ← hTact]
  show _ = _ + M.Λ * metric E a b + -M.κ * _
  have hg : J.FJ.g a b = metric E a b := rfl
  have hΛ : (toSMData M δ).Λ = M.Λ := rfl
  have hκ : (toSMData M δ).κ = M.κ := rfl
  rw [hg, hΛ, hκ]
  ring

include h in
/-- **The symmetric native Einstein residual is the native coframe row on metric directions**:
`½(𝓔^{cd} + 𝓔^{dc}) = -(κ/v) 𝓔₀(Y)(x)[(S_{cd}e, 0, 0, 0, 0)]`, `S_{cd} = metricS e (symTest c d)`. -/
theorem einsteinRes_sym_row (x : R4) (c d : Fin 4) :
    (1 / 2 : ℝ) * (einsteinRes M.toData Y x c d + einsteinRes M.toData Y x d c) =
      -(M.κ / volume (Y x).1) * contEuler (L0 M.toData) Y x
        (coframeDir (metricS (Y x).1 (symTest c d) * (Y x).1)) := by
  have hE := h.det_ne x
  have hv : volume (Y x).1 ≠ 0 := by
    rw [volume_of_det_pos (h.det_pos x)]; exact hE
  have hk := symTest_transpose c d
  rw [coframe_row_einstein M.toData M.cliff M.sigma_eq M.κ_ne h.smooth one_pos h.perL h.det_pos x
    (metricS_symm _ hk), metricVarM_metricS hE hk, sum_symTest]
  field_simp
  rw [mul_div_assoc, div_self M.κ_ne, mul_one]

end

end RenewalGeometry.RecordTuple
