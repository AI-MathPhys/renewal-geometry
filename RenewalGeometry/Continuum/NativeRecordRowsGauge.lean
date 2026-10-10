/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRowsDirac

/-!
# The Yang–Mills and Higgs residuals of the actual tuple of a native field

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`, bridge step P2 (gauge
and Higgs rows).  For a native field satisfying `RecordTuple.TupleHyp`, with the slab theory
data `SlabData.toSMData` of its slab model:

* **`rA_toTuple`** — the Yang–Mills residual of the tuple is the image under `φ` of the native
  Yang–Mills residual `ActualJetGauge.ymRes` of the native jets with the `𝔤`-current
  `Jg = πg Jnat` (`Jnat` represents the native matter current, `Jnat_rep`; `Jg` represents it on
  the gauge Lie algebra, `Jg_rep`); it is `𝔤`-valued (`rA_mem`: `𝔤` is a Lie subalgebra
  containing the potential and its jets, `ymRes_Jg_mem`), and the native gauge row **in the
  `𝔤`-directions** is `𝓔₀(Y)[(0, X, 0, 0, 0)] = v g^{νσ}⟨X_ν, φ⁻¹r^A_σ⟩` (`gauge_row_toTuple`,
  `X` with values in `𝔤`; the gauge sector of the corrected encoding lives in `𝔤`);
* **`rH_toTuple`** — the Higgs residual of the tuple is `waveN - S_H`, and the native Higgs row is
  `𝓔₀(Y)[(0, 0, η, 0, 0)] = 2v⟨η, r_H⟩` (`higgs_row_toTuple`).

Generic: `ymRes_map` (naturality of the Yang–Mills residual under a Lie algebra homomorphism),
`rieszVec_eq_of` (uniqueness of Riesz vectors).
-/

open Finset
open scoped Matrix ContDiff

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic -/

section Generic

variable {𝔤 𝔥 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- **Naturality of the Yang–Mills residual** under a Lie algebra homomorphism. -/
theorem ymRes_map (f : 𝔤 →ₗ⁅ℝ⁆ 𝔥) (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤)
    (ddA : Fin 4 → Fin 4 → Fin 4 → 𝔤) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (J : Fin 4 → 𝔤) (ν : Fin 4) :
    f (ActualJetGauge.ymRes A dA ddA gi Γ J ν) =
      ActualJetGauge.ymRes (fun μ => f (A μ)) (fun γ μ => f (dA γ μ)) (fun α γ μ => f (ddA α γ μ))
        gi Γ (fun σ => f (J σ)) ν := by
  unfold ActualJetGauge.ymRes ActualJetGauge.ymDiv ActualJetGauge.dFm ActualJetGauge.Fm
    ActualJetWriter.fieldStrength
  simp only [map_sub, map_sum, map_smul, map_add, LieHom.map_lie]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Uniqueness of Riesz vectors**: if `B(y, w) = c(y)` for all `y` then `w = rieszVec c`. -/
theorem rieszVec_eq_of {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0)
    (c : W →ₗ[ℝ] ℝ) {w : W} (hw : ∀ y, B y w = c y) : w = rieszVec hB c := by
  have h := hB (w - rieszVec hB c) fun y => by rw [map_sub, hw, riesz_apply]; ring
  exact sub_eq_zero.1 h

end Generic

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} {M : SlabModel 𝔄 𝓗 𝓢 m}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `φ` as a Lie algebra homomorphism (commutator brackets). -/
def phiLie (M : SlabModel 𝔄 𝓗 𝓢 m) : 𝔄 →ₗ⁅ℝ⁆ MatLie m where
  toLinearMap := M.φ.toLinearMap
  map_lie' {a b} := by
    show M.φ (a * b - b * a) = M.φ a * M.φ b - M.φ b * M.φ a
    rw [map_sub, map_mul, map_mul]

theorem phiLie_apply (a : 𝔄) : phiLie M a = M.φ a := rfl

variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hδ : 0 < δ) (h : TupleHyp M δ Y)

/-! ### The jets of the tuple in native form -/

/-- The Higgs component field. -/
def Hf (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : 𝓗 := (Y y).2.2.1

include h in
theorem contDiff_Hf : ContDiff ℝ ∞ (Hf Y) := (projH (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).contDiff.comp h.smooth

include h in
theorem jet1_Hf (x : R4) (μ : Fin 4) : ((jet1 Y x).2 μ).2.2.1 = pd (Hf Y) μ x :=
  (pd_clm (projH (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) ((h.smooth.differentiable (by simp)) x) μ).symm

include hδ h in
theorem dA_toTuple (x : R4) (γ μ : Fin 4) :
    ((toTuple hδ h).jet x).dA γ μ = M.φ (dAf Y x γ μ) := by
  show pd (toTuple hδ h).A γ x μ = _
  rw [← ActualJetBridge.pd_apply ((toTuple hδ h).A_smooth.differentiable (by simp) x) γ μ]
  have hd : DifferentiableAt ℝ (fun y => Af Y y μ) x :=
    (contDiff_Af h.smooth μ).differentiable (by simp) x
  exact pd_clm (LinearMap.toContinuousLinearMap M.φ.toLinearMap) hd γ

include hδ h in
theorem ddA_toTuple (x : R4) (α γ μ : Fin 4) :
    ((toTuple hδ h).jet x).ddA α γ μ = M.φ (ddAf Y x α γ μ) := by
  show pd (pd (toTuple hδ h).A γ) α x μ = _
  rw [← ActualJetBridge.pd_apply ((ActualJetBridge.contDiff_pd (toTuple hδ h).A_smooth γ).differentiable
    (by simp) x) α μ]
  have hfun : (fun y => pd (toTuple hδ h).A γ y μ) = fun y => M.φ (dAf Y y γ μ) := by
    funext y
    exact dA_toTuple hδ h y γ μ
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun y => dAf Y y γ μ) x :=
    (contDiff_dAf h.smooth γ μ).differentiable (by simp) x
  exact pd_clm (LinearMap.toContinuousLinearMap M.φ.toLinearMap) hd α

include hδ h in
/-- The covariant Higgs derivative of the tuple is the native one: `D_μH = K_μ`. -/
theorem DH_toTuple (x : R4) (μ : Fin 4) :
    ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
        ((toTuple hδ h).jet x).dH μ = Kf M.toData Y x μ := by
  unfold ActualJetGauge.DH Kf KH
  rw [HSp.lie_def, jet1_Hf h x μ]
  show pd (Hf Y) μ x + M.ρH (M.φ.symm (M.φ ((Y x).2.1 μ))) (Y x).2.2.1 = _
  rw [AlgEquiv.symm_apply_apply, add_comm]
  rfl

include hδ h in
/-- In the margin and the adapted gauge the smoothed slab gamma matrices are the native
`γ^ν(e)`. -/
theorem gamU_eq (x : R4) (ν : Fin 4) :
    gamU M δ (ginvOf (gF (eF Y) x)) ν = gammaMu M.toData ν (Y x).1 := by
  unfold gamU
  rw [gammaMu_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [frUs_eq_frU hδ (h.margin x)]
  congr 1
  exact frU_eq_of_adapted (h.adapted x) (h.det_ne x) (h.chart hδ x) a ν

/-- **The native Yang–Mills current** `J_σ = g_{σν}R⁻¹(curVal_ν)` at a point. -/
def Jnat (M : SlabModel 𝔄 𝓗 𝓢 m) (δ : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) (σ : Fin 4) : 𝔄 :=
  ∑ ν, gF (eF Y) x σ ν • rieszVec M.ipA_nondeg
    (curVal M δ (ginvOf (gF (eF Y) x)) (Y x).2.2.1 (Kf M.toData Y x) (Y x).2.2.2.1 (Y x).2.2.2.2 ν)

theorem ginvOf_mul_gF {E : Mat} (hE : E.det ≠ 0) (a c : Fin 4) :
    ∑ b, (metric E)⁻¹ a b * metric E b c = if a = c then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (metric E) (isUnit_iff_ne_zero.mpr (det_metric_ne_zero hE))
  have := congrFun (congrFun h a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

include hδ h in
/-- **`Jnat` represents the native matter current**: `v g^{νσ}⟨X_ν, J_σ⟩ = -j(X)`. -/
theorem Jnat_rep (x : R4) (X : Fin 4 → 𝔄) :
    volume (Y x).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) x) ν σ * M.ipA (X ν) (Jnat M δ Y x σ) =
      -gaugeCur M.toData (jet1 Y x) X := by
  have hE := h.det_ne x
  set w : Fin 4 → 𝔄 := fun ν => rieszVec M.ipA_nondeg
    (curVal M δ (ginvOf (gF (eF Y) x)) (Y x).2.2.1 (Kf M.toData Y x) (Y x).2.2.2.1 (Y x).2.2.2.2 ν)
    with hw
  have hJ : ∀ σ, Jnat M δ Y x σ = ∑ ν, gF (eF Y) x σ ν • w ν := fun σ => rfl
  have h1 : ∀ ν, ∑ σ, ginvOf (gF (eF Y) x) ν σ * M.ipA (X ν) (Jnat M δ Y x σ) =
      curVal M δ (ginvOf (gF (eF Y) x)) (Y x).2.2.1 (Kf M.toData Y x) (Y x).2.2.2.1 (Y x).2.2.2.2
        ν (X ν) := by
    intro ν
    have hδν : ∀ ν', (∑ σ, ginvOf (gF (eF Y) x) ν σ * gF (eF Y) x σ ν') =
        if ν = ν' then 1 else 0 := fun ν' => ginvOf_mul_gF hE ν ν'
    calc ∑ σ, ginvOf (gF (eF Y) x) ν σ * M.ipA (X ν) (Jnat M δ Y x σ)
        = ∑ σ, ∑ ν', ginvOf (gF (eF Y) x) ν σ * (gF (eF Y) x σ ν' * M.ipA (X ν) (w ν')) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hJ, map_sum, Finset.mul_sum]
          simp only [map_smul, smul_eq_mul]
      _ = ∑ ν', (∑ σ, ginvOf (gF (eF Y) x) ν σ * gF (eF Y) x σ ν') * M.ipA (X ν) (w ν') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun σ _ => by ring
      _ = M.ipA (X ν) (w ν) := by simp [hδν]
      _ = _ := riesz_apply M.ipA_nondeg
          (curValL M δ (ginvOf (gF (eF Y) x)) (Y x).2.2.1 (Kf M.toData Y x) (Y x).2.2.2.1
            (Y x).2.2.2.2 ν) (X ν)
  simp only [h1]
  have hγ : ∀ μ, gammaMu M.toData μ (Y x).1 = gamU M δ (ginvOf (gF (eF Y) x)) μ :=
    fun μ => (gamU_eq hδ h x μ).symm
  unfold gaugeCur curVal
  simp only [KH_jet1, ginv_eF, jet1_fst, hγ, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg, sub_neg_eq_add, Finset.mul_sum, Complex.re_sum,
    mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, neg_neg, neg_add_rev]
  have hswap : ∑ μ, ∑ ν, volume (Y x).1 * (ginvOf (gF (eF Y) x) μ ν *
      M.hermH (Kf M.toData Y x μ) (M.ρH (X ν) (Y x).2.2.1)) =
      ∑ ν, ∑ μ, volume (Y x).1 * (ginvOf (gF (eF Y) x) μ ν *
        M.hermH (Kf M.toData Y x μ) (M.ρH (X ν) (Y x).2.2.1)) := Finset.sum_comm
  rw [hswap]
  simp only [Complex.add_re, Complex.re_sum, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- **The `𝔤`-component of the native Yang–Mills current** `J^𝔤_σ = πg J_σ` (the current of the
physical gauge rows: `v g^{νσ}⟨X_ν, J^𝔤_σ⟩ = -j(X)` for `𝔤`-valued `X`, `Jg_rep`). -/
def Jg (M : SlabModel 𝔄 𝓗 𝓢 m) (δ : ℝ) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) (σ : Fin 4) : 𝔄 :=
  M.πg (Jnat M δ Y x σ)

theorem Jg_mem (x : R4) (σ : Fin 4) : Jg M δ Y x σ ∈ M.gSub := M.πg_mem _

include hδ h in
/-- `J^𝔤` represents the native matter current on the gauge Lie algebra. -/
theorem Jg_rep (x : R4) (X : Fin 4 → 𝔄) (hX : ∀ ν, X ν ∈ M.gSub) :
    volume (Y x).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) x) ν σ * M.ipA (X ν) (Jg M δ Y x σ) =
      -gaugeCur M.toData (jet1 Y x) X := by
  rw [← Jnat_rep hδ h x X]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
  unfold Jg
  rw [M.ipA_πg (hX ν)]

include hδ h in
theorem Jcur_toTuple (x : R4) (σ : Fin 4) :
    (toSMData M δ).Jcur ((toTuple hδ h).jet x).FJ.g ((toTuple hδ h).jet x).FJ.gi
        ((toTuple hδ h).jet x).H
        (ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
          ((toTuple hδ h).jet x).dH)
        ((toTuple hδ h).jet x).ψ ((toTuple hδ h).jet x).ψb σ = M.φ (Jg M δ Y x σ) := by
  have hDH : ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
      ((toTuple hδ h).jet x).dH = Kf M.toData Y x := funext fun μ => DH_toTuple hδ h x μ
  show Jcur M δ (gF (eF Y) x) (ginvOf (gF (eF Y) x)) (Y x).2.2.1 _ (Y x).2.2.2.1 (Y x).2.2.2.2 σ = _
  rw [hDH]
  unfold Jcur Jg Jnat
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, map_smul]

include hδ h in
/-- **The Yang–Mills residual of the tuple** is `φ` of the native Yang–Mills residual with the
`𝔤`-current `J^𝔤`. -/
theorem rA_toTuple (x : R4) (σ : Fin 4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).rA σ =
      M.φ (ActualJetGauge.ymRes (Af Y x) (dAf Y x) (ddAf Y x) (ginvOf (gF (eF Y) x))
        (chr (ginvOf (gF (eF Y) x)) (EHFieldVariation.dF (gF (eF Y)) x)) (Jg M δ Y x) σ) := by
  rw [← phiLie_apply, ymRes_map]
  have hdA : ((toTuple hδ h).jet x).dA = fun γ μ => phiLie M (dAf Y x γ μ) :=
    funext fun γ => funext fun μ => dA_toTuple hδ h x γ μ
  have hddA : ((toTuple hδ h).jet x).ddA = fun α γ μ => phiLie M (ddAf Y x α γ μ) :=
    funext fun α => funext fun γ => funext fun μ => ddA_toTuple hδ h x α γ μ
  have hJ : (toSMData M δ).Jcur ((toTuple hδ h).jet x).FJ.g ((toTuple hδ h).jet x).FJ.gi
        ((toTuple hδ h).jet x).H
        (ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
          ((toTuple hδ h).jet x).dH)
        ((toTuple hδ h).jet x).ψ ((toTuple hδ h).jet x).ψb =
      fun σ => phiLie M (Jg M δ Y x σ) := funext fun σ => Jcur_toTuple hδ h x σ
  simp only [ActualJet.res]
  rw [hdA, hddA, hJ]
  rfl

/-! ### The gauge jets lie in the gauge Lie algebra -/

/-- A derivative of a `𝔤`-valued function is `𝔤`-valued. -/
theorem pd_mem_gSub {f : R4 → 𝔄} {x : R4} (hf : DifferentiableAt ℝ f x)
    (hmem : ∀ y, f y ∈ M.gSub) (γ : Fin 4) : pd f γ x ∈ M.gSub := by
  set L : 𝔄 →L[ℝ] 𝔄 := ContinuousLinearMap.id ℝ 𝔄 - M.πg with hL
  have h0 : (fun y => L (f y)) = fun _ => 0 := by
    funext y
    simp [hL, M.πg_of_mem (hmem y)]
  have h1 := pd_clm L hf γ
  rw [h0] at h1
  have h2 : pd (fun _ : R4 => (0 : 𝔄)) γ x = 0 := by
    unfold SobolevOpen.pd; simp
  rw [h2] at h1
  have h3 : pd f γ x - M.πg (pd f γ x) = 0 := by
    simpa [hL] using h1.symm
  rw [sub_eq_zero] at h3
  rw [h3]
  exact M.πg_mem _

include h in
theorem Af_mem (y : R4) (μ : Fin 4) : Af Y y μ ∈ M.gSub := by
  have := h.gauge y μ
  rw [← M.gLie_eq] at this
  exact this

include h in
theorem dAf_mem (y : R4) (γ μ : Fin 4) : dAf Y y γ μ ∈ M.gSub :=
  pd_mem_gSub ((contDiff_Af h.smooth μ).differentiable (by simp) y) (fun y' => Af_mem h y' μ) γ

include h in
theorem ddAf_mem (y : R4) (α γ μ : Fin 4) : ddAf Y y α γ μ ∈ M.gSub :=
  pd_mem_gSub ((contDiff_dAf h.smooth γ μ).differentiable (by simp) y)
    (fun y' => dAf_mem h y' γ μ) α

theorem lie_mem_gSub {a b : 𝔄} (ha : a ∈ M.gSub) (hb : b ∈ M.gSub) : ⁅a, b⁆ ∈ M.gSub := by
  rw [Ring.lie_def]
  exact M.gSub_lie a ha b hb

include h in
/-- **The native Yang–Mills residual with the `𝔤`-current is `𝔤`-valued** (`𝔤` is a Lie
subalgebra containing the potential and its jets). -/
theorem ymRes_Jg_mem (x : R4) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (σ : Fin 4) :
    ActualJetGauge.ymRes (Af Y x) (dAf Y x) (ddAf Y x) gi Γ (Jg M δ Y x) σ ∈ M.gSub := by
  have hA := fun μ => Af_mem h x μ
  have hdA := fun γ μ => dAf_mem h x γ μ
  have hddA := fun α γ μ => ddAf_mem h x α γ μ
  have hF : ∀ μ ν, ActualJetGauge.Fm (Af Y x) (dAf Y x) μ ν ∈ M.gSub := by
    intro μ ν
    unfold ActualJetGauge.Fm ActualJetWriter.fieldStrength
    exact M.gSub.add_mem (M.gSub.sub_mem (hdA μ ν) (hdA ν μ)) (lie_mem_gSub (hA μ) (hA ν))
  have hdF : ∀ γ μ ν, ActualJetGauge.dFm (Af Y x) (dAf Y x) (ddAf Y x) γ μ ν ∈ M.gSub := by
    intro γ μ ν
    unfold ActualJetGauge.dFm
    exact M.gSub.add_mem (M.gSub.add_mem (M.gSub.sub_mem (hddA γ μ ν) (hddA γ ν μ))
      (lie_mem_gSub (hdA γ μ) (hA ν))) (lie_mem_gSub (hA μ) (hdA γ ν))
  unfold ActualJetGauge.ymRes ActualJetGauge.ymDiv
  refine M.gSub.sub_mem (M.gSub.sum_mem fun μ _ => M.gSub.sum_mem fun ρ _ => ?_) (Jg_mem x σ)
  refine M.gSub.smul_mem _ (M.gSub.add_mem (M.gSub.sub_mem (hdF ρ μ σ) ?_)
    (lie_mem_gSub (hA ρ) (hF μ σ)))
  exact M.gSub.sum_mem fun l _ => M.gSub.add_mem (M.gSub.smul_mem _ (hF l σ))
    (M.gSub.smul_mem _ (hF μ l))

include hδ h in
/-- **The Yang–Mills residual of the tuple is `𝔤`-valued**: `φ⁻¹ r^A_σ ∈ 𝔤`. -/
theorem rA_mem (x : R4) (σ : Fin 4) :
    M.φ.symm ((((toTuple hδ h).jet x).res (toSMData M δ)).rA σ) ∈ M.gSub := by
  rw [rA_toTuple hδ h x σ, AlgEquiv.symm_apply_apply]
  exact ymRes_Jg_mem h x _ _ σ

include hδ h in
/-- **The native gauge row in the `𝔤`-directions in terms of the Yang–Mills residual of the
tuple**: `𝓔₀(Y)(x)[(0, X, 0, 0, 0)] = v g^{νσ}⟨X_ν, φ⁻¹r^A_σ⟩` for every `𝔤`-valued `X`. -/
theorem gauge_row_toTuple (x : R4) (X : Fin 4 → 𝔄) (hX : ∀ ν, X ν ∈ M.gSub) :
    contEuler (L0 M.toData) Y x (gaugeDir X) =
      volume (Y x).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) x) ν σ *
        M.ipA (X ν) (M.φ.symm ((((toTuple hδ h).jet x).res (toSMData M δ)).rA σ)) := by
  rw [ym_euler_row_ymRes M.toData M.ipA_symm M.ipA_inv h.smooth h.det_pos x (Jnat M δ Y x)
    (Jnat_rep hδ h x) X]
  simp only [rA_toTuple hδ h x, AlgEquiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  unfold ActualJetGauge.ymRes
  rw [map_sub, map_sub]
  congr 1
  unfold Jg
  rw [M.ipA_πg (hX ν)]

/-! ### The Higgs row -/

include h in
/-- The derivative of the covariant Higgs derivative: `∂_ρK_μ = ρ_H(∂_ρA_μ)H + ρ_H(A_μ)∂_ρH +
∂_ρ∂_μH`. -/
theorem pd_Kf (x : R4) (ρ μ : Fin 4) :
    pd (fun y => Kf M.toData Y y μ) ρ x =
      pd (pd (Hf Y) μ) ρ x + M.ρH (dAf Y x ρ μ) (Y x).2.2.1 +
        M.ρH ((Y x).2.1 μ) (pd (Hf Y) ρ x) := by
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  have hfun : (fun y => Kf M.toData Y y μ) =
      fun y => M.ρHL (Af Y y μ) (Hf Y y) + pd (Hf Y) μ y := by
    funext y
    unfold Kf KH
    rw [jet1_Hf h y μ]
    rfl
  have hA : HasDerivAt (fun s : ℝ => Af Y (x + s • PeriodicCube.ev ρ) μ) (dAf Y x ρ μ) 0 :=
    ActualJetBridge.hasDerivAt_line0 (d := 3)
      ((contDiff_Af h.smooth μ).differentiable (by simp) x) ρ
  have hH : HasDerivAt (fun s : ℝ => Hf Y (x + s • PeriodicCube.ev ρ)) (pd (Hf Y) ρ x) 0 :=
    ActualJetBridge.hasDerivAt_line0 (d := 3) ((contDiff_Hf h).differentiable (by simp) x) ρ
  have hdH : HasDerivAt (fun s : ℝ => pd (Hf Y) μ (x + s • PeriodicCube.ev ρ))
      (pd (pd (Hf Y) μ) ρ x) 0 :=
    ActualJetBridge.hasDerivAt_line0 (d := 3)
      ((ActualJetBridge.contDiff_pd (contDiff_Hf h) μ).differentiable (by simp) x) ρ
  have h1 := ((M.ρHL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA).clm_apply hH).add hdH
  have hd : DifferentiableAt ℝ (fun y => M.ρHL (Af Y y μ) (Hf Y y) + pd (Hf Y) μ y) x := by
    rw [← hfun]
    exact (contDiff_Kf M.toData h.smooth μ).differentiable (by simp) x
  rw [hfun, ActualJetBridge.pd_eq_of_line hd h1]
  simp only [Function.comp_apply, zero_smul, add_zero, Data.ρHL_apply]
  have e : Hf Y x = (Y x).2.2.1 := rfl
  have e' : Af Y x μ = (Y x).2.1 μ := rfl
  rw [e, e']
  abel

include hδ h in
/-- **The covariant wave operator of the tuple is the native one.** -/
theorem waveH_toTuple (x : R4) :
    ActualJetGauge.waveH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).dA
        ((toTuple hδ h).jet x).H ((toTuple hδ h).jet x).dH ((toTuple hδ h).jet x).ddH
        ((toTuple hδ h).jet x).FJ.gi
        (chr ((toTuple hδ h).jet x).FJ.gi ((toTuple hδ h).jet x).FJ.dg) =
      waveN M.toData Y x := by
  have hDH : ∀ l, ActualJetGauge.DH ((toTuple hδ h).jet x).A ((toTuple hδ h).jet x).H
      ((toTuple hδ h).jet x).dH l = Kf M.toData Y x l := fun l => DH_toTuple hδ h x l
  unfold ActualJetGauge.waveH waveN
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp only [hDH]
  rw [pd_Kf h x ρ μ]
  unfold ActualJetGauge.dDH
  rw [dA_toTuple hδ h x ρ μ]
  simp only [HSp.lie_def'', AlgEquiv.symm_apply_apply]
  have e1 : ((toTuple hδ h).jet x).ddH ρ μ = pd (pd (Hf Y) μ) ρ x := rfl
  have e2 : ((toTuple hδ h).jet x).dH ρ = pd (Hf Y) ρ x := rfl
  have e3 : ((toTuple hδ h).jet x).A μ = M.φ ((Y x).2.1 μ) := rfl
  have e4 : ((toTuple hδ h).jet x).A ρ = M.φ ((Y x).2.1 ρ) := rfl
  have e5 : (((toTuple hδ h).jet x).H : 𝓗) = (Y x).2.2.1 := rfl
  simp only [e1, e2, e3, e4, e5, AlgEquiv.symm_apply_apply]
  rw [HSp.lie_def' (M := M) (M.φ ((Y x).2.1 ρ)) (Kf M.toData Y x μ), AlgEquiv.symm_apply_apply]
  have e6 : ((toTuple hδ h).jet x).FJ.gi = ginvOf (gF (eF Y) x) := rfl
  have e7 : ((toTuple hδ h).jet x).FJ.dg = EHFieldVariation.dF (gF (eF Y)) x := rfl
  rw [e6, e7]
  rfl

/-- The Higgs source of the native Lagrangian (`SlabData.SH`, as a vector of `𝓗`). -/
def SHn (M : SlabModel 𝔄 𝓗 𝓢 m) (H : 𝓗) (ψ : 𝓢) (ψb : CoSpinor 𝓢) : 𝓗 :=
  (1 / 2 : ℝ) • rieszVec M.hermH_nondeg (srcVal M H ψ ψb)

/-- The Higgs source represents the native potential and Yukawa covector:
`2v⟨η, S_H⟩ = v DV(H)[η] + v Re Ψ̄𝓜_𝐘(η)Ψ`. -/
theorem SH_rep (H : 𝓗) (ψ : 𝓢) (ψb : CoSpinor 𝓢) (v : ℝ) (η : 𝓗) :
    2 * v * M.hermH η (SHn M H ψ ψb) =
      v * potGrad M.toData H η + v * (ψb (M.yukawa η ψ)).re := by
  unfold SHn
  rw [map_smul, smul_eq_mul]
  have := riesz_apply M.hermH_nondeg (srcValL M H ψ ψb) η
  simp only [srcValL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  unfold srcVal potGrad
  ring

include hδ h in
/-- **The Higgs residual of the tuple** is `□_AH - S_H` with the native wave operator. -/
theorem rH_toTuple (x : R4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).rH =
      (waveN M.toData Y x - SHn M (Y x).2.2.1 (Y x).2.2.2.1 (Y x).2.2.2.2 : 𝓗) := by
  show ActualJetGauge.higgsRes _ _ _ _ _ _ _ _ = _
  unfold ActualJetGauge.higgsRes
  rw [waveH_toTuple hδ h x]
  rfl

include hδ h in
/-- **The native Higgs row in terms of the Higgs residual of the tuple**:
`𝓔₀(Y)(x)[(0, 0, η, 0, 0)] = 2v⟨η, r_H⟩`. -/
theorem higgs_row_toTuple (x : R4) (η : 𝓗) :
    contEuler (L0 M.toData) Y x (higgsDir η) =
      2 * volume (Y x).1 * M.hermH η ((((toTuple hδ h).jet x).res (toSMData M δ)).rH) := by
  rw [higgs_euler_row M.toData M.hermH_symm M.gLie M.rhoH_skew h.smooth h.gauge h.det_pos x η]
  have hr : M.hermH η ((((toTuple hδ h).jet x).res (toSMData M δ)).rH) =
      M.hermH η (waveN M.toData Y x - SHn M (Y x).2.2.1 (Y x).2.2.2.1 (Y x).2.2.2.2) :=
    congrArg (M.hermH η) (rH_toTuple hδ h x)
  rw [hr, map_sub, mul_sub, SH_rep]
  ring

end

end RenewalGeometry.RecordTuple
