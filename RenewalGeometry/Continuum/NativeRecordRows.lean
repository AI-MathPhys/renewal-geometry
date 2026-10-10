/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRowsEtr

/-!
# The slab residuals of a native field are algebraic images of its Euler rows

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (bridge step P2, the
identities `bosF = M_B(e)·𝓡_B`, `dirF = M_D(e)·𝓡_D` of the composition plan).

For a native field `Y` satisfying `RecordTuple.TupleHyp` (unit period, adapted Lorentz gauge,
temporal internal gauge, physical co-spinors, gauge Lie subspace, chart margin), with actual
field tuple `z = toTuple` and slab theory data `SlabData.toSMData`:

* **`bosF_toTuple`** — `bosF(z)(x) = MB(e(x)) (𝓡_B^𝔤(Y)(x))`: the trace-reversed Einstein,
  Yang–Mills and Higgs residuals of the tuple are fixed linear images of the **physical** native
  bosonic Euler covector `𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB πg` (gauge rows tested in the gauge Lie
  algebra `𝔤` only, `NativeTail.RBP`), with coefficients that are smooth functions of the coframe
  value only (`contDiffOn_MB`);
* **`dirF_toTuple`** — `dirF(z)(x) = MD(e(x)) (𝓡_D(Y)(x))` for the Dirac and dual Dirac residuals.

The extraction maps (`MBf`, `MDf`) invert the native rows: the Einstein row through the metric
directions `metricS e (symTest c d)` (`einsteinRes_sym_row`), the Yang–Mills and Higgs rows
through the Riesz maps of the invariant forms, the Dirac row through a basis of physical
(`ℂ`-linear) co-spinors (`clinCoord`), the dual Dirac row through the complex structure.
-/

open Finset
open scoped Matrix ContDiff

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect NativeStressEuler NativeTail ActualJetState ActualJetCompleteForcing

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The bosonic direction space `(δe, δA, δH)`. -/
abbrev Bos (𝔄 𝓗 : Type*) [NormedRing 𝔄] [NormedAddCommGroup 𝓗] := Mat × (Fin 4 → 𝔄) × 𝓗

/-- The Dirac direction space `(δΨ, δΨ̄)`. -/
abbrev Dir (𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] := 𝓢 × CoSpinor 𝓢

/-! ### Physical co-spinor coordinates -/

/-- The coordinate functionals of the standard basis of `𝓢`, as continuous linear maps. -/
def coordL (i : Fin (Module.finrank ℝ 𝓢)) : 𝓢 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ 𝓢).coord i)

/-- **The physical co-spinor of a real coordinate** `φ_i = ℓ_i - iℓ_i∘J` (`ℂ`-linear,
`Re φ_i = ℓ_i`). -/
def clinCoord (i : Fin (Module.finrank ℝ 𝓢)) : CoSpinor 𝓢 :=
  Complex.ofRealCLM.comp (coordL i) - Complex.I • Complex.ofRealCLM.comp ((coordL i).comp M.J)

theorem re_clinCoord (i : Fin (Module.finrank ℝ 𝓢)) (w : 𝓢) :
    (clinCoord M i w).re = (Module.finBasis ℝ 𝓢).coord i w := by
  simp [clinCoord, coordL]

theorem isCLin_clinCoord (i : Fin (Module.finrank ℝ 𝓢)) : IsCLin M.toModel (clinCoord M i) := by
  intro w
  have hJJ : M.J (M.J w) = -w := by
    rw [← ContinuousLinearMap.mul_apply, M.J_sq]; simp
  simp only [clinCoord, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, hJJ, map_neg, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  ring

/-- A spinor is determined by its real parts against the physical coordinate co-spinors. -/
theorem spinor_expand (w : 𝓢) :
    w = ∑ i, (clinCoord M i w).re • Module.finBasis ℝ 𝓢 i := by
  simp only [re_clinCoord]
  exact ((Module.finBasis ℝ 𝓢).sum_repr w).symm.trans
    (Finset.sum_congr rfl fun i _ => by rw [Module.Basis.coord_apply])

/-! ### The extraction maps -/

/-- The trace-reversed Einstein component of the bosonic extraction. -/
def EtrOf (E : Mat) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) : Met :=
  traceRev (fun a b => metric E a b) (fun a b => (metric E)⁻¹ a b)
    (lowerE E fun c d => -(M.κ / volume E) * ρ (metricS E (symTest c d) * E, 0, 0))

/-- The Yang–Mills component of the bosonic extraction. -/
def rAOf (E : Mat) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) (σ : Fin 4) : MatLie m :=
  M.φ (∑ ν, metric E σ ν • ((volume E)⁻¹ •
    rieszVec M.ipA_nondeg (fun y => ρ (0, Pi.single ν y, 0))))

/-- The Higgs component of the bosonic extraction. -/
def rHOf (E : Mat) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) : 𝓗 :=
  (2 * volume E)⁻¹ • rieszVec M.hermH_nondeg (fun η => ρ (0, 0, η))

/-- **The bosonic extraction** `MB(e)𝓡 = (𝓔^{tr}, r^A, r_H)`. -/
def MBf (E : Mat) (ρ : Bos 𝔄 𝓗 →L[ℝ] ℝ) : BosP m (HSp M) :=
  (EtrOf M E ρ, rAOf M E ρ, (rHOf M E ρ : 𝓗))

/-- The Dirac component of the Dirac extraction. -/
def rDOf (E : Mat) (ρ : Dir 𝓢 →L[ℝ] ℝ) : 𝓢 :=
  (volume E)⁻¹ • ∑ i, ρ (0, clinCoord M i) • Module.finBasis ℝ 𝓢 i

/-- The dual Dirac component of the Dirac extraction. -/
def rDbOf (E : Mat) (ρ : Dir 𝓢 →L[ℝ] ℝ) : CoSpinor 𝓢 :=
  -(volume E)⁻¹ • (Complex.ofRealCLM.comp (ρ.comp (ContinuousLinearMap.inl ℝ 𝓢 (CoSpinor 𝓢))) -
    Complex.I • Complex.ofRealCLM.comp ((ρ.comp (ContinuousLinearMap.inl ℝ 𝓢 (CoSpinor 𝓢))).comp M.J))

/-- **The Dirac extraction** `MD(e)𝓡 = (r_D, r̄_D)`. -/
def MDf (E : Mat) (ρ : Dir 𝓢 →L[ℝ] ℝ) : 𝓢 × CoSpinor 𝓢 := (rDOf M E ρ, rDbOf M E ρ)

/-! ### Riesz vectors are linear in the functional -/

theorem rieszVec_smul {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) (r : ℝ) (c : W → ℝ) :
    rieszVec hB (fun y => r * c y) = r • rieszVec hB c := by
  unfold rieszVec
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

theorem rieszVec_add {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ x, (∀ y, B y x = 0) → x = 0) (c c' : W → ℝ) :
    rieszVec hB (fun y => c y + c' y) = rieszVec hB c + rieszVec hB c' := by
  unfold rieszVec
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [add_smul]

/-! ### The pointwise identities -/

variable {M}
variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hδ : 0 < δ) (h : TupleHyp M δ Y)

theorem RB_coframe (x : R4) (k : Mat) :
    RB M.toData Y x (k, 0, 0) = contEuler (L0 M.toData) Y x (coframeDir k) := rfl

theorem RB_gauge (x : R4) (X : Fin 4 → 𝔄) :
    RB M.toData Y x (0, X, 0) = contEuler (L0 M.toData) Y x (gaugeDir X) := rfl

theorem RB_higgs (x : R4) (η : 𝓗) :
    RB M.toData Y x (0, 0, η) = contEuler (L0 M.toData) Y x (higgsDir η) := rfl

theorem RD_psiBar (x : R4) (φ : CoSpinor 𝓢) :
    RD M.toData Y x (0, φ) = contEuler (L0 M.toData) Y x (psiBarDir φ) := rfl

theorem RD_psi (x : R4) (χ : 𝓢) :
    RD M.toData Y x (χ, 0) = contEuler (L0 M.toData) Y x (psiDir χ) := rfl

theorem EtrOf_RBP (E : Mat) (x : R4) :
    EtrOf M E (RBP M.toData M.πg Y x) = EtrOf M E (RB M.toData Y x) := by
  have key : ∀ k : Mat, RBP M.toData M.πg Y x (k, 0, 0) = RB M.toData Y x (k, 0, 0) := fun k => by
    rw [RBP_apply, gaugeProjB_coframe]
  unfold EtrOf
  congr 2
  funext c d
  exact congrArg (fun t => -(M.κ / volume E) * t) (key _)

theorem rHOf_RBP (E : Mat) (x : R4) :
    rHOf M E (RBP M.toData M.πg Y x) = rHOf M E (RB M.toData Y x) := by
  have key : ∀ η : 𝓗, RBP M.toData M.πg Y x (0, 0, η) = RB M.toData Y x (0, 0, η) := fun η => by
    rw [RBP_apply, gaugeProjB_higgs]
  unfold rHOf
  congr 2
  funext η
  exact key η

include hδ h in
theorem Etr_extract (x : R4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).Etr =
      EtrOf M (Y x).1 (RBP M.toData M.πg Y x) := by
  rw [EtrOf_RBP, Etr_toTuple hδ h x]
  unfold EtrOf
  congr 1
  funext a b
  unfold lowerE
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  beta_reduce
  rw [einsteinRes_sym_row h x c d]
  rfl

include hδ h in
theorem rA_extract (x : R4) (σ : Fin 4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).rA σ =
      rAOf M (Y x).1 (RBP M.toData M.πg Y x) σ := by
  have hE := h.det_ne x
  have hv : volume (Y x).1 ≠ 0 := by
    rw [volume_of_det_pos (h.det_pos x)]; exact hE
  set r : Fin 4 → 𝔄 := fun σ => M.φ.symm ((((toTuple hδ h).jet x).res (toSMData M δ)).rA σ)
    with hr
  set w : Fin 4 → 𝔄 := fun ν => ∑ σ, ginvOf (gF (eF Y) x) ν σ • r σ with hw
  have hwmem : ∀ ν, w ν ∈ M.gSub := fun ν =>
    M.gSub.sum_mem fun σ _ => M.gSub.smul_mem _ (rA_mem hδ h x σ)
  have hrow : ∀ ν (y : 𝔄), RBP M.toData M.πg Y x (0, Pi.single ν y, 0) =
      volume (Y x).1 * M.ipA y (w ν) := by
    intro ν y
    have hX : ∀ μ, (Pi.single ν (M.πg y) : Fin 4 → 𝔄) μ ∈ M.gSub := by
      intro μ
      by_cases hμ : μ = ν
      · subst hμ; rw [Pi.single_eq_same]; exact M.πg_mem y
      · rw [Pi.single_eq_of_ne hμ]; exact M.gSub.zero_mem
    rw [RBP_apply, gaugeProjB_gauge, gaugeSlots_single, RB_gauge,
      gauge_row_toTuple hδ h x _ hX]
    congr 1
    rw [Finset.sum_eq_single ν (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
    simp only [Pi.single_eq_same]
    have e : ∑ σ, ginvOf (gF (eF Y) x) ν σ * M.ipA (M.πg y) (r σ) = M.ipA (M.πg y) (w ν) := by
      simp only [hw, map_sum, map_smul, smul_eq_mul]
    rw [e, M.ipA_πg_symm, M.πg_of_mem (hwmem ν)]
  have hwν : ∀ ν, w ν = (volume (Y x).1)⁻¹ •
      rieszVec M.ipA_nondeg (fun y => RBP M.toData M.πg Y x (0, Pi.single ν y, 0)) := by
    intro ν
    rw [← rieszVec_smul]
    refine rieszVec_eq_of M.ipA_nondeg
      ((volume (Y x).1)⁻¹ • ((RBP M.toData M.πg Y x).comp ((ContinuousLinearMap.inr ℝ Mat _).comp
        ((ContinuousLinearMap.inl ℝ (Fin 4 → 𝔄) 𝓗).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => 𝔄) ν)))).toLinearMap) (fun y => ?_)
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    have := hrow ν y
    show M.ipA y (w ν) = (volume (Y x).1)⁻¹ * RBP M.toData M.πg Y x (0, Pi.single ν y, 0)
    rw [this]
    field_simp
  have hrσ : r σ = ∑ ν, metric (Y x).1 σ ν • w ν := by
    simp only [hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have hδ' : ∀ τ, ∑ ν, metric (Y x).1 σ ν * ginvOf (gF (eF Y) x) ν τ =
        if σ = τ then 1 else 0 := fun τ => sum_metric_ginv hE σ τ
    simp only [← Finset.sum_smul, hδ', ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  unfold rAOf
  rw [← AlgEquiv.apply_symm_apply M.φ ((((toTuple hδ h).jet x).res (toSMData M δ)).rA σ)]
  congr 1
  rw [show M.φ.symm ((((toTuple hδ h).jet x).res (toSMData M δ)).rA σ) = r σ from rfl, hrσ]
  exact Finset.sum_congr rfl fun ν _ => by rw [hwν ν]; rfl

include hδ h in
theorem rH_extract (x : R4) :
    ((((toTuple hδ h).jet x).res (toSMData M δ)).rH : 𝓗) =
      rHOf M (Y x).1 (RBP M.toData M.πg Y x) := by
  rw [rHOf_RBP]
  have hE := h.det_ne x
  have hv : volume (Y x).1 ≠ 0 := by
    rw [volume_of_det_pos (h.det_pos x)]; exact hE
  unfold rHOf
  rw [← rieszVec_smul]
  refine rieszVec_eq_of M.hermH_nondeg
    ((2 * volume (Y x).1)⁻¹ • ((RB M.toData Y x).comp ((ContinuousLinearMap.inr ℝ Mat _).comp
      (ContinuousLinearMap.inr ℝ (Fin 4 → 𝔄) 𝓗))).toLinearMap) (fun η => ?_)
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, smul_eq_mul]
  show M.hermH η _ = (2 * volume (Y x).1)⁻¹ * RB M.toData Y x (0, 0, η)
  rw [RB_higgs, higgs_row_toTuple hδ h x]
  field_simp

/-- **The bosonic slab residual of the tuple is the bosonic extraction of the physical native
row**: `bosF(z)(x) = MB(e(x)) 𝓡_B^𝔤(Y)(x)`, `𝓡_B^𝔤 = 𝓡_B ∘ gaugeProjB πg` (gauge rows in `𝔤`). -/
theorem bosF_toTuple (x : R4) :
    bosF (toSMData M δ) (toTuple hδ h) x = MBf M (Y x).1 (RBP M.toData M.πg Y x) := by
  unfold bosF MBf
  refine Prod.ext (Etr_extract hδ h x) (Prod.ext (funext fun σ => rA_extract hδ h x σ) ?_)
  exact rH_extract hδ h x

include hδ h in
theorem rD_extract (x : R4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).rD = rDOf M (Y x).1 (RD M.toData Y x) := by
  have hE := h.det_ne x
  have hv : volume (Y x).1 ≠ 0 := by
    rw [volume_of_det_pos (h.det_pos x)]; exact hE
  show ((toTuple hδ h).jet x).rD (diracD M) _ _ = _
  rw [rD_toTuple hδ h x]
  unfold rDOf
  conv_lhs => rw [spinor_expand M (diracRes M.toModel Y x)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, RD_psiBar, psibar_row_model M.toModel h.smooth h.det_pos x
    (isCLin_clinCoord M i)]
  congr 1
  field_simp

include hδ h in
theorem rDb_extract (x : R4) :
    (((toTuple hδ h).jet x).res (toSMData M δ)).rDb = rDbOf M (Y x).1 (RD M.toData Y x) := by
  have hE := h.det_ne x
  have hv : volume (Y x).1 ≠ 0 := by
    rw [volume_of_det_pos (h.det_pos x)]; exact hE
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  show ((toTuple hδ h).jet x).rD (diracDb M) _ _ = _
  rw [rDb_toTuple hδ h x]
  have hC := isCLin_diracResBar M.toModel hYd h.clin x
  ext χ
  have h1 := psi_row_model M.toModel h.smooth h.det_pos h.clin x χ
  have h2 := psi_row_model M.toModel h.smooth h.det_pos h.clin x (M.J χ)
  rw [← RD_psi] at h1 h2
  have h3 := hC χ
  unfold rDbOf
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.inl_apply,
    Complex.real_smul]
  rw [h1, h2, h3]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.neg_re, Complex.neg_im]
    field_simp
    simp
  · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.sub_im, Complex.neg_re, Complex.neg_im]
    field_simp
    simp [mul_comm]

/-- **The Dirac slab residual of the tuple is the Dirac extraction of the native row**:
`dirF(z)(x) = MD(e(x)) 𝓡_D(Y)(x)`. -/
theorem dirF_toTuple (x : R4) :
    dirF (toSMData M δ) (toTuple hδ h) x = MDf M (Y x).1 (RD M.toData Y x) := by
  unfold dirF MDf
  exact Prod.ext (rD_extract hδ h x) (rDb_extract hδ h x)

end

end RenewalGeometry.RecordTuple
