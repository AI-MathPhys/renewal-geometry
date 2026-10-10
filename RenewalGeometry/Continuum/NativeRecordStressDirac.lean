/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRowsEinstein

/-!
# The Dirac stress of the actual tuple of a native field

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`, bridge step P2
(Dirac stress in the Einstein row).  The slab theory data `SlabData.toSMData` carry the Dirac
stress in the frame form `SlabData.TD` (`T_{AB} = Σ_C(P_{ABC}(Ψ̄, X_C) - P_{ABC}(X̄_C, Ψ)) +
P''_{AB}(H)(Ψ̄, Ψ)`).  For a native field satisfying `RecordTuple.TupleHyp`:

* `Xs_D_toTuple`, `Xs_Db_toTuple` — the slab spinor jets are the native frame jets
  `X_A = e_A{}^γ∇_γΨ`, `X̄_A = e_A{}^γ∇_γΨ̄`;
* `cof_toTuple` — the slab coframe is the native coframe `θ^A{}_μ = e^A{}_μ`;
* `frame_TD` (generic) — the frame stress is the symmetrisation of
  `η_{AB}ℓ - η_{BB}Re((i/2)[Ψ̄γ^BX_A - X̄_Aγ^BΨ])`;
* **`coordTD_toTuple`** — the coordinate Dirac stress of the tuple is the lowered symmetric part
  of the native Dirac stress `NativeStressEuler.diracStressUp`.
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

/-! ### The frame form of the slab Dirac stress (generic) -/

/-- The unsymmetrised frame Dirac stress
`η_{AB}(Re((i/2)Σ_C[Ψ̄γ^CX_C - X̄_Cγ^CΨ]) - Re Ψ̄𝓜Ψ) - η_{BB}Re((i/2)[Ψ̄γ^BX_A - X̄_Aγ^BΨ])`. -/
def Tu (M : SlabModel 𝔄 𝓗 𝓢 m) (H : 𝓗) (ψ : 𝓢) (X : Fin 4 → 𝓢) (ψb : CoSpinor 𝓢)
    (Xb : Fin 4 → CoSpinor 𝓢) (A B : Fin 4) : ℝ :=
  eta A B * ((Complex.I / 2 * ∑ C, (ψb (M.γ C (X C)) - Xb C (M.γ C ψ))).re -
      (ψb (M.yukawa H ψ)).re) -
    eta B B * (Complex.I / 2 * (ψb (M.γ B (X A)) - Xb A (M.γ B ψ))).re

theorem sum_Pu_left (A B : Fin 4) (φ : CoSpinor 𝓢) (X : Fin 4 → 𝓢) :
    ∑ C, Pu M A B C φ (X C) = eta A B * (Complex.I / 2 * ∑ C, φ (M.γ C (X C))).re -
      eta B B * (Complex.I / 2 * φ (M.γ B (X A))).re := by
  unfold Pu
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum,
    Complex.re_sum]

theorem sum_Pu_right (A B : Fin 4) (Xb : Fin 4 → CoSpinor 𝓢) (ψ : 𝓢) :
    ∑ C, Pu M A B C (Xb C) ψ = eta A B * (Complex.I / 2 * ∑ C, Xb C (M.γ C ψ)).re -
      eta B B * (Complex.I / 2 * Xb A (M.γ B ψ)).re := by
  unfold Pu
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum,
    Complex.re_sum]

/-- **The frame Dirac stress of the slab data is the symmetrised native frame stress.** -/
theorem frame_TD (H : HSp M) (ψ : 𝓢) (X : Fin 4 → 𝓢) (ψb : CoSpinor 𝓢)
    (Xb : Fin 4 → CoSpinor 𝓢) (A B : Fin 4) :
    (TD M).frame H ψ X ψb Xb A B =
      (1 / 2 : ℝ) * (Tu M H ψ X ψb Xb A B + Tu M H ψ X ψb Xb B A) := by
  unfold ActualJetRecon.DiracStressForm.frame TD
  simp only [LinearMap.neg_apply, Ps_apply, Pyuk_apply, Finset.sum_add_distrib]
  rw [show ∑ C, (1 / 2 : ℝ) * (Pu M A B C ψb (X C) + Pu M B A C ψb (X C)) =
      (1 / 2 : ℝ) * (∑ C, Pu M A B C ψb (X C) + ∑ C, Pu M B A C ψb (X C)) by
    rw [← Finset.sum_add_distrib, Finset.mul_sum],
    show ∑ C, -((1 / 2 : ℝ) * (Pu M A B C (Xb C) ψ + Pu M B A C (Xb C) ψ)) =
      -((1 / 2 : ℝ) * (∑ C, Pu M A B C (Xb C) ψ + ∑ C, Pu M B A C (Xb C) ψ)) by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib]]
  rw [sum_Pu_left, sum_Pu_left, sum_Pu_right, sum_Pu_right]
  unfold Tu
  have hη : eta B A = eta A B := PalatiniEuler.eta_symm B A
  rw [hη]
  simp only [Finset.mul_sum, Complex.re_sum, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
  ring

/-! ### The slab jets of the tuple -/

variable {δ : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hδ : 0 < δ) (h : TupleHyp M δ Y)

/-- The native frame spinor jets `X_A = e_A{}^γ∇_γΨ`. -/
def Xn (M : SlabModel 𝔄 𝓗 𝓢 m) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) (A : Fin 4) : 𝓢 :=
  ∑ γ, ((Y x).1)⁻¹ γ A • DPsi M.toData (jet1 Y x) γ

/-- The native frame co-spinor jets `X̄_A = e_A{}^γ∇_γΨ̄`. -/
def Xbn (M : SlabModel 𝔄 𝓗 𝓢 m) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) (A : Fin 4) : CoSpinor 𝓢 :=
  ∑ γ, ((Y x).1)⁻¹ γ A • DPsiBar M.toData (jet1 Y x) γ

include hδ h in
theorem Xs_D_toTuple (x : R4) (A : Fin 4) :
    ((toTuple hδ h).jet x).Xs (diracD M) ((toTuple hδ h).jet x).ψ ((toTuple hδ h).jet x).cψ A =
      Xn M Y x A := by
  set J := (toTuple hδ h).jet x
  have hYd : Differentiable ℝ Y := h.smooth.differentiable (by simp)
  have hq : (fun l => ((jet1 Y x).2 l).1) = qJ Y x := by
    funext l
    exact (pd_clm (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))
      (hYd x) l).symm
  unfold ActualJet.Xs
  have hω : (J.LJ (diracD M)).ω =
      fun B => toEndAlg (slabOmega M.toModel (Y x).1 (qJ Y x) (Y x).2.1 B) :=
    funext fun B => omega_D_toTuple hδ h x B
  have hdψ : ActualJetSpinor.dψf J.FJ J.cψ =
      fun B => ∑ γ, ((Y x).1)⁻¹ γ B • ((jet1 Y x).2 γ).2.2.2.1 := by
    funext B
    unfold ActualJetSpinor.dψf
    refine Finset.sum_congr rfl fun γ _ => ?_
    have h1 : J.FJ.e B γ = ((Y x).1)⁻¹ γ B := e_toTuple hδ h x B γ
    have h2 : J.cψ γ = ((jet1 Y x).2 γ).2.2.2.1 :=
      pd_clm (projψ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hYd x) γ
    rw [h1, h2]
  rw [hω, hdψ]
  have hs := slab_cov_eq M.toModel (h.det_ne x) (qJ Y x) (Y x).2.1 (Y x).2.2.2.1
    (fun γ => ((jet1 Y x).2 γ).2.2.2.1) A
  refine Eq.trans ?_ (hs.trans ?_)
  · unfold cov
    rfl
  · unfold Xn DPsi omC
    rw [hq]
    rfl

include hδ h in
theorem Xs_Db_toTuple (x : R4) (A : Fin 4) :
    ((toTuple hδ h).jet x).Xs (diracDb M) ((toTuple hδ h).jet x).ψb ((toTuple hδ h).jet x).cψb A =
      Xbn M Y x A :=
  cov_Db_toTuple hδ h x A

include hδ h in
/-- The slab coframe of the tuple is the native coframe: `θ^A{}_μ = e^A{}_μ`. -/
theorem cof_toTuple (x : R4) (A μ : Fin 4) :
    ActualJetRecon.cof ((toTuple hδ h).jet x).FJ.g lorentzSign ((toTuple hδ h).jet x).AF.fr A μ =
      (Y x).1 A μ := by
  set E := (Y x).1
  have hE := h.det_ne x
  have he : ((toTuple hδ h).jet x).AF.fr = fun A μ => E⁻¹ μ A := by
    rw [← ((toTuple hδ h).jet x).e_eq]
    funext A μ
    exact e_toTuple hδ h x A μ
  rw [he]
  unfold ActualJetRecon.cof
  have hm : metric E * E⁻¹ = Eᵀ * eta := by
    unfold metric
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv E hE.isUnit, Matrix.mul_one]
  have h1 := congrFun (congrFun hm μ) A
  rw [Matrix.mul_apply] at h1
  show lorentzSign A * ∑ ν, metric E μ ν * E⁻¹ ν A = E A μ
  rw [h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eta, Matrix.diagonal_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases A <;> simp [lorentzSign]

include h in
/-- `∇_μΨ = Σ_A e^A{}_μ X_A`. -/
theorem DPsi_inv (x : R4) (μ : Fin 4) :
    ∑ A, (Y x).1 A μ • Xn M Y x A = DPsi M.toData (jet1 Y x) μ := by
  have hE := h.det_ne x
  unfold Xn
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hδ' : ∀ γ, ∑ A, (Y x).1 A μ * ((Y x).1)⁻¹ γ A = if γ = μ then 1 else 0 := by
    intro γ
    have := congrFun (congrFun (Matrix.nonsing_inv_mul (Y x).1 hE.isUnit) γ) μ
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun A _ => mul_comm _ _
  simp only [← Finset.sum_smul, hδ', ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

include h in
/-- `∇_μΨ̄ = Σ_A e^A{}_μ X̄_A`. -/
theorem DPsiBar_inv (x : R4) (μ : Fin 4) :
    ∑ A, (Y x).1 A μ • Xbn M Y x A = DPsiBar M.toData (jet1 Y x) μ := by
  have hE := h.det_ne x
  unfold Xbn
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hδ' : ∀ γ, ∑ A, (Y x).1 A μ * ((Y x).1)⁻¹ γ A = if γ = μ then 1 else 0 := by
    intro γ
    have := congrFun (congrFun (Matrix.nonsing_inv_mul (Y x).1 hE.isUnit) γ) μ
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun A _ => mul_comm _ _
  simp only [← Finset.sum_smul, hδ', ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-! ### The lowered native Dirac stress in frame form -/

/-- `g_{ab} = Σ_{AB} e^A{}_a e^B{}_b η_{AB}`. -/
theorem metric_frame (E : Mat) (a b : Fin 4) :
    metric E a b = ∑ A, ∑ B, E A a * E B b * eta A B := by
  unfold metric
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
  ring

/-- `g_{bd}γ^d(e) = Σ_B e^B{}_b η_{BB} γ^B`. -/
theorem sum_metric_gammaMu {E : Mat} (hE : E.det ≠ 0) (b : Fin 4) :
    ∑ d, metric E b d • gammaMu M.toData d E = ∑ B, (E B b * eta B B) • M.γ B := by
  have hm : metric E * E⁻¹ = Eᵀ * eta := by
    unfold metric
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv E hE.isUnit, Matrix.mul_one]
  simp only [gammaMu_eq, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h1 := congrFun (congrFun hm b) B
  rw [Matrix.mul_apply] at h1
  rw [h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eta, Matrix.diagonal_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include h in
/-- `Σ_μ γ^μ(e)∇_μΨ = Σ_C γ^C X_C`. -/
theorem sum_gammaMu_DPsi (x : R4) :
    ∑ μ, gammaMu M.toData μ (Y x).1 (DPsi M.toData (jet1 Y x) μ) = ∑ C, M.γ C (Xn M Y x C) := by
  unfold Xn
  simp only [gammaMu_eq, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_comm

include h in
/-- `Σ_μ (∇_μΨ̄)γ^μ(e)Ψ = Σ_C X̄_C γ^CΨ`. -/
theorem sum_DPsiBar_gammaMu (x : R4) :
    ∑ μ, DPsiBar M.toData (jet1 Y x) μ (gammaMu M.toData μ (Y x).1 (Y x).2.2.2.1) =
      ∑ C, Xbn M Y x C (M.γ C (Y x).2.2.2.1) := by
  unfold Xbn
  simp only [gammaMu_eq, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.sum_comm]

include h in
/-- The native Dirac Lagrangian in frame form. -/
theorem diracLag_frame (x : R4) :
    diracLag M.toData (jet1 Y x) =
      (Complex.I / 2 * ∑ C, ((Y x).2.2.2.2 (M.γ C (Xn M Y x C)) -
          Xbn M Y x C (M.γ C (Y x).2.2.2.1))).re - ((Y x).2.2.2.2 (M.yukawa (Y x).2.2.1
            (Y x).2.2.2.1)).re := by
  unfold diracLag
  rw [Complex.sub_re]
  congr 2
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, show (jet1 Y x).1 = Y x from rfl, ← map_sum,
    sum_gammaMu_DPsi h x, sum_DPsiBar_gammaMu h x, map_sum]

include h in
/-- `g_{ac}g_{bd}T_D^{cd} = g_{ab}ℓ_D - g_{bd}Θ_a{}^d`. -/
theorem lowerE_dsU_aux (x : R4) (a b : Fin 4) :
    lowerE (Y x).1 (diracStressUp M.toData (jet1 Y x)) a b =
      metric (Y x).1 a b * diracLag M.toData (jet1 Y x) -
        ∑ d, metric (Y x).1 b d * thetaN M.toData (jet1 Y x) a d := by
  have hE := h.det_ne x
  set E := (Y x).1
  have hδ := sum_metric_ginv hE
  have hj : (jet1 Y x).1.1 = E := rfl
  unfold lowerE diracStressUp
  rw [hj]
  have h1 : ∑ c, ∑ d, metric E a c * metric E b d * ginv E c d = metric E a b := by
    calc ∑ c, ∑ d, metric E a c * metric E b d * ginv E c d
        = ∑ c, metric E a c * ∑ d, metric E b d * ginv E d c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [ginv_symm E c d]; ring
      _ = metric E a b := by simp [hδ, PalatiniEuler.metric_symm E a b]
  have h2 : ∑ c, ∑ d, metric E a c * metric E b d *
      ∑ μ, ginv E c μ * thetaN M.toData (jet1 Y x) μ d =
      ∑ d, metric E b d * thetaN M.toData (jet1 Y x) a d := by
    calc ∑ c, ∑ d, metric E a c * metric E b d *
          ∑ μ, ginv E c μ * thetaN M.toData (jet1 Y x) μ d
        = ∑ d, metric E b d * ∑ μ, (∑ c, metric E a c * ginv E c μ) *
            thetaN M.toData (jet1 Y x) μ d := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun c _ => ?_
          ring
      _ = _ := by simp [hδ]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← h2, ← h1, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- A double-sum identity for the real parts of complex bilinear expressions. -/
theorem re_double_sum (c d : Fin 4 → ℝ) (P Q : Fin 4 → Fin 4 → ℂ) :
    (Complex.I / 2 * (∑ A, (d A : ℂ) * ∑ B, (c B : ℂ) * P B A -
      ∑ B, (c B : ℂ) * ∑ A, (d A : ℂ) * Q A B)).re =
      ∑ A, ∑ B, d A * c B * (Complex.I / 2 * (P B A - Q A B)).re := by
  have h : Complex.I / 2 * (∑ A, (d A : ℂ) * ∑ B, (c B : ℂ) * P B A -
      ∑ B, (c B : ℂ) * ∑ A, (d A : ℂ) * Q A B) =
      ∑ A, ∑ B, ((d A * c B : ℝ) : ℂ) * (Complex.I / 2 * (P B A - Q A B)) := by
    simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun B A => Complex.I / 2 * ((c B : ℂ) * ((d A : ℂ) * Q A B)))]
    congr 1
    · refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      push_cast; ring
    · refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      push_cast; ring
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Complex.re_ofReal_mul]

include h in
/-- `g_{bd}Θ_a{}^d = Σ_{AB} e^A{}_a e^B{}_b η_{BB} Re((i/2)[Ψ̄γ^BX_A - X̄_Aγ^BΨ])`. -/
theorem sum_g_theta (x : R4) (a b : Fin 4) :
    ∑ d, metric (Y x).1 b d * thetaN M.toData (jet1 Y x) a d =
      ∑ A, ∑ B, (Y x).1 A a * (Y x).1 B b * (eta B B * (Complex.I / 2 *
        ((Y x).2.2.2.2 (M.γ B (Xn M Y x A)) - Xbn M Y x A (M.γ B (Y x).2.2.2.1))).re) := by
  have hE := h.det_ne x
  set E := (Y x).1
  set ψ := (Y x).2.2.2.1
  set ψb := (Y x).2.2.2.2
  have hj : (jet1 Y x).1.1 = E := rfl
  have hψ : (jet1 Y x).1.2.2.2.1 = ψ := rfl
  have hψb : (jet1 Y x).1.2.2.2.2 = ψb := rfl
  have h1 : ∀ d, metric E b d * thetaN M.toData (jet1 Y x) a d =
      (((metric E b d : ℝ) : ℂ) * (Complex.I / 2 *
        (ψb (gammaMu M.toData d E (DPsi M.toData (jet1 Y x) a)) -
          DPsiBar M.toData (jet1 Y x) a (gammaMu M.toData d E ψ)))).re := by
    intro d
    unfold thetaN
    rw [hj, hψ, hψb, Complex.re_ofReal_mul]
  simp only [h1, ← Complex.re_sum]
  have h2 : ∑ d, ((metric E b d : ℝ) : ℂ) * (Complex.I / 2 *
        (ψb (gammaMu M.toData d E (DPsi M.toData (jet1 Y x) a)) -
          DPsiBar M.toData (jet1 Y x) a (gammaMu M.toData d E ψ))) =
      Complex.I / 2 * (ψb ((∑ d, metric E b d • gammaMu M.toData d E)
          (DPsi M.toData (jet1 Y x) a)) -
        DPsiBar M.toData (jet1 Y x) a ((∑ d, metric E b d • gammaMu M.toData d E) ψ)) := by
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, Complex.real_smul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [h2, sum_metric_gammaMu hE b, ← DPsi_inv h x a, ← DPsiBar_inv h x a]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_sum, map_smul, Complex.real_smul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  convert re_double_sum (fun B => E B b * eta B B) (fun A => E A a)
    (fun B A => ψb (M.γ B (Xn M Y x A))) (fun A B => Xbn M Y x A (M.γ B ψ)) using 1
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  ring

include h in
/-- **The lowered native Dirac stress in frame form**:
`g_{ac}g_{bd}T_D^{cd} = Σ_{AB} e^A{}_a e^B{}_b T_{AB}` with `T_{AB} = Tu`. -/
theorem lowerE_dsU_frame (x : R4) (a b : Fin 4) :
    lowerE (Y x).1 (diracStressUp M.toData (jet1 Y x)) a b =
      ∑ A, ∑ B, (Y x).1 A a * (Y x).1 B b *
        Tu M (Y x).2.2.1 (Y x).2.2.2.1 (Xn M Y x) (Y x).2.2.2.2 (Xbn M Y x) A B := by
  rw [lowerE_dsU_aux h x a b, sum_g_theta h x a b, metric_frame, diracLag_frame h x,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold Tu
  ring

include hδ h in
/-- **The coordinate Dirac stress of the tuple is the lowered symmetric native Dirac stress.** -/
theorem coordTD_toTuple (x : R4) (a b : Fin 4) :
    (TD M).coord ((toTuple hδ h).jet x).FJ.g lorentzSign ((toTuple hδ h).jet x).AF.fr
        ((toTuple hδ h).jet x).H ((toTuple hδ h).jet x).ψ
        (((toTuple hδ h).jet x).Xs (diracD M) ((toTuple hδ h).jet x).ψ ((toTuple hδ h).jet x).cψ)
        ((toTuple hδ h).jet x).ψb
        (((toTuple hδ h).jet x).Xs (diracDb M) ((toTuple hδ h).jet x).ψb
          ((toTuple hδ h).jet x).cψb) a b =
      lowerE (Y x).1 (fun c d => (1 / 2 : ℝ) * (diracStressUp M.toData (jet1 Y x) c d +
        diracStressUp M.toData (jet1 Y x) d c)) a b := by
  have hX : ((toTuple hδ h).jet x).Xs (diracD M) ((toTuple hδ h).jet x).ψ
      ((toTuple hδ h).jet x).cψ = Xn M Y x := funext fun A => Xs_D_toTuple hδ h x A
  have hXb : ((toTuple hδ h).jet x).Xs (diracDb M) ((toTuple hδ h).jet x).ψb
      ((toTuple hδ h).jet x).cψb = Xbn M Y x := funext fun A => Xs_Db_toTuple hδ h x A
  rw [hX, hXb, lowerE_smul, lowerE_add,
    lowerE_symm (Y x).1 (diracStressUp M.toData (jet1 Y x)), lowerE_dsU_frame h x a b,
    lowerE_dsU_frame h x b a]
  unfold ActualJetRecon.DiracStressForm.coord
  simp only [cof_toTuple hδ h x, frame_TD]
  have hw : ∑ A, ∑ B, (Y x).1 A b * (Y x).1 B a *
      Tu M (Y x).2.2.1 (Y x).2.2.2.1 (Xn M Y x) (Y x).2.2.2.2 (Xbn M Y x) A B =
      ∑ A, ∑ B, (Y x).1 A a * (Y x).1 B b *
        Tu M (Y x).2.2.1 (Y x).2.2.2.1 (Xn M Y x) (Y x).2.2.2.2 (Xbn M Y x) B A := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => by ring
  rw [hw, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  show (Y x).1 A a * (Y x).1 B b *
      (1 / 2 * (Tu M (Y x).2.2.1 (Y x).2.2.2.1 (Xn M Y x) (Y x).2.2.2.2 (Xbn M Y x) A B +
        Tu M (Y x).2.2.1 (Y x).2.2.2.1 (Xn M Y x) (Y x).2.2.2.2 (Xbn M Y x) B A)) = _
  ring

end

end RenewalGeometry.RecordTuple
