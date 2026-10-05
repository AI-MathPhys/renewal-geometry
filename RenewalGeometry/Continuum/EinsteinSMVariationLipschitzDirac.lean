/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationLipschitzMatter

/-!
# First-variation Lipschitz estimates: the Dirac–Yukawa sector
  (`prop:variation-continuity`, Einstein–Standard-Model action-closure manuscript)

`dirac_lipschitz`: on uniformly bounded strong-packet jet fields and banks in a set `P` on which
the Yukawa map is bounded and Lipschitz (`YukawaLipOn`),
`‖diracCov_{θ₁}(R₁) - diracCov_{θ₂}(R₂)‖_{L¹(Q)} ≤ C (d(R₁,R₂) + |θ₁-θ₂|)`.  The covector is split
into the strong bilinear part (`strongCoeff1`, potential variable × spinor pair), the strong
trilinear part (`strongCoeff2`, potential variable × `Ψ̄` × `Ψ`) and the weak part, written as a
bilinear coefficient `weakDirac e` in `(1, Ψ̄, Ψ)` and the spinor gradients.

`YukawaLipOn`: the paper's Yukawa matrices are bank coordinates and `𝓜_Y` is linear in them; the
abstract `FermionCarrier` only provides `θ ↦ 𝓜_{Y,θ}` (`YukawaContinuous` is continuity), so the
Lipschitz dependence on the bank on `P` is a hypothesis (disclosed scoping; satisfied by the
trivial carrier, `yukawaLipOn_trivial`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace VarLip

/-! ### The weak coefficient as a bilinear coefficient field -/

section WeakDirac

variable {C : Type} [Fintype C]

/-- `M ↦ (W ↦ M(·, W) ∘ πτ)`. -/
def weakPost : (TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ) →L[ℝ] (GradVal C →L[ℝ] RJet C →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (GradVal C) (TestVal C →L[ℝ] ℝ) (RJet C →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ (RJet C) (TestVal C) ℝ).flip (πτ (C := C)))).comp
    (ContinuousLinearMap.flipₗᵢ ℝ (TestVal C) (GradVal C) ℝ).toContinuousLinearMap

/-- The weak Dirac coefficient `(s, U) ↦ W ↦ [T ↦ weakCoeff e (s, U) (πτ T) W]`. -/
def weakDirac (e : CoframeFibre) :
    (ℝ × (SpinorFibre C × SpinorFibre C)) →L[ℝ] GradVal C →L[ℝ] RJet C →L[ℝ] ℝ :=
  (weakPost (C := C)).comp (weakCoeff e)

theorem weakDirac_apply (e : CoframeFibre) (sU : ℝ × (SpinorFibre C × SpinorFibre C))
    (W : GradVal C) : weakDirac e sU W = ((weakCoeff e sU).flip W).comp (πτ (C := C)) := rfl

theorem contDiffOn_weakDirac {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (weakDirac (C := C)) coframeGL :=
  show ContDiffOn ℝ n (fun e => (ContinuousLinearMap.compL ℝ (ℝ × (SpinorFibre C × SpinorFibre C))
      (TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ) (GradVal C →L[ℝ] RJet C →L[ℝ] ℝ) (weakPost (C := C)))
      (weakCoeff e)) coframeGL from
  (CovSmooth.contDiffOn_weakCoeff (C := C) (n := n)).continuousLinearMap_comp
    (ContinuousLinearMap.compL ℝ (ℝ × (SpinorFibre C × SpinorFibre C))
      (TestVal C →L[ℝ] GradVal C →L[ℝ] ℝ) (GradVal C →L[ℝ] RJet C →L[ℝ] ℝ) (weakPost (C := C)))

end WeakDirac

/-! ### Yukawa hypothesis and pointwise bounds -/

section YukawaSec

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- **Bounded Lipschitz Yukawa map on a bank set `P`**: `‖𝓜^{lin}_{Y,θ}‖, ‖𝓜_{Y,θ}(0)‖ ≤ M_y` and
both are `L_y`-Lipschitz in the bank coordinates. -/
structure YukawaLipOn (P : Set (CoefficientBank Ysec)) (Ly My : ℝ) : Prop where
  nonneg_L : 0 ≤ Ly
  nonneg_M : 0 ≤ My
  bound_lin : ∀ θ ∈ P, ‖yukL FC θ‖ ≤ My
  bound_zero : ∀ θ ∈ P, ‖FC.yukawa θ 0‖ ≤ My
  lip_lin : ∀ θ₁ ∈ P, ∀ θ₂ ∈ P,
    ENNReal.ofReal ‖yukL FC θ₁ - yukL FC θ₂‖ ≤ ENNReal.ofReal Ly * bankDist θ₁ θ₂
  lip_zero : ∀ θ₁ ∈ P, ∀ θ₂ ∈ P,
    ENNReal.ofReal ‖FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0‖ ≤ ENNReal.ofReal Ly * bankDist θ₁ θ₂

theorem norm_prod_le_add' {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (p : E × F) : ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

theorem norm_tuple_le {E₁ E₂ E₃ E₄ E₅ : Type*} [SeminormedAddCommGroup E₁]
    [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃] [SeminormedAddCommGroup E₄]
    [SeminormedAddCommGroup E₅] (a : E₁) (b : E₂) (c : E₃) (d : E₄) (L : E₅) :
    ‖((a, b, c, d), L)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖L‖ := by
  have h1 := norm_prod_le_add' ((a, b, c, d), L)
  have h2 := norm_prod_le_add' (a, b, c, d)
  have h3 := norm_prod_le_add' (b, c, d)
  have h4 := norm_prod_le_add' (c, d)
  simp only at h1 h2 h3 h4
  linarith

theorem norm_potVar'_le (θ : CoefficientBank Ysec) (R : RJet FC.C) :
    ‖potVar' FC θ R‖ ≤ ‖R.de‖ + ‖R.A‖ + ‖yukL FC θ‖ * ‖R.H‖ +
      (‖FC.yukawa θ 0‖ + 1 + ‖yukL FC θ‖) := by
  have e : potVar' FC θ R = ((R.de, R.A, FC.yukawa θ R.H, (1 : ℝ)), yukL FC θ) := rfl
  have hy : ‖FC.yukawa θ R.H‖ ≤ ‖yukL FC θ‖ * ‖R.H‖ + ‖FC.yukawa θ 0‖ := by
    rw [yukawa_eq FC θ R.H]
    exact (norm_add_le _ _).trans (add_le_add ((yukL FC θ).le_opNorm _) le_rfl)
  have h := norm_tuple_le R.de R.A (FC.yukawa θ R.H) (1 : ℝ) (yukL FC θ)
  rw [norm_one] at h
  rw [e]
  linarith

theorem norm_potVar'_sub_le (θ₁ θ₂ : CoefficientBank Ysec) (R₁ R₂ : RJet FC.C) :
    ‖potVar' FC θ₁ R₁ - potVar' FC θ₂ R₂‖ ≤ ‖R₁.de - R₂.de‖ + ‖R₁.A - R₂.A‖ +
      ‖yukL FC θ₁‖ * ‖R₁.H - R₂.H‖ + ‖yukL FC θ₁ - yukL FC θ₂‖ * ‖R₂.H‖ +
      ‖FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0‖ + ‖yukL FC θ₁ - yukL FC θ₂‖ := by
  have e : potVar' FC θ₁ R₁ - potVar' FC θ₂ R₂ = ((R₁.de - R₂.de, R₁.A - R₂.A,
      FC.yukawa θ₁ R₁.H - FC.yukawa θ₂ R₂.H, (1 : ℝ) - 1), yukL FC θ₁ - yukL FC θ₂) := rfl
  have hy : ‖FC.yukawa θ₁ R₁.H - FC.yukawa θ₂ R₂.H‖ ≤ ‖yukL FC θ₁‖ * ‖R₁.H - R₂.H‖ +
      ‖yukL FC θ₁ - yukL FC θ₂‖ * ‖R₂.H‖ + ‖FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0‖ := by
    rw [yukawa_eq FC θ₁ R₁.H, yukawa_eq FC θ₂ R₂.H]
    have e : yukL FC θ₁ R₁.H + FC.yukawa θ₁ 0 - (yukL FC θ₂ R₂.H + FC.yukawa θ₂ 0) =
        yukL FC θ₁ (R₁.H - R₂.H) + (yukL FC θ₁ - yukL FC θ₂) R₂.H +
          (FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((yukL FC θ₁).le_opNorm _) ((yukL FC θ₁ - yukL FC θ₂).le_opNorm _))) le_rfl)
  have h := norm_tuple_le (R₁.de - R₂.de) (R₁.A - R₂.A)
    (FC.yukawa θ₁ R₁.H - FC.yukawa θ₂ R₂.H) ((1 : ℝ) - 1) (yukL FC θ₁ - yukL FC θ₂)
  rw [e]
  refine h.trans ?_
  rw [sub_self, norm_zero]
  linarith

theorem continuous_potVar' (θ : CoefficientBank Ysec) : Continuous (potVar' FC θ) := by
  have : potVar' FC θ =
      fun R => (potVarL FC θ R + ((0, 0, FC.yukawa θ 0, 1) : PotVar FC), yukL FC θ) := by
    funext R; simp only [potVar', potVar_eq]
  rw [this]
  exact ((potVarL FC θ).continuous.add continuous_const).prodMk continuous_const

theorem diracCov_eq_parts (θ : CoefficientBank Ysec) (R : RJet FC.C) :
    diracCov FC θ R = strongCoeff1 FC R.e (potVar' FC θ R) (pU FC R) +
      strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ + weakDirac R.e ((1 : ℝ), pU FC R) (pW FC R) :=
  rfl

end YukawaSec

/-! ### Packet bounds of the Dirac fields -/

section DiracPackets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem eLpNorm_le_pt2 {E : Type*} [NormedAddCommGroup E] {f : X → E} {u v : X → ℝ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h : ∀ x, ‖f x‖ ≤ u x + v x) : eLpNorm f p μ ≤ eLpNorm u p μ + eLpNorm v p μ :=
  (eLpNorm_mono_real h).trans (eLpNorm_add_le hu hv hp)

theorem eLpNorm_norm_le {E : Type*} [NormedAddCommGroup E] {f : X → E} {p : ℝ≥0∞} {b : ℝ≥0∞}
    (h : eLpNorm f p μ ≤ b) : eLpNorm (fun x => ‖f x‖) p μ ≤ b := by
  rwa [eLpNorm_norm]

theorem eLpNorm_cmul_norm_le {E : Type*} [NormedAddCommGroup E] {f : X → E} {c : ℝ} (hc : 0 ≤ c)
    {b : ℝ≥0∞} (h : eLpNorm f 2 μ ≤ b) :
    eLpNorm (fun x => c * ‖f x‖) 2 μ ≤ ENNReal.ofReal c * b := by
  refine (eLpNorm_const_mul_le c).trans ?_
  rw [abs_of_nonneg hc, eLpNorm_norm]
  gcongr

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec} {Q : ChartBox T}
  {Ke : Set CoframeFibre} {B : ℝ≥0∞} {R R₁ R₂ : E4 → RJet FC.C}

theorem JetBound.aesm_potVar' (h : JetBound Q Ke B R) (θ : CoefficientBank Ysec) :
    AEStronglyMeasurable (fun x => potVar' FC θ (R x)) Q.μ :=
  (continuous_potVar' FC θ).comp_aestronglyMeasurable h.meas

theorem JetBound.aesm_pU (h : JetBound Q Ke B R) :
    AEStronglyMeasurable (fun x => pU FC (R x)) Q.μ :=
  (pU FC).continuous.comp_aestronglyMeasurable h.meas

theorem JetBound.aesm_pW (h : JetBound Q Ke B R) :
    AEStronglyMeasurable (fun x => pW FC (R x)) Q.μ :=
  (pW FC).continuous.comp_aestronglyMeasurable h.meas

theorem JetBound.aesm_sU (h : JetBound Q Ke B R) :
    AEStronglyMeasurable (fun x => ((1 : ℝ), pU FC (R x))) Q.μ :=
  aestronglyMeasurable_const.prodMk h.aesm_pU

theorem JetBound.bpU (h : JetBound Q Ke B R) :
    eLpNorm (fun x => pU FC (R x)) 2 Q.μ ≤ cQ Q * B + cQ Q * B :=
  (eLpNorm_le_pt2 h.m_Ψb.norm h.m_Ψ.norm (by norm_num) fun x => norm_prod_le_add' _).trans
    (add_le_add (eLpNorm_norm_le h.bΨb2) (eLpNorm_norm_le h.bΨ2))

theorem JetBound.bpW (h : JetBound Q Ke B R) :
    eLpNorm (fun x => pW FC (R x)) 2 Q.μ ≤ cQ Q * B + cQ Q * B :=
  (eLpNorm_le_pt2 h.m_dΨ.norm h.m_dΨb.norm (by norm_num) fun x => norm_prod_le_add' _).trans
    (add_le_add (eLpNorm_norm_le h.bdΨ2) (eLpNorm_norm_le h.bdΨb2))

theorem JetBound.bsU (h : JetBound Q Ke B R) :
    eLpNorm (fun x => ((1 : ℝ), pU FC (R x))) 2 Q.μ ≤
      cQ Q * ENNReal.ofReal 1 + (cQ Q * B + cQ Q * B) := by
  refine (eLpNorm_le_pt2 (u := fun _ => ‖(1 : ℝ)‖) aestronglyMeasurable_const h.aesm_pU.norm
    (by norm_num) fun x => norm_prod_le_add' _).trans (add_le_add ?_ (eLpNorm_norm_le h.bpU))
  exact eLpNorm_const_le_cmax _ |>.trans (by unfold cQ; rw [norm_norm, norm_one])

theorem dist_pU (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => pU FC (R₁ x) - pU FC (R₂ x)) 2 Q.μ ≤ (cQ Q + cQ Q) * D := by
  refine (eLpNorm_le_pt2 (h₁.m_Ψb.sub h₂.m_Ψb).norm (h₁.m_Ψ.sub h₂.m_Ψ).norm (by norm_num)
    fun x => norm_prod_le_add' _).trans ?_
  rw [add_mul]
  exact add_le_add (eLpNorm_norm_le (dist_Ψb2 h₁ h₂ hD)) (eLpNorm_norm_le (dist_Ψ2 h₁ h₂ hD))

theorem dist_pW (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => pW FC (R₁ x) - pW FC (R₂ x)) 2 Q.μ ≤ (cQ Q + cQ Q) * D := by
  refine (eLpNorm_le_pt2 (h₁.m_dΨ.sub h₂.m_dΨ).norm (h₁.m_dΨb.sub h₂.m_dΨb).norm (by norm_num)
    fun x => norm_prod_le_add' _).trans ?_
  rw [add_mul]
  exact add_le_add (eLpNorm_norm_le (dist_dΨ2 h₁ h₂ hD)) (eLpNorm_norm_le (dist_dΨb2 h₁ h₂ hD))

theorem dist_sU (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) :
    eLpNorm (fun x => ((1 : ℝ), pU FC (R₁ x)) - ((1 : ℝ), pU FC (R₂ x))) 2 Q.μ ≤
      (cQ Q + cQ Q) * D := by
  refine le_trans (eLpNorm_mono_real (g := fun x => ‖pU FC (R₁ x) - pU FC (R₂ x)‖) fun x => ?_)
    (eLpNorm_norm_le (dist_pU h₁ h₂ hD))
  rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero]
  exact max_le (norm_nonneg _) le_rfl

/-- `L²` bound of the potential variable field. -/
theorem JetBound.bpotVar' (h : JetBound Q Ke B R) {θ : CoefficientBank Ysec} {My : ℝ}
    (hMy : 0 ≤ My) (hL : ‖yukL FC θ‖ ≤ My) (h0 : ‖FC.yukawa θ 0‖ ≤ My) :
    eLpNorm (fun x => potVar' FC θ (R x)) 2 Q.μ ≤
      cQ Q * B + cQ Q * B + ENNReal.ofReal My * (cQ Q * B) +
        cQ Q * ENNReal.ofReal (My + 1 + My) := by
  have hpt : ∀ x, ‖potVar' FC θ (R x)‖ ≤
      (‖(R x).de‖ + ‖(R x).A‖ + My * ‖(R x).H‖) + (My + 1 + My) := by
    intro x
    have := norm_potVar'_le FC θ (R x)
    have := mul_le_mul_of_nonneg_right hL (norm_nonneg (R x).H)
    linarith
  refine (eLpNorm_le_pt2 ((h.m_de.norm.add h.m_A.norm).add (h.m_H.norm.const_mul My))
    aestronglyMeasurable_const (by norm_num) hpt).trans (add_le_add ?_ ?_)
  · refine (eLpNorm_add_le (h.m_de.norm.add h.m_A.norm) (h.m_H.norm.const_mul My)
      (by norm_num)).trans (add_le_add ((eLpNorm_add_le h.m_de.norm h.m_A.norm
      (by norm_num)).trans (add_le_add (eLpNorm_norm_le h.bde2) (eLpNorm_norm_le h.bA2)))
      (eLpNorm_cmul_norm_le hMy h.bH2))
  · refine (eLpNorm_const_le_cmax _).trans ?_
    unfold cQ
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- `L²` Lipschitz bound of the potential variable field. -/
theorem dist_potVar' (h₁ : JetBound Q Ke B R₁) (h₂ : JetBound Q Ke B R₂)
    {θ₁ θ₂ : CoefficientBank Ysec} {My Ly : ℝ} (hMy : 0 ≤ My) (hLy : 0 ≤ Ly)
    (hL : ‖yukL FC θ₁‖ ≤ My)
    (hlin : ENNReal.ofReal ‖yukL FC θ₁ - yukL FC θ₂‖ ≤ ENNReal.ofReal Ly * bankDist θ₁ θ₂)
    (hzero : ENNReal.ofReal ‖FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0‖ ≤
      ENNReal.ofReal Ly * bankDist θ₁ θ₂) {D : ℝ≥0∞}
    (hD : jetDist Q R₁ R₂ ≤ D) (hDθ : bankDist θ₁ θ₂ ≤ D) :
    eLpNorm (fun x => potVar' FC θ₁ (R₁ x) - potVar' FC θ₂ (R₂ x)) 2 Q.μ ≤
      (cQ Q + cQ Q + ENNReal.ofReal My * cQ Q + ENNReal.ofReal Ly * (cQ Q * B) +
        cQ Q * (ENNReal.ofReal Ly + ENNReal.ofReal Ly)) * D := by
  obtain ⟨δL, hδL⟩ : ∃ r, r = ‖yukL FC θ₁ - yukL FC θ₂‖ := ⟨_, rfl⟩
  obtain ⟨δ0, hδ0⟩ : ∃ r, r = ‖FC.yukawa θ₁ 0 - FC.yukawa θ₂ 0‖ := ⟨_, rfl⟩
  have hδL0 : 0 ≤ δL := by rw [hδL]; exact norm_nonneg _
  have hδ00 : 0 ≤ δ0 := by rw [hδ0]; exact norm_nonneg _
  have hpt : ∀ x, ‖potVar' FC θ₁ (R₁ x) - potVar' FC θ₂ (R₂ x)‖ ≤
      (‖(R₁ x).de - (R₂ x).de‖ + ‖(R₁ x).A - (R₂ x).A‖ + My * ‖(R₁ x).H - (R₂ x).H‖ +
        δL * ‖(R₂ x).H‖) + (δ0 + δL) := by
    intro x
    have := norm_potVar'_sub_le FC θ₁ θ₂ (R₁ x) (R₂ x)
    have := mul_le_mul_of_nonneg_right hL (norm_nonneg ((R₁ x).H - (R₂ x).H))
    rw [← hδL, ← hδ0] at *
    linarith
  have m1 := (h₁.m_de.sub h₂.m_de).norm
  have m2 := (h₁.m_A.sub h₂.m_A).norm
  have m3 := ((h₁.m_H.sub h₂.m_H).norm.const_mul My)
  have m4 := (h₂.m_H.norm.const_mul δL)
  refine (eLpNorm_le_pt2 (((m1.add m2).add m3).add m4) aestronglyMeasurable_const (by norm_num)
    hpt).trans ?_
  have hδLD : ENNReal.ofReal δL ≤ ENNReal.ofReal Ly * D := by
    rw [hδL]; exact hlin.trans (by gcongr)
  have hδ0D : ENNReal.ofReal δ0 ≤ ENNReal.ofReal Ly * D := by
    rw [hδ0]; exact hzero.trans (by gcongr)
  have b1 : eLpNorm (fun x => ‖(R₁ x).de - (R₂ x).de‖ + ‖(R₁ x).A - (R₂ x).A‖ +
      My * ‖(R₁ x).H - (R₂ x).H‖ + δL * ‖(R₂ x).H‖) 2 Q.μ ≤
      cQ Q * D + cQ Q * D + ENNReal.ofReal My * (cQ Q * D) +
        ENNReal.ofReal δL * (cQ Q * B) := by
    refine (eLpNorm_add_le ((m1.add m2).add m3) m4 (by norm_num)).trans (add_le_add ?_
      (eLpNorm_cmul_norm_le hδL0 h₂.bH2))
    refine (eLpNorm_add_le (m1.add m2) m3 (by norm_num)).trans (add_le_add ?_
      (eLpNorm_cmul_norm_le hMy (dist_H2 h₁ h₂ hD)))
    exact (eLpNorm_add_le m1 m2 (by norm_num)).trans (add_le_add
      (eLpNorm_norm_le (dist_de2 h₁ h₂ hD)) (eLpNorm_norm_le (dist_A2 h₁ h₂ hD)))
  have b2 : eLpNorm (fun _ : E4 => δ0 + δL) 2 Q.μ ≤
      cQ Q * (ENNReal.ofReal Ly * D + ENNReal.ofReal Ly * D) := by
    refine (eLpNorm_const_le_cmax _).trans ?_
    unfold cQ
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith), ENNReal.ofReal_add hδ00 hδL0]
    gcongr
  calc _ ≤ (cQ Q * D + cQ Q * D + ENNReal.ofReal My * (cQ Q * D) +
        ENNReal.ofReal δL * (cQ Q * B)) +
        cQ Q * (ENNReal.ofReal Ly * D + ENNReal.ofReal Ly * D) := add_le_add b1 b2
    _ ≤ (cQ Q * D + cQ Q * D + ENNReal.ofReal My * (cQ Q * D) +
        ENNReal.ofReal Ly * D * (cQ Q * B)) +
        cQ Q * (ENNReal.ofReal Ly * D + ENNReal.ofReal Ly * D) := by gcongr
    _ = _ := by ring

end DiracPackets

/-! ### The Dirac–Yukawa sector -/

section DiracSector

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

theorem ennreal_mul_le_mul_right {a b : ℝ≥0∞} (D : ℝ≥0∞) (h : a ≤ b) : a * D ≤ b * D := by
  gcongr

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
/-- **`prop:variation-continuity`, Dirac–Yukawa sector, jet form**: on uniformly bounded
strong-packet jet fields and banks in a set `P` on which the Yukawa map is bounded and Lipschitz,
`‖diracCov_{θ₁}(R₁) - diracCov_{θ₂}(R₂)‖_{L¹(Q)} ≤ C (d(R₁,R₂) + |θ₁-θ₂|)`. -/
theorem dirac_lipschitz (Q : ChartBox T) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {P : Set (CoefficientBank Ysec)} {Ly My : ℝ}
    (hY : YukawaLipOn FC P Ly My) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ Cd : ℝ≥0∞, Cd ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet FC.C) (θ₁ θ₂ : CoefficientBank Ysec),
      θ₁ ∈ P → θ₂ ∈ P → JetBound Q Ke B R₁ → JetBound Q Ke B R₂ →
        eLpNorm (fun x => diracCov FC θ₁ (R₁ x) - diracCov FC θ₂ (R₂ x)) 1 Q.μ ≤
          Cd * (jetDist Q R₁ R₂ + bankDist θ₁ θ₂) := by
  have hcQ := cQ_ne_top Q
  obtain ⟨cB, hcB⟩ : ∃ r : ℝ≥0∞, r = cQ Q * B := ⟨_, rfl⟩
  obtain ⟨BY, hBY⟩ : ∃ r : ℝ≥0∞, r = cB + cB + ENNReal.ofReal My * cB +
      cQ Q * ENNReal.ofReal (My + 1 + My) := ⟨_, rfl⟩
  obtain ⟨BU, hBU⟩ : ∃ r : ℝ≥0∞, r = cB + cB := ⟨_, rfl⟩
  obtain ⟨BSU, hBSU⟩ : ∃ r : ℝ≥0∞, r = cQ Q * ENNReal.ofReal 1 + BU := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ r : ℝ≥0∞, r = BY + BU + BSU := ⟨_, rfl⟩
  obtain ⟨KY, hKY⟩ : ∃ r : ℝ≥0∞, r = cQ Q + cQ Q + ENNReal.ofReal My * cQ Q +
      ENNReal.ofReal Ly * cB + cQ Q * (ENNReal.ofReal Ly + ENNReal.ofReal Ly) := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ r : ℝ≥0∞, r = cQ Q + KY + (cQ Q + cQ Q) := ⟨_, rfl⟩
  have hcBt : cB ≠ ⊤ := by rw [hcB]; exact ENNReal.mul_ne_top hcQ hB
  have hBst : Bs ≠ ⊤ := by
    rw [hBs, hBSU, hBU, hBY]
    finiteness
  have hKdt : Kd ≠ ⊤ := by
    rw [hKd, hKY]
    finiteness
  -- comparisons with the uniform constants
  have cBU : cB ≤ BU := by rw [hBU]; exact le_self_add
  have BYs : BY ≤ Bs := by rw [hBs]; exact le_self_add.trans le_self_add
  have BUs : BU ≤ Bs := by rw [hBs]; exact le_add_self.trans le_self_add
  have BSUs : BSU ≤ Bs := by rw [hBs]; exact le_add_self
  have cBs : cB ≤ Bs := cBU.trans BUs
  have cQd : cQ Q ≤ Kd := by rw [hKd]; exact le_self_add.trans le_self_add
  have KYd : KY ≤ Kd := by rw [hKd]; exact le_add_self.trans le_self_add
  have cQ2d : cQ Q + cQ Q ≤ Kd := by rw [hKd]; exact le_add_self
  obtain ⟨K1, hK1, h1⟩ :=
    coeff2_lip (CovSmooth.contDiffOn_strongCoeff1 FC (n := 1)) hKe hsub hBst
  obtain ⟨K2, hK2, h2⟩ :=
    coeff3_lip (CovSmooth.contDiffOn_strongCoeff2 FC (n := 1)) hKe hsub hBst
  obtain ⟨K3, hK3, h3⟩ :=
    coeff2_lip (contDiffOn_weakDirac (C := FC.C) (n := 1)) hKe hsub hBst
  refine ⟨(K1 + K2 + K3) * Kd, by finiteness, ?_⟩
  intro R₁ R₂ θ₁ θ₂ hθ₁ hθ₂ h₁ h₂
  obtain ⟨D, hD⟩ : ∃ d, d = jetDist Q R₁ R₂ + bankDist θ₁ θ₂ := ⟨_, rfl⟩
  have hDj : jetDist Q R₁ R₂ ≤ D := by rw [hD]; exact le_self_add
  have hDθ : bankDist θ₁ θ₂ ≤ D := by rw [hD]; exact le_add_self
  -- packet bounds
  have bY₁ : eLpNorm (fun x => potVar' FC θ₁ (R₁ x)) 2 Q.μ ≤ Bs :=
    (h₁.bpotVar' hY.nonneg_M (hY.bound_lin θ₁ hθ₁) (hY.bound_zero θ₁ hθ₁)).trans
      (by rw [← hcB, ← hBY]; exact BYs)
  have bY₂ : eLpNorm (fun x => potVar' FC θ₂ (R₂ x)) 2 Q.μ ≤ Bs :=
    (h₂.bpotVar' hY.nonneg_M (hY.bound_lin θ₂ hθ₂) (hY.bound_zero θ₂ hθ₂)).trans
      (by rw [← hcB, ← hBY]; exact BYs)
  have bU₁ : eLpNorm (fun x => pU FC (R₁ x)) 2 Q.μ ≤ Bs :=
    h₁.bpU.trans (by rw [← hcB, ← hBU]; exact BUs)
  have bU₂ : eLpNorm (fun x => pU FC (R₂ x)) 2 Q.μ ≤ Bs :=
    h₂.bpU.trans (by rw [← hcB, ← hBU]; exact BUs)
  have bW₁ : eLpNorm (fun x => pW FC (R₁ x)) 2 Q.μ ≤ Bs :=
    h₁.bpW.trans (by rw [← hcB, ← hBU]; exact BUs)
  have bW₂ : eLpNorm (fun x => pW FC (R₂ x)) 2 Q.μ ≤ Bs :=
    h₂.bpW.trans (by rw [← hcB, ← hBU]; exact BUs)
  have bS₁ : eLpNorm (fun x => ((1 : ℝ), pU FC (R₁ x))) 2 Q.μ ≤ Bs :=
    h₁.bsU.trans (by rw [← hcB, ← hBU, ← hBSU]; exact BSUs)
  have bS₂ : eLpNorm (fun x => ((1 : ℝ), pU FC (R₂ x))) 2 Q.μ ≤ Bs :=
    h₂.bsU.trans (by rw [← hcB, ← hBU, ← hBSU]; exact BSUs)
  have bΨb₁ : eLpNorm (fun x => (R₁ x).Ψb) 4 Q.μ ≤ Bs := h₁.bΨb4.trans (by rw [← hcB]; exact cBs)
  have bΨb₂ : eLpNorm (fun x => (R₂ x).Ψb) 4 Q.μ ≤ Bs := h₂.bΨb4.trans (by rw [← hcB]; exact cBs)
  have bΨ₁ : eLpNorm (fun x => (R₁ x).Ψ) 4 Q.μ ≤ Bs := h₁.bΨ4.trans (by rw [← hcB]; exact cBs)
  have bΨ₂ : eLpNorm (fun x => (R₂ x).Ψ) 4 Q.μ ≤ Bs := h₂.bΨ4.trans (by rw [← hcB]; exact cBs)
  -- differences
  have de : eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ Kd * D :=
    (dist_e h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQd)
  have dY : eLpNorm (fun x => potVar' FC θ₁ (R₁ x) - potVar' FC θ₂ (R₂ x)) 2 Q.μ ≤ Kd * D :=
    (dist_potVar' h₁ h₂ hY.nonneg_M hY.nonneg_L (hY.bound_lin θ₁ hθ₁)
      (hY.lip_lin θ₁ hθ₁ θ₂ hθ₂) (hY.lip_zero θ₁ hθ₁ θ₂ hθ₂) hDj hDθ).trans
      (ennreal_mul_le_mul_right D (by rw [← hcB, ← hKY]; exact KYd))
  have dU : eLpNorm (fun x => pU FC (R₁ x) - pU FC (R₂ x)) 2 Q.μ ≤ Kd * D :=
    (dist_pU h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQ2d)
  have dW : eLpNorm (fun x => pW FC (R₁ x) - pW FC (R₂ x)) 2 Q.μ ≤ Kd * D :=
    (dist_pW h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQ2d)
  have dS : eLpNorm (fun x => ((1 : ℝ), pU FC (R₁ x)) - ((1 : ℝ), pU FC (R₂ x))) 2 Q.μ ≤
      Kd * D := (dist_sU h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQ2d)
  have dΨb : eLpNorm (fun x => (R₁ x).Ψb - (R₂ x).Ψb) 4 Q.μ ≤ Kd * D :=
    (dist_Ψb4 h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQd)
  have dΨ : eLpNorm (fun x => (R₁ x).Ψ - (R₂ x).Ψ) 4 Q.μ ≤ Kd * D :=
    (dist_Ψ4 h₁ h₂ hDj).trans (ennreal_mul_le_mul_right D cQd)
  -- the three parts
  have t1 := h1 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => potVar' FC θ₁ (R₁ x))
    (fun x => potVar' FC θ₂ (R₂ x)) (fun x => pU FC (R₁ x)) (fun x => pU FC (R₂ x)) (Kd * D)
    h₁.m_e h₂.m_e h₁.chart h₂.chart (h₁.aesm_potVar' θ₁) (h₂.aesm_potVar' θ₂) h₁.aesm_pU
    h₂.aesm_pU bY₁ bY₂ bU₁ bU₂ de dY dU
  have t2 := h2 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => potVar' FC θ₁ (R₁ x))
    (fun x => potVar' FC θ₂ (R₂ x)) (fun x => (R₁ x).Ψb) (fun x => (R₂ x).Ψb)
    (fun x => (R₁ x).Ψ) (fun x => (R₂ x).Ψ) (Kd * D)
    h₁.m_e h₂.m_e h₁.chart h₂.chart (h₁.aesm_potVar' θ₁) (h₂.aesm_potVar' θ₂) h₁.m_Ψb h₂.m_Ψb
    h₁.m_Ψ h₂.m_Ψ bY₁ bY₂ bΨb₁ bΨb₂ bΨ₁ bΨ₂ de dY dΨb dΨ
  have t3 := h3 Q.μ (fun x => (R₁ x).e) (fun x => (R₂ x).e) (fun x => ((1 : ℝ), pU FC (R₁ x)))
    (fun x => ((1 : ℝ), pU FC (R₂ x))) (fun x => pW FC (R₁ x)) (fun x => pW FC (R₂ x)) (Kd * D)
    h₁.m_e h₂.m_e h₁.chart h₂.chart h₁.aesm_sU h₂.aesm_sU h₁.aesm_pW h₂.aesm_pW bS₁ bS₂ bW₁ bW₂
    de dS dW
  have c1 := (CovSmooth.contDiffOn_strongCoeff1 FC (n := 1)).continuousOn
  have c2 := (CovSmooth.contDiffOn_strongCoeff2 FC (n := 1)).continuousOn
  have c3 := (contDiffOn_weakDirac (C := FC.C) (n := 1)).continuousOn
  have m11 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₁.m_e h₁.chart)
    (h₁.aesm_potVar' θ₁)) h₁.aesm_pU
  have m12 := aesm_apply (aesm_apply (aesm_coeff c1 hsub h₂.m_e h₂.chart)
    (h₂.aesm_potVar' θ₂)) h₂.aesm_pU
  have m21 := aesm_apply (aesm_apply (aesm_apply (aesm_coeff c2 hsub h₁.m_e h₁.chart)
    (h₁.aesm_potVar' θ₁)) h₁.m_Ψb) h₁.m_Ψ
  have m22 := aesm_apply (aesm_apply (aesm_apply (aesm_coeff c2 hsub h₂.m_e h₂.chart)
    (h₂.aesm_potVar' θ₂)) h₂.m_Ψb) h₂.m_Ψ
  have m31 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₁.m_e h₁.chart) h₁.aesm_sU) h₁.aesm_pW
  have m32 := aesm_apply (aesm_apply (aesm_coeff c3 hsub h₂.m_e h₂.chart) h₂.aesm_sU) h₂.aesm_pW
  rw [← hD]
  calc eLpNorm (fun x => diracCov FC θ₁ (R₁ x) - diracCov FC θ₂ (R₂ x)) 1 Q.μ
      ≤ _ := eLpNorm_sum3_sub m11 m12 m21 m22 m31 m32
    _ ≤ K1 * (Kd * D) + K2 * (Kd * D) + K3 * (Kd * D) := add_le_add (add_le_add t1.1 t2.1) t3.1
    _ = (K1 + K2 + K3) * Kd * D := by ring

end DiracSector

end VarLip
end EinsteinSM
end RenewalGeometry
