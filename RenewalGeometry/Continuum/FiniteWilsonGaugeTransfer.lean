/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FiniteWilsonZeroDefect
import RenewalGeometry.GaugeTheory.NativeActionGaugeInvariance

/-!
# Transfer of the finite Wilson hypotheses along a site gauge
  (`thm:finite-Wilson-zero-defect`, normalization step, Einstein–SM action closure)

The proof of `thm:finite-Wilson-zero-defect` begins with a same-record site-gauge normalization
and then uses: "The same-record gauge transformation leaves the complete action, the physical
action-covector norm, the literal curvature and Higgs-gradient norms, their Wilson moduli, and the
positive internal-link spinor graph norms unchanged."  The invariance lemmas of
`NativeGauge` (`prop:rooted-gauge-certificate`) are stated for link configurations; this file
transfers them to the encodings in which the Wilson criterion
`FiniteWilsonZeroDefect.finite_wilson_criterion` is stated (`curvPacket`, `higgsPacket`,
`adLinks`, `higgsLinks`, `wilsonShiftR`, `gridNorm`, `spinGraph`, `dualGraph`).

For a gauge transform `y'` of a record `y` (`NativeGauge.IsGaugeTransform`, i.e.
`e^{hA'_μ(x)} = g_x e^{hA_μ(x)} g_{x+μ}⁻¹`, `H' = ρ_H(g)H`, `Ψ' = ρ_S(g)Ψ`, `Ψ̄' = Ψ̄ρ_S(g)⁻¹`,
coframe unchanged), with `g` in the gauge group of a covariant packet and `ρ_H(G)` isometric
(unitarity of the internal representations):

* `coframe_eq`: the coframe (hence `coframeM`, `qM`, `ωM` and the reconstructed coframes) is
  unchanged;
* `curvPacket_gauge`, `gridNorm_curvPacket_gauge`: the literal curvature packet is conjugated,
  its `L²_h` norm unchanged (on the plaquette chart);
* `higgsPacket_gauge`, `gridNorm_higgsPacket_gauge`: the Higgs-gradient packet is rotated by
  `ρ_H(g)`, its norm unchanged;
* `openLinkR_cov`, `wilsonShiftR_cov`: covariance of the open finite links and Wilson shifts
  (endpoint cancellation, `eq:open-finite-link`); `gridNorm_wilson_curv_gauge`,
  `gridNorm_wilson_higgs_gauge`: the Wilson screens of both packets are unchanged;
* `adUnit_gauge`, `higgsUnit_gauge`, `spinUnit_gauge`: unitarity of the transformed links;
* `gridNorm_higgs_gauge`, `gridNorm_psi_gauge`, `gridNorm_psiBar_gauge`,
  `gridNorm_spinGraph_gauge`, `gridNorm_dualGraph_gauge`: the Higgs and spinor bounds and the
  positive internal-link spinor graph norms are unchanged.
-/

open NormedSpace Finset Filter Topology
open scoped BigOperators

namespace RenewalGeometry.FiniteWilsonTransfer

open ShiftedJetAction (Grid unitVec)
open NativeDensity NativeGauge FiniteWilsonZeroDefect TorusPiecewiseConstantTranslation

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Covariance of open links and Wilson shifts -/

section OpenLinks

variable {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ} [NeZero N]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Endpoint cancellation along open finite links** (`eq:open-finite-link`): if the links are
covariant, `V'_μ(x) R_{x+μ} = R_x V_μ(x)`, then `𝒰'_{μ,m}(x) R_{x+mμ} = R_x 𝒰_{μ,m}(x)`. -/
theorem openLinkR_cov (V V' : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F))
    (R : (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d)
    (hcov : ∀ x w, V' μ x (R (x + Pi.single μ 1) w) = R x (V μ x w)) (m : ℕ) :
    ∀ x w, openLinkR V' μ m x (R (x + Pi.single μ (m : ZMod N)) w) =
      R x (openLinkR V μ m x w) := by
  induction m with
  | zero => intro x w; simp [openLinkR]
  | succ m ih =>
    intro x w
    have hpos : x + Pi.single μ ((m + 1 : ℕ) : ZMod N) =
        x + Pi.single μ 1 + Pi.single μ (m : ZMod N) := by
      rw [add_assoc, ← Pi.single_add]
      push_cast
      rw [add_comm (1 : ZMod N)]
    change V' μ x (openLinkR V' μ m (x + Pi.single μ 1)
        (R (x + Pi.single μ ((m + 1 : ℕ) : ZMod N)) w)) =
      R x (V μ x (openLinkR V μ m (x + Pi.single μ 1) w))
    rw [hpos, ih, hcov]

/-- Covariance of the Wilson shift differences. -/
theorem wilsonShiftR_cov (V V' : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F))
    (R : (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d)
    (hcov : ∀ x w, V' μ x (R (x + Pi.single μ 1) w) = R x (V μ x w)) (m : ℕ)
    (Y : (d → ZMod N) → F) (x : d → ZMod N) :
    (wilsonShiftR V' μ m (fun z => R z (Y z)) - fun z => R z (Y z)) x =
      R x ((wilsonShiftR V μ m Y - Y) x) := by
  simp only [Pi.sub_apply, wilsonShiftR, map_sub]
  rw [openLinkR_cov V V' R μ hcov m x]

/-- Pointwise isometries preserve the grid `L²` norm. -/
theorem gridNorm_iso (R : (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (Y : (d → ZMod N) → F) :
    gridNorm (fun z => R z (Y z)) = gridNorm Y := by
  unfold gridNorm
  simp only [LinearIsometryEquiv.norm_map]

/-- **The Wilson screens are gauge invariant** (abstract form). -/
theorem gridNorm_wilsonShiftR_cov (V V' : d → (d → ZMod N) → (F ≃ₗᵢ[ℝ] F))
    (R : (d → ZMod N) → (F ≃ₗᵢ[ℝ] F)) (μ : d)
    (hcov : ∀ x w, V' μ x (R (x + Pi.single μ 1) w) = R x (V μ x w)) (m : ℕ)
    (Y : (d → ZMod N) → F) :
    gridNorm (wilsonShiftR V' μ m (fun z => R z (Y z)) - fun z => R z (Y z)) =
      gridNorm (wilsonShiftR V μ m Y - Y) := by
  have e : (wilsonShiftR V' μ m (fun z => R z (Y z)) - fun z => R z (Y z)) =
      fun x => R x ((wilsonShiftR V μ m Y - Y) x) := funext (wilsonShiftR_cov V V' R μ hcov m Y)
  rw [e, gridNorm_iso]

end OpenLinks

/-! ### Isometries of the gauge group -/

section Isos

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- Conjugation by a norm-preserving gauge element as a linear isometry. -/
def conjIso (g : 𝔄ˣ) (hg : ∀ X : 𝔄, ‖(g : 𝔄) * X * ↑g⁻¹‖ = ‖X‖) : 𝔄 ≃ₗᵢ[ℝ] 𝔄 where
  toFun X := (g : 𝔄) * X * ↑g⁻¹
  invFun X := ↑g⁻¹ * X * g
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
  norm_map' := hg

@[simp] theorem conjIso_apply (g : 𝔄ˣ) (hg : ∀ X : 𝔄, ‖(g : 𝔄) * X * ↑g⁻¹‖ = ‖X‖) (X : 𝔄) :
    conjIso g hg X = (g : 𝔄) * X * ↑g⁻¹ := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A represented gauge element `ρ(g)` acting isometrically, as a linear isometry. -/
def repIso (ρ : 𝔄 →ₐ[ℝ] (F →L[ℝ] F)) (g : 𝔄ˣ) (hg : ∀ v, ‖ρ g v‖ = ‖v‖) : F ≃ₗᵢ[ℝ] F where
  toFun v := ρ g v
  invFun v := ρ ↑g⁻¹ v
  left_inv v := algHom_inv_apply ρ g v
  right_inv v := algHom_apply_inv ρ g v
  map_add' v w := map_add _ v w
  map_smul' c v := map_smul _ c v
  norm_map' := hg

@[simp] theorem repIso_apply (ρ : 𝔄 →ₐ[ℝ] (F →L[ℝ] F)) (g : 𝔄ˣ) (hg : ∀ v, ‖ρ g v‖ = ‖v‖)
    (v : F) : repIso ρ g hg v = ρ g v := rfl

/-- Componentwise action on the curvature packet. -/
def conjPacket (L : 𝔄 ≃ₗᵢ[ℝ] 𝔄) : (Fin 4 → Fin 4 → 𝔄) ≃ₗᵢ[ℝ] (Fin 4 → Fin 4 → 𝔄) :=
  piIso (ι := Fin 4) (piIso (ι := Fin 4) L)

@[simp] theorem conjPacket_apply (L : 𝔄 ≃ₗᵢ[ℝ] 𝔄) (w : Fin 4 → Fin 4 → 𝔄) (a b : Fin 4) :
    conjPacket L w a b = L (w a b) := rfl

/-- Componentwise action on the Higgs-gradient packet. -/
def higgsVec (L : F ≃ₗᵢ[ℝ] F) : (Fin 4 → F) ≃ₗᵢ[ℝ] (Fin 4 → F) := piIso (ι := Fin 4) L

@[simp] theorem higgsVec_apply (L : F ≃ₗᵢ[ℝ] F) (w : Fin 4 → F) (a : Fin 4) :
    higgsVec L w a = L (w a) := rfl

end Isos

/-! ### Records related by a site gauge -/

section Transfer

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (C : CovData 𝔄 𝓗 𝓢) {N : ℕ} [NeZero N]
variable {g : Grid N → 𝔄ˣ} {y y' : Grid N → Field 𝔄 𝓗 𝓢}

theorem coframe_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') : coframe y' = coframe y :=
  congrArg LinkConfig.e hy.2

theorem exp_gauge_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (μ : Fin 4) (x : Grid N) :
    exp ((N : ℝ)⁻¹ • gauge y' μ x) =
      (g x : 𝔄) * exp ((N : ℝ)⁻¹ • gauge y μ x) * ↑(g (x + unitVec N μ))⁻¹ :=
  congrFun (congrFun (congrArg LinkConfig.U hy.2) μ) x

theorem exp_neg_gauge_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (μ : Fin 4) (x : Grid N) :
    exp (-((N : ℝ)⁻¹ • gauge y' μ x)) =
      (g (x + unitVec N μ) : 𝔄) * exp (-((N : ℝ)⁻¹ • gauge y μ x)) * ↑(g x)⁻¹ := by
  set a := (N : ℝ)⁻¹ • gauge y μ x
  set b := (N : ℝ)⁻¹ • gauge y' μ x
  have h1 : exp b * ((g (x + unitVec N μ) : 𝔄) * exp (-a) * ↑(g x)⁻¹) = 1 := by
    rw [exp_gauge_eq C hy μ x]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (exp a), NativeDensity.exp_mul_exp_neg, one_mul, Units.mul_inv]
  calc exp (-b) = exp (-b) * (exp b * ((g (x + unitVec N μ) : 𝔄) * exp (-a) * ↑(g x)⁻¹)) := by
        rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, NativeDensity.exp_neg_mul_exp, one_mul]

theorem higgs_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (x : Grid N) :
    higgs y' x = C.ρH (g x) (higgs y x) :=
  congrFun (congrArg LinkConfig.H hy.2) x

theorem psi_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (x : Grid N) :
    psi y' x = C.ρS (g x) (psi y x) :=
  congrFun (congrArg LinkConfig.Ψ hy.2) x

theorem psiBar_eq (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (x : Grid N) :
    psiBar y' x = (psiBar y x).comp (C.ρS ↑(g x)⁻¹) :=
  congrFun (congrArg LinkConfig.Ψb hy.2) x

/-! #### The literal curvature packet -/

/-- **The literal curvature packet is conjugated** on the plaquette chart. -/
theorem curvPacket_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hP : ∀ x μ ν, ‖plaq (toLinks (N : ℝ)⁻¹ y) x μ ν - 1‖ < 1) (x : Grid N) (μ ν : Fin 4) :
    curvPacket N y' x μ ν = (g x : 𝔄) * curvPacket N y x μ ν * ↑(g x)⁻¹ := by
  simp only [curvPacket, fieldStrength_eq_curv, hy.2]
  exact curv_gauge C hy.1 _ _ x μ ν (hP x μ ν)

theorem norm_curvPacket_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hP : ∀ x μ ν, ‖plaq (toLinks (N : ℝ)⁻¹ y) x μ ν - 1‖ < 1) (x : Grid N) :
    curvPacket N y' x = conjPacket (conjIso (g x) (C.norm_conj _ (hy.1 x))) (curvPacket N y x) := by
  funext μ ν
  simp only [conjPacket_apply, conjIso_apply]
  exact curvPacket_gauge C hy hP x μ ν

/-- The `L²_h` norm of the literal curvature packet is unchanged. -/
theorem gridNorm_curvPacket_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hP : ∀ x μ ν, ‖plaq (toLinks (N : ℝ)⁻¹ y) x μ ν - 1‖ < 1) :
    gridNorm (curvPacket N y') = gridNorm (curvPacket N y) := by
  have e : curvPacket N y' = fun x =>
      conjPacket (conjIso (g x) (C.norm_conj _ (hy.1 x))) (curvPacket N y x) :=
    funext (norm_curvPacket_gauge C hy hP)
  rw [e, gridNorm_iso]

/-- The adjoint links are covariant. -/
theorem adLinks_cov (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hAd : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖)
    (hAd' : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y' μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y' μ x))‖ = ‖X‖) (μ : Fin 4) (x : Grid N)
    (w : Fin 4 → Fin 4 → 𝔄) :
    adLinks N y' hAd' μ x (conjPacket (conjIso (g (x + Pi.single μ 1))
        (C.norm_conj _ (hy.1 _))) w) =
      conjPacket (conjIso (g x) (C.norm_conj _ (hy.1 x))) (adLinks N y hAd μ x w) := by
  funext a b
  simp only [adLinks, piIso_apply, adIso_apply, conjIso_apply, conjPacket_apply]
  rw [exp_gauge_eq C hy μ x, exp_neg_gauge_eq C hy μ x]
  change (g x : 𝔄) * _ * ↑(g (x + unitVec N μ))⁻¹ *
      ((g (x + unitVec N μ) : 𝔄) * w a b * ↑(g (x + unitVec N μ))⁻¹) *
      ((g (x + unitVec N μ) : 𝔄) * _ * ↑(g x)⁻¹) = _
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- **The Wilson screen of the curvature packet is unchanged.** -/
theorem gridNorm_wilson_curv_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hP : ∀ x μ ν, ‖plaq (toLinks (N : ℝ)⁻¹ y) x μ ν - 1‖ < 1)
    (hAd : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖)
    (hAd' : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y' μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y' μ x))‖ = ‖X‖) (μ : Fin 4) (m : ℕ) :
    gridNorm (wilsonShiftR (adLinks N y' hAd') μ m (curvPacket N y') - curvPacket N y') =
      gridNorm (wilsonShiftR (adLinks N y hAd) μ m (curvPacket N y) - curvPacket N y) := by
  have e : curvPacket N y' = fun x =>
      conjPacket (conjIso (g x) (C.norm_conj _ (hy.1 x))) (curvPacket N y x) :=
    funext (norm_curvPacket_gauge C hy hP)
  rw [e]
  exact gridNorm_wilsonShiftR_cov (adLinks N y hAd) (adLinks N y' hAd')
    (fun x => conjPacket (conjIso (g x) (C.norm_conj _ (hy.1 x)))) μ
    (fun x w => adLinks_cov C hy hAd hAd' μ x w) m (curvPacket N y)

/-- Unitarity of the transformed adjoint links. -/
theorem adUnit_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hAd : ∀ x μ (X : 𝔄), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖) (x : Grid N) (μ : Fin 4) (X : 𝔄) :
    ‖exp ((N : ℝ)⁻¹ • gauge y' μ x) * X * exp (-((N : ℝ)⁻¹ • gauge y' μ x))‖ = ‖X‖ := by
  rw [exp_gauge_eq C hy μ x, exp_neg_gauge_eq C hy μ x]
  set k := g (x + unitVec N μ)
  have e : (g x : 𝔄) * exp ((N : ℝ)⁻¹ • gauge y μ x) * ↑k⁻¹ * X *
      ((k : 𝔄) * exp (-((N : ℝ)⁻¹ • gauge y μ x)) * ↑(g x)⁻¹) =
      (g x : 𝔄) * (exp ((N : ℝ)⁻¹ • gauge y μ x) * (↑k⁻¹ * X * ↑(k⁻¹)⁻¹) *
        exp (-((N : ℝ)⁻¹ • gauge y μ x))) * ↑(g x)⁻¹ := by
    simp only [inv_inv, mul_assoc]
  rw [e, C.norm_conj _ (hy.1 x), hAd, C.norm_conj _ (inv_mem (hy.1 _))]

/-! #### The Higgs-gradient packet -/

variable (hρH : ∀ k ∈ C.G, ∀ v : 𝓗, ‖C.ρH k v‖ = ‖v‖)
include hρH

theorem higgsPacket_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (x : Grid N) :
    higgsPacket C.toData N y' x =
      higgsVec (repIso C.ρH (g x) (hρH _ (hy.1 x))) (higgsPacket C.toData N y x) := by
  funext μ
  simp only [higgsPacket, higgsVec_apply, repIso_apply, higgsLink_eq_hLink, hy.2]
  exact hLink_gauge C g _ _ x μ

theorem gridNorm_higgsPacket_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') :
    gridNorm (higgsPacket C.toData N y') = gridNorm (higgsPacket C.toData N y) := by
  rw [funext (higgsPacket_gauge C hρH hy), gridNorm_iso]

theorem gridNorm_higgs_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') :
    gridNorm (higgs y') = gridNorm (higgs y) := by
  have e : higgs y' = fun x => repIso C.ρH (g x) (hρH _ (hy.1 x)) (higgs y x) :=
    funext (higgs_eq C hy)
  rw [e, gridNorm_iso]

omit hρH in
theorem rhoH_exp (h : ℝ) (A : 𝔄) : exp (h • C.ρHL A) = C.ρH (exp (h • A)) := by
  rw [NativeDensity.algHom_map_exp C.ρH C.ρH_cont, map_smul, Data.ρHL_apply]

/-- Unitarity of the transformed Higgs links. -/
theorem higgsUnit_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hUH : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y μ x)) v‖ = ‖v‖) (x : Grid N)
    (μ : Fin 4) (v : 𝓗) : ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y' μ x)) v‖ = ‖v‖ := by
  rw [rhoH_exp, exp_gauge_eq C hy μ x, map_mul, map_mul]
  have h2 := hUH x μ (C.ρH ↑(g (x + unitVec N μ))⁻¹ v)
  rw [rhoH_exp] at h2
  simp only [ContinuousLinearMap.mul_apply]
  rw [hρH _ (hy.1 x), h2, hρH _ (inv_mem (hy.1 _))]

/-- The Higgs links are covariant. -/
theorem higgsLinks_cov (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hUH : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y μ x)) v‖ = ‖v‖)
    (hUH' : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y' μ x)) v‖ = ‖v‖) (μ : Fin 4)
    (x : Grid N) (w : Fin 4 → 𝓗) :
    higgsLinks C.toData N y' hUH' μ x
        (higgsVec (repIso C.ρH (g (x + Pi.single μ 1)) (hρH _ (hy.1 _))) w) =
      higgsVec (repIso C.ρH (g x) (hρH _ (hy.1 x))) (higgsLinks C.toData N y hUH μ x w) := by
  funext a
  simp only [higgsLinks, piIso_apply, repIso_apply, higgsVec_apply]
  change exp ((N : ℝ)⁻¹ • C.ρHL (gauge y' μ x)) (C.ρH (g (x + unitVec N μ)) (w a)) =
    C.ρH (g x) (exp ((N : ℝ)⁻¹ • C.ρHL (gauge y μ x)) (w a))
  rw [rhoH_exp, rhoH_exp, exp_gauge_eq C hy μ x, map_mul, map_mul]
  simp only [ContinuousLinearMap.mul_apply, algHom_inv_apply]

/-- **The Wilson screen of the Higgs-gradient packet is unchanged.** -/
theorem gridNorm_wilson_higgs_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hUH : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y μ x)) v‖ = ‖v‖)
    (hUH' : ∀ x μ (v : 𝓗), ‖exp ((N : ℝ)⁻¹ • C.ρHL (gauge y' μ x)) v‖ = ‖v‖) (μ : Fin 4)
    (m : ℕ) :
    gridNorm (wilsonShiftR (higgsLinks C.toData N y' hUH') μ m (higgsPacket C.toData N y') -
        higgsPacket C.toData N y') =
      gridNorm (wilsonShiftR (higgsLinks C.toData N y hUH) μ m (higgsPacket C.toData N y) -
        higgsPacket C.toData N y) := by
  rw [funext (higgsPacket_gauge C hρH hy)]
  exact gridNorm_wilsonShiftR_cov (higgsLinks C.toData N y hUH) (higgsLinks C.toData N y' hUH')
    (fun x => higgsVec (repIso C.ρH (g x) (hρH _ (hy.1 x)))) μ
    (fun x w => higgsLinks_cov C hρH hy hUH hUH' μ x w) m (higgsPacket C.toData N y)

omit hρH

/-! #### Spinors and the positive internal-link graphs -/

theorem spinUnit_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y')
    (hU : ∀ x μ (v : 𝓢), ‖C.ρS (exp ((N : ℝ)⁻¹ • gauge y μ x)) v‖ = ‖v‖) (x : Grid N)
    (μ : Fin 4) (v : 𝓢) : ‖C.ρS (exp ((N : ℝ)⁻¹ • gauge y' μ x)) v‖ = ‖v‖ := by
  rw [exp_gauge_eq C hy μ x, map_mul, map_mul]
  simp only [ContinuousLinearMap.mul_apply]
  rw [C.ρS_isom _ (hy.1 x), hU, C.ρS_isom _ (inv_mem (hy.1 _))]

theorem gridNorm_psi_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') :
    gridNorm (psi y') = gridNorm (psi y) := by
  have e : psi y' = fun x => repIso C.ρS (g x) (C.ρS_isom _ (hy.1 x)) (psi y x) :=
    funext (psi_eq C hy)
  rw [e, gridNorm_iso]

theorem gridNorm_psiBar_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') :
    gridNorm (psiBar y') = gridNorm (psiBar y) := by
  unfold gridNorm
  simp only [psiBar_eq C hy, norm_comp_ρS_inv C (hy.1 _)]

theorem spinGraph_eq_intLink (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) :
    NativeSpinorGraph.spinGraph C.toData (N : ℝ)⁻¹ y x μ =
      intLink C (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) x μ := rfl

theorem dualGraph_eq_intLinkBar (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) :
    NativeSpinorGraph.dualGraph C.toData (N : ℝ)⁻¹ y x μ =
      intLinkBar C (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) x μ := by
  simp only [NativeSpinorGraph.dualGraph, intLinkBar, toLinks, ring_inverse_exp]

theorem gridNorm_spinGraph_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (μ : Fin 4) :
    gridNorm (fun x => NativeSpinorGraph.spinGraph C.toData (N : ℝ)⁻¹ y' x μ) =
      gridNorm (fun x => NativeSpinorGraph.spinGraph C.toData (N : ℝ)⁻¹ y x μ) := by
  unfold gridNorm
  simp only [spinGraph_eq_intLink, hy.2, norm_intLink_gauge C hy.1]

theorem gridNorm_dualGraph_gauge (hy : IsGaugeTransform C (N : ℝ)⁻¹ g y y') (μ : Fin 4) :
    gridNorm (fun x => NativeSpinorGraph.dualGraph C.toData (N : ℝ)⁻¹ y' x μ) =
      gridNorm (fun x => NativeSpinorGraph.dualGraph C.toData (N : ℝ)⁻¹ y x μ) := by
  unfold gridNorm
  simp only [dualGraph_eq_intLinkBar, hy.2, norm_intLinkBar_gauge C hy.1]

end Transfer

end

end RenewalGeometry.FiniteWilsonTransfer
