/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMRegularityUpgrade
import RenewalGeometry.Continuum.EinsteinSMCovectorSmoothness
import RenewalGeometry.Analysis.PartialDerivativesC1

/-!
# Regularity upgrade on a common slab: classical fields (`cor:strong-solution-upgrade`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMRegularityUpgrade.lean`.  This file proves the regularity step of
`cor:strong-solution-upgrade` for fields of the regularity the manuscript's Sobolev class yields
(bosons `C²`, spinors `C¹` on the open slab; the Sobolev class itself is treated in
`EinsteinSMSlabSobolev.lean`):

* `eulerRowW`, **`eulerRowW_eq_zero`** (du Bois-Reymond with minimal regularity): the Euler row
  `E(x)(w) = Λ(x)(valEmb w) - Σ_i ∂_i(Λ(·)(derEmb_i w))(x)` vanishes pointwise as soon as `Λ` is
  continuous and only the derivative-direction coefficients `Λ(·)(derEmb_i w)` are `C¹` (the
  first-order spinor rows need no second derivative of the spinors, whose time regularity in the
  manuscript's class is only `C¹_t`); `eulerRowW_eq_eulerRow` identifies it with `eulerRow` when
  `Λ` is differentiable;
* `zeroD`, `totalCovJet_derEmb_zeroD`: the derivative-direction coefficients of the total covector
  do not depend on the spinor gradients;
* `ClassicalSlab`: bosons `C²`, spinors `C¹` on the open slab, nondegenerate coframe, spatial
  periodicity; `contDiffOn_totalCov_derEmb`, `continuousOn_totalCovJet`;
* `hasWeakPartial_slab`, `limitJet_ae_eq_redJet`: classical derivatives are the weak derivatives
  on every slab chart, so the packets of a reduced limit with classical fields agree a.e. with the
  classical jet;
* **`strong_solution_upgrade_classical`**: under the hypotheses of `thm:reduced-closure`, every
  cutoff subsequence has a further subsequence with a limit whose distributional Euler identities,
  if the limit fields are classical (`ClassicalSlab`), hold pointwise: all Euler rows of the
  classical jet vanish at every point of `(0,T) × (0,1)³` in every admissible direction.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace SlabReg

open SobolevOpen (pd box IsTest MemW12 HasWeakPartial)

/-! ### du Bois-Reymond with minimal regularity -/

section Rows

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {r : ℕ}

/-- **The Euler row in direction `w`**:
`E(x)(w) = Λ(x)(valEmb w) - Σ_i ∂_i(y ↦ Λ(y)(derEmb_i w))(x)`. -/
def eulerRowW (Λ : E4 → RJet C →L[ℝ] ℝ) (x : E4) (w : FieldVal C) : ℝ :=
  Λ x (valEmb C w) - ∑ i, pd (fun y => Λ y (derEmb C i w)) i x

theorem eulerRowW_eq_eulerRow {Λ : E4 → RJet C →L[ℝ] ℝ} {x : E4}
    (hΛ : DifferentiableAt ℝ Λ x) (w : FieldVal C) : eulerRowW Λ x w = eulerRow Λ x w := by
  simp only [eulerRowW, eulerRow, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pd_clm_comp hΛ (ContinuousLinearMap.apply ℝ ℝ (derEmb C i w)) i

theorem eulerRowW_neg (Λ : E4 → RJet C →L[ℝ] ℝ) (x : E4) (w : FieldVal C) :
    eulerRowW Λ x (-w) = -eulerRowW Λ x w := by
  simp only [eulerRowW, map_neg]
  have : ∀ i, pd (fun y => -Λ y (derEmb C i w)) i x = -pd (fun y => Λ y (derEmb C i w)) i x :=
    fun i => by
      unfold SobolevOpen.pd
      rw [show (fun y => -Λ y (derEmb C i w)) = -(fun y => Λ y (derEmb C i w)) from rfl,
        fderiv_neg]
      rfl
  simp only [this, Finset.sum_neg_distrib]
  ring

theorem pd_mul_local {ψ g : E4 → ℝ} {x : E4} (hψ : DifferentiableAt ℝ ψ x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => ψ y * g y) i x = pd ψ i x * g x + ψ x * pd g i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_mul hψ hg, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **Integration by parts against a periodic bump, minimal regularity.** -/
theorem integral_bump_mul_eulerRowW {Λ : E4 → RJet C →L[ℝ] ℝ}
    (hΛc : ContinuousOn Λ (cylSlab T))
    (hΛd : ∀ i (w : FieldVal C), ContDiffOn ℝ 1 (fun y => Λ y (derEmb C i w)) (cylSlab T))
    (hΛper : ∀ n x, Λ (x + spatialShift n) = Λ x)
    (hEuler : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest left r K,
        ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, Λ x (testJet v.val x) = 0)
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {ψ : E4 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hper : ∀ n x, ψ (x + spatialShift n) = ψ x) {a b : ℝ}
    (ha : t₀ < a) (hb : b < t₁) (hz : ∀ x, x 0 ∉ Icc a b → ψ x = 0) {w : FieldVal C}
    (hw : IsAdmissible left w) :
    ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, ψ x * eulerRowW Λ x w = 0 := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQ
  let K : CylRegion T := ⟨Icc a b ×ˢ univ, isCompact_Icc.prod isCompact_univ, fun p hp =>
    ⟨⟨h0.trans (ha.trans_le hp.1.1), hp.1.2.trans_lt (hb.trans h1)⟩, trivial⟩⟩
  have hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁ := fun p hp => ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩
  have hlift : K.lift = (fun x : E4 => x 0) ⁻¹' Icc a b := by
    ext x; simp [CylRegion.lift, K, cylProj]
  have hsupp : tsupport ψ ⊆ K.lift := by
    rw [hlift]
    refine closure_minimal (fun x hx => ?_) (isClosed_Icc.preimage (continuous_apply 0))
    by_contra hxK
    exact hx (hz x hxK)
  set v : CrTest left r K := scaledTest K hψ hper hsupp hw
  have hE := hEuler K t₀ t₁ h0 h01 h1 hK v
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hgd : ∀ i, ∀ x ∈ cylSlab T, DifferentiableAt ℝ (fun y => Λ y (derEmb C i w)) x :=
    fun i x hx => ((hΛd i w).contDiffAt ((isOpen_cylSlab T).mem_nhds hx)).differentiableAt
      one_ne_zero
  set f : Fin 4 → E4 → ℝ := fun i x => ψ x * Λ x (derEmb C i w) with hf
  have hfC : ∀ i, ContDiffOn ℝ 1 (f i) (cylSlab T) := fun i =>
    (hψ.of_le (by simp)).contDiffOn.mul (hΛd i w)
  have hclQ : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hdiv := integral_div_slab_eq_zero h0 h01 h1 (f := f) (isOpen_cylSlab T) hclQ hfC
    (fun x hx => by
      have : ψ x = 0 := hz x fun h => by
        rcases hx with hx | hx <;> rw [hx] at h <;> linarith [h.1, h.2]
      simp [hf, this])
    (fun j x => by
      simp only [hf]
      rw [hper, hΛper])
  have hpt : ∀ x ∈ Q.set, ψ x * eulerRowW Λ x w =
      Λ x (testJet v.val x) - ∑ i, pd (f i) i x := by
    intro x hx
    have hxs : x ∈ cylSlab T := hclQ (subset_closure hx)
    have hv : v.val = scaledField ψ w := rfl
    rw [hv, testJet_scaled hψd, map_add, map_smul, map_sum]
    simp only [hf, pd_mul_local (hψd x) (hgd _ x hxs), map_smul, smul_eq_mul, eulerRowW,
      Finset.sum_add_distrib]
    rw [mul_sub, Finset.mul_sum]
    ring
  have hcont1 : ContinuousOn (fun x => Λ x (testJet v.val x)) (cylSlab T) :=
    hΛc.clm_apply (continuous_testJet v).continuousOn
  have hcont2 : ContinuousOn (fun x => ∑ i, pd (f i) i x) (cylSlab T) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact ((hfC i).continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply
      continuousOn_const
  rw [setIntegral_congr_fun Q.isOpen.measurableSet hpt,
    integral_sub (integrableOn_slab_of_continuousOn hcont1)
      (integrableOn_slab_of_continuousOn hcont2), hE, hdiv, sub_zero]

/-- **du Bois-Reymond with minimal regularity**: if `Λ` is continuous and spatially periodic on
the open slab, its derivative-direction coefficients `Λ(·)(derEmb_i w)` are `C¹`, and the induced
functional vanishes on every physical test, the Euler row vanishes in every admissible direction
at every point of the open fundamental box `(0,T) × (0,1)³`. -/
theorem eulerRowW_eq_zero {Λ : E4 → RJet C →L[ℝ] ℝ} (hΛc : ContinuousOn Λ (cylSlab T))
    (hΛd : ∀ i (w : FieldVal C), ContDiffOn ℝ 1 (fun y => Λ y (derEmb C i w)) (cylSlab T))
    (hΛper : ∀ n x, Λ (x + spatialShift n) = Λ x)
    (hEuler : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest left r K,
        ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, Λ x (testJet v.val x) = 0)
    {x₀ : E4} (hx₀ : x₀ 0 ∈ Ioo 0 T) (hx₀s : ∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1)
    {w : FieldVal C} (hw : IsAdmissible left w) : eulerRowW Λ x₀ w = 0 := by
  have hcontRow : ∀ w : FieldVal C, ContinuousOn (fun x => eulerRowW Λ x w) (cylSlab T) := by
    intro w
    have hpd : ∀ i, ContinuousOn (fun x => pd (fun y => Λ y (derEmb C i w)) i x) (cylSlab T) :=
      fun i => ((hΛd i w).continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply
        continuousOn_const
    exact (hΛc.clm_apply continuousOn_const).sub (continuousOn_finsetSum _ fun i _ => hpd i)
  have key : ∀ w : FieldVal C, IsAdmissible left w → ¬ 0 < eulerRowW Λ x₀ w := by
    intro w hw hpos
    set t₀ := x₀ 0 / 2
    set t₁ := (x₀ 0 + T) / 2
    have h0 : 0 < t₀ := by simp only [t₀]; linarith [hx₀.1]
    have h01 : t₀ < t₁ := by simp only [t₀, t₁]; linarith [hx₀.1, hx₀.2]
    have h1 : t₁ < T := by simp only [t₁]; linarith [hx₀.2]
    have ht : x₀ 0 ∈ Ioo t₀ t₁ := ⟨by simp only [t₀]; linarith [hx₀.1],
      by simp only [t₁]; linarith [hx₀.2]⟩
    set g : E4 → ℝ := fun x => eulerRowW Λ x w
    have hslab : x₀ ∈ cylSlab T := hx₀
    have hgc : ContinuousAt g x₀ :=
      (hcontRow w).continuousAt ((isOpen_cylSlab T).mem_nhds hslab)
    obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hgc (g x₀ / 2) (half_pos hpos)
    obtain ⟨ψ, hψs, hψp, ⟨a, b, ha, hb, hz⟩, hψn, hψ0, hψl⟩ := exists_slab_bump ht hx₀s hρ₁
    have hint := integral_bump_mul_eulerRowW hΛc hΛd hΛper hEuler h0 h01 h1 hψs hψp ha hb hz hw
    set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
    have hgpos : ∀ x ∈ Q.set, ψ x ≠ 0 → 0 < g x := by
      intro x hx hne
      have hxs := (mem_slabChart.mp hx).2
      have hd : dist x x₀ < ρ₁ := (dist_pi_lt_iff hρ₁).mpr fun j => by
        rw [Real.dist_eq]; exact hψl x hxs hne j
      have := hball hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hnn : 0 ≤ᵐ[volume.restrict Q.set] fun x => ψ x * g x := by
      refine (ae_restrict_iff' Q.isOpen.measurableSet).mpr (Eventually.of_forall fun x hx => ?_)
      by_cases hne : ψ x = 0
      · simp [hne]
      · exact mul_nonneg (hψn x) (hgpos x hx hne).le
    have hcont : ContinuousOn (fun x => ψ x * g x) (cylSlab T) :=
      hψs.continuous.continuousOn.mul (hcontRow w)
    have hpos' : 0 < ∫ x in Q.set, ψ x * g x := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_slab_of_continuousOn hcont)]
      set W := (cylSlab T ∩ (fun x => ψ x * g x) ⁻¹' Ioi 0) ∩ Q.set
      have hWo : IsOpen W :=
        (hcont.isOpen_inter_preimage (isOpen_cylSlab T) isOpen_Ioi).inter Q.isOpen
      have hx₀Q : x₀ ∈ Q.set := mem_slabChart.mpr ⟨ht, hx₀s⟩
      have hx₀W : x₀ ∈ W := ⟨⟨hslab, mul_pos hψ0 hpos⟩, hx₀Q⟩
      refine lt_of_lt_of_le (hWo.measure_pos volume ⟨x₀, hx₀W⟩) (measure_mono fun x hx => ?_)
      exact ⟨ne_of_gt hx.1.2, hx.2⟩
    have : ∫ x in Q.set, ψ x * g x = 0 := hint
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine key (-w) hw.neg ?_
    rw [eulerRowW_neg]; linarith
  · exact key w hw hgt

end Rows


/-! ### The derivative-direction coefficients do not see the spinor gradients -/

section ZeroD

variable {C : Type} [Fintype C]

/-- The jet with its spinor-gradient slots set to zero. -/
def zeroD (R : RJet C) : RJet C := RJet.mk R.e R.de R.A R.F R.H R.K R.Ψ 0 R.Ψb 0

theorem zeroD_mem_jetGL {R : RJet C} (h : R ∈ jetGL C) : zeroD R ∈ jetGL C := h

theorem πτ_derEmb (i : Fin 4) (w : FieldVal C) : πτ (derEmb C i w) = 0 := by
  simp [πτ, derEmb_apply]

/-- The total first-variation covector at a jet: first-order gravity + Yang–Mills + Higgs +
complete Dirac–Yukawa. -/
def totalCovJet {Ysec : Type} (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec)
    (R : RJet FC.C) : RJet FC.C →L[ℝ] ℝ :=
  gravCov θ R + (bosonCov θ R + diracCov FC θ R)

theorem totalCov_eq_totalCovJet {Ysec : Type} {FC : FermionCarrier Ysec}
    (θ : CoefficientBank Ysec) (L : LimitFields FC.C) (x : E4) :
    totalCov θ L x = totalCovJet FC θ (limitJet L x) := rfl

theorem diracCov_derEmb_zeroD {Ysec : Type} (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec)
    (R : RJet FC.C) (i : Fin 4) (w : FieldVal FC.C) :
    diracCov FC θ R (derEmb FC.C i w) = diracCov FC θ (zeroD R) (derEmb FC.C i w) := by
  have h1 : (zeroD R).e = R.e := rfl
  have h2 : potVar' FC θ (zeroD R) = potVar' FC θ R := rfl
  have h3 : pU FC (zeroD R) = pU FC R := rfl
  have h4 : (zeroD R).Ψb = R.Ψb := rfl
  have h5 : (zeroD R).Ψ = R.Ψ := rfl
  simp only [diracCov, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, πτ_derEmb,
    map_zero, h1, h2, h3, h4, h5]

/-- **The derivative-direction coefficients of the total covector do not depend on the spinor
gradients.** -/
theorem totalCovJet_derEmb_zeroD {Ysec : Type} (FC : FermionCarrier Ysec)
    (θ : CoefficientBank Ysec) (R : RJet FC.C) (i : Fin 4) (w : FieldVal FC.C) :
    totalCovJet FC θ R (derEmb FC.C i w) = totalCovJet FC θ (zeroD R) (derEmb FC.C i w) := by
  have he : (zeroD R).e = R.e := rfl
  have hde : (zeroD R).de = R.de := rfl
  have hA : (zeroD R).A = R.A := rfl
  have hF : (zeroD R).F = R.F := rfl
  have hH : (zeroD R).H = R.H := rfl
  have hK : (zeroD R).K = R.K := rfl
  have h1 : gravCov θ (zeroD R) = gravCov θ R := by simp only [gravCov, he, hde]
  have h2 : bosonCov θ (zeroD R) = bosonCov θ R := by simp only [bosonCov, he, hA, hF, hH, hK]
  simp only [totalCovJet, ContinuousLinearMap.add_apply, h1, h2]
  rw [diracCov_derEmb_zeroD]

/-- The total covector is `C^n` on the jet chart. -/
theorem contDiffOn_totalCovJet {Ysec : Type} (FC : FermionCarrier Ysec)
    (θ : CoefficientBank Ysec) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun R => totalCovJet FC θ R) (jetGL FC.C) := by
  have g := CovSmooth.contDiffOn_gravCov (C := FC.C) (n := n) θ
  have b := CovSmooth.contDiffOn_bosonCov (C := FC.C) (n := n) θ
  have d := CovSmooth.contDiffOn_diracCov (n := n) FC θ
  have bd := b.add d
  exact g.add bd

end ZeroD

/-! ### Classical fields on the slab -/

section Classical

variable {T : ℝ} {C : Type} [Fintype C]

/-- **Classical regularity on the open slab**: bosons `(e, A, H)` of class `C²`, spinors of class
`C¹`, nondegenerate coframe, spatial periodicity (fields on `(0,T) × 𝕋³`). -/
structure ClassicalSlab (T : ℝ) (z : FieldTuple C) : Prop where
  e : ContDiffOn ℝ 2 z.e (cylSlab T)
  A : ContDiffOn ℝ 2 z.A (cylSlab T)
  H : ContDiffOn ℝ 2 z.H (cylSlab T)
  Ψ : ContDiffOn ℝ 1 z.Ψ (cylSlab T)
  Ψb : ContDiffOn ℝ 1 z.Ψb (cylSlab T)
  gl : ∀ x ∈ cylSlab T, z.e x ∈ coframeGL
  per_e : ∀ n x, z.e (x + spatialShift n) = z.e x
  per_A : ∀ n x, z.A (x + spatialShift n) = z.A x
  per_H : ∀ n x, z.H (x + spatialShift n) = z.H x
  per_Ψ : ∀ n x, z.Ψ (x + spatialShift n) = z.Ψ x
  per_Ψb : ∀ n x, z.Ψb (x + spatialShift n) = z.Ψb x

theorem contDiffOn_pd_slab {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    {n : WithTop ℕ∞} (hf : ContDiffOn ℝ (n + 1) f (cylSlab T)) (i : Fin 4) :
    ContDiffOn ℝ n (fun x => pd f i x) (cylSlab T) :=
  (hf.fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply contDiffOn_const

theorem contDiffOn_apply' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] {f : E4 → ι → F} {n : WithTop ℕ∞} {s : Set E4}
    (hf : ContDiffOn ℝ n f s) (ν : ι) : ContDiffOn ℝ n (fun y => f y ν) s :=
  (contDiff_apply ℝ F ν).comp_contDiffOn hf

theorem contDiffOn_comm {f g : E4 → LieFibre} {s : Set E4} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun x => comm (f x) (g x)) s := by
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  have hfij : ∀ a b, ContDiffOn ℝ n (fun x => f x a b) s := fun a b =>
    contDiffOn_apply' (contDiffOn_apply' hf a) b
  have hgij : ∀ a b, ContDiffOn ℝ n (fun x => g x a b) s := fun a b =>
    contDiffOn_apply' (contDiffOn_apply' hg a) b
  simp only [comm, mmul, Pi.sub_apply]
  exact (ContDiffOn.sum fun k _ => (hfij i k).mul (hgij k j)).sub
    (ContDiffOn.sum fun k _ => (hgij i k).mul (hfij k j))

theorem contDiffOn_higgsAct {f : E4 → LieFibre} {g : E4 → HiggsFibre} {s : Set E4}
    {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun x => higgsAct (f x) (g x)) s := by
  refine contDiffOn_pi.mpr fun i => ?_
  simp only [higgsAct]
  exact ContDiffOn.sum fun j _ =>
    (contDiffOn_apply' (contDiffOn_apply' hf _) _).mul (contDiffOn_apply' hg j)

theorem contDiffOn_curvatureF' {A : E4 → ConnFibre} (hA : ContDiffOn ℝ 2 A (cylSlab T)) :
    ContDiffOn ℝ 1 (fun x => curvatureF A x) (cylSlab T) := by
  refine contDiffOn_pi.mpr fun μ => contDiffOn_pi.mpr fun ν => ?_
  unfold curvatureF
  have h1 : ContDiffOn ℝ 1 A (cylSlab T) := hA.of_le (by norm_num)
  exact ((contDiffOn_pd_slab (n := 1) (contDiffOn_apply' hA ν) μ).sub
    (contDiffOn_pd_slab (n := 1) (contDiffOn_apply' hA μ) ν)).add
    (contDiffOn_comm (contDiffOn_apply' h1 μ) (contDiffOn_apply' h1 ν))

theorem contDiffOn_covDerivHiggs' {A : E4 → ConnFibre} {H : E4 → HiggsFibre}
    (hA : ContDiffOn ℝ 2 A (cylSlab T)) (hH : ContDiffOn ℝ 2 H (cylSlab T)) :
    ContDiffOn ℝ 1 (fun x => covDerivHiggs A H x) (cylSlab T) := by
  refine contDiffOn_pi.mpr fun μ => ?_
  unfold covDerivHiggs
  exact (contDiffOn_pd_slab (n := 1) hH μ).add
    (contDiffOn_higgsAct (contDiffOn_apply' (hA.of_le (by norm_num)) μ) (hH.of_le (by norm_num)))

theorem contDiffOn_pd_family {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    {n : WithTop ℕ∞} (hf : ContDiffOn ℝ (n + 1) f (cylSlab T)) :
    ContDiffOn ℝ n (fun x => fun i => pd f i x) (cylSlab T) :=
  contDiffOn_pi.mpr fun i => contDiffOn_pd_slab hf i

/-- The jet of classical fields is continuous on the open slab. -/
theorem continuousOn_redJet_classical {z : FieldTuple C} (hz : ClassicalSlab T z) :
    ContinuousOn (redJet z) (cylSlab T) := by
  have hF := (contDiffOn_curvatureF' hz.A).continuousOn
  have hK := (contDiffOn_covDerivHiggs' hz.A hz.H).continuousOn
  have pe := (contDiffOn_pd_family (n := 1) hz.e).continuousOn
  have pΨ := (contDiffOn_pd_family (n := 0) hz.Ψ).continuousOn
  have pΨb := (contDiffOn_pd_family (n := 0) hz.Ψb).continuousOn
  unfold redJet RJet.mk
  exact hz.e.continuousOn.prodMk (pe.prodMk (hz.A.continuousOn.prodMk (hF.prodMk
    (hz.H.continuousOn.prodMk (hK.prodMk (hz.Ψ.continuousOn.prodMk (pΨ.prodMk
      (hz.Ψb.continuousOn.prodMk pΨb))))))))

/-- The jet with zeroed spinor gradients is `C¹` on the open slab for classical fields. -/
theorem contDiffOn_zeroD_redJet {z : FieldTuple C} (hz : ClassicalSlab T z) :
    ContDiffOn ℝ 1 (fun x => zeroD (redJet z x)) (cylSlab T) := by
  have hF := contDiffOn_curvatureF' hz.A
  have hK := contDiffOn_covDerivHiggs' hz.A hz.H
  have pe := contDiffOn_pd_family (n := 1) hz.e
  have h0 : ContDiffOn ℝ 1 (fun _ : E4 => (0 : Fin 4 → SpinorFibre C)) (cylSlab T) :=
    contDiffOn_const
  unfold zeroD redJet RJet.mk
  exact (hz.e.of_le (by norm_num)).prodMk (pe.prodMk ((hz.A.of_le (by norm_num)).prodMk
    (hF.prodMk ((hz.H.of_le (by norm_num)).prodMk (hK.prodMk (hz.Ψ.prodMk (h0.prodMk
      (hz.Ψb.prodMk h0))))))))

theorem redJet_mem_jetGL {z : FieldTuple C} (hz : ClassicalSlab T z) {x : E4}
    (hx : x ∈ cylSlab T) : redJet z x ∈ jetGL C := hz.gl x hx

theorem redJet_periodic {z : FieldTuple C} (hz : ClassicalSlab T z) (n : Fin 3 → ℤ) (x : E4) :
    redJet z (x + spatialShift n) = redJet z x := by
  have pe := pd_periodic (hz.per_e n)
  have pA := pd_periodic (hz.per_A n)
  have pH := pd_periodic (hz.per_H n)
  have pΨ := pd_periodic (hz.per_Ψ n)
  have pΨb := pd_periodic (hz.per_Ψb n)
  have pAν : ∀ ν i y, pd (fun y => z.A y ν) i (y + spatialShift n) = pd (fun y => z.A y ν) i y :=
    fun ν => pd_periodic (fun y => by rw [hz.per_A n y])
  have hF : curvatureF z.A (x + spatialShift n) = curvatureF z.A x := by
    funext μ ν; simp only [curvatureF, pAν, hz.per_A n]
  have hK : covDerivHiggs z.A z.H (x + spatialShift n) = covDerivHiggs z.A z.H x := by
    funext μ; simp only [covDerivHiggs, pH, hz.per_A n, hz.per_H n]
  simp only [redJet, hF, hK, pe, pΨ, pΨb, hz.per_e n, hz.per_A n, hz.per_H n, hz.per_Ψ n,
    hz.per_Ψb n]

end Classical


/-! ### Classical derivatives are the weak derivatives on the slab charts -/

section Weak

variable {T : ℝ}

/-- A smooth time cutoff equal to `1` on `[t₀, t₁]` and supported in a compact subinterval of
`(0, T)`. -/
theorem exists_time_cutoff {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t ∈ Icc t₀ t₁, ρ t = 1) ∧
      ∃ a b, 0 < a ∧ b < T ∧ ∀ t, t ∉ Icc a b → ρ t = 0 := by
  set δ := min t₀ (T - t₁) / 2
  have hδ : 0 < δ := by have := lt_min h0 (sub_pos.mpr h1); positivity
  have hδ1 : δ < t₀ := by
    have := min_le_left t₀ (T - t₁); simp only [δ]; linarith
  have hδ2 : δ < T - t₁ := by
    have := min_le_right t₀ (T - t₁); simp only [δ]; linarith [sub_pos.mpr h1]
  let β : ContDiffBump ((t₀ + t₁) / 2) := ⟨(t₁ - t₀) / 2, (t₁ - t₀) / 2 + δ,
    by linarith, by linarith⟩
  refine ⟨β, β.contDiff, fun t ht => β.one_of_mem_closedBall ?_, t₀ - δ, t₁ + δ, by linarith,
    by linarith, fun t ht => β.zero_of_le_dist ?_⟩
  · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> simp only [β] <;> linarith [ht.1, ht.2]
  · rw [Real.dist_eq]
    simp only [mem_Icc, not_and_or, not_le] at ht
    show (t₁ - t₀) / 2 + δ ≤ |t - (t₀ + t₁) / 2|
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- **Classical derivatives are weak derivatives on the slab charts**: a `C¹` function on the open
slab has its classical partial derivatives as weak partial derivatives on every slab chart. -/
theorem hasWeakPartial_slab {u : E4 → ℂ} (hu : ContDiffOn ℝ 1 u (cylSlab T)) {t₀ t₁ : ℝ}
    (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) (i : Fin 4) :
    HasWeakPartial (slabChart t₀ t₁ h0 h01 h1 (T := T)).set i u (pd u i) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  obtain ⟨ρ, hρ, hρ1, a, b, ha, hb, hρ0⟩ := exists_time_cutoff h0 h01 h1
  set v : E4 → ℂ := fun x => ((ρ (x 0) : ℝ) : ℂ) * u x
  have hρc : ContDiff ℝ 1 fun x : E4 => ((ρ (x 0) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((hρ.of_le (by simp)).comp (contDiff_apply ℝ ℝ 0))
  have hv : ContDiff ℝ 1 v := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x 0 ∈ Ioo 0 T
    · exact hρc.contDiffAt.mul (hu.contDiffAt ((isOpen_cylSlab T).mem_nhds hx))
    · have hopen : IsOpen {x' : E4 | x' 0 ∉ Icc a b} :=
        (isClosed_Icc.preimage (continuous_apply 0)).isOpen_compl
      have hxm : x 0 ∉ Icc a b := fun h => hx ⟨ha.trans_le h.1, h.2.trans_lt hb⟩
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hopen.mem_nhds hxm) fun x' hx' => ?_)
      simp [v, hρ0 _ hx']
  have hw := SobolevOpen.hasWeakPartial_of_contDiff Q.set hv i
  intro φ hφ
  have hQ : ∀ x ∈ Q.set, v =ᶠ[𝓝 x] u := fun x hx =>
    Filter.eventuallyEq_of_mem (Q.isOpen.mem_nhds hx) fun y hy => by
      simp [v, hρ1 _ (Ioo_subset_Icc_self (mem_slabChart.mp hy).1)]
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * u x) = fun x => ((pd φ i x : ℝ) : ℂ) * v x := by
    funext x
    by_cases hx : x ∈ Q.set
    · rw [(hQ x hx).self_of_nhds]
    · have : pd φ i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hφ.subset (SobolevOpen.tsupport_pd_subset φ i h)))
      simp [this]
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * pd u i x) = fun x => ((φ x : ℝ) : ℂ) * pd v i x := by
    funext x
    by_cases hx : x ∈ Q.set
    · rw [show pd v i x = pd u i x by unfold SobolevOpen.pd; rw [(hQ x hx).fderiv_eq]]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))
      simp [this]
  rw [e1, e2]
  exact hw φ hφ

theorem contDiffOn_comp_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E4 → F} {n : WithTop ℕ∞} {s : Set E4}
    (hf : ContDiffOn ℝ n f s) (ℓ : F →L[ℝ] G) : ContDiffOn ℝ n (fun x => ℓ (f x)) s :=
  ℓ.contDiff.comp_contDiffOn hf

theorem pd_comp_clm_slab {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E4 → F} (hf : ContDiffOn ℝ 1 f (cylSlab T))
    (ℓ : F →L[ℝ] G) {x : E4} (hx : x ∈ cylSlab T) (i : Fin 4) :
    pd (fun y => ℓ (f y)) i x = ℓ (pd f i x) :=
  pd_clm_comp ((hf.contDiffAt ((isOpen_cylSlab T).mem_nhds hx)).differentiableAt one_ne_zero) ℓ i

theorem locallyIntegrableOn_of_memLp_chart {Q : ChartBox T} {g : E4 → ℂ}
    (hg : MemLp g 2 (volume.restrict Q.set)) : LocallyIntegrableOn g Q.set :=
  IntegrableOn.locallyIntegrableOn (show IntegrableOn g Q.set volume from
    hg.integrable (by norm_num))

theorem locallyIntegrableOn_of_continuousOn_slab {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁}
    {h1 : t₁ < T} {g : E4 → ℂ} (hg : ContinuousOn g (cylSlab T)) :
    LocallyIntegrableOn g (slabChart t₀ t₁ h0 h01 h1 (T := T)).set := by
  have hcl := isCompact_closure_slabChart h0 h01 h1 (T := T)
  have hsub : closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  exact (((hg.mono hsub).integrableOn_compact hcl).mono_set subset_closure).locallyIntegrableOn

end Weak


/-! ### The packets of a reduced limit with classical fields -/

section Packets

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- The field tuple `(e, A, H, Ψ, Ψ̄)` of limit fields. -/
def limitTuple (L : LimitFields C) : FieldTuple C := FieldTuple.mk L.e L.A L.H L.Ψ L.Ψb

variable {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T}
  {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
  {θ₀ : CoefficientBank Ysec}

theorem continuousOn_pd_of_C1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E4 → F} (hu : ContDiffOn ℝ 1 u (cylSlab T)) (i : Fin 4) :
    ContinuousOn (fun x => pd u i x) (cylSlab T) :=
  (hu.continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply continuousOn_const

/-- The weak coframe gradient of the limit is the classical one a.e. on the chart. -/
theorem de_ae_eq (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) z θ L θ₀)
    (hz : ClassicalSlab T (limitTuple L)) (i : Fin 4) (c : Fin 4 × Fin 4) :
    ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.de x i c = ((pd L.e i x c.1 c.2 : ℝ) : ℂ) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  set ℓ : CoframeFibre →L[ℝ] ℂ := Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) c.2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) c.1))
  have he : ContDiffOn ℝ 1 L.e (cylSlab T) := hz.e.of_le (by norm_num)
  have hu : ContDiffOn ℝ 1 (fun x => ℓ (L.e x)) (cylSlab T) := contDiffOn_comp_clm he ℓ
  have hcl := hasWeakPartial_slab hu h0 h01 h1 i
  have hw : HasWeakPartial Q.set i (fun x => ℓ (L.e x)) (fun x => L.de x i c) :=
    (hRC.coframe_mem c).weak i
  have hae := hw.ae_eq Q.isOpen hcl
    (locallyIntegrableOn_of_memLp_chart ((hRC.coframe_mem c).memLp_grad i))
    (locallyIntegrableOn_of_continuousOn_slab (continuousOn_pd_of_C1 hu i))
  filter_upwards [hae] with x hx hxQ
  have hxs : x ∈ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1) (subset_closure hxQ)
  rw [hx hxQ, pd_comp_clm_slab he ℓ hxs i]
  rfl

theorem spinor_ae_eq {Ψ : E4 → SpinorFibre C} {dΨ : E4 → Fin 4 → Fin 4 × C → ℂ}
    (hmem : MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (spinorC Ψ) dΨ)
    (hΨ : ContDiffOn ℝ 1 Ψ (cylSlab T)) (i : Fin 4) (c : Fin 4 × C) :
    ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set → dΨ x i c = pd Ψ i x c.1 c.2 := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  set ℓ : SpinorFibre C →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : C => ℂ) c.2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => C → ℂ) c.1)
  have hu : ContDiffOn ℝ 1 (fun x => ℓ (Ψ x)) (cylSlab T) := contDiffOn_comp_clm hΨ ℓ
  have hcl := hasWeakPartial_slab hu h0 h01 h1 i
  have hw : HasWeakPartial Q.set i (fun x => ℓ (Ψ x)) (fun x => dΨ x i c) := (hmem c).weak i
  have hae := hw.ae_eq Q.isOpen hcl (locallyIntegrableOn_of_memLp_chart ((hmem c).memLp_grad i))
    (locallyIntegrableOn_of_continuousOn_slab (continuousOn_pd_of_C1 hu i))
  filter_upwards [hae] with x hx hxQ
  have hxs : x ∈ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1) (subset_closure hxQ)
  rw [hx hxQ, pd_comp_clm_slab hΨ ℓ hxs i]
  rfl

theorem integrable_test_mul {Ω : Set E4} {φ : E4 → ℝ} (hφ : IsTest Ω φ) {g : E4 → ℂ}
    (hg : LocallyIntegrableOn g Ω) : Integrable fun x => ((φ x : ℝ) : ℂ) * g x :=
  SobolevOpen.integrable_mul_of_locallyIntegrableOn hg
    (Complex.continuous_ofReal.comp hφ.smooth.continuous)
    (hφ.compact.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero _).trans hφ.subset)

theorem integrable_pdtest_mul {Ω : Set E4} {φ : E4 → ℝ} (hφ : IsTest Ω φ) (μ : Fin 4)
    {g : E4 → ℂ} (hg : LocallyIntegrableOn g Ω) :
    Integrable fun x => ((pd φ μ x : ℝ) : ℂ) * g x :=
  SobolevOpen.integrable_mul_of_locallyIntegrableOn hg
    (Complex.continuous_ofReal.comp (SobolevOpen.continuous_pd (hφ.smooth.of_le (by simp)) μ))
    ((SobolevOpen.hasCompactSupport_pd hφ.compact μ).comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero _).trans
      ((SobolevOpen.tsupport_pd_subset φ μ).trans hφ.subset))

/-- The weak curvature of the limit is the classical curvature a.e. on the chart. -/
theorem curv_ae_eq (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) z θ L θ₀)
    (hz : ClassicalSlab T (limitTuple L)) (μ ν : Fin 4) (i j : Fin 5) :
    ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.F x μ ν i j = curvatureF L.A x μ ν i j := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hA : ContDiffOn ℝ 1 L.A (cylSlab T) := hz.A.of_le (by norm_num)
  set ℓ : Fin 4 → ConnFibre →L[ℝ] ℂ := fun κ =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => Fin 5 → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) κ))
  have hu : ∀ κ, ContDiffOn ℝ 1 (fun x => ℓ κ (L.A x)) (cylSlab T) := fun κ =>
    contDiffOn_comp_clm hA (ℓ κ)
  have hwν := hasWeakPartial_slab (hu ν) h0 h01 h1 μ
  have hwμ := hasWeakPartial_slab (hu μ) h0 h01 h1 ν
  have hlocA : ∀ κ, LocallyIntegrableOn (fun x => ℓ κ (L.A x)) Q.set := fun κ =>
    locallyIntegrableOn_of_continuousOn_slab (hu κ).continuousOn
  have hlocP : ∀ κ κ', LocallyIntegrableOn (fun x => pd (fun y => ℓ κ (L.A y)) κ' x) Q.set :=
    fun κ κ' => locallyIntegrableOn_of_continuousOn_slab (continuousOn_pd_of_C1 (hu κ) κ')
  have hFm : MemLp (fun x => L.F x μ ν i j) 2 Q.μ :=
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp hRC.curv_mem μ) ν) i) j
  have hcomm : ContinuousOn (fun x => comm (L.A x μ) (L.A x ν) i j) (cylSlab T) := by
    have := (contDiffOn_comm (contDiffOn_apply' hA μ) (contDiffOn_apply' hA ν)).continuousOn
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn this)
  have hv : LocallyIntegrableOn (fun x => L.F x μ ν i j - comm (L.A x μ) (L.A x ν) i j) Q.set :=
    (locallyIntegrableOn_of_memLp_chart hFm).sub (locallyIntegrableOn_of_continuousOn_slab hcomm)
  have hw : LocallyIntegrableOn (fun x => pd (fun y => ℓ ν (L.A y)) μ x -
      pd (fun y => ℓ μ (L.A y)) ν x) Q.set := (hlocP ν μ).sub (hlocP μ ν)
  have key := SobolevOpen.ae_eq_of_integral_test Q.isOpen hv hw (fun φ hφ => by
    have hc := hRC.curv_weak μ ν i j φ hφ
    have e1 := hwν φ hφ
    have e2 := hwμ φ hφ
    have i1 := integrable_pdtest_mul hφ μ (hlocA ν)
    have i2 := integrable_pdtest_mul hφ ν (hlocA μ)
    have i3 := integrable_test_mul hφ (hlocP ν μ)
    have i4 := integrable_test_mul hφ (hlocP μ ν)
    have e3 : ∫ x, ((φ x : ℝ) : ℂ) * (pd (fun y => ℓ ν (L.A y)) μ x -
        pd (fun y => ℓ μ (L.A y)) ν x) = (∫ x, ((φ x : ℝ) : ℂ) * pd (fun y => ℓ ν (L.A y)) μ x) -
          ∫ x, ((φ x : ℝ) : ℂ) * pd (fun y => ℓ μ (L.A y)) ν x := by
      rw [← integral_sub i3 i4]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have e4 : ∫ x, (((pd φ μ x : ℝ) : ℂ) * L.A x ν i j - ((pd φ ν x : ℝ) : ℂ) * L.A x μ i j) =
        (∫ x, ((pd φ μ x : ℝ) : ℂ) * ℓ ν (L.A x)) - ∫ x, ((pd φ ν x : ℝ) : ℂ) * ℓ μ (L.A x) := by
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [ℓ])
    have e1' : ∫ x, ((pd φ μ x : ℝ) : ℂ) * ℓ ν (L.A x) =
        -∫ x, ((φ x : ℝ) : ℂ) * pd (fun y => ℓ ν (L.A y)) μ x := e1
    have e2' : ∫ x, ((pd φ ν x : ℝ) : ℂ) * ℓ μ (L.A x) =
        -∫ x, ((φ x : ℝ) : ℂ) * pd (fun y => ℓ μ (L.A y)) ν x := e2
    rw [hc, e4, e1', e2', e3]
    ring)
  filter_upwards [key] with x hx hxQ
  have hxs : x ∈ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1) (subset_closure hxQ)
  have h := hx hxQ
  have p1 : pd (fun y => ℓ ν (L.A y)) μ x = pd (fun y => L.A y ν) μ x i j := by
    have := pd_comp_clm_slab hA (ℓ ν) hxs μ
    have h2 : pd (fun y => L.A y ν) μ x =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν) (pd L.A μ x) :=
      pd_comp_clm_slab hA (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν)
        hxs μ
    rw [this, h2]
    simp [ℓ]
  have p2 : pd (fun y => ℓ μ (L.A y)) ν x = pd (fun y => L.A y μ) ν x i j := by
    have := pd_comp_clm_slab hA (ℓ μ) hxs ν
    have h2 : pd (fun y => L.A y μ) ν x =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) μ) (pd L.A ν x) :=
      pd_comp_clm_slab hA (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) μ)
        hxs ν
    rw [this, h2]
    simp [ℓ]
  rw [p1, p2] at h
  simp only [curvatureF, Pi.add_apply, Pi.sub_apply]
  linear_combination h

/-- The weak covariant Higgs gradient of the limit is the classical one a.e. on the chart. -/
theorem covgrad_ae_eq (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) z θ L θ₀)
    (hz : ClassicalSlab T (limitTuple L)) (μ : Fin 4) (i : Fin 2) :
    ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.K x μ i = covDerivHiggs L.A L.H x μ i := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hA : ContDiffOn ℝ 1 L.A (cylSlab T) := hz.A.of_le (by norm_num)
  have hH : ContDiffOn ℝ 1 L.H (cylSlab T) := hz.H.of_le (by norm_num)
  set ℓ : HiggsFibre →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) i
  have hu : ContDiffOn ℝ 1 (fun x => ℓ (L.H x)) (cylSlab T) := contDiffOn_comp_clm hH ℓ
  have hwH := hasWeakPartial_slab hu h0 h01 h1 μ
  have hlocH : LocallyIntegrableOn (fun x => ℓ (L.H x)) Q.set :=
    locallyIntegrableOn_of_continuousOn_slab hu.continuousOn
  have hlocP : LocallyIntegrableOn (fun x => pd (fun y => ℓ (L.H y)) μ x) Q.set :=
    locallyIntegrableOn_of_continuousOn_slab (continuousOn_pd_of_C1 hu μ)
  have hKm : MemLp (fun x => L.K x μ i) 2 Q.μ :=
    memLp_pi_iff.mp (memLp_pi_iff.mp hRC.covgrad_mem μ) i
  have hact : ContinuousOn (fun x => higgsAct (L.A x μ) (L.H x) i) (cylSlab T) :=
    (continuous_apply i).comp_continuousOn
      (contDiffOn_higgsAct (contDiffOn_apply' hA μ) hH).continuousOn
  have hv : LocallyIntegrableOn (fun x => L.K x μ i - higgsAct (L.A x μ) (L.H x) i) Q.set :=
    (locallyIntegrableOn_of_memLp_chart hKm).sub (locallyIntegrableOn_of_continuousOn_slab hact)
  have key := SobolevOpen.ae_eq_of_integral_test Q.isOpen hv hlocP (fun φ hφ => by
    have hc := hRC.covgrad_weak μ i φ hφ
    have e1 := hwH φ hφ
    have e1' : (∫ x, ((pd φ μ x : ℝ) : ℂ) * L.H x i) =
        -∫ x, ((φ x : ℝ) : ℂ) * pd (fun y => ℓ (L.H y)) μ x := e1
    rw [hc, e1', neg_neg])
  filter_upwards [key] with x hx hxQ
  have hxs : x ∈ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1) (subset_closure hxQ)
  have h := hx hxQ
  have p1 : pd (fun y => ℓ (L.H y)) μ x = pd L.H μ x i := pd_comp_clm_slab hH ℓ hxs μ
  rw [p1] at h
  simp only [covDerivHiggs, Pi.add_apply]
  linear_combination h

/-- **The packets of a reduced limit with classical fields are its classical derivatives**: on
every slab chart the limit jet equals the classical jet almost everywhere. -/
theorem limitJet_ae_eq_redJet (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) z θ L θ₀)
    (hz : ClassicalSlab T (limitTuple L)) :
    ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      limitJet L x = redJet (limitTuple L) x := by
  have hde : ∀ᵐ x, ∀ i c, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.de x i c = ((pd L.e i x c.1 c.2 : ℝ) : ℂ) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun c => de_ae_eq hRC hz i c
  have hF : ∀ᵐ x, ∀ μ ν i j, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.F x μ ν i j = curvatureF L.A x μ ν i j :=
    ae_all_iff.mpr fun μ => ae_all_iff.mpr fun ν => ae_all_iff.mpr fun i =>
      ae_all_iff.mpr fun j => curv_ae_eq hRC hz μ ν i j
  have hK : ∀ᵐ x, ∀ μ i, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.K x μ i = covDerivHiggs L.A L.H x μ i :=
    ae_all_iff.mpr fun μ => ae_all_iff.mpr fun i => covgrad_ae_eq hRC hz μ i
  have hΨ : ∀ᵐ x, ∀ i c, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.dΨ x i c = pd L.Ψ i x c.1 c.2 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun c => spinor_ae_eq hRC.spinor_weak.2.1 hz.Ψ i c
  have hΨb : ∀ᵐ x, ∀ i c, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      L.dΨb x i c = pd L.Ψb i x c.1 c.2 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun c =>
      spinor_ae_eq hRC.cospinor_weak.2.1 hz.Ψb i c
  filter_upwards [hde, hF, hK, hΨ, hΨb] with x xde xF xK xΨ xΨb hxQ
  refine RJet.ext' rfl ?_ rfl ?_ rfl ?_ rfl ?_ rfl ?_
  · funext i a μ
    simp only [limitJet, redJet, RJet.mk_de, toJet, reJet, limitTuple, FieldTuple.mk, FieldTuple.e]
    rw [xde i (a, μ) hxQ, Complex.ofReal_re]
  · funext μ ν i j
    simp only [limitJet, redJet, RJet.mk_F, limitTuple, FieldTuple.mk, FieldTuple.A]
    exact xF μ ν i j hxQ
  · funext μ i
    simp only [limitJet, redJet, RJet.mk_K, limitTuple, FieldTuple.mk, FieldTuple.A, FieldTuple.H]
    exact xK μ i hxQ
  · funext i s c
    simp only [limitJet, redJet, RJet.mk_dΨ, limitTuple, FieldTuple.mk, FieldTuple.Ψ]
    exact xΨ i (s, c) hxQ
  · funext i s c
    simp only [limitJet, redJet, RJet.mk_dΨb, limitTuple, FieldTuple.mk, FieldTuple.Ψb]
    exact xΨb i (s, c) hxQ

end Packets


/-! ### The regularity upgrade for classical limit fields -/

section Upgrade

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- The classical covector field of classical fields. -/
def classicalCov (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) (z : FieldTuple FC.C)
    (x : E4) : RJet FC.C →L[ℝ] ℝ :=
  totalCovJet FC θ (redJet z x)

theorem continuousOn_classicalCov (θ : CoefficientBank Ysec) {z : FieldTuple FC.C}
    (hz : ClassicalSlab T z) : ContinuousOn (classicalCov FC θ z) (cylSlab T) :=
  (contDiffOn_totalCovJet FC θ (n := 0)).continuousOn.comp (continuousOn_redJet_classical hz)
    fun _ hx => redJet_mem_jetGL hz hx

theorem contDiffOn_classicalCov_derEmb (θ : CoefficientBank Ysec) {z : FieldTuple FC.C}
    (hz : ClassicalSlab T z) (i : Fin 4) (w : FieldVal FC.C) :
    ContDiffOn ℝ 1 (fun y => classicalCov FC θ z y (derEmb FC.C i w)) (cylSlab T) := by
  have h := ((contDiffOn_totalCovJet FC θ (n := 1)).comp (contDiffOn_zeroD_redJet hz)
    fun _ hx => zeroD_mem_jetGL (redJet_mem_jetGL hz hx)).clm_apply
      (contDiffOn_const (c := derEmb FC.C i w))
  refine h.congr fun y _ => ?_
  simp only [classicalCov, Function.comp_apply]
  exact totalCovJet_derEmb_zeroD FC θ (redJet z y) i w

theorem classicalCov_periodic (θ : CoefficientBank Ysec) {z : FieldTuple FC.C}
    (hz : ClassicalSlab T z) (n : Fin 3 → ℤ) (x : E4) :
    classicalCov FC θ z (x + spatialShift n) = classicalCov FC θ z x := by
  simp only [classicalCov, redJet_periodic hz n x]

/-- The distributional identity of the limit transfers to the classical covector field. -/
theorem integral_classicalCov_eq_zero {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hz : ClassicalSlab T (limitTuple L)) {r : ℕ} {K : CylRegion T} {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T)
    (hae : ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
      limitJet L x = redJet (limitTuple L) x)
    (v : CrTest FC.left r K)
    (he : gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
      smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v = 0) :
    ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
      classicalCov FC θ₀ (limitTuple L) x (testJet v.val x) = 0 := by
  have hJ := continuousOn_redJet_classical hz
  have hgl : MapsTo (redJet (limitTuple L)) (cylSlab T) (jetGL FC.C) := fun _ hx => redJet_mem_jetGL hz hx
  have cg : ContinuousOn (fun x => gravCov θ₀ (redJet (limitTuple L) x)) (cylSlab T) :=
    (CovSmooth.contDiffOn_gravCov (C := FC.C) (n := 0) θ₀).continuousOn.comp hJ hgl
  have cb : ContinuousOn (fun x => bosonCov θ₀ (redJet (limitTuple L) x)) (cylSlab T) :=
    (CovSmooth.contDiffOn_bosonCov (C := FC.C) (n := 0) θ₀).continuousOn.comp hJ hgl
  have cd : ContinuousOn (fun x => diracCov FC θ₀ (redJet (limitTuple L) x)) (cylSlab T) :=
    (CovSmooth.contDiffOn_diracCov (n := 0) FC θ₀).continuousOn.comp hJ hgl
  have hT' : ContinuousOn (testJet v.val) (cylSlab T) := (continuous_testJet v).continuousOn
  have sg : ContinuousOn (fun x => gravCov θ₀ (redJet (limitTuple L) x) (testJet v.val x)) (cylSlab T) :=
    cg.clm_apply hT'
  have sb : ContinuousOn (fun x => bosonCov θ₀ (redJet (limitTuple L) x) (testJet v.val x)) (cylSlab T) :=
    cb.clm_apply hT'
  have sd : ContinuousOn (fun x => diracCov FC θ₀ (redJet (limitTuple L) x) (testJet v.val x)) (cylSlab T) :=
    cd.clm_apply hT'
  have i1 := integrableOn_slab_of_continuousOn (h0 := h0) (h01 := h01) (h1 := h1) sg
  have i2 := integrableOn_slab_of_continuousOn (h0 := h0) (h01 := h01) (h1 := h1) (sb.add sd)
  have c1 : ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, gravCov θ₀ (limitJet L x) (testJet v.val x) =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, gravCov θ₀ (redJet (limitTuple L) x) (testJet v.val x) := by
    refine setIntegral_congr_ae (slabChart t₀ t₁ h0 h01 h1 (T := T)).isOpen.measurableSet ?_
    filter_upwards [hae] with x hx hxQ
    rw [hx hxQ]
  have c2 : ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, (bosonCov θ₀ (limitJet L x) + diracCov FC θ₀ (limitJet L x))
      (testJet v.val x) = ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, (bosonCov θ₀ (redJet (limitTuple L) x) (testJet v.val x) +
        diracCov FC θ₀ (redJet (limitTuple L) x) (testJet v.val x)) := by
    refine setIntegral_congr_ae (slabChart t₀ t₁ h0 h01 h1 (T := T)).isOpen.measurableSet ?_
    filter_upwards [hae] with x hx hxQ
    rw [hx hxQ, ContinuousLinearMap.add_apply]
  have he' : (∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, gravCov θ₀ (limitJet L x) (testJet v.val x)) +
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, (bosonCov θ₀ (limitJet L x) + diracCov FC θ₀ (limitJet L x))
        (testJet v.val x) = 0 := he
  rw [c1, c2] at he'
  have e : ∀ x, classicalCov FC θ₀ (limitTuple L) x (testJet v.val x) =
      gravCov θ₀ (redJet (limitTuple L) x) (testJet v.val x) +
        (bosonCov θ₀ (redJet (limitTuple L) x) (testJet v.val x) +
          diracCov FC θ₀ (redJet (limitTuple L) x) (testJet v.val x)) := fun x => by
    simp only [classicalCov, totalCovJet, ContinuousLinearMap.add_apply]
  simp only [e]
  have hadd := integral_add i1 i2
  simp only [Pi.add_apply] at hadd
  rw [hadd]
  exact he'

/-- **`cor:strong-solution-upgrade` for classical limit fields.**  Under the hypotheses of
`thm:reduced-closure`, every cutoff subsequence has a further subsequence with a limit `(L, θ₀)`
in the reduced topology such that, if the limit fields are classical (`ClassicalSlab`: bosons
`C²`, spinors `C¹`, nondegenerate coframe, on the open slab), then (i) on every slab chart the
packets of the limit are its classical derivatives a.e.; (ii) the distributional Euler identities
hold pointwise: every Euler row of the classical first-variation covector field vanishes at every
point of the fundamental box `(0,T) × (0,1)³` in every admissible direction (symmetric metric,
`smLie` gauge, chiral spinor variations) — the second-order bosonic (Einstein, Yang–Mills,
Higgs) rows and the first-order spinor rows. -/
theorem strong_solution_upgrade_classical (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀) ∧
      (ClassicalSlab T (limitTuple L) →
        (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
          ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
            limitJet L x = redJet (limitTuple L) x) ∧
        ∀ x₀ : E4, x₀ 0 ∈ Ioo 0 T → (∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1) →
          ∀ w : FieldVal FC.C, IsAdmissible FC.left w →
            eulerRowW (classicalCov FC θ₀ (limitTuple L)) x₀ w = 0) := by
  obtain ⟨ψ, hψ, L, θ₀, -, hRC, -, heuler, -⟩ := reduced_closure hT reg hcert hcons hstat hyuk ns hns
  refine ⟨ψ, hψ, L, θ₀, fun t₀ t₁ h0 h01 h1 => (hRC t₀ t₁ h0 h01 h1).1, fun hz => ?_⟩
  have hae := fun t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) =>
    limitJet_ae_eq_redJet (hRC t₀ t₁ h0 h01 h1).1 hz
  refine ⟨hae, fun x₀ hx₀ hx₀s w hw => ?_⟩
  have hint : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left reg.r0 K,
        ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
          classicalCov FC θ₀ (limitTuple L) x (testJet v.val x) = 0 :=
    fun K t₀ t₁ h0 h01 h1 hK v => integral_classicalCov_eq_zero hz h0 h01 h1
      (hae t₀ t₁ h0 h01 h1) v (heuler K t₀ t₁ h0 h01 h1 hK v)
  exact eulerRowW_eq_zero (continuousOn_classicalCov θ₀ hz)
    (contDiffOn_classicalCov_derEmb θ₀ hz) (classicalCov_periodic θ₀ hz) hint hx₀ hx₀s hw

end Upgrade

end SlabReg
end EinsteinSM
end RenewalGeometry
