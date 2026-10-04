/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationJets

/-!
# The identification of first variations of smooth fields with jet covectors, and dual norms
  (infrastructure for `prop:reduced-continuity`, `prop:weak-fermion`,
  `prop:variation-continuity`, Einstein–Standard-Model action-closure manuscript)

* `norm_testJet_le`: for `r ≥ 1`, the test jet of `v ∈ 𝒱_K` is bounded by `‖v‖_{C^r}`;
  `lipschitz_test_e`, `lipschitz_test_Ψ`, `lipschitz_test_Ψb`: the test values are
  `‖v‖_{C^r}`-Lipschitz.
* `continuousOn_redJet`: the jet of smooth reconstructed fields is continuous on the open slab.
* `IsLocalDensity`: a density depends only on the germ of the fields.
* `actionVariation_eq_cov` (**identification**): if a local density `L` factors through a `C¹`
  jet density `G` on the nondegenerate chart (`L z x = G(redJet z x)`) and the covector
  `Cov R T = DG(R)[redVar R T]`, then for smooth fields whose coframe lies in a compact subset of
  the chart on the slab box, `D𝒮(z)[v] = ∫_Q Cov(redJet z)(testJet v)`.
* `dual_tendsto_of_L1`: `L¹` operator convergence of covector fields gives convergence of the
  induced functionals in the norm of `(𝒱_K^r)^*` (`r ≥ 1`), stated as the uniform estimate
  `|ℓ_n(v) - ℓ(v)| ≤ ε ‖v‖_{C^r}` for all tests, eventually in `n`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd)

/-! ### Test jets are controlled by the test norm -/

section TestJets

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}

theorem norm_family_le {F : Type*} [NormedAddCommGroup F] {f : Fin 4 → F} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ‖f i‖ ≤ c) : ‖f‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).mpr h

/-- **The test jet is bounded by the `C^r` test norm** (`r ≥ 1`). -/
theorem norm_testJet_le (hr : 1 ≤ r) (v : CrTest left r K) (x : E4) :
    ‖testJet v.val x‖ ≤ ‖v‖ := by
  have h0 : 0 ≤ ‖v‖ := norm_nonneg v
  have ke := isCylTest_e v; have kA := isCylTest_A v; have kH := isCylTest_H v
  have kΨ := isCylTest_Ψ v; have kΨb := isCylTest_Ψb v
  simp only [testJet, RJet.mk, norm_prod_le_iff]
  refine ⟨(norm_le_crNorm ke r x).trans (crNorm_e_le v),
    norm_family_le h0 fun i => (norm_pd_le_crNorm ke hr i x).trans (crNorm_e_le v),
    (norm_le_crNorm kA r x).trans (crNorm_A_le v),
    norm_family_le h0 fun i => (norm_pd_le_crNorm kA hr i x).trans (crNorm_A_le v),
    (norm_le_crNorm kH r x).trans (crNorm_H_le v),
    norm_family_le h0 fun i => (norm_pd_le_crNorm kH hr i x).trans (crNorm_H_le v),
    (norm_le_crNorm kΨ r x).trans (crNorm_Ψ_le v),
    norm_family_le h0 fun i => (norm_pd_le_crNorm kΨ hr i x).trans (crNorm_Ψ_le v),
    (norm_le_crNorm kΨb r x).trans (crNorm_Ψb_le v),
    norm_family_le h0 fun i => (norm_pd_le_crNorm kΨb hr i x).trans (crNorm_Ψb_le v)⟩

theorem lipschitz_test_e (hr : 1 ≤ r) (v : CrTest left r K) (x y : E4) :
    ‖v.val.e x - v.val.e y‖ ≤ ‖v‖ * ‖x - y‖ :=
  (norm_sub_le_crNorm (isCylTest_e v) hr x y).trans
    (mul_le_mul_of_nonneg_right (crNorm_e_le v) (norm_nonneg _))

theorem lipschitz_test_Ψ (hr : 1 ≤ r) (v : CrTest left r K) (x y : E4) :
    ‖v.val.Ψ x - v.val.Ψ y‖ ≤ ‖v‖ * ‖x - y‖ :=
  (norm_sub_le_crNorm (isCylTest_Ψ v) hr x y).trans
    (mul_le_mul_of_nonneg_right (crNorm_Ψ_le v) (norm_nonneg _))

theorem lipschitz_test_Ψb (hr : 1 ≤ r) (v : CrTest left r K) (x y : E4) :
    ‖v.val.Ψb x - v.val.Ψb y‖ ≤ ‖v‖ * ‖x - y‖ :=
  (norm_sub_le_crNorm (isCylTest_Ψb v) hr x y).trans
    (mul_le_mul_of_nonneg_right (crNorm_Ψb_le v) (norm_nonneg _))

theorem contDiff_test {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : IsCylTest K f) : ContDiff ℝ 1 f := hf.smooth.of_le (by simp)

theorem continuous_testJet (v : CrTest left r K) : Continuous (testJet v.val) := by
  have ce := contDiff_test (isCylTest_e v); have cA := contDiff_test (isCylTest_A v)
  have cH := contDiff_test (isCylTest_H v); have cΨ := contDiff_test (isCylTest_Ψ v)
  have cΨb := contDiff_test (isCylTest_Ψb v)
  have pe : Continuous fun x => (fun i => pd v.val.e i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd ce i
  have pA : Continuous fun x => (fun i => pd v.val.A i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd cA i
  have pH : Continuous fun x => (fun i => pd v.val.H i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd cH i
  have pΨ : Continuous fun x => (fun i => pd v.val.Ψ i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd cΨ i
  have pΨb : Continuous fun x => (fun i => pd v.val.Ψb i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd cΨb i
  unfold testJet RJet.mk
  exact ce.continuous.prodMk (pe.prodMk (cA.continuous.prodMk (pA.prodMk
    (cH.continuous.prodMk (pH.prodMk (cΨ.continuous.prodMk (pΨ.prodMk
      (cΨb.continuous.prodMk pΨb))))))))

end TestJets

/-! ### Smooth fields on the slab -/

section SmoothSlab

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool}

theorem isOpen_cylSlab (T : ℝ) : IsOpen (cylSlab T) :=
  isOpen_Ioo.preimage (continuous_apply 0)

theorem differentiableAt_of_contDiffOn_slab {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → F} (hf : ContDiffOn ℝ ∞ f (cylSlab T)) {x : E4} (hx : x ∈ cylSlab T) :
    DifferentiableAt ℝ f x :=
  ((hf.contDiffAt ((isOpen_cylSlab T).mem_nhds hx)).differentiableAt (by simp))

theorem continuousOn_pd_slab {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → F} (hf : ContDiffOn ℝ ∞ f (cylSlab T)) (i : Fin 4) :
    ContinuousOn (fun x => pd f i x) (cylSlab T) := by
  have := hf.continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) (by simp)
  exact this.clm_apply continuousOn_const

theorem continuousOn_pd_family {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → F} (hf : ContDiffOn ℝ ∞ f (cylSlab T)) :
    ContinuousOn (fun x => fun i => pd f i x) (cylSlab T) :=
  continuousOn_pi.mpr fun i => continuousOn_pd_slab hf i

theorem contDiffOn_apply_slab {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → Fin 4 → F} (hf : ContDiffOn ℝ ∞ f (cylSlab T)) (ν : Fin 4) :
    ContDiffOn ℝ ∞ (fun y => f y ν) (cylSlab T) :=
  (contDiff_apply ℝ F ν).comp_contDiffOn hf

theorem continuousOn_comm' {f g : E4 → LieFibre} {s : Set E4} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => comm (f x) (g x)) s := by
  have hc : Continuous fun p : LieFibre × LieFibre => comm p.1 p.2 := by
    unfold comm mmul; fun_prop
  have := hc.comp_continuousOn (hf.prodMk hg)
  simpa only [Function.comp_def] using this

theorem continuousOn_higgsAct' {f : E4 → LieFibre} {g : E4 → HiggsFibre} {s : Set E4}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => higgsAct (f x) (g x)) s := by
  have hc : Continuous fun p : LieFibre × HiggsFibre => higgsAct p.1 p.2 := by
    unfold higgsAct; fun_prop
  have := hc.comp_continuousOn (hf.prodMk hg)
  simpa only [Function.comp_def] using this

theorem continuousOn_curvatureF {A : E4 → ConnFibre} (hA : ContDiffOn ℝ ∞ A (cylSlab T)) :
    ContinuousOn (fun x => curvatureF A x) (cylSlab T) := by
  refine continuousOn_pi.mpr fun μ => continuousOn_pi.mpr fun ν => ?_
  unfold curvatureF
  exact ((continuousOn_pd_slab (contDiffOn_apply_slab hA ν) μ).sub
    (continuousOn_pd_slab (contDiffOn_apply_slab hA μ) ν)).add
    (continuousOn_comm' (continuousOn_pi.mp hA.continuousOn μ)
      (continuousOn_pi.mp hA.continuousOn ν))

theorem continuousOn_covDerivHiggs {A : E4 → ConnFibre} {H : E4 → HiggsFibre}
    (hA : ContDiffOn ℝ ∞ A (cylSlab T)) (hH : ContDiffOn ℝ ∞ H (cylSlab T)) :
    ContinuousOn (fun x => covDerivHiggs A H x) (cylSlab T) := by
  refine continuousOn_pi.mpr fun μ => ?_
  unfold covDerivHiggs
  exact (continuousOn_pd_slab hH μ).add
    (continuousOn_higgsAct' (continuousOn_pi.mp hA.continuousOn μ) hH.continuousOn)

theorem continuousOn_redJet_of {z : FieldTuple C} (he : ContDiffOn ℝ ∞ z.e (cylSlab T))
    (hA : ContDiffOn ℝ ∞ z.A (cylSlab T)) (hH : ContDiffOn ℝ ∞ z.H (cylSlab T))
    (hΨ : ContDiffOn ℝ ∞ z.Ψ (cylSlab T)) (hΨb : ContDiffOn ℝ ∞ z.Ψb (cylSlab T)) :
    ContinuousOn (redJet z) (cylSlab T) := by
  have hF := continuousOn_curvatureF hA
  have hK := continuousOn_covDerivHiggs hA hH
  have pe := continuousOn_pd_family he
  have pΨ := continuousOn_pd_family hΨ
  have pΨb := continuousOn_pd_family hΨb
  unfold redJet RJet.mk
  exact he.continuousOn.prodMk (pe.prodMk (hA.continuousOn.prodMk (hF.prodMk
    (hH.continuousOn.prodMk (hK.prodMk (hΨ.continuousOn.prodMk (pΨ.prodMk
      (hΨb.continuousOn.prodMk pΨb))))))))

/-- The jet of smooth reconstructed fields is continuous on the open slab. -/
theorem continuousOn_redJet (z : SmoothFields T left) :
    ContinuousOn (redJet z.z) (cylSlab T) :=
  continuousOn_redJet_of z.smooth_e z.smooth_A z.smooth_H z.smooth_Ψ z.smooth_Ψb

theorem closure_slabChart_subset {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ {x : E4 | x 0 ∈ Icc t₀ t₁} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_Icc.preimage (continuous_apply 0))
  exact Ioo_subset_Icc_self (mem_slabChart.mp hx).1

theorem slabTime_subset_cylSlab {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h1 : t₁ < T) :
    {x : E4 | x 0 ∈ Icc t₀ t₁} ⊆ cylSlab T := fun x hx =>
  ⟨h0.trans_le hx.1, hx.2.trans_lt h1⟩

theorem isCompact_closure_slabChart {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    IsCompact (closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set) := by
  refine (isCompact_univ_pi fun i => isCompact_Icc
    (a := (slabChart t₀ t₁ h0 h01 h1 (T := T)).a i)
    (b := (slabChart t₀ t₁ h0 h01 h1 (T := T)).b i)).of_isClosed_subset isClosed_closure ?_
  refine closure_minimal (fun x hx i _ => ?_) (isClosed_set_pi fun _ _ => isClosed_Icc)
  exact Ioo_subset_Icc_self (hx i (mem_univ i))

end SmoothSlab

/-! ### Continuity of the variation direction -/

section RedVarCont

variable {C : Type} [Fintype C]

theorem continuous_Fdot : Continuous fun p : ConnFibre × ConnFibre × (Fin 4 → ConnFibre) =>
    Fdot p.1 p.2.1 p.2.2 := by
  unfold Fdot comm mmul; fun_prop

theorem continuous_Kdot : Continuous fun p : ConnFibre × HiggsFibre × ConnFibre × HiggsFibre ×
    (Fin 4 → HiggsFibre) => Kdot p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  unfold Kdot higgsAct; fun_prop

theorem continuous_fderiv_metricLiftL' : Continuous (fderiv ℝ metricLiftL) :=
  (contDiff_metricLiftL (n := 1)).continuous_fderiv one_ne_zero

/-- The variation direction is jointly continuous in the jet and the test jet. -/
theorem continuous_redVar : Continuous fun p : RJet C × RJet C => redVar p.1 p.2 := by
  have h1 : Continuous fun p : RJet C × RJet C => p.1 := continuous_fst
  have h2 : Continuous fun p : RJet C × RJet C => p.2 := continuous_snd
  have ce : Continuous fun p : RJet C × RJet C => p.1.e := (πe (C := C)).continuous.comp h1
  have cte : Continuous fun p : RJet C × RJet C => p.2.e := (πe (C := C)).continuous.comp h2
  have cde : Continuous fun p : RJet C × RJet C => p.1.de := (πde (C := C)).continuous.comp h1
  have ctde : Continuous fun p : RJet C × RJet C => p.2.de := (πde (C := C)).continuous.comp h2
  have cA : Continuous fun p : RJet C × RJet C => p.1.A := (πA (C := C)).continuous.comp h1
  have ctA : Continuous fun p : RJet C × RJet C => p.2.A := (πA (C := C)).continuous.comp h2
  have ctF : Continuous fun p : RJet C × RJet C => p.2.F := (πF (C := C)).continuous.comp h2
  have cH : Continuous fun p : RJet C × RJet C => p.1.H := (πH (C := C)).continuous.comp h1
  have ctH : Continuous fun p : RJet C × RJet C => p.2.H := (πH (C := C)).continuous.comp h2
  have ctK : Continuous fun p : RJet C × RJet C => p.2.K := (πK (C := C)).continuous.comp h2
  have c1 : Continuous fun p : RJet C × RJet C => metricLiftL p.1.e p.2.e :=
    ((contDiff_metricLiftL (n := 0)).continuous.comp ce).clm_apply cte
  have c2 : Continuous fun p : RJet C × RJet C =>
      (fun μ => fderiv ℝ metricLiftL p.1.e (p.1.de μ) p.2.e + metricLiftL p.1.e (p.2.de μ)) :=
    continuous_pi fun μ => (((continuous_fderiv_metricLiftL'.comp ce).clm_apply
      ((continuous_apply μ).comp cde)).clm_apply cte).add
      (((contDiff_metricLiftL (n := 0)).continuous.comp ce).clm_apply ((continuous_apply μ).comp ctde))
  have c3 : Continuous fun p : RJet C × RJet C => Fdot p.1.A p.2.A p.2.F :=
    continuous_Fdot.comp (cA.prodMk (ctA.prodMk ctF))
  have c4 : Continuous fun p : RJet C × RJet C => Kdot p.1.A p.1.H p.2.A p.2.H p.2.K :=
    continuous_Kdot.comp (cA.prodMk (cH.prodMk (ctA.prodMk (ctH.prodMk ctK))))
  unfold redVar RJet.mk
  exact c1.prodMk (c2.prodMk (ctA.prodMk (c3.prodMk (ctH.prodMk (c4.prodMk
    (((πΨ (C := C)).continuous.comp h2).prodMk (((πdΨ (C := C)).continuous.comp h2).prodMk
      (((πΨb (C := C)).continuous.comp h2).prodMk ((πdΨb (C := C)).continuous.comp h2)))))))))

theorem continuousOn_redVar_comp {J Tj : E4 → RJet C} {s : Set E4} (hJ : ContinuousOn J s)
    (hT : ContinuousOn Tj s) : ContinuousOn (fun x => redVar (J x) (Tj x)) s :=
  (continuous_redVar (C := C)).comp_continuousOn (f := fun x => (J x, Tj x)) (hJ.prodMk hT)

theorem continuous_redVar2 : Continuous fun T' : RJet C => redVar2 T' := by
  have hc : Continuous fun p : LieFibre × LieFibre => comm p.1 p.2 := by
    unfold comm mmul; fun_prop
  have hh : Continuous fun p : LieFibre × HiggsFibre => higgsAct p.1 p.2 := by
    unfold higgsAct; fun_prop
  have cA : Continuous fun T' : RJet C => T'.A := (πA (C := C)).continuous
  have cH : Continuous fun T' : RJet C => T'.H := (πH (C := C)).continuous
  unfold redVar2 RJet.mk
  exact continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk
    ((continuous_pi fun μ => continuous_pi fun ν => hc.comp
      (((continuous_apply μ).comp cA).prodMk ((continuous_apply ν).comp cA))).prodMk
    (continuous_const.prodMk ((continuous_pi fun μ => hh.comp
      (((continuous_apply μ).comp cA).prodMk cH)).prodMk continuous_const)))))

end RedVarCont

/-! ### Local densities and the identification of first variations -/

section Identification

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool}

/-- A density depends only on the germ of the fields at the point. -/
def IsLocalDensity (L : FieldTuple C → E4 → ℝ) : Prop :=
  ∀ (z z' : FieldTuple C) (x : E4), z.e =ᶠ[𝓝 x] z'.e → z.A =ᶠ[𝓝 x] z'.A →
    z.H =ᶠ[𝓝 x] z'.H → z.Ψ =ᶠ[𝓝 x] z'.Ψ → z.Ψb =ᶠ[𝓝 x] z'.Ψb → L z x = L z' x

theorem eventuallyEq_zero_of_time {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) {t₀ t₁ : ℝ}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {x : E4} (hx : x 0 ∉ Icc t₀ t₁) :
    f =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (hf.eq_zero_of_time hK hx)

/-- Outside the time support of the test, the varied fields agree with the fields near `x`. -/
theorem variation_eventuallyEq {r : ℕ} {K : CylRegion T} (z : FieldTuple C)
    (v : CrTest left r K) {t₀ t₁ : ℝ} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {x : E4}
    (hx : x 0 ∉ Icc t₀ t₁) (ε : ℝ) :
    (z + ε • variationDirection z v.val).e =ᶠ[𝓝 x] z.e ∧
      (z + ε • variationDirection z v.val).A =ᶠ[𝓝 x] z.A ∧
      (z + ε • variationDirection z v.val).H =ᶠ[𝓝 x] z.H ∧
      (z + ε • variationDirection z v.val).Ψ =ᶠ[𝓝 x] z.Ψ ∧
      (z + ε • variationDirection z v.val).Ψb =ᶠ[𝓝 x] z.Ψb := by
  have he := eventuallyEq_zero_of_time (isCylTest_e v) hK hx
  have hA := eventuallyEq_zero_of_time (isCylTest_A v) hK hx
  have hH := eventuallyEq_zero_of_time (isCylTest_H v) hK hx
  have hΨ := eventuallyEq_zero_of_time (isCylTest_Ψ v) hK hx
  have hΨb := eventuallyEq_zero_of_time (isCylTest_Ψb v) hK hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [he] with y hy
    change z.e y + ε • metricLiftL (z.e y) (v.val.e y) = z.e y
    rw [show v.val.e y = 0 from hy, map_zero, smul_zero, add_zero]
  · filter_upwards [hA] with y hy
    change z.A y + ε • v.val.A y = z.A y
    rw [show v.val.A y = 0 from hy, smul_zero, add_zero]
  · filter_upwards [hH] with y hy
    change z.H y + ε • v.val.H y = z.H y
    rw [show v.val.H y = 0 from hy, smul_zero, add_zero]
  · filter_upwards [hΨ] with y hy
    change z.Ψ y + ε • v.val.Ψ y = z.Ψ y
    rw [show v.val.Ψ y = 0 from hy, smul_zero, add_zero]
  · filter_upwards [hΨb] with y hy
    change z.Ψb y + ε • v.val.Ψb y = z.Ψb y
    rw [show v.val.Ψb y = 0 from hy, smul_zero, add_zero]

set_option maxHeartbeats 1000000 in
/-- **Identification of the first variation of smooth fields with the jet covector.**  Let `L`
be a local density which, at every point where the fields are differentiable with nondegenerate
coframe, equals `G(redJet)` for a `C¹` jet density `G`, and let `Cov R T = DG(R)[redVar R T]`.
For smooth fields whose coframe lies in a compact subset of the chart on the slab box `Q`
containing the time support of the region `K`, and every test `v ∈ 𝒱_K`,
`D𝒮(z)[v] = ∫_Q Cov(redJet z)(testJet v)`. -/
theorem actionVariation_eq_cov {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (z : SmoothFields T left)
    (v : CrTest left r K) {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke)
    {L : FieldTuple C → E4 → ℝ} (hloc : IsLocalDensity L) {G : RJet C → ℝ}
    (hG : ContDiffOn ℝ 1 G (jetGL C))
    (hfac : ∀ (z' : FieldTuple C) (x : E4), DifferentiableAt ℝ z'.e x →
      DifferentiableAt ℝ z'.A x → DifferentiableAt ℝ z'.H x → DifferentiableAt ℝ z'.Ψ x →
      DifferentiableAt ℝ z'.Ψb x → z'.e x ∈ coframeGL → L z' x = G (redJet z' x))
    {Cov : RJet C → RJet C →L[ℝ] ℝ}
    (hCov : ∀ R ∈ jetGL C, ∀ T', fderiv ℝ G R (redVar R T') = Cov R T') :
    actionVariation T L z.z (variationDirection z.z v.val) =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, Cov (redJet z.z x) (testJet v.val x) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  set w := variationDirection z.z v.val
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hQS : Q.set ⊆ cylSlab T := subset_closure.trans hclS
  have hcomp := isCompact_closure_slabChart h0 h01 h1 (T := T)
  set J : E4 → RJet C := redJet z.z
  set J₁ : E4 → RJet C := fun x => redVar (J x) (testJet v.val x)
  set J₂ : E4 → RJet C := fun x => redVar2 (testJet v.val x)
  have hJc : ContinuousOn J (closure Q.set) := (continuousOn_redJet z).mono hclS
  have hTc : Continuous (testJet v.val) := continuous_testJet v
  have hJ₁c : ContinuousOn J₁ (closure Q.set) :=
    continuousOn_redVar_comp hJc hTc.continuousOn
  have hJ₂c : Continuous J₂ := continuous_redVar2.comp hTc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hJc
  obtain ⟨M₁, hM₁⟩ := hcomp.exists_bound_of_continuousOn hJ₁c
  obtain ⟨M₂, hM₂⟩ := hcomp.exists_bound_of_continuousOn hJ₂c.continuousOn
  set Kc : Set (RJet C) := {R | R.e ∈ Ke} ∩ Metric.closedBall 0 M
  have hKc : IsCompact Kc :=
    (isCompact_closedBall (0 : RJet C) M).inter_left
      (hKe.isClosed.preimage (πe (C := C)).continuous)
  have hKcGL : Kc ⊆ jetGL C := fun R hR => hKGL hR.1
  -- the factorization along the variation, uniformly for small `ε`
  obtain ⟨δ, hδ, hδGL⟩ := hKe.exists_cthickening_subset_open isOpen_coframeGL hKGL
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ _ (subset_closure (mem_slabChart.mpr
    ⟨by simp only [Fin.cons_zero]; constructor <;> linarith,
      fun i => by simp only [Fin.cons_succ]; constructor <;> norm_num⟩ :
      (Fin.cons ((t₀ + t₁) / 2) (fun _ => (1 / 2 : ℝ)) : E4) ∈ Q.set)))
  have hfacε : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ Q.set,
      L (z.z + ε • w) x = G (J x + ε • J₁ x + ε ^ 2 • J₂ x) := by
    have hball : Metric.ball (0 : ℝ) (δ / (M₁ + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with ε hε x hx
    have hxS := hQS hx
    have hze := differentiableAt_of_contDiffOn_slab z.smooth_e hxS
    have hzA := differentiableAt_of_contDiffOn_slab z.smooth_A hxS
    have hzH := differentiableAt_of_contDiffOn_slab z.smooth_H hxS
    have hzΨ := differentiableAt_of_contDiffOn_slab z.smooth_Ψ hxS
    have hzΨb := differentiableAt_of_contDiffOn_slab z.smooth_Ψb hxS
    have hve := ((contDiff_test (isCylTest_e v)).differentiable one_ne_zero) x
    have hvA := ((contDiff_test (isCylTest_A v)).differentiable one_ne_zero) x
    have hvH := ((contDiff_test (isCylTest_H v)).differentiable one_ne_zero) x
    have hvΨ := ((contDiff_test (isCylTest_Ψ v)).differentiable one_ne_zero) x
    have hvΨb := ((contDiff_test (isCylTest_Ψb v)).differentiable one_ne_zero) x
    have hė := differentiableAt_metricLift hze hve
    -- nondegeneracy of the varied coframe
    have hGL : (z.z + ε • w).e x ∈ coframeGL := by
      refine hδGL (Metric.mem_cthickening_of_dist_le _ (z.z.e x) δ Ke (hzK x (subset_closure hx))
        ?_)
      have hε' : |ε| < δ / (M₁ + 1) := by simpa [Real.dist_eq] using hε
      have hw : ‖metricLiftL (z.z.e x) (v.val.e x)‖ ≤ M₁ := by
        have := hM₁ x (subset_closure hx)
        have h' : ‖(J₁ x).e‖ ≤ ‖J₁ x‖ := by
          simp only [RJet.e]; exact norm_fst_le _
        exact h'.trans this
      change dist (z.z.e x + ε • metricLiftL (z.z.e x) (v.val.e x)) (z.z.e x) ≤ δ
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |ε| * ‖metricLiftL (z.z.e x) (v.val.e x)‖ ≤ (δ / (M₁ + 1)) * M₁ :=
            mul_le_mul hε'.le hw (norm_nonneg _) (by positivity)
        _ ≤ δ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    rw [hfac (z.z + ε • w) x (hze.add (hė.const_smul ε)) (hzA.add (hvA.const_smul ε))
      (hzH.add (hvH.const_smul ε)) (hzΨ.add (hvΨ.const_smul ε)) (hzΨb.add (hvΨb.const_smul ε))
      hGL]
    rw [redJet_variation hze hzA hzH hzΨ hzΨb hve hvA hvH hvΨ hvΨb ε]
  have hout : ∀ ε : ℝ, ∀ x, x 0 ∉ Icc t₀ t₁ → L (z.z + ε • w) x = L z.z x := by
    intro ε x hx
    obtain ⟨h1', h2', h3', h4', h5'⟩ := variation_eventuallyEq z.z v hK hx ε
    exact hloc _ _ x h1' h2' h3' h4' h5'
  have hQm : MeasurableSet Q.set := (SobolevOpen.isOpen_box Q.a Q.b).measurableSet
  have hJm : AEMeasurable J (volume.restrict Q.set) :=
    ((hJc.mono subset_closure).aestronglyMeasurable hQm).aemeasurable
  have hJ₁m : AEMeasurable J₁ (volume.restrict Q.set) :=
    ((hJ₁c.mono subset_closure).aestronglyMeasurable hQm).aemeasurable
  have hJ₂m : AEMeasurable J₂ (volume.restrict Q.set) := hJ₂c.aemeasurable
  rw [actionVariation_eq_box h0 h01 h1 isOpen_jetGL hG hKc hKcGL hout hfacε hJm hJ₁m hJ₂m
    (fun x hx => ⟨hzK x (subset_closure hx), mem_closedBall_zero_iff.mpr (hM x (subset_closure hx))⟩)
    (fun x hx => hM₁ x (subset_closure hx)) (fun x hx => hM₂ x (subset_closure hx))]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  exact hCov (J x) (hKGL (hzK x (subset_closure hx))) (testJet v.val x)



end Identification

/-! ### Convergence in the dual test norm -/

section Dual

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}

/-- **Dual-norm convergence from `L¹` operator convergence of covectors.**  If the covector fields
`Λ_n → Λ` in `L¹(μ; RJet^*)`, then the functionals `v ↦ ∫ Λ_n(testJet v)` converge to
`v ↦ ∫ Λ(testJet v)` in the norm of `(𝒱_K^r)^*` (`r ≥ 1`): for every `ε > 0`, eventually
`|ℓ_n(v) - ℓ(v)| ≤ ε ‖v‖_{C^r}` for all tests `v`. -/
theorem dual_tendsto_of_L1 (hr : 1 ≤ r) {μ : Measure E4} [IsFiniteMeasure μ] {Λ : ℕ → E4 → RJet C →L[ℝ] ℝ}
    {Λ₀ : E4 → RJet C →L[ℝ] ℝ} (hΛ : RenewalGeometry.LpTendsto μ 1 Λ Λ₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |∫ x, Λ n x (testJet v.val x) ∂μ - ∫ x, Λ₀ x (testJet v.val x) ∂μ| ≤ ε * ‖v‖ := by
  filter_upwards [FirstVariationCalculus.uniform_of_L1_op hΛ hε] with n hn
  intro v
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · have h' : ∀ x, testJet v.val x = 0 := fun x =>
      norm_le_zero_iff.mp ((norm_testJet_le hr v x).trans h0.symm.le)
    simp [h', ← h0]
  · have hτm : AEStronglyMeasurable (fun x => ‖v‖⁻¹ • testJet v.val x) μ :=
      by
      have hc := continuous_testJet v
      exact Continuous.aestronglyMeasurable (by fun_prop)
    have h1 : ∀ᵐ x ∂μ, ‖‖v‖⁻¹ • testJet v.val x‖ ≤ 1 := Eventually.of_forall fun x => by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, mul_one]
      exact norm_testJet_le hr v x
    have h2 := hn _ hτm h1
    simp only [map_smul, smul_eq_mul, integral_const_mul, ← mul_sub, abs_mul, abs_inv,
      abs_norm] at h2
    rwa [inv_mul_le_iff₀ hpos, mul_comm] at h2

end Dual

end EinsteinSM
end RenewalGeometry
