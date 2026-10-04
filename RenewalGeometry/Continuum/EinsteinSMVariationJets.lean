/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMProductCalculus
import RenewalGeometry.Analysis.FirstVariationCalculus

/-!
# Jets, test jets and the reduction of first variations to a chart box
  (infrastructure for `prop:reduced-continuity`, `prop:weak-fermion`,
  `prop:variation-continuity`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMFieldSpaces.lean` and `EinsteinSMCompactnessCertificates.lean`.

* **Test bounds.**  For a test section and `r ≥ 1`, `|f(x)|`, `‖Df(x)‖` and the Lipschitz constant
  of `f` are bounded by `‖f‖_{C^r}` (`norm_le_crNorm`, `norm_fderiv_le_crNorm`,
  `norm_sub_le_crNorm`); every entry of a test tuple is bounded by the test norm.
* **The slab box of a region.**  Every compact `K ⋐ (0,T) × 𝕋³` lies in a slab `[t₀,t₁] × 𝕋³`,
  `0 < t₀ < t₁ < T`; `slabBox K` is the chart box `(t₀,t₁) × (0,1)³`, contained in the fundamental
  domain `cylFund T` of `M`.  For integrands vanishing off the lifted region,
  `∫_{cylFund T} = ∫_{slabBox K}` (`setIntegral_cylFund_eq_slabBox`): the two sets differ by
  finitely many coordinate hyperplanes, which are Lebesgue-null.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

/- The ten-fold product of jet fibres needs larger instance terms than the default bound. -/
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Bounds on test sections from the `C^r` norm -/

section TestBounds

variable {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iSup_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r j : ℕ} (hj : j ≤ r) :
    (⨆ x, ‖iteratedFDeriv ℝ j f x‖) ≤ crNorm r f := by
  unfold crNorm
  exact Finset.single_le_sum (f := fun j => ⨆ x, ‖iteratedFDeriv ℝ j f x‖)
    (fun j _ => Real.iSup_nonneg fun x => norm_nonneg _) (Finset.mem_range.mpr (by omega))

theorem norm_le_crNorm {f : E4 → F} (hf : IsCylTest K f) (r : ℕ) (x : E4) :
    ‖f x‖ ≤ crNorm r f := by
  refine le_trans ?_ (iSup_le_crNorm hf (Nat.zero_le r))
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
  exact le_ciSup (hf.bddAbove_norm_iteratedFDeriv 0) x

theorem norm_fderiv_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 1 ≤ r) (x : E4) :
    ‖fderiv ℝ f x‖ ≤ crNorm r f := by
  refine le_trans ?_ (iSup_le_crNorm hf hr)
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
  exact le_ciSup (hf.bddAbove_norm_iteratedFDeriv 1) x

theorem norm_single_E4_le (i : Fin 4) : ‖(Pi.single i (1 : ℝ) : E4)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem norm_pd_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 1 ≤ r) (i : Fin 4)
    (x : E4) : ‖pd f i x‖ ≤ crNorm r f := by
  unfold pd
  refine ((fderiv ℝ f x).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_left (norm_single_E4_le i) (norm_nonneg _)).trans ?_
  rw [mul_one]; exact norm_fderiv_le_crNorm hf hr x

/-- A test section is Lipschitz with constant `‖f‖_{C^r}` (`r ≥ 1`). -/
theorem norm_sub_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 1 ≤ r) (x y : E4) :
    ‖f x - f y‖ ≤ crNorm r f * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.smooth.differentiable (by simp)).differentiableAt)
    (fun z _ => norm_fderiv_le_crNorm hf hr z) (mem_univ y) (mem_univ x)

end TestBounds

section TupleBounds

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}

theorem crNorm_e_le (v : CrTest left r K) : crNorm r v.val.e ≤ ‖v‖ := by
  rw [CrTest.norm_def, testNorm]
  have := crNorm_nonneg r v.val.A; have := crNorm_nonneg r v.val.H
  have := crNorm_nonneg r v.val.Ψ; have := crNorm_nonneg r v.val.Ψb
  linarith

theorem crNorm_A_le (v : CrTest left r K) : crNorm r v.val.A ≤ ‖v‖ := by
  rw [CrTest.norm_def, testNorm]
  have := crNorm_nonneg r v.val.e; have := crNorm_nonneg r v.val.H
  have := crNorm_nonneg r v.val.Ψ; have := crNorm_nonneg r v.val.Ψb
  linarith

theorem crNorm_H_le (v : CrTest left r K) : crNorm r v.val.H ≤ ‖v‖ := by
  rw [CrTest.norm_def, testNorm]
  have := crNorm_nonneg r v.val.e; have := crNorm_nonneg r v.val.A
  have := crNorm_nonneg r v.val.Ψ; have := crNorm_nonneg r v.val.Ψb
  linarith

theorem crNorm_Ψ_le (v : CrTest left r K) : crNorm r v.val.Ψ ≤ ‖v‖ := by
  rw [CrTest.norm_def, testNorm]
  have := crNorm_nonneg r v.val.e; have := crNorm_nonneg r v.val.A
  have := crNorm_nonneg r v.val.H; have := crNorm_nonneg r v.val.Ψb
  linarith

theorem crNorm_Ψb_le (v : CrTest left r K) : crNorm r v.val.Ψb ≤ ‖v‖ := by
  rw [CrTest.norm_def, testNorm]
  have := crNorm_nonneg r v.val.e; have := crNorm_nonneg r v.val.A
  have := crNorm_nonneg r v.val.H; have := crNorm_nonneg r v.val.Ψ
  linarith

theorem isCylTest_e (v : CrTest left r K) : IsCylTest K v.val.e := v.val_mem.1
theorem isCylTest_A (v : CrTest left r K) : IsCylTest K v.val.A := v.val_mem.2.1
theorem isCylTest_H (v : CrTest left r K) : IsCylTest K v.val.H := v.val_mem.2.2.1
theorem isCylTest_Ψ (v : CrTest left r K) : IsCylTest K v.val.Ψ := v.val_mem.2.2.2.1
theorem isCylTest_Ψb (v : CrTest left r K) : IsCylTest K v.val.Ψb := v.val_mem.2.2.2.2.1

end TupleBounds

/-! ### The slab box of a compact region -/

/-- Every compact region lies in a slab `[t₀, t₁] × 𝕋³` with `0 < t₀ < t₁ < T`. -/
theorem CylRegion.exists_slab {T : ℝ} (hT : 0 < T) (K : CylRegion T) :
    ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ < t₁ ∧ t₁ < T ∧ ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁ := by
  set S := Prod.fst '' K.carrier
  have hS : IsCompact S := K.isCompact.image continuous_fst
  have hST : S ⊆ Ioo 0 T := by rintro _ ⟨p, hp, rfl⟩; exact (K.subset hp).1
  rcases S.eq_empty_or_nonempty with hSe | hSn
  · refine ⟨T / 4, 3 * T / 4, by positivity, by linarith, by linarith, fun p hp => ?_⟩
    exact absurd (show p.1 ∈ S from ⟨p, hp, rfl⟩) (by rw [hSe]; exact notMem_empty _)
  · obtain ⟨m, hmS, hm⟩ := hS.exists_isMinOn hSn continuousOn_id
    obtain ⟨M, hMS, hM⟩ := hS.exists_isMaxOn hSn continuousOn_id
    have hm0 := (hST hmS).1
    have hMT := (hST hMS).2
    have hmM : m ≤ M := hm hMS
    refine ⟨m / 2, (M + T) / 2, by positivity, by linarith, by linarith, fun p hp => ?_⟩
    have h1 : m ≤ p.1 := hm ⟨p, hp, rfl⟩
    have h2 : p.1 ≤ M := hM ⟨p, hp, rfl⟩
    exact ⟨by linarith, by linarith⟩

/-- Coordinate hyperplanes are Lebesgue-null. -/
theorem volume_coord_eq (j : Fin 4) (c : ℝ) : volume {x : E4 | x j = c} = 0 := by
  have hsub : {x : E4 | x j = c} ⊆ Set.pi univ fun i => if i = j then {c} else univ := by
    intro x hx i _
    by_cases h : i = j
    · subst h; simpa using hx
    · simp [h]
  refine measure_mono_null hsub ?_
  rw [volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

theorem ae_coord_ne (j : Fin 4) (c : ℝ) : ∀ᵐ x : E4, x j ≠ c := by
  rw [ae_iff]; simpa using volume_coord_eq j c

/-- The chart box `(t₀, t₁) × (0,1)³`. -/
def slabChart {T : ℝ} (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) : ChartBox T where
  a := Fin.cons t₀ 0
  b := Fin.cons t₁ 1
  lt := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h01
    · simp
  time_pos := by simpa using h0
  time_lt := by simpa using h1
  spatial_le := by intro i; simp

theorem mem_slabChart {T t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T} {x : E4} :
    x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ↔
      x 0 ∈ Ioo t₀ t₁ ∧ ∀ i : Fin 3, x i.succ ∈ Ioo 0 1 := by
  simp only [ChartBox.set, SobolevOpen.box, slabChart, Set.mem_pi, mem_univ, true_implies]
  constructor
  · intro h; exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩
  · rintro ⟨h0', hi⟩ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0'
    · simpa using hi i

theorem slabChart_subset_cylFund {T t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T} :
    (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ cylFund T := by
  intro x hx
  obtain ⟨hx0, hxi⟩ := mem_slabChart.mp hx
  exact ⟨⟨h0.trans hx0.1, hx0.2.trans h1⟩, fun i => ⟨(hxi i).1.le, (hxi i).2⟩⟩

theorem measurableSet_cylFund (T : ℝ) : MeasurableSet (cylFund T) := by
  have : cylFund T = (fun x : E4 => x 0) ⁻¹' Ioo 0 T ∩ ⋂ i : Fin 3,
      (fun x : E4 => x i.succ) ⁻¹' Ico 0 1 := by
    ext x; simp [cylFund]
  rw [this]
  exact ((measurable_pi_apply 0) measurableSet_Ioo).inter
    (MeasurableSet.iInter fun i => (measurable_pi_apply i.succ) measurableSet_Ico)

/-- **Reduction to the slab box**: for an integrand vanishing at times outside `[t₀, t₁]`, the
integral over the fundamental domain `(0,T) × [0,1)³` equals the integral over the chart box
`(t₀,t₁) × (0,1)³`. -/
theorem setIntegral_cylFund_eq_slab {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E4 → E}
    (hf : ∀ x, x 0 ∉ Icc t₀ t₁ → f x = 0) :
    ∫ x in cylFund T, f x = ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, f x := by
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (measurableSet_cylFund T).nullMeasurableSet
    slabChart_subset_cylFund ?_
  filter_upwards [ae_coord_ne 0 t₀, ae_coord_ne 0 t₁, ae_coord_ne 1 0, ae_coord_ne 2 0,
    ae_coord_ne 3 0] with x hx0 hx1 hy1 hy2 hy3 hx
  refine hf x fun ht => hx.2 (mem_slabChart.mpr ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hx0),
    lt_of_le_of_ne ht.2 hx1⟩, fun i => ?_⟩)
  have hi := hx.1.2 i
  refine ⟨lt_of_le_of_ne hi.1 ?_, hi.2⟩
  fin_cases i
  · exact Ne.symm hy1
  · exact Ne.symm hy2
  · exact Ne.symm hy3

/-- The time support of a test section supported in a region inside `[t₀, t₁] × 𝕋³`. -/
theorem IsCylTest.eq_zero_of_time {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) {t₀ t₁ : ℝ}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {x : E4} (hx : x 0 ∉ Icc t₀ t₁) :
    x ∉ tsupport f :=
  fun h => hx (hK _ (hf.support h))

/-! ### Jets -/

section Jets

variable {C : Type} [Fintype C]

/-- The reduced jet fibre `(e, ∂e, A, F, H, K, Ψ, ∂Ψ, Ψ̄, ∂Ψ̄)`; the same fibre carries test jets
`(k, ∂k, a, ∂a, η_H, ∂η_H, η, ∂η, η̄, ∂η̄)` (with `∂a` in the `F` slot, `(∂a)_{μν} = ∂_μ a_ν`). -/
abbrev RJet (C : Type) [Fintype C] : Type :=
  CoframeFibre × CoframeJet × ConnFibre × (Fin 4 → ConnFibre) × HiggsFibre ×
    (Fin 4 → HiggsFibre) × SpinorFibre C × (Fin 4 → SpinorFibre C) × SpinorFibre C ×
      (Fin 4 → SpinorFibre C)

namespace RJet

/-- Build a jet from its ten entries. -/
def mk (e : CoframeFibre) (de : CoframeJet) (A : ConnFibre) (F : Fin 4 → ConnFibre)
    (H : HiggsFibre) (K : Fin 4 → HiggsFibre) (Ψ : SpinorFibre C) (dΨ : Fin 4 → SpinorFibre C)
    (Ψb : SpinorFibre C) (dΨb : Fin 4 → SpinorFibre C) : RJet C :=
  (e, de, A, F, H, K, Ψ, dΨ, Ψb, dΨb)

variable (R : RJet C)

def e : CoframeFibre := R.1
def de : CoframeJet := R.2.1
def A : ConnFibre := R.2.2.1
def F : Fin 4 → ConnFibre := R.2.2.2.1
def H : HiggsFibre := R.2.2.2.2.1
def K : Fin 4 → HiggsFibre := R.2.2.2.2.2.1
def Ψ : SpinorFibre C := R.2.2.2.2.2.2.1
def dΨ : Fin 4 → SpinorFibre C := R.2.2.2.2.2.2.2.1
def Ψb : SpinorFibre C := R.2.2.2.2.2.2.2.2.1
def dΨb : Fin 4 → SpinorFibre C := R.2.2.2.2.2.2.2.2.2

@[simp] theorem mk_e e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).e = e := rfl
@[simp] theorem mk_de e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).de = de := rfl
@[simp] theorem mk_A e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).A = A := rfl
@[simp] theorem mk_F e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).F = F := rfl
@[simp] theorem mk_H e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).H = H := rfl
@[simp] theorem mk_K e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).K = K := rfl
@[simp] theorem mk_Ψ e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).Ψ = Ψ := rfl
@[simp] theorem mk_dΨ e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).dΨ = dΨ := rfl
@[simp] theorem mk_Ψb e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).Ψb = Ψb := rfl
@[simp] theorem mk_dΨb e de A F H K Ψ dΨ Ψb dΨb :
    (mk (C := C) e de A F H K Ψ dΨ Ψb dΨb).dΨb = dΨb := rfl

theorem eta : mk R.e R.de R.A R.F R.H R.K R.Ψ R.dΨ R.Ψb R.dΨb = R := rfl

@[simp] theorem add_e (R R' : RJet C) : (R + R').e = R.e + R'.e := rfl
@[simp] theorem add_de (R R' : RJet C) : (R + R').de = R.de + R'.de := rfl
@[simp] theorem add_A (R R' : RJet C) : (R + R').A = R.A + R'.A := rfl
@[simp] theorem add_F (R R' : RJet C) : (R + R').F = R.F + R'.F := rfl
@[simp] theorem add_H (R R' : RJet C) : (R + R').H = R.H + R'.H := rfl
@[simp] theorem add_K (R R' : RJet C) : (R + R').K = R.K + R'.K := rfl
@[simp] theorem add_Ψ (R R' : RJet C) : (R + R').Ψ = R.Ψ + R'.Ψ := rfl
@[simp] theorem add_dΨ (R R' : RJet C) : (R + R').dΨ = R.dΨ + R'.dΨ := rfl
@[simp] theorem add_Ψb (R R' : RJet C) : (R + R').Ψb = R.Ψb + R'.Ψb := rfl
@[simp] theorem add_dΨb (R R' : RJet C) : (R + R').dΨb = R.dΨb + R'.dΨb := rfl
@[simp] theorem smul_e (c : ℝ) (R : RJet C) : (c • R).e = c • R.e := rfl
@[simp] theorem smul_de (c : ℝ) (R : RJet C) : (c • R).de = c • R.de := rfl
@[simp] theorem smul_A (c : ℝ) (R : RJet C) : (c • R).A = c • R.A := rfl
@[simp] theorem smul_F (c : ℝ) (R : RJet C) : (c • R).F = c • R.F := rfl
@[simp] theorem smul_H (c : ℝ) (R : RJet C) : (c • R).H = c • R.H := rfl
@[simp] theorem smul_K (c : ℝ) (R : RJet C) : (c • R).K = c • R.K := rfl
@[simp] theorem smul_Ψ (c : ℝ) (R : RJet C) : (c • R).Ψ = c • R.Ψ := rfl
@[simp] theorem smul_dΨ (c : ℝ) (R : RJet C) : (c • R).dΨ = c • R.dΨ := rfl
@[simp] theorem smul_Ψb (c : ℝ) (R : RJet C) : (c • R).Ψb = c • R.Ψb := rfl
@[simp] theorem smul_dΨb (c : ℝ) (R : RJet C) : (c • R).dΨb = c • R.dΨb := rfl

theorem ext' {R R' : RJet C} (he : R.e = R'.e) (hde : R.de = R'.de) (hA : R.A = R'.A)
    (hF : R.F = R'.F) (hH : R.H = R'.H) (hK : R.K = R'.K) (hΨ : R.Ψ = R'.Ψ)
    (hdΨ : R.dΨ = R'.dΨ) (hΨb : R.Ψb = R'.Ψb) (hdΨb : R.dΨb = R'.dΨb) : R = R' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := R
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := R'
  simp_all only [e, de, A, F, H, K, Ψ, dΨ, Ψb, dΨb]

end RJet

/-- The reduced jet of smooth fields: values, first jets of coframe and spinors, curvature and
covariant Higgs gradient. -/
def redJet (z : FieldTuple C) (x : E4) : RJet C :=
  RJet.mk (z.e x) (fun i => pd z.e i x) (z.A x) (curvatureF z.A x) (z.H x)
    (covDerivHiggs z.A z.H x) (z.Ψ x) (fun i => pd z.Ψ i x) (z.Ψb x) (fun i => pd z.Ψb i x)

/-- The test jet `(k, ∂k, a, ∂a, η_H, ∂η_H, η, ∂η, η̄, ∂η̄)` of a test tuple. -/
def testJet (v : FieldTuple C) (x : E4) : RJet C :=
  RJet.mk (v.e x) (fun i => pd v.e i x) (v.A x) (fun i => pd v.A i x) (v.H x)
    (fun i => pd v.H i x) (v.Ψ x) (fun i => pd v.Ψ i x) (v.Ψb x) (fun i => pd v.Ψb i x)

/-- `Ḟ_{μν} = ∂_μa_ν - ∂_νa_μ + [a_μ, A_ν] + [A_μ, a_ν]`. -/
def Fdot (A a : ConnFibre) (da : Fin 4 → ConnFibre) : Fin 4 → ConnFibre :=
  fun μ ν => da μ ν - da ν μ + comm (a μ) (A ν) + comm (A μ) (a ν)

/-- `K̇_μ = ∂_μη + ρ_H(a_μ)H + ρ_H(A_μ)η`. -/
def Kdot (A : ConnFibre) (H : HiggsFibre) (a : ConnFibre) (η : HiggsFibre)
    (dη : Fin 4 → HiggsFibre) : Fin 4 → HiggsFibre :=
  fun μ => dη μ + higgsAct (a μ) H + higgsAct (A μ) η

/-- **The variation direction on jets**: the first-order change of the reduced jet along the
complete variation `v̂ = (ė(k), a, η_H, η, η̄)` (`eq:metric-lift`). -/
def redVar (R T : RJet C) : RJet C :=
  RJet.mk (metricLiftL R.e T.e)
    (fun μ => fderiv ℝ metricLiftL R.e (R.de μ) T.e + metricLiftL R.e (T.de μ)) T.A
    (Fdot R.A T.A T.F) T.H (Kdot R.A R.H T.A T.H T.K) T.Ψ T.dΨ T.Ψb T.dΨb

/-- The second-order part of the jet along the variation. -/
def redVar2 (T : RJet C) : RJet C :=
  RJet.mk 0 0 0 (fun μ ν => comm (T.A μ) (T.A ν)) 0 (fun μ => higgsAct (T.A μ) T.H) 0 0 0 0

end Jets

/-! ### The jet of `z + ε v̂` -/

section JetExpansion

variable {C : Type} [Fintype C]

theorem pd_add_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F}
    {x : E4} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (ε : ℝ) (i : Fin 4) :
    pd (f + ε • g) i x = pd f i x + ε • pd g i x := by
  unfold pd
  rw [fderiv_add hf (hg.const_smul ε), fderiv_const_smul hg]
  rfl

theorem pd_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → Fin 4 → F}
    {x : E4} (hf : DifferentiableAt ℝ f x) (i ν : Fin 4) :
    pd (fun y => f y ν) i x = pd f i x ν := by
  unfold pd
  have h : HasFDerivAt (fun y => f y ν) ((ContinuousLinearMap.proj ν).comp (fderiv ℝ f x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => F) ν).hasFDerivAt.comp x
      hf.hasFDerivAt
  rw [h.fderiv]; rfl

theorem mmul_add_left' {n : Type*} [Fintype n] (X Y Z : n → n → ℂ) :
    mmul (X + Y) Z = mmul X Z + mmul Y Z := by
  funext i j; simp [mmul, add_mul, Finset.sum_add_distrib]

theorem mmul_add_right' {n : Type*} [Fintype n] (X Y Z : n → n → ℂ) :
    mmul X (Y + Z) = mmul X Y + mmul X Z := by
  funext i j; simp [mmul, mul_add, Finset.sum_add_distrib]

theorem mmul_smul_left' {n : Type*} [Fintype n] (c : ℝ) (X Z : n → n → ℂ) :
    mmul (c • X) Z = c • mmul X Z := by
  funext i j
  simp only [mmul, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem mmul_smul_right' {n : Type*} [Fintype n] (c : ℝ) (X Z : n → n → ℂ) :
    mmul X (c • Z) = c • mmul X Z := by
  funext i j
  simp only [mmul, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem comm_expand {n : Type*} [Fintype n] (X Y X' Y' : n → n → ℂ) (ε : ℝ) :
    comm (X + ε • Y) (X' + ε • Y') =
      comm X X' + ε • (comm X Y' + comm Y X') + ε ^ 2 • comm Y Y' := by
  simp only [comm, mmul_add_left', mmul_add_right', mmul_smul_left', mmul_smul_right', smul_add,
    smul_sub, smul_smul, sq]
  abel

theorem higgsAct_expand (X Y : LieFibre) (u w : HiggsFibre) (ε : ℝ) :
    higgsAct (X + ε • Y) (u + ε • w) =
      higgsAct X u + ε • (higgsAct Y u + higgsAct X w) + ε ^ 2 • higgsAct Y w := by
  funext i
  simp only [higgsAct, Pi.add_apply, Pi.smul_apply, Complex.real_smul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- **The jet of `z + ε v̂`** is the polynomial `J + ε J₁ + ε² J₂` in `ε`, with
`J₁ = redVar J (testJet v)` and `J₂ = redVar2 (testJet v)`, at every point where the fields and
the test are differentiable. -/
theorem redJet_variation {z v : FieldTuple C} {x : E4}
    (he : DifferentiableAt ℝ z.e x) (hA : DifferentiableAt ℝ z.A x)
    (hH : DifferentiableAt ℝ z.H x) (hΨ : DifferentiableAt ℝ z.Ψ x)
    (hΨb : DifferentiableAt ℝ z.Ψb x) (hve : DifferentiableAt ℝ v.e x)
    (hvA : DifferentiableAt ℝ v.A x) (hvH : DifferentiableAt ℝ v.H x)
    (hvΨ : DifferentiableAt ℝ v.Ψ x) (hvΨb : DifferentiableAt ℝ v.Ψb x) (ε : ℝ) :
    redJet (z + ε • variationDirection z v) x =
      redJet z x + ε • redVar (redJet z x) (testJet v x) + ε ^ 2 • redVar2 (testJet v x) := by
  have hė : DifferentiableAt ℝ (metricLift z.e v.e) x := differentiableAt_metricLift he hve
  have hAν : ∀ ν, DifferentiableAt ℝ (fun y => z.A y ν) x := fun ν =>
    differentiableAt_pi.mp hA ν
  have haν : ∀ ν, DifferentiableAt ℝ (fun y => v.A y ν) x := fun ν =>
    differentiableAt_pi.mp hvA ν
  refine RJet.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [redJet, redVar, redVar2, variationDirection, FieldTuple.mk, FieldTuple.e,
      metricLift_eq, testJet]
  · funext i
    simp only [redJet, redVar, redVar2, RJet.add_de, RJet.smul_de, RJet.mk_de, RJet.mk_e,
      Pi.add_apply, Pi.smul_apply, smul_zero, Pi.zero_apply, add_zero, testJet]
    rw [show (z + ε • variationDirection z v).e = z.e + ε • metricLift z.e v.e from rfl,
      pd_add_smul' he hė, pd_metricLift he hve]
  · simp [redJet, redVar, redVar2, variationDirection, FieldTuple.mk, FieldTuple.A, testJet]
  · funext μ ν
    simp only [redJet, redVar, redVar2, RJet.add_F, RJet.smul_F, RJet.mk_F, RJet.mk_A,
      Pi.add_apply, Pi.smul_apply, testJet, Fdot]
    have hzA : (z + ε • variationDirection z v).A = z.A + ε • v.A := rfl
    simp only [curvatureF, hzA, Pi.add_apply, Pi.smul_apply]
    have e1 : pd (fun y => z.A y ν + ε • v.A y ν) μ x =
        pd (fun y => z.A y ν) μ x + ε • pd v.A μ x ν := by
      rw [show (fun y => z.A y ν + ε • v.A y ν) = (fun y => z.A y ν) + ε • fun y => v.A y ν
        from rfl, pd_add_smul' (hAν ν) (haν ν), pd_apply hvA]
    have e2 : pd (fun y => z.A y μ + ε • v.A y μ) ν x =
        pd (fun y => z.A y μ) ν x + ε • pd v.A ν x μ := by
      rw [show (fun y => z.A y μ + ε • v.A y μ) = (fun y => z.A y μ) + ε • fun y => v.A y μ
        from rfl, pd_add_smul' (hAν μ) (haν μ), pd_apply hvA]
    rw [e1, e2, comm_expand]
    simp only [RJet.A, RJet.F, smul_add, smul_sub]
    abel
  · simp [redJet, redVar, redVar2, variationDirection, FieldTuple.mk, FieldTuple.H, testJet]
  · funext μ
    simp only [redJet, redVar, redVar2, RJet.add_K, RJet.smul_K, RJet.mk_K, RJet.mk_A,
      RJet.mk_H, Pi.add_apply, Pi.smul_apply, testJet, Kdot]
    have hzA : (z + ε • variationDirection z v).A = z.A + ε • v.A := rfl
    have hzH : (z + ε • variationDirection z v).H = z.H + ε • v.H := rfl
    simp only [covDerivHiggs, hzA, hzH, Pi.add_apply, Pi.smul_apply]
    rw [pd_add_smul' hH hvH, higgsAct_expand]
    simp only [smul_add]
    abel
  · simp [redJet, redVar, redVar2, variationDirection, FieldTuple.mk, FieldTuple.Ψ, testJet]
  · funext i
    simp only [redJet, redVar, redVar2, RJet.add_dΨ, RJet.smul_dΨ, RJet.mk_dΨ, Pi.add_apply,
      Pi.smul_apply, smul_zero, Pi.zero_apply, add_zero, testJet]
    rw [show (z + ε • variationDirection z v).Ψ = z.Ψ + ε • v.Ψ from rfl]
    exact pd_add_smul' hΨ hvΨ ε i
  · simp [redJet, redVar, redVar2, variationDirection, FieldTuple.mk, FieldTuple.Ψb, testJet]
  · funext i
    simp only [redJet, redVar, redVar2, RJet.add_dΨb, RJet.smul_dΨb, RJet.mk_dΨb, Pi.add_apply,
      Pi.smul_apply, smul_zero, Pi.zero_apply, add_zero, testJet]
    rw [show (z + ε • variationDirection z v).Ψb = z.Ψb + ε • v.Ψb from rfl]
    exact pd_add_smul' hΨb hvΨb ε i

end JetExpansion

/-! ### First variations of local densities as box integrals -/

section Reduction

variable {C : Type} [Fintype C]

/-- **First variation of a jet-local density.**  Suppose that on the slab box `Q` and for small
`ε` the density of `z + ε w` is `G(J + εJ₁ + ε²J₂)` for a `C¹` function `G` of the jet, with `J`
in a compact subset of the domain of `G` and `J₁, J₂` bounded, and that the density does not
change at times outside `[t₀, t₁]`.  Then `D𝒮(z)[w] = ∫_Q DG(J)[J₁]`. -/
theorem actionVariation_eq_box {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {L : FieldTuple C → E4 → ℝ} {z w : FieldTuple C} {G : RJet C → ℝ} {U : Set (RJet C)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {Kc : Set (RJet C)} (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) {J J₁ J₂ : E4 → RJet C}
    (hout : ∀ ε : ℝ, ∀ x, x 0 ∉ Icc t₀ t₁ → L (z + ε • w) x = L z x)
    (hfac : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
      L (z + ε • w) x = G (J x + ε • J₁ x + ε ^ 2 • J₂ x))
    (hJm : AEMeasurable J (volume.restrict (slabChart t₀ t₁ h0 h01 h1 (T := T)).set))
    (hJ₁m : AEMeasurable J₁ (volume.restrict (slabChart t₀ t₁ h0 h01 h1 (T := T)).set))
    (hJ₂m : AEMeasurable J₂ (volume.restrict (slabChart t₀ t₁ h0 h01 h1 (T := T)).set))
    (hJK : ∀ x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, J x ∈ Kc) {C₁ C₂ : ℝ}
    (hJ₁ : ∀ x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, ‖J₁ x‖ ≤ C₁)
    (hJ₂ : ∀ x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, ‖J₂ x‖ ≤ C₂) :
    actionVariation T L z w =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, fderiv ℝ G (J x) (J₁ x) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hQm : MeasurableSet Q.set := (SobolevOpen.isOpen_box Q.a Q.b).measurableSet
  have : IsFiniteMeasure (volume.restrict Q.set) :=
    isFiniteMeasure_restrict.mpr (SobolevOpen.volume_box_ne_top Q.a Q.b)
  have hae : ∀ {P : E4 → Prop}, (∀ x ∈ Q.set, P x) → ∀ᵐ x ∂(volume.restrict Q.set), P x :=
    fun {P} h => (ae_restrict_iff' hQm).mpr (Eventually.of_forall h)
  have hD := FirstVariationCalculus.hasDerivAt_integral_curve hU hG hKc hKU hJm hJ₁m hJ₂m
    (hae hJK) (hae hJ₁) (hae hJ₂)
  unfold actionVariation
  refine (hD.congr_of_eventuallyEq ?_).deriv
  have h00 := hfac.self_of_nhds
  filter_upwards [hfac] with ε hε
  rw [setIntegral_cylFund_eq_slab h0 h01 h1 (fun x hx => by rw [hout ε x hx, sub_self])]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  have h0x := h00 x hx
  simp only [zero_smul, add_zero, zero_pow two_ne_zero] at h0x
  rw [hε x hx, h0x]

end Reduction


/-! ### Jet projections -/

section Projections

variable {C : Type} [Fintype C]

/-- The jet projections as continuous linear maps. -/
def πe : RJet C →L[ℝ] CoframeFibre := ContinuousLinearMap.fst ℝ _ _
def πde : RJet C →L[ℝ] CoframeJet := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def πA : RJet C →L[ℝ] ConnFibre :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.snd ℝ _ _))
def πF : RJet C →L[ℝ] (Fin 4 → ConnFibre) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
def πH : RJet C →L[ℝ] HiggsFibre :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      (ContinuousLinearMap.snd ℝ _ _))))
def πK : RJet C →L[ℝ] (Fin 4 → HiggsFibre) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))))

@[simp] theorem πe_apply (R : RJet C) : πe R = R.e := rfl
@[simp] theorem πde_apply (R : RJet C) : πde R = R.de := rfl
@[simp] theorem πA_apply (R : RJet C) : πA R = R.A := rfl
@[simp] theorem πF_apply (R : RJet C) : πF R = R.F := rfl
@[simp] theorem πH_apply (R : RJet C) : πH R = R.H := rfl
@[simp] theorem πK_apply (R : RJet C) : πK R = R.K := rfl

def πΨ : RJet C →L[ℝ] SpinorFibre C :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ _ _))))))
def πdΨ : RJet C →L[ℝ] (Fin 4 → SpinorFibre C) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))))))
def πΨb : RJet C →L[ℝ] SpinorFibre C :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))))))))
def πdΨb : RJet C →L[ℝ] (Fin 4 → SpinorFibre C) :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))))))))

@[simp] theorem πΨ_apply (R : RJet C) : πΨ R = R.Ψ := rfl
@[simp] theorem πdΨ_apply (R : RJet C) : πdΨ R = R.dΨ := rfl
@[simp] theorem πΨb_apply (R : RJet C) : πΨb R = R.Ψb := rfl
@[simp] theorem πdΨb_apply (R : RJet C) : πdΨb R = R.dΨb := rfl

/-- The open set of jets with nondegenerate coframe. -/
def jetGL (C : Type) [Fintype C] : Set (RJet C) := {R | R.e ∈ coframeGL}

theorem isOpen_jetGL : IsOpen (jetGL C) :=
  isOpen_coframeGL.preimage continuous_fst

end Projections

end EinsteinSM
end RenewalGeometry
