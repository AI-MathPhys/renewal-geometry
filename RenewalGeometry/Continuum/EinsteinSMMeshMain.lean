/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMeshSector

/-!
# Smooth local action consistency (`prop:mesh-consistency`): assembly

Einstein–Standard-Model action-closure manuscript, `prop:mesh-consistency` / `eq:mesh-C1`.

For a bounded `C^{1,1}` coframe/gauge/matter family `f` (spatially periodic, `smLie`-valued gauge
field, coframe values in a fixed compact subset of the nondegenerate chart: the "common
inverse-coframe bound"), nodal sampling `q_h = sampleRec h f` followed by the cardinal
reconstruction `z_h = 𝒥_h q_h` (`reconFields`) gives a comparison regulator whose consistency
defect satisfies `c_h(K) ≤ C_K h` (`mesh_consistency`), uniformly over the family.

The test lift `𝓘_h v` is the nodal sampling of the complete variation `v̂ = (ė(k), a, …)` at the
reconstructed coframe, time-periodized with period `P ≥ T` (`liftRec`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-! ### Sampled families and their reconstructions -/

theorem one_div_N_pos {N : ℕ} (hN : 0 < N) : (0 : ℝ) < 1 / N :=
  one_div_pos.mpr (Nat.cast_pos.mpr hN)

/-- The chiral spinors as a submodule. -/
def chiralSub (left : FC.C → Bool) : Submodule ℝ (SpinorFibre FC.C) where
  carrier := {ψ | IsChiral left ψ}
  add_mem' := fun {a b} ha hb s c hs => by
    show a s c + b s c = 0; rw [ha s c hs, hb s c hs, add_zero]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun r a ha s c hs => by
    show r • a s c = 0; rw [ha s c hs, smul_zero]

/-- The dual-chiral spinors as a submodule. -/
def cochiralSub (left : FC.C → Bool) : Submodule ℝ (SpinorFibre FC.C) where
  carrier := {ψ | IsCoChiral left ψ}
  add_mem' := fun {a b} ha hb s c hs => by
    show a s c + b s c = 0; rw [ha s c hs, hb s c hs, add_zero]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun r a ha s c hs => by
    show r • a s c = 0; rw [ha s c hs, smul_zero]

/-- **A bounded `C^{1,1}` comparison family member** with constant `B`, coframe values in `Kf`,
spatially `1`-periodic, with `smLie`-valued gauge field. -/
structure SampledFamily (B : ℝ) (Kf : Set CoframeFibre) (f : FieldTuple FC.C) : Prop where
  c11 : FieldC11 FC f B
  chart : ∀ y, f.e y ∈ Kf
  per_e : ∀ (n : Fin 3 → ℤ) y, f.e (y + spatialShift n) = f.e y
  per_A : ∀ (n : Fin 3 → ℤ) y, f.A (y + spatialShift n) = f.A y
  per_H : ∀ (n : Fin 3 → ℤ) y, f.H (y + spatialShift n) = f.H y
  per_Ψ : ∀ (n : Fin 3 → ℤ) y, f.Ψ (y + spatialShift n) = f.Ψ y
  per_Ψb : ∀ (n : Fin 3 → ℤ) y, f.Ψb (y + spatialShift n) = f.Ψb y
  lie : ∀ y μ, f.A y μ ∈ smLie
  chiral : ∀ y, IsChiral FC.left (f.Ψ y)
  cochiral : ∀ y, IsCoChiral FC.left (f.Ψb y)

theorem jc_add {d : ℕ} (j p : Fin d → ℤ) : jc (j + p) = jc j + jc p := by
  funext i; simp [jc]

theorem smul_jc_spatial {N : ℕ} (hN : 0 < N) (n : Fin 3 → ℤ) :
    (1 / (N : ℝ)) • jc (Fin.cons 0 (fun i => (N : ℤ) * n i) : Fin 4 → ℤ) = spatialShift n := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [jc, spatialShift]
  · simp [jc, spatialShift]
    field_simp

theorem recon_samp_periodic {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}
    (hN : 0 < N) {g : E4 → W} (hg : ∀ (n : Fin 3 → ℤ) y, g (y + spatialShift n) = g y)
    (n : Fin 3 → ℤ) (y : E4) :
    recon (1 / (N : ℝ)) (samp (1 / (N : ℝ)) g) (y + spatialShift n) =
      recon (1 / (N : ℝ)) (samp (1 / (N : ℝ)) g) y := by
  rw [← smul_jc_spatial hN n]
  refine recon_add_shift (by positivity) _ (fun j => ?_) y
  simp only [samp, jc_add, smul_add, smul_jc_spatial hN n, hg]

/-- **The reconstructed fields `z_h = 𝒥_h(q_h)`** of the sampled family member, as smooth local
fields on `(0,T) × 𝕋³`. -/
def reconSmooth (T : ℝ) {N : ℕ} (hN : 0 < N) {B : ℝ} {Kf : Set CoframeFibre}
    {f : FieldTuple FC.C} (hf : SampledFamily FC B Kf f) : SmoothFields T FC.left where
  z := reconFields FC (1 / N) (sampleRec FC (1 / N) f)
  smooth_e := (contDiff_recon (one_div_N_pos hN) _).contDiffOn
  smooth_A := (contDiff_recon (one_div_N_pos hN) _).contDiffOn
  smooth_H := (contDiff_recon (one_div_N_pos hN) _).contDiffOn
  smooth_Ψ := (contDiff_recon (one_div_N_pos hN) _).contDiffOn
  smooth_Ψb := (contDiff_recon (one_div_N_pos hN) _).contDiffOn
  periodic_e := recon_samp_periodic hN hf.per_e
  periodic_A := recon_samp_periodic hN hf.per_A
  periodic_H := recon_samp_periodic hN hf.per_H
  periodic_Ψ := recon_samp_periodic hN hf.per_Ψ
  periodic_Ψb := recon_samp_periodic hN hf.per_Ψb
  lie := fun x μ => by
    have hm := recon_mem (S := Submodule.pi univ fun _ : Fin 4 => smLie)
      (g := samp (1 / (N : ℝ)) f.A) (one_div_N_pos hN)
      (fun j => Submodule.mem_pi.mpr fun μ _ => hf.lie _ μ) x
    exact Submodule.mem_pi.mp hm μ (mem_univ μ)
  chiral := fun x => recon_mem (S := chiralSub FC FC.left) (g := samp (1 / (N : ℝ)) f.Ψ)
    (one_div_N_pos hN) (fun j => hf.chiral _) x
  cochiral := fun x => recon_mem (S := cochiralSub FC FC.left) (g := samp (1 / (N : ℝ)) f.Ψb)
    (one_div_N_pos hN) (fun j => hf.cochiral _) x

theorem reconSmooth_z (T : ℝ) {N : ℕ} (hN : 0 < N) {B : ℝ} {Kf : Set CoframeFibre}
    {f : FieldTuple FC.C} (hf : SampledFamily FC B Kf f) :
    (reconSmooth FC T hN hf).z = reconFields FC (1 / N) (sampleRec FC (1 / N) f) := rfl

/-- The reconstruction of a `C^{1,1}` tuple's samples is `C^{1,1}` with constant `cRec B`. -/
theorem fieldC11_reconFields {f : FieldTuple FC.C} {B : ℝ} (hf : FieldC11 FC f B) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) : FieldC11 FC (reconFields FC h (sampleRec FC h f)) (cRec * B) :=
  ⟨isC11_recon_samp hf.e hh hh1, isC11_recon_samp hf.A hh hh1, isC11_recon_samp hf.H hh hh1,
    isC11_recon_samp hf.Ψ hh hh1, isC11_recon_samp hf.Ψb hh hh1⟩

theorem ptSmall_reconFields_sub {f : FieldTuple FC.C} {B : ℝ} (hf : FieldC11 FC f B) {h : ℝ}
    (hh : 0 < h) (y : E4) :
    PtSmall FC (reconFields FC h (sampleRec FC h f) - f) y ((cVal 4 + cDer 4) * B * h) := by
  have hB := hf.nonneg
  have hv := cVal_nonneg (d := 4); have hd := cDer_nonneg (d := 4)
  have k0 : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E4 → W}, IsC11 g B →
      ‖recon h (samp h g) y - g y‖ ≤ (cVal 4 + cDer 4) * B * h := fun hg =>
    (norm_recon_samp_sub_le' hg hh y).trans (by nlinarith [mul_nonneg hd (mul_nonneg hB hh.le)])
  have k1 : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E4 → W}, IsC11 g B →
      ‖fderiv ℝ (recon h (samp h g) - g) y‖ ≤ (cVal 4 + cDer 4) * B * h := fun hg => by
    rw [fderiv_sub ((contDiff_recon hh _).differentiable (by simp) y) (hg.differentiable y)]
    exact (norm_fderiv_recon_samp_sub_le hg hh y).trans
      (by nlinarith [mul_nonneg hv (mul_nonneg hB hh.le)])
  exact ⟨k0 hf.e, k1 hf.e, k0 hf.A, k1 hf.A, k0 hf.H, k1 hf.H, k0 hf.Ψ, k1 hf.Ψ, k0 hf.Ψb,
    k1 hf.Ψb⟩

/-! ### Tests and complete variations -/

section Tests

variable {T : ℝ} {K : CylRegion T}

theorem fieldC11_of_test {r₀ : ℕ} (hr : 2 ≤ r₀) {v : FieldTuple FC.C}
    (hv : v ∈ testSubmodule FC.left K) (hn : testNorm r₀ v ≤ 1) : FieldC11 FC v 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hv
  have n1 := crNorm_nonneg r₀ v.e; have n2 := crNorm_nonneg r₀ v.A
  have n3 := crNorm_nonneg r₀ v.H; have n4 := crNorm_nonneg r₀ v.Ψ
  have n5 := crNorm_nonneg r₀ v.Ψb
  unfold testNorm at hn
  exact ⟨(isC11_of_isCylTest h1 hr).mono (by linarith),
    (isC11_of_isCylTest h2 hr).mono (by linarith), (isC11_of_isCylTest h3 hr).mono (by linarith),
    (isC11_of_isCylTest h4 hr).mono (by linarith), (isC11_of_isCylTest h5 hr).mono (by linarith)⟩

theorem cylTest_eq_zero {t₀ t₁ : ℝ} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E4 → F} (hg : IsCylTest K g) {y : E4}
    (hy : y 0 ∉ Ioo t₀ t₁) : g y = 0 :=
  image_eq_zero_of_notMem_tsupport fun hy' => hy (hK _ (hg.support hy'))

end Tests

/-- Uniform `C^{1,1}` bound of the metric lift `ė(k)` at a `C^{1,1}` coframe in a compact set. -/
theorem exists_metricLift_c11 {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e k : E4 → CoframeFibre, IsC11 e Bz → (∀ y, e y ∈ Ke) → IsC11 k 1 →
      IsC11 (metricLift e k) C := by
  obtain ⟨C₀, hC₀⟩ := exists_IsC11_comp (E := E4) isOpen_univ
    (contDiff_metricLiftL (n := 2)).contDiffOn hKe (subset_univ _) Bz
  refine ⟨4 * |C₀|, by positivity, fun e k he hK hk => ?_⟩
  have h1 := hC₀ e he hK
  have h2 := h1.bilin (ContinuousLinearMap.id ℝ (CoframeFibre →L[ℝ] CoframeFibre)) hk
  have hC := h1.nonneg
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CoframeFibre →L[ℝ] CoframeFibre)
  refine (h2.mono ?_).congr fun y => rfl
  rw [abs_of_nonneg hC]
  nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ (CoframeFibre →L[ℝ] CoframeFibre))]

theorem variationDirection_eq_zero {z v : FieldTuple FC.C} {y : E4} (he : v.e y = 0)
    (hA : v.A y = 0) (hH : v.H y = 0) (hΨ : v.Ψ y = 0) (hΨb : v.Ψb y = 0) :
    (variationDirection z v).e y = 0 ∧ (variationDirection z v).A y = 0 ∧
      (variationDirection z v).H y = 0 ∧ (variationDirection z v).Ψ y = 0 ∧
      (variationDirection z v).Ψb y = 0 := by
  refine ⟨?_, hA, hH, hΨ, hΨb⟩
  show metricLift z.e v.e y = 0
  rw [metricLift_eq, he, map_zero]


/-! ### The periodized complete variation agrees with `v̂` near the box -/

theorem tper_eventuallyEq_self {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {P : ℕ}
    (hP : 0 < P) {g : E4 → W} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < P)
    (hg : ∀ y, y 0 ∉ Icc a b → g y = 0) {y : E4} (h1 : b - P < y 0) (h2 : y 0 < P + a) :
    tper P g =ᶠ[𝓝 y] g := by
  have := tper_eventuallyEq hP ha hab hb hg 0 (y := y) (by simpa using h1) (by simpa using h2)
  simpa using this

theorem eventuallyEq_zero_of_time {W : Type*} [NormedAddCommGroup W] {g : E4 → W} {a b : ℝ}
    (hg : ∀ y, y 0 ∉ Icc a b → g y = 0) {y : E4} (hy : y 0 ∉ Icc a b) : g =ᶠ[𝓝 y] 0 := by
  have ho : IsOpen {x : E4 | x 0 ∉ Icc a b} :=
    (isClosed_Icc.preimage (continuous_apply 0)).isOpen_compl
  exact Filter.eventually_of_mem (ho.mem_nhds hy) fun x hx => hg x hx

theorem gjet_congr {d d' : FieldTuple FC.C} {x : E4} (he : d.e =ᶠ[𝓝 x] d'.e) :
    gjet FC d x = gjet FC d' x := by
  have hj : eJet d.e x = eJet d'.e x := funext fun i =>
    show fderiv ℝ d.e x (unitE i) = fderiv ℝ d'.e x (unitE i) by rw [he.fderiv_eq]
  simp only [gjet, he.eq_of_nhds, hj]

theorem gjet_zero (x : E4) : gjet FC (0 : FieldTuple FC.C) x = 0 := by
  have h0 : DifferentiableAt ℝ (0 : FieldTuple FC.C).e x := differentiableAt_const _
  have := gjet_sub FC h0 h0 (x := x)
  rw [sub_self, sub_self] at this
  exact this.symm

section Identification

variable {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
  (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {P : ℕ} (hTP : T ≤ P) {r : ℕ}

include h0 h01 h1 hK hTP

/-- Germ data of the periodized variation `ṽ = tper_P v̂`: it agrees with `v̂` near every point of
time in `(t₁ - P, P + t₀)`, and `v̂` vanishes near every point of time outside `[t₀, t₁]`. -/
theorem tperTuple_germ (z : FieldTuple FC.C) (v : CrTest FC.left r K) {x : E4}
    (hx1 : t₁ - P < x 0) (hx2 : x 0 < P + t₀) :
    let vh := variationDirection z v.val
    let vt := tperTuple FC P vh
    vt.e =ᶠ[𝓝 x] vh.e ∧ vt.A =ᶠ[𝓝 x] vh.A ∧ vt.H =ᶠ[𝓝 x] vh.H ∧ vt.Ψ =ᶠ[𝓝 x] vh.Ψ ∧
      vt.Ψb =ᶠ[𝓝 x] vh.Ψb := by
  intro vh vt
  have hP : 0 < P := by
    have : (0 : ℝ) < P := by linarith
    exact_mod_cast this
  have hb : t₁ < (P : ℝ) := by linarith
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := v.2
  have hz : ∀ y, y 0 ∉ Icc t₀ t₁ → vh.e y = 0 ∧ vh.A y = 0 ∧ vh.H y = 0 ∧ vh.Ψ y = 0 ∧
      vh.Ψb y = 0 := fun y hy =>
    have hy' : y 0 ∉ Ioo t₀ t₁ := fun h => hy (Ioo_subset_Icc_self h)
    variationDirection_eq_zero FC (cylTest_eq_zero hK k1 hy') (cylTest_eq_zero hK k2 hy')
      (cylTest_eq_zero hK k3 hy') (cylTest_eq_zero hK k4 hy') (cylTest_eq_zero hK k5 hy')
  exact ⟨tper_eventuallyEq_self hP h0 h01.le hb (fun y hy => (hz y hy).1) hx1 hx2,
    tper_eventuallyEq_self hP h0 h01.le hb (fun y hy => (hz y hy).2.1) hx1 hx2,
    tper_eventuallyEq_self hP h0 h01.le hb (fun y hy => (hz y hy).2.2.1) hx1 hx2,
    tper_eventuallyEq_self hP h0 h01.le hb (fun y hy => (hz y hy).2.2.2.1) hx1 hx2,
    tper_eventuallyEq_self hP h0 h01.le hb (fun y hy => (hz y hy).2.2.2.2) hx1 hx2⟩

theorem vh_germ_zero (z : FieldTuple FC.C) (v : CrTest FC.left r K) {x : E4}
    (hx : x 0 ∉ Icc t₀ t₁) :
    let vh := variationDirection z v.val
    vh.e =ᶠ[𝓝 x] (0 : FieldTuple FC.C).e ∧ vh.A =ᶠ[𝓝 x] (0 : FieldTuple FC.C).A ∧
      vh.H =ᶠ[𝓝 x] (0 : FieldTuple FC.C).H ∧ vh.Ψ =ᶠ[𝓝 x] (0 : FieldTuple FC.C).Ψ ∧
      vh.Ψb =ᶠ[𝓝 x] (0 : FieldTuple FC.C).Ψb := by
  intro vh
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := v.2
  have hz : ∀ y, y 0 ∉ Icc t₀ t₁ → vh.e y = 0 ∧ vh.A y = 0 ∧ vh.H y = 0 ∧ vh.Ψ y = 0 ∧
      vh.Ψb y = 0 := fun y hy =>
    have hy' : y 0 ∉ Ioo t₀ t₁ := fun h => hy (Ioo_subset_Icc_self h)
    variationDirection_eq_zero FC (cylTest_eq_zero hK k1 hy') (cylTest_eq_zero hK k2 hy')
      (cylTest_eq_zero hK k3 hy') (cylTest_eq_zero hK k4 hy') (cylTest_eq_zero hK k5 hy')
  exact ⟨eventuallyEq_zero_of_time (fun y hy => (hz y hy).1) hx,
    eventuallyEq_zero_of_time (fun y hy => (hz y hy).2.1) hx,
    eventuallyEq_zero_of_time (fun y hy => (hz y hy).2.2.1) hx,
    eventuallyEq_zero_of_time (fun y hy => (hz y hy).2.2.2.1) hx,
    eventuallyEq_zero_of_time (fun y hy => (hz y hy).2.2.2.2) hx⟩

theorem time_window_of_mem_box {x : E4} (hx : x ∈ compBox P) :
    t₁ - P < x 0 ∧ x 0 < P + t₀ := by
  have a := hx.1 0
  have b := hx.2 0
  simp [compBox] at a b
  constructor <;> linarith

theorem time_window_of_mem_slab {x : E4} (hx : x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set) :
    t₁ - P < x 0 ∧ x 0 < P + t₀ := by
  obtain ⟨hx0, -⟩ := mem_slabChart.mp hx
  constructor <;> linarith [hx0.1, hx0.2]

/-- **Identification of the continuum Standard-Model first variation with the box integral of the
packet density along the periodized complete variation.** -/
theorem firstVariation_sm_eq_box (θ : CoefficientBank Ysec) (z : SmoothFields T FC.left)
    {Bz : ℝ} (hzC : FieldC11 FC z.z Bz) (v : CrTest FC.left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL) (hzK : ∀ x, z.z.e x ∈ Ke) :
    firstVariation T FC θ .standardModel z.z v.val = ∫ x in compBox P,
      fderiv ℝ (smPt FC θ) (contJet FC z.z x)
        (contJetDeriv FC z.z (tperTuple FC P (variationDirection z.z v.val)) x) := by
  rw [smVariation_eq_cov FC θ h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) z v hKe
    hKeGL (fun x _ => hzK x)]
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := v.2
  have hvd : ∀ x, DiffAt FC v.val x := fun x =>
    ⟨k1.smooth.differentiable (by simp) x, k2.smooth.differentiable (by simp) x,
      k3.smooth.differentiable (by simp) x, k4.smooth.differentiable (by simp) x,
      k5.smooth.differentiable (by simp) x⟩
  have hpt : ∀ x, t₁ - P < x 0 → x 0 < P + t₀ →
      (bosonCov θ (redJet z.z x) + diracCov FC θ (redJet z.z x)) (testJet v.val x) =
        fderiv ℝ (smPt FC θ) (contJet FC z.z x)
          (contJetDeriv FC z.z (tperTuple FC P (variationDirection z.z v.val)) x) := by
    intro x hx1 hx2
    rw [smCov_eq_contJetDeriv FC θ (hzC.diffAt FC x) (hvd x) (hKeGL (hzK x))]
    obtain ⟨g1, g2, g3, g4, g5⟩ := tperTuple_germ FC h0 h01 h1 hK hTP z.z v hx1 hx2
    rw [contJetDeriv_congr FC z.z g1 g2 g3 g4 g5]
  rw [setIntegral_congr_fun (slabChart t₀ t₁ h0 h01 h1 (T := T)).isOpen.measurableSet
    fun x hx => hpt x (time_window_of_mem_slab h0 h01 h1 hK hTP hx).1
      (time_window_of_mem_slab h0 h01 h1 hK hTP hx).2]
  refine integral_slab_eq_compBox h0 h01 h1 hTP fun x hx hxt => ?_
  obtain ⟨w1, w2⟩ := time_window_of_mem_box h0 h01 h1 hK hTP hx
  obtain ⟨g1, g2, g3, g4, g5⟩ := tperTuple_germ FC h0 h01 h1 hK hTP z.z v w1 w2
  obtain ⟨e1, e2, e3, e4, e5⟩ := vh_germ_zero FC h0 h01 h1 hK hTP z.z v hxt
  rw [contJetDeriv_congr FC z.z (g1.trans e1) (g2.trans e2) (g3.trans e3) (g4.trans e4)
    (g5.trans e5), contJetDeriv_zero, map_zero]

/-- **Identification of the continuum gravitational first variation with the box integral of the
first-order density along the periodized complete variation.** -/
theorem firstVariation_grav_eq_box (θ : CoefficientBank Ysec) (z : SmoothFields T FC.left)
    {Bz : ℝ} (hzC : FieldC11 FC z.z Bz) (v : CrTest FC.left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL) (hzK : ∀ x, z.z.e x ∈ Ke) :
    firstVariation T FC θ .gravity z.z v.val = ∫ x in compBox P,
      fderiv ℝ (gravPt θ) (gjet FC z.z x)
        (gjet FC (tperTuple FC P (variationDirection z.z v.val)) x) := by
  rw [gravVariation_eq_cov FC θ h0 h01 h1 hK z v hKe hKeGL (fun x _ => hzK x)]
  obtain ⟨k1, -⟩ := v.2
  have hpt : ∀ x, t₁ - P < x 0 → x 0 < P + t₀ →
      gravCov θ (redJet z.z x) (testJet v.val x) = fderiv ℝ (gravPt θ) (gjet FC z.z x)
        (gjet FC (tperTuple FC P (variationDirection z.z v.val)) x) := by
    intro x hx1 hx2
    have hR : redJet z.z x ∈ jetGL FC.C := hKeGL (hzK x)
    rw [← fderiv_gravPt_redVar θ hR, fderiv_gravPt_gproj FC θ hR, gproj_redJet,
      gproj_redVar FC (z := z.z) (v := v.val) (hzC.e.differentiable x)
        (k1.smooth.differentiable (by simp) x)]
    obtain ⟨g1, -⟩ := tperTuple_germ FC h0 h01 h1 hK hTP z.z v hx1 hx2
    rw [gjet_congr FC g1]
  rw [setIntegral_congr_fun (slabChart t₀ t₁ h0 h01 h1 (T := T)).isOpen.measurableSet
    fun x hx => hpt x (time_window_of_mem_slab h0 h01 h1 hK hTP hx).1
      (time_window_of_mem_slab h0 h01 h1 hK hTP hx).2]
  refine integral_slab_eq_compBox h0 h01 h1 hTP fun x hx hxt => ?_
  obtain ⟨w1, w2⟩ := time_window_of_mem_box h0 h01 h1 hK hTP hx
  obtain ⟨g1, -⟩ := tperTuple_germ FC h0 h01 h1 hK hTP z.z v w1 w2
  obtain ⟨e1, -⟩ := vh_germ_zero FC h0 h01 h1 hK hTP z.z v hxt
  rw [gjet_congr FC (g1.trans e1), gjet_zero, map_zero]

end Identification


/-! ### `prop:mesh-consistency` -/

theorem sum_sector (F : Sector → ℝ≥0∞) : ∑ b, F b = F .gravity + F .standardModel :=
  Finset.sum_pair (by decide)

/-- **The per-test sector estimates** behind `eq:mesh-C1`: for every member of the bounded
`C^{1,1}` family, every mesh `h = 1/N` with `N ≥ N₀`, every physical test with `‖v‖_{C^{r₀}} ≤ 1`
and both sectors, `|D S_{b,h}(q_h)[𝓘_h v] - D𝒮_{b,θ}(z_h)[v]| ≤ C h`. -/
theorem exists_mesh_sector_bound [Nonempty FC.C] (θ : CoefficientBank Ysec) {T t₀ t₁ : ℝ}
    (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {P : ℕ} (hTP : T ≤ P) {r₀ : ℕ} (hr : 2 ≤ r₀)
    {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre} (hKf : IsCompact Kf)
    (hKfGL : Kf ⊆ coframeGL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ f : FieldTuple FC.C, SampledFamily FC B Kf f →
      ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ v ∈ testSubmodule FC.left K, testNorm r₀ v ≤ 1 →
      ∀ b : Sector, |finiteVar (sectorAction FC θ P N b) (sampleRec FC (1 / N) f)
          (liftRec FC P N (1 / N) (reconFields FC (1 / N) (sampleRec FC (1 / N) f)) v) -
        firstVariation T FC θ b (reconFields FC (1 / N) (sampleRec FC (1 / N) f)) v| ≤
        C * (1 / N) := by
  have hP' : (0 : ℝ) < P := by linarith
  have hP : 0 < P := by exact_mod_cast hP'
  have hb : t₁ < (P : ℝ) := by linarith
  obtain ⟨δ, hδ, hδU⟩ := hKf.exists_cthickening_subset_open isOpen_coframeGL hKfGL
  set Ke := cthickening δ Kf
  have hKe : IsCompact Ke := hKf.cthickening
  have hKeGL : Ke ⊆ coframeGL := hδU
  have hcR := one_le_cRec
  set Bz := cRec * B
  have hBz : 0 ≤ Bz := by positivity
  obtain ⟨Cml, hCml0, hCml⟩ := exists_metricLift_c11 hKe Bz
  set Bv := Cml + 1
  have hBv : 0 ≤ Bv := by positivity
  have hgap : 0 < (P : ℝ) + t₀ - t₁ := by linarith
  set Bt := max Bv (2 * Bv / (P + t₀ - t₁))
  have hBt : 0 ≤ Bt := le_max_of_le_left hBv
  set BW := cRec * Bt
  have hBW : 0 ≤ BW := by positivity
  set Benv := Bz + Bt + BW
  have hBenv : 0 ≤ Benv := by positivity
  set κ := (cVal 4 + cDer 4) * Bt
  have hκ : 0 ≤ κ := by
    have := cVal_nonneg (d := 4); have := cDer_nonneg (d := 4); positivity
  obtain ⟨Csm, h₀, hh₀, hSM⟩ := exists_sm_estimate FC θ hKe hKeGL hBenv hκ P
  obtain ⟨Cgr, hGR⟩ := exists_grav_estimate FC θ hKe hKeGL hBenv hκ P
  set h₁ := min h₀ (min 1 (δ / (cVal 4 * B + 1)))
  have hcv := cVal_nonneg (d := 4)
  have hh₁ : 0 < h₁ := lt_min hh₀ (lt_min one_pos (by positivity))
  refine ⟨|Csm| + |Cgr|, by positivity, ⌈1 / h₁⌉₊ + 1, fun f hf N hN₀ hN v hv hn b => ?_⟩
  set h : ℝ := 1 / N with hhdef
  have hh : 0 < h := one_div_N_pos hN
  have hhh₁ : h ≤ h₁ := by
    have hN' : (1 / h₁ : ℝ) < N := by
      have := Nat.le_ceil (1 / h₁)
      have h2 : ((⌈1 / h₁⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN₀
      push_cast at h2
      linarith
    rw [hhdef, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hh₁] at hN'
    linarith
  have hhh₀ : h ≤ h₀ := hhh₁.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := hhh₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ : h ≤ δ / (cVal 4 * B + 1) := hhh₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  set q := sampleRec FC h f
  set zS := reconSmooth FC T hN hf
  set z := reconFields FC h q
  have hzC : FieldC11 FC z Bz := fieldC11_reconFields FC hf.c11 hh hh1
  have hzK : ∀ y, z.e y ∈ Ke := fun y => by
    refine mem_cthickening_of_dist_le (z.e y) (f.e y) δ Kf (hf.chart y) ?_
    rw [dist_eq_norm]
    refine (norm_recon_samp_sub_le' hf.c11.e hh y).trans ?_
    rw [le_div_iff₀ (by positivity)] at hhδ
    nlinarith
  -- the test and its complete variation
  have hv1 : FieldC11 FC v 1 := fieldC11_of_test FC hr hv hn
  set vh := variationDirection z v
  have hvh : FieldC11 FC vh Bv :=
    ⟨(hCml z.e v.e hzC.e hzK hv1.e).mono (by linarith), hv1.A.mono (by linarith),
      hv1.H.mono (by linarith), hv1.Ψ.mono (by linarith), hv1.Ψb.mono (by linarith)⟩
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := id hv
  have hz0 : ∀ y, y 0 ∉ Icc t₀ t₁ → vh.e y = 0 ∧ vh.A y = 0 ∧ vh.H y = 0 ∧ vh.Ψ y = 0 ∧
      vh.Ψb y = 0 := fun y hy =>
    have hy' : y 0 ∉ Ioo t₀ t₁ := fun h => hy (Ioo_subset_Icc_self h)
    variationDirection_eq_zero FC (cylTest_eq_zero hK k1 hy') (cylTest_eq_zero hK k2 hy')
      (cylTest_eq_zero hK k3 hy') (cylTest_eq_zero hK k4 hy') (cylTest_eq_zero hK k5 hy')
  set vt := tperTuple FC P vh
  have hvt : FieldC11 FC vt Bt :=
    ⟨isC11_tper hP h0 h01.le hb (fun y hy => (hz0 y hy).1) hvh.e,
      isC11_tper hP h0 h01.le hb (fun y hy => (hz0 y hy).2.1) hvh.A,
      isC11_tper hP h0 h01.le hb (fun y hy => (hz0 y hy).2.2.1) hvh.H,
      isC11_tper hP h0 h01.le hb (fun y hy => (hz0 y hy).2.2.2.1) hvh.Ψ,
      isC11_tper hP h0 h01.le hb (fun y hy => (hz0 y hy).2.2.2.2) hvh.Ψb⟩
  have hw : liftRec FC P N h z v = sampleRec FC h vt := liftRec_eq_sampleRec_tper FC hP hN z v
  rw [hw]
  set w := sampleRec FC h vt
  have hWC : FieldC11 FC (reconFields FC h w) BW := fieldC11_reconFields FC hvt hh hh1
  have hsm : ∀ y, PtSmall FC (reconFields FC h w - vt) y (κ * h) := fun y => by
    have := ptSmall_reconFields_sub FC hvt hh y
    simpa only [κ] using this
  have hzE : FieldC11 FC z Benv := hzC.mono FC (by simp only [Benv]; linarith)
  have hWE : FieldC11 FC (reconFields FC h w) Benv := hWC.mono FC (by simp only [Benv]; linarith)
  have hvE : FieldC11 FC vt Benv := hvt.mono FC (by simp only [Benv]; linarith)
  have hCsm : Csm * h ≤ (|Csm| + |Cgr|) * h :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
      hh.le
  have hCgr : Cgr * h ≤ (|Csm| + |Cgr|) * h :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
      hh.le
  cases b
  · have hid : firstVariation T FC θ .gravity z v = ∫ x in compBox P,
        fderiv ℝ (gravPt θ) (gjet FC z x) (gjet FC vt x) :=
      firstVariation_grav_eq_box FC h0 h01 h1 hK hTP (r := r₀) θ zS hzC
        (⟨v, hv⟩ : CrTest FC.left r₀ K) hKe hKeGL hzK
    calc _ = |finiteVar (gravAction FC θ P N) q w - ∫ x in compBox P,
          fderiv ℝ (gravPt θ) (gjet FC z x) (gjet FC vt x)| := by rw [hid]; rfl
      _ ≤ Cgr * h := hGR N q w vt hN hzE hWE hvE hzK hsm
      _ ≤ _ := hCgr
  · have hid : firstVariation T FC θ .standardModel z v = ∫ x in compBox P,
        fderiv ℝ (smPt FC θ) (contJet FC z x) (contJetDeriv FC z vt x) :=
      firstVariation_sm_eq_box FC h0 h01 h1 hK hTP (r := r₀) θ zS hzC
        (⟨v, hv⟩ : CrTest FC.left r₀ K) hKe hKeGL hzK
    calc _ = |finiteVar (smAction FC θ P N) q w - ∫ x in compBox P,
          fderiv ℝ (smPt FC θ) (contJet FC z x) (contJetDeriv FC z vt x)| := by rw [hid]; rfl
      _ ≤ Csm * h := hSM N q w vt hN hhh₀ hzE hWE hvE hzK hsm
      _ ≤ _ := hCsm


/-- **`prop:mesh-consistency`, `eq:mesh-C1`**: on a bounded `C^{1,1}` coframe/gauge/matter family
with coframe values in a fixed compact subset `Kf` of the nondegenerate chart (common
inverse-coframe bound), the comparison regulator of `app:reconstruction` (cardinal
reconstruction of nodal samples, lattice comparison action, sampled test lifts) satisfies
`c_h(K) ≤ C_K h`, `h = 1/N`, uniformly over the family. -/
theorem mesh_consistency [Nonempty FC.C] (θ : CoefficientBank Ysec) {T t₀ t₁ : ℝ}
    (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {P : ℕ} (hTP : T ≤ P) {r₀ : ℕ} (hr : 2 ≤ r₀)
    {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre} (hKf : IsCompact Kf)
    (hKfGL : Kf ⊆ coframeGL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ f : FieldTuple FC.C, SampledFamily FC B Kf f →
      ∀ N : ℕ, N₀ ≤ N → 0 < N →
        comparisonDefect FC T θ P N r₀ K (sampleRec FC (1 / N) f) ≤
          ENNReal.ofReal (C * (1 / N)) := by
  obtain ⟨C, hC, N₀, hb⟩ := exists_mesh_sector_bound FC θ h0 h01 h1 hK hTP hr hB hKf hKfGL
  refine ⟨2 * C, by positivity, N₀, fun f hf N hN₀ hN => ?_⟩
  have hh : (0 : ℝ) < 1 / N := one_div_N_pos hN
  have hs : ∀ b : Sector, (⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm r₀ v.1 ≤ 1),
      ENNReal.ofReal |finiteVar (sectorAction FC θ P N b) (sampleRec FC (1 / N) f)
        (liftRec FC P N (1 / N) (reconFields FC (1 / N) (sampleRec FC (1 / N) f)) v.1) -
      firstVariation T FC θ b (reconFields FC (1 / N) (sampleRec FC (1 / N) f)) v.1|) ≤
        ENNReal.ofReal (C * (1 / N)) := fun b =>
    iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (hb f hf N hN₀ hN v.1 v.2 hv b)
  unfold comparisonDefect
  rw [sum_sector]
  refine (add_le_add (hs .gravity) (hs .standardModel)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

/-! ### Non-vacuity -/

/-- The constant flat family (identity coframe, zero gauge, Higgs and spinor fields) is a member
of the sampled class with `B = ‖flatCoframe‖` and `Kf = {flatCoframe}`. -/
theorem sampledFamily_flat :
    SampledFamily FC ‖flatCoframe‖ {flatCoframe}
      ((fun _ => flatCoframe, 0, 0, 0, 0) : FieldTuple FC.C) := by
  have hc : IsC11 (fun _ : E4 => flatCoframe) ‖flatCoframe‖ := IsC11.const flatCoframe
  have hB : 0 ≤ ‖flatCoframe‖ := norm_nonneg _
  have h0 : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W],
      IsC11 (0 : E4 → W) ‖flatCoframe‖ := fun {W} _ _ =>
    (IsC11.const (0 : W)).mono (by simpa using hB) |>.congr fun _ => rfl
  exact ⟨⟨hc, h0, h0, h0, h0⟩, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => smLie.zero_mem, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

theorem flatCoframe_mem_GL : flatCoframe ∈ coframeGL := by
  show (Matrix.of flatCoframe).det ≠ 0
  have : Matrix.of flatCoframe = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext a μ; simp [flatCoframe, Matrix.one_apply]
  rw [this, Matrix.det_one]; exact one_ne_zero

/-- Non-vacuity of `mesh_consistency`: its hypotheses are met (for the trivial carrier, any bank,
any compact region with time support in `(t₀,t₁)`) by the flat family. -/
example (θ : CoefficientBank Unit) {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {P : ℕ} (hTP : T ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      comparisonDefect (trivialCarrier Unit) T θ P N 2 K
        (sampleRec (trivialCarrier Unit) (1 / N)
          ((fun _ => flatCoframe, 0, 0, 0, 0) : FieldTuple (trivialCarrier Unit).C)) ≤
        ENNReal.ofReal (C * (1 / N)) := by
  haveI : Nonempty (trivialCarrier Unit).C := ⟨()⟩
  obtain ⟨C, hC, N₀, hb⟩ := mesh_consistency (trivialCarrier Unit) θ h0 h01 h1 hK hTP le_rfl
    (norm_nonneg flatCoframe) (isCompact_singleton (x := flatCoframe))
    (Set.singleton_subset_iff.mpr flatCoframe_mem_GL)
  exact ⟨C, hC, N₀, fun N hN₀ hN => hb _ (sampledFamily_flat _) N hN₀ hN⟩

end Comparison
end EinsteinSM
end RenewalGeometry
