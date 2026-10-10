/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetStateConvergence
import RenewalGeometry.Continuum.LocalCalibrationBudgets
import RenewalGeometry.Continuum.NativeSampledSourcePhys
import RenewalGeometry.Continuum.NativeClosureUnconditional

/-!
# Sampled smooth solutions: convergence of the actual tuples of the reconstructions

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty` ("Smooth
Fourier decay and the aliasing formula give uniform `H^q` bounds and convergence of each fixed
number of reconstructed derivatives … derivative convergence controls the initial and harmonic
mismatches").

For a smooth `2π`-periodic native field `Y` (the periodic extension of a solution), sampled on the
odd grids `n = 2m + 1` (`h = 2π/n`) and reconstructed trigonometrically:

* **`cn_recon`** — `𝓘_h^trig 𝖲_h Y → Y` in `C^N` for every `N` (sampling/reconstruction
  consistency `TrigConv.norm_iteratedFDeriv_recon_sub_le`, error `O(h)` in every `C^j`);
* `cn_dilField` — the dilation to unit spatial period preserves `C^N` convergence;
* **`tupleCN_of_fields`** — native fields converging in `C^N` give actual field tuples
  (`RecordTuple.toTuple`) converging in `C^N` (`StateConv.TupleCN`);
* `metCompact_toTuple` — the metric of the actual tuple of a native field satisfying the tuple
  hypotheses stays in a compact subset of the Lorentzian chart (lattice periodicity);
* `tupleHyp_dil_periodic` — the dilated periodic field satisfies the tuple hypotheses;
* **`exists_chart_margin`** — a compact coframe chart `K_e` and a frame margin `δ > 0` containing
  the coframe values of `Y` and, eventually, of all reconstructions;
* **`exactOn_dil`** — the actual tuple of the dilated solution is an exact solution of the slab
  data on the slab (native Euler equations on the buffered slab, `bosF_dil`/`dirF_dil`, and the
  harmonic gauge of its metric).
-/

open Filter Topology Set Metric Finset
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.CalibrationSampling

open SobolevOpen (pd)
open CNConv StateConv RecordTuple SlabData NativeDensity NativeModel NativeFrameBridge
  ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState CoupledBootstrap FieldScaling
  PalatiniEuler NativeBosonicEuler ActualJetFrame
open DiscreteEulerConsistency (R4 pos samp IsPeriodic realVec contEuler limDensity)
open ShiftedPlaquette
open NativeScaling (Mat metric)
open TrigInterp (recon reconLow tau)
open LocalCalibration (oddN meshOdd tendsto_meshOdd)

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Sampling and reconstruction -/

section Recon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Nodal sampling followed by trigonometric reconstruction converges in `C^N`** for every
smooth `2π`-periodic field, along the odd grids `n = 2m + 1`. -/
theorem cn_recon {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) (hper : IsPeriodic (2 * π) Y) (N : ℕ) :
    CN N atTop (fun m => recon (oddN m) (samp (n := oddN m) (meshOdd m) Y)) Y := by
  obtain ⟨M, hM⟩ := TrigConv.exists_bound_iteratedFDeriv hY (by positivity) hper (N + 5)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  choose C hC0 hC using fun j : ℕ => TrigConv.norm_iteratedFDeriv_recon_sub_le (V := V) j
  set Cs : ℝ := ∑ j ∈ Finset.range (N + 1), C j with hCs
  have hCj : ∀ j ≤ N, C j ≤ Cs := fun j hj =>
    Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.2 (by omega))
  refine ⟨Eventually.of_forall fun m => by exact VecTrig.contDiff_tp _ _, hY,
    ⟨M, fun j hj z => hM j (by omega) z⟩, fun ε hε => ?_⟩
  have hh : Tendsto (fun m => Cs * M * meshOdd m) atTop (𝓝 0) := by
    simpa using (tendsto_meshOdd.mono_right nhdsWithin_le_nhds).const_mul (Cs * M)
  filter_upwards [(tendsto_order.1 hh).2 ε hε] with m hm j hj z
  have hodd : Odd (oddN m) := ⟨m, rfl⟩
  have h1 := hC j (oddN m) hodd Y M hY hper (fun r hr z => hM r (by omega) z) z
  have hmesh : 0 ≤ meshOdd m := (LocalCalibration.meshOdd_pos m).le
  calc _ ≤ C j * M * (2 * π / (oddN m : ℕ)) := h1
    _ = C j * M * meshOdd m := rfl
    _ ≤ Cs * M * meshOdd m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCj j hj) hM0) hmesh
    _ ≤ ε := hm.le

end Recon

/-! ### From native fields to actual tuples -/

section Tuples

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)
variable {ι : Type*} {l : Filter ι} {N : ℕ}

/-- The dilation to unit spatial period preserves `C^N` convergence. -/
theorem cn_dilField {W : ι → R4 → Field 𝔄 𝓗 𝓢} {W₀ : R4 → Field 𝔄 𝓗 𝓢} (h : CN N l W W₀)
    (t₀ : ℝ) : CN N l (fun i => dilField t₀ (W i)) (dilField t₀ W₀) :=
  ((h.affine (2 * π) (Pi.single 0 t₀)).clm
    (fieldScale (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) two_pi_ne : Field 𝔄 𝓗 𝓢 →L[ℝ] Field 𝔄 𝓗 𝓢)).congr
    (Eventually.of_forall fun i => rfl) rfl

/-- The metric of a coframe as a smooth map. -/
theorem contDiff_metricF : ContDiff ℝ ∞ (fun e : Mat => fun i j : Fin 4 => metric e i j) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [metric_apply']
  fun_prop

variable {M}

/-- **Native fields converging in `C^N` give actual field tuples converging in `C^N`.** -/
theorem tupleCN_of_fields {δ : ℝ} (hδ : 0 < δ) {W : ι → R4 → Field 𝔄 𝓗 𝓢}
    {W₀ : R4 → Field 𝔄 𝓗 𝓢} (hW : CN N l W W₀) (h0 : TupleHyp M δ W₀) {z : ι → STuple M}
    (hz : ∀ᶠ i in l, ∃ h : TupleHyp M δ (W i), z i = toTuple hδ h) :
    TupleCN N l z (toTuple hδ h0) := by
  have hz' : ∀ᶠ i in l, ∃ h : TupleHyp M δ (W i), z i = toTuple hδ h := hz
  have he : CN N l (fun i x => (W i x).1) (fun x => (W₀ x).1) :=
    hW.clm (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (CN_comp_contDiff contDiff_metricF he).congr ?_ rfl
    filter_upwards [hz'] with i ⟨h, hi⟩
    rw [hi]; rfl
  · refine (CN.pi fun μ => (hW.clm (projAμ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ)).clm
      (LinearMap.toContinuousLinearMap M.φ.toLinearMap)).congr ?_ rfl
    filter_upwards [hz'] with i ⟨h, hi⟩
    rw [hi]; rfl
  · refine (hW.clm (projH (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).congr ?_ rfl
    filter_upwards [hz'] with i ⟨h, hi⟩
    rw [hi]; rfl
  · refine (hW.clm (projψ (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).congr ?_ rfl
    filter_upwards [hz'] with i ⟨h, hi⟩
    rw [hi]; rfl
  · refine (hW.clm (projψb (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))).congr ?_ rfl
    filter_upwards [hz'] with i ⟨h, hi⟩
    rw [hi]; rfl

/-- The unit cube `[0, 1]⁴`. -/
def cube : Set R4 := Set.pi univ fun _ => Icc 0 1

theorem isCompact_cube : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc

/-- A `ℤ⁴`-periodic map takes all its values on the unit cube. -/
theorem exists_cube_of_zperiodic {α : Type*} {f : R4 → α} (hf : PeriodicCube.IsZPeriodic f)
    (x : R4) : ∃ x' ∈ cube, f x = f x' := by
  set k : Fin 4 → ℤ := fun μ => ⌊x μ⌋
  refine ⟨x - PeriodicCube.zvec k, fun μ _ => ?_, ?_⟩
  · simp only [Pi.sub_apply, PeriodicCube.zvec, k]
    exact ⟨by linarith [Int.floor_le (x μ)], by linarith [Int.lt_floor_add_one (x μ)]⟩
  · have := hf k (x - PeriodicCube.zvec k)
    rw [sub_add_cancel] at this
    exact this

/-- **The metric of the actual tuple stays in a compact subset of the Lorentzian chart.** -/
theorem metCompact_toTuple {δ : ℝ} (hδ : 0 < δ) {W₀ : R4 → Field 𝔄 𝓗 𝓢}
    (h0 : TupleHyp M δ W₀) : MetCompact (toTuple hδ h0) := by
  have hper : PeriodicCube.IsZPeriodic (eF W₀) := fun k x => by
    have := h0.perL k x
    simpa using this
  refine ⟨(fun e : Mat => fun i j : Fin 4 => metric e i j) '' (eF W₀ '' cube),
    (isCompact_cube.image (contDiff_eF' h0.smooth).continuous).image
      contDiff_metricF.continuous, ?_, fun x => ?_⟩
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact ⟨metric_det_ne (h0.det_ne x), h0.chart hδ x⟩
  · obtain ⟨x', hx', he⟩ := exists_cube_of_zperiodic hper x
    refine ⟨eF W₀ x', ⟨x', hx', rfl⟩, ?_⟩
    show (fun i j => metric (eF W₀ x') i j) = gF (eF W₀) x
    rw [← he]; rfl

end Tuples

/-! ### Periodicity of the continuum Euler covector -/

section PeriodicEuler

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem jet1_add_of_periodic' {Y : R4 → V} {a : R4} (hY : ∀ z, Y (z + a) = Y z) (z : R4) :
    DiscreteEulerConsistency.jet1 Y (z + a) = DiscreteEulerConsistency.jet1 Y z := by
  have e : (fun z => Y (z + a)) = Y := funext hY
  simp only [DiscreteEulerConsistency.jet1]
  rw [← fderiv_comp_add_right, e, hY]

theorem contEuler_add_of_periodic' (L : V × (Fin 4 → V) → ℝ) {Y : R4 → V} {a : R4}
    (hY : ∀ z, Y (z + a) = Y z) (z : R4) : contEuler L Y (z + a) = contEuler L Y z := by
  unfold contEuler
  rw [jet1_add_of_periodic' hY]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← fderiv_comp_add_right]
  congr 2
  funext z'
  simp only [jet1_add_of_periodic' hY]

end PeriodicEuler

/-! ### Fixed gauges, chart margins and exactness of the reference -/

section Reference

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **The fixed gauges of a native field** (`cor:local-calibration-nonempty`: "compatible fixed
gauges"): adapted Lorentz gauge (lower-triangular coframe with positive diagonal), temporal
internal gauge `A₀ = 0`, gauge potential in the gauge Lie subspace, physical co-spinors. -/
structure FieldGauge (Y : R4 → Field 𝔄 𝓗 𝓢) : Prop where
  adapted : ∀ z, IsAdaptedCoframe (Y z).1
  temporal : ∀ z, (Y z).2.1 0 = 0
  gauge : ∀ z μ, (Y z).2.1 μ ∈ M.gSub
  clin : ∀ z, IsCLin M.toModel (Y z).2.2.2.2

variable {M}

/-- Samples of a field in the fixed gauges are in the nodal gauges. -/
theorem nodalGauge_samp {Y : R4 → Field 𝔄 𝓗 𝓢} (hg : FieldGauge M Y) (n : ℕ) (h : ℝ) :
    NodalGauge M (samp (n := n) h Y) :=
  ⟨fun y => hg.adapted _, fun y => hg.temporal _, fun y μ => hg.gauge _ μ, fun y => hg.clin _⟩

/-- The dilation of a `2π`-periodic field is `ℤ⁴`-periodic. -/
theorem dil_shift_periodic {Y : R4 → Field 𝔄 𝓗 𝓢} (hper : IsPeriodic (2 * π) Y) (t₀ : ℝ)
    (k : Fin 4 → ℤ) (x : R4) :
    dilField t₀ Y (x + PeriodicCube.zvec k) = dilField t₀ Y x := by
  rw [dilField_apply, dilField_apply]
  congr 1
  rw [smul_add, add_right_comm]
  exact hper.add_intVec k _

/-- **The dilated periodic field satisfies the tuple hypotheses.** -/
theorem tupleHyp_dil_periodic {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hper : IsPeriodic (2 * π) Y) (hg : FieldGauge M Y) {δ : ℝ}
    (hmarg : ∀ z, Margin δ (ginvOf (fun i j => metric ((2 * π) • (Y z).1) i j))) (t₀ : ℝ) :
    TupleHyp M δ (dilField t₀ Y) where
  smooth := (fieldScale (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) two_pi_ne).contDiff.comp
    (hY.comp ((contDiff_const_smul (2 * π)).add contDiff_const))
  per k x := by
    rw [sshift_eq_zvec]
    exact dil_shift_periodic hper t₀ _ x
  perL k x := by
    show eF _ ((1 : ℝ) • (x + PeriodicCube.zvec k)) = eF _ ((1 : ℝ) • x)
    rw [one_smul, one_smul]
    unfold eF
    rw [dil_shift_periodic hper]
  adapted x := by
    have ha := hg.adapted ((2 * π) • x + Pi.single 0 t₀)
    rw [dilField_apply, fieldScale_apply]
    refine ⟨fun a μ h => ?_, fun a => ?_⟩
    · simp [ha.1 a μ h]
    · simpa using mul_pos two_pi_pos (ha.2 a)
  margin x := hmarg _
  temporal x := by
    rw [dilField_apply, fieldScale_apply]
    simp [hg.temporal]
  gauge x μ := by
    rw [dilField_apply, fieldScale_apply, ← M.gLie_eq]
    exact M.gSub.smul_mem _ (hg.gauge _ μ)
  clin x := by
    rw [dilField_apply, fieldScale_apply]
    exact hg.clin _

/-- The range of a continuous `2π`-periodic field is compact. -/
theorem isCompact_range_of_periodic {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : R4 → W}
    (hG : Continuous G) {L : ℝ} (hL : 0 < L) (hper : IsPeriodic L G) :
    IsCompact (Set.range G) := by
  set Q : Set R4 := Set.pi univ (fun _ => Icc 0 L)
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have e : Set.range G = G '' Q := by
    refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
    rintro _ ⟨z, rfl⟩
    set k : Fin 4 → ℤ := fun μ => ⌊z μ / L⌋
    set z' : R4 := z - L • realVec k
    have hz' : z' ∈ Q := by
      intro μ _
      simp only [z', Pi.sub_apply, Pi.smul_apply, realVec, smul_eq_mul, k]
      constructor
      · have := Int.floor_le (z μ / L); rw [le_div_iff₀ hL] at this; linarith
      · have := Int.lt_floor_add_one (z μ / L); rw [div_lt_iff₀ hL] at this; linarith
    refine ⟨z', hz', ?_⟩
    have := hper.add_intVec k z'
    rw [show z' + L • realVec k = z by simp [z']] at this
    exact this.symm
  rw [e]
  exact hQ.image hG

/-- The inverse metric of the scaled coframe. -/
def ginvS (e : Mat) : Fin 4 → Fin 4 → ℝ := ginvOf (fun i j => metric ((2 * π) • e) i j)

theorem continuousOn_ginvS : ContinuousOn ginvS {e : Mat | 0 < e.det} := by
  have h1 : Continuous fun e : Mat => fun i j : Fin 4 => metric ((2 * π) • e) i j :=
    contDiff_metricF.continuous.comp (continuous_const_smul (2 * π))
  refine contDiffOn_ginvOf.continuousOn.comp h1.continuousOn fun e he => ?_
  show (Matrix.of fun i j => metric ((2 * π) • e) i j).det ≠ 0
  refine metric_det_ne ?_
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ two_pi_ne) (ne_of_gt he)

/-- **A compact coframe chart with a frame margin** containing a neighbourhood of the coframe
values of a smooth periodic field in the Lorentzian chart. -/
theorem exists_chart_margin {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hper : IsPeriodic (2 * π) Y) (hdet : ∀ z, 0 < (Y z).1.det)
    (hchart : ∀ z, IsLorChart (ginvS (Y z).1)) :
    ∃ (Ke : Set Mat) (δ ε : ℝ), IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ 0 < δ ∧ 0 < ε ∧
      (∀ e ∈ Ke, Margin δ (ginvS e)) ∧ ∀ z (e : Mat), dist e (Y z).1 ≤ ε → e ∈ Ke := by
  set E0 : Set Mat := Set.range fun z => (Y z).1 with hE0
  have hE0c : IsCompact E0 := isCompact_range_of_periodic
    (continuous_fst.comp hY.continuous) two_pi_pos fun z μ => by
      show (Y _).1 = (Y z).1
      rw [hper z μ]
  set O : Set Mat := {e : Mat | 0 < e.det} ∩ ginvS ⁻¹' {gi | IsLorChart gi} with hO
  have hOo : IsOpen O := continuousOn_ginvS.isOpen_inter_preimage
    (isOpen_lt continuous_const (continuous_id.matrix_det)) isOpen_isLorChart
  have hE0O : E0 ⊆ O := by
    rintro _ ⟨z, rfl⟩
    exact ⟨hdet z, hchart z⟩
  obtain ⟨ε, hε, hεO⟩ := hE0c.exists_cthickening_subset_open hOo hE0O
  set Ke : Set Mat := cthickening ε E0 with hKe
  have hKec : IsCompact Ke := hE0c.cthickening
  have hKg : IsCompact (ginvS '' Ke) :=
    hKec.image_of_continuousOn (continuousOn_ginvS.mono fun e he => (hεO he).1)
  obtain ⟨δ, hδ, hmarg⟩ := exists_margin hKg (by rintro _ ⟨e, he, rfl⟩; exact (hεO he).2)
  refine ⟨Ke, δ, ε, hKec, fun e he => (hεO he).1, hδ, hε, fun e he => hmarg _ ⟨e, he, rfl⟩,
    fun z e he => mem_cthickening_of_dist_le e (Y z).1 ε E0 ⟨z, rfl⟩ he⟩

/-- `ξ` reduced to the buffered comparison box by spatial periods. -/
theorem exists_buf_rep {t₀ t₁ b : ℝ} (hb : 0 < b) {ξ : R4} (hξ : ξ 0 ∈ Icc t₀ t₁) :
    ∃ k : Fin 4 → ℤ, ξ - (2 * π) • realVec k ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b) := by
  set k : Fin 4 → ℤ := Fin.cons 0 (fun i => ⌊ξ i.succ / (2 * π)⌋) with hk
  refine ⟨k, ⟨?_, fun i => ?_⟩⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, realVec, smul_eq_mul, hk, Fin.cons_zero,
      Int.cast_zero, mul_zero, sub_zero]
    exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, realVec, smul_eq_mul, hk, Fin.cons_succ]
    have hL := two_pi_pos
    constructor
    · have := Int.floor_le (ξ i.succ / (2 * π)); rw [le_div_iff₀ hL] at this; linarith
    · have := Int.lt_floor_add_one (ξ i.succ / (2 * π)); rw [div_lt_iff₀ hL] at this; linarith

/-- **The actual tuple of the dilated solution is exact on the slab**: the bosonic and Dirac slab
residuals vanish by the **physical** native Euler equations on the buffered slab
(`𝓔₀(Y) ∘ physF πg = 0`: coframe, `𝔤`-gauge, Higgs, spinor and co-spinor directions; `bosF_dil`,
`dirF_dil` read only these rows), and the harmonic defect vanishes by the harmonic gauge of its
metric. -/
theorem exactOn_dil {δ : ℝ} (hδ : 0 < δ) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hper : IsPeriodic (2 * π) Y) (hdet : ∀ z, 0 < (Y z).1.det) {t₀ t₁ b : ℝ} (hb : 0 < b)
    (h01 : t₀ < t₁)
    (hsol : ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
      (contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z).comp
        (NativeTail.physF M.πg) = 0)
    (h : TupleHyp M δ (dilField t₀ Y))
    (hharm : ∀ x : R4, x 0 ∈ Icc 0 (slabT t₀ t₁) → CF (toTuple hδ h) x = 0) :
    ExactOn (toSMData M δ) (slabT t₀ t₁) (toTuple hδ h) := by
  have hRper0 : IsPeriodic (2 * π) (NativeTail.Rfull M.toData Y) := fun z μ =>
    contEuler_add_of_periodic' _ (fun w => hper w μ) z
  have hRper : IsPeriodic (2 * π)
      (fun z => (NativeTail.Rfull M.toData Y z).comp (NativeTail.physF M.πg)) := fun z μ => by
    show (NativeTail.Rfull M.toData Y (z + _)).comp _ = _
    rw [hRper0 z μ]
  have hR0 : ∀ x : R4, x 0 ∈ Icc 0 (slabT t₀ t₁) →
      (NativeTail.Rfull M.toData Y ((2 * π) • x + Pi.single 0 t₀)).comp
        (NativeTail.physF M.πg) = 0 := by
    intro x hx
    set ξ : R4 := (2 * π) • x + Pi.single 0 t₀
    have hξ : ξ 0 ∈ Icc t₀ t₁ := by
      have hT : slabT t₀ t₁ * (2 * π) = t₁ - t₀ := by
        unfold slabT; field_simp
      simp only [ξ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
      constructor
      · nlinarith [hx.1, two_pi_pos]
      · nlinarith [hx.2, two_pi_pos]
    obtain ⟨k, hk⟩ := exists_buf_rep hb hξ
    have := hRper.add_intVec k (ξ - (2 * π) • realVec k)
    rw [sub_add_cancel] at this
    rw [this]
    exact hsol _ hk
  intro x hx
  refine ⟨?_, ?_, hharm x hx⟩
  · refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun P => ?_
    rw [bosF_dil hδ hdet h P x]
    have : NativeTail.RBP M.toData M.πg Y ((2 * π) • x + Pi.single 0 t₀) = 0 :=
      NativeTail.RBP_eq_zero_of M.toData (hR0 x hx)
    rw [this, map_zero]
  · refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun P => ?_
    rw [dirF_dil hδ hdet h P x]
    have : NativeTail.RD M.toData Y ((2 * π) • x + Pi.single 0 t₀) = 0 :=
      NativeTail.RD_eq_zero_of M.toData (hR0 x hx)
    rw [this, map_zero]

end Reference


end RenewalGeometry.CalibrationSampling

end
