/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeCalibrationSampling

/-!
# `cor:local-calibration-nonempty`: the calibration class of `thm:native-closure` is non-empty

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty`: "Let `z_*` be
a smooth solution on a compact slab, with compatible fixed gauges and a smooth periodic extension
to the buffered comparison box that remains in the chosen field-value chart.  Nodal sampling
followed by trigonometric reconstruction yields records for `S_h^loc` with `σ_h = O(h)` and with
the budgets of `thm:native-closure` tending to zero for a suitable `K_h → ∞`.  Thus the
quantitative hypotheses are nonempty."

**`local_calibration_nonempty`**: for a slab model `M`, a smooth `2π`-periodic native field `Y`
(the periodic extension of a solution: native Euler equations on the buffered slab
`[t₀ - b, t₁ + b) × [0, 2π)³` in the **physical directions**, `𝓔₀(Y) ∘ physF πg = 0` — coframe,
gauge directions in the gauge Lie algebra `𝔤`, Higgs, spinor and co-spinor directions; the gauge
sector of the corrected encoding lives in `𝔤`, the non-gauge directions of `𝔄` are not imposed), in the fixed gauges (`FieldGauge`: adapted Lorentz gauge, temporal
internal gauge, gauge Lie subspace, physical co-spinors), with coframe values in a compact chart
`K_e⁰ ⊂ {det > 0}` and in the Lorentzian chart, whose dilated metric is in harmonic gauge on the
slab, and for cutoffs `c₁h^{-β} ≤ K_h ≤ c₂h^{-β}` (`0 < β < 1/(k+4)`, `k ≥ 4`), along the odd grids
`n = 2m + 1` (`h = 2π/n`) there are a frame margin `δ > 0`, the reference tuple
`z_* = toTuple(dilField t₀ Y)` with its reference class (`z_*` is exact on the slab and lies in
`refSet`), a compact chart `K_e`, an amplitude `A` and `C_σ, C ≥ 0` such that the sampled records
`u_h = 𝖲_h Y`:

1. eventually satisfy all the record hypotheses of `thm:native-closure` (`RecordHyp`, with
   `σ_h = C_σ h`);
2. have `hK_h → 0`, `K_h → ∞` and `τ_{h,k+2}(K_h) → 0`;
3. have `D^full_{h,k} = i_{h,k} + γ_{h,k} + F_{h,k} → 0` — the initial `H^k` mismatch
   `i_{h,k}` and the harmonic mismatch `γ_{h,k}` by the `C^N` convergence of the reconstructions
   (`CalibrationSampling.cn_recon`) and the `C^N` continuity of the actual-jet state and harmonic
   defect (`StateConv.init_tendsto`, `StateConv.harm_tendsto`), the forcing budget `F_{h,k}` by
   `LocalCalibration.sampled_native_source_phys`;
4. hence (`thm:native-closure`, `ClosureUnconditional.native_closure_unconditional`) eventually
   `‖𝒰_h - 𝒰_*‖_{C_tH^k} + ‖Riem‖_{L²H^{k-1}} + ‖T^{SM}‖_{L²H^k} ≤ C D^full_{h,k} → 0`.

`local_calibration_nonempty_exists` takes `K_h = h^{-β}`.  Disclosed renderings (as in
`thm:native-closure`): `Σ = 𝕋³`, period-`2π` native box, odd grids, adapted Lorentz gauge,
`SlabModel` hypotheses; the harmonic gauge of the reference is stated for the metric of the dilated
field in the unit-period slab coordinates.
-/

open Filter Topology Set Metric Finset Asymptotics
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.LocalCalibrationClosed

open SobolevOpen (pd)
open CNConv StateConv RecordTuple SlabData NativeDensity NativeModel NativeFrameBridge
  ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState CoupledBootstrap FieldScaling
  PalatiniEuler NativeBosonicEuler ActualJetFrame CalibrationSampling SlabSymmetric
  ClosureUnconditional ActualJetCompleteForcing
open DiscreteEulerConsistency (R4 pos samp IsPeriodic realVec contEuler limDensity eulerRow)
open ShiftedPlaquette
open ShiftedJetAction (Grid)
open NativeScaling (Mat metric)
open TrigInterp (recon reconLow tau)
open NativeRate (forcingBudget)
open LocalCalibration (oddN meshOdd tendsto_meshOdd)

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The slab model of the native slab data in the orthonormal coordinates `slabX`. -/
abbrev slabMod {δ : ℝ} (hδ : 0 < δ) {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢) (k : ℕ) {t₀ t₁ : ℝ} (h01 : t₀ < t₁) :=
  slabModel (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
    (slabT_pos h01)

open Classical in
set_option maxHeartbeats 1600000 in
/-- **`cor:local-calibration-nonempty`** (see the module docstring). -/
theorem local_calibration_nonempty {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hper : IsPeriodic (2 * π) Y) (hg : FieldGauge M Y) {Ke₀ : Set Mat} (hKe₀ : IsCompact Ke₀)
    (hdet₀ : ∀ e ∈ Ke₀, 0 < e.det) (hYe : ∀ z, (Y z).1 ∈ Ke₀)
    (hchart : ∀ z, IsLorChart (ginvS (Y z).1)) {k : ℕ} (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀) (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁)
    (hsol : ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
      (contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z).comp
        (NativeTail.physF M.πg) = 0)
    (hharm : ∀ x : R4, x 0 ∈ Icc 0 (slabT t₀ t₁) → ∀ l,
      ActualJetWriter.C (ginvOf (gF (eF (dilField t₀ Y)) x))
        (fun α => pd (gF (eF (dilField t₀ Y))) α x) l = 0)
    {β c₁ c₂ : ℝ} (hβ : 0 < β) (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
    (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β))
    {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp M δ (dilField t₀ Y)) (Ke : Set Mat) (A Cσ C : ℝ)
      (Kr : Set (Fin (ActualJetKato.dimS m (HSp M) 𝓢 (CoSpinor 𝓢)) → ℝ)) (R₁ : ℝ),
      IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ 0 ≤ Cσ ∧ 0 ≤ C ∧
      IsCompact Kr ∧ Kr ⊆ chartC (slabX M) ∧ 0 ≤ R₁ ∧
      ExactOn (toSMData M δ) (slabT t₀ t₁) (toTuple hδ hT) ∧
      toTuple hδ hT ∈ refSet (toSMData M δ) (slabX M) k (slabT t₀ t₁) Kr R₁ ∧
      (∀ᶠ m in atTop, RecordHyp M δ Ke A t₀ t₁ b (oddN m) (samp (n := oddN m) (meshOdd m) Y)
        (Kh m) (Cσ * meshOdd m)) ∧
      Tendsto (fun m => meshOdd m * Kh m) atTop (𝓝 0) ∧ Tendsto Kh atTop atTop ∧
      Tendsto (fun m => tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y)) atTop
        (𝓝 0) ∧
      Tendsto (fun m => ‖(slabMod M hδ eY eYD k h01).init
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)) -
          (slabMod M hδ eY eYD k h01).init (toTuple hδ hT)‖) atTop (𝓝 0) ∧
      Tendsto (fun m => (slabMod M hδ eY eYD k h01).harm
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)))
        atTop (𝓝 0) ∧
      Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) atTop (𝓝 0) ∧
      (∀ᶠ m in atTop, dist ((slabMod M hδ eY eYD k h01).obs
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)))
          ((slabMod M hδ eY eYD k h01).obs (toTuple hδ hT)) ≤
        C * (‖(slabMod M hδ eY eYD k h01).init
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)) -
          (slabMod M hδ eY eYD k h01).init (toTuple hδ hT)‖ +
          (slabMod M hδ eY eYD k h01).harm
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)) +
          forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
            (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
            (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y)))) ∧
      Tendsto (fun m => dist ((slabMod M hδ eY eYD k h01).obs
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)))
          ((slabMod M hδ eY eYD k h01).obs (toTuple hδ hT))) atTop (𝓝 0) := by
  have hdet : ∀ z, 0 < (Y z).1.det := fun z => hdet₀ _ (hYe z)
  -- the chart margin
  obtain ⟨Ke', δ, ε, hKe'c, hKe'det, hδ, hε, hmarg, hnear⟩ :=
    exists_chart_margin hY hper hdet hchart
  have hT : TupleHyp M δ (dilField t₀ Y) :=
    tupleHyp_dil_periodic hY hper hg (fun z => hmarg _ (hnear z _ (by simp [hε.le]))) t₀
  set zs := toTuple hδ hT with hzs
  -- exactness and the reference class
  have hex : ExactOn (toSMData M δ) (slabT t₀ t₁) zs :=
    exactOn_dil hδ hper hdet hb h01 hsol hT fun x hx => funext (hharm x hx)
  obtain ⟨Kr, R₁, hKr, hKO, hR₁, hzsR⟩ :=
    exists_refSet_of_exact (toSMData M δ) (slabX M) hex k
  -- the source budgets of the sampled records
  obtain ⟨Ke, A, Cs, Cσ, c_res, τs, hKec, hKedet, -, hCs, hCσ, hcres, hτs, hev, -, hτm, -, hF⟩ :=
    LocalCalibration.sampled_native_source_phys M.toData M.πg hKe₀ hdet₀ hY hper hYe k (by omega)
      hCk hb h0 h1 hsol hβ hβk hc₁ Kh hKh
  -- reconstructions in the chart margin
  have hrec0 := cn_recon hY hper (k + 3)
  have hnearev : ∀ᶠ m in atTop, ∀ x,
      (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y) x).1 ∈ Ke' := by
    filter_upwards [hrec0.conv ε hε] with m hm x
    have h1' := hm 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h1'
    refine hnear x _ ?_
    rw [dist_eq_norm]
    exact (norm_fst_le _).trans h1'
  have hTev : ∀ᶠ m in atTop, TupleHyp M δ
      (dilField t₀ (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y))) := by
    filter_upwards [hnearev] with m hm
    exact tupleHyp_dil ⟨m, rfl⟩ (nodalGauge_samp hg _ _) hKe'det hm
      (fun e he _ => hmarg e he) t₀
  -- the record hypotheses
  have hrec : ∀ᶠ m in atTop, RecordHyp M δ Ke A t₀ t₁ b (oddN m)
      (samp (n := oddN m) (meshOdd m) Y) (Kh m) (Cσ * meshOdd m) := by
    filter_upwards [hev, hKh, hTev] with m hm hKm hTm
    exact ⟨⟨m, rfl⟩, hKm.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
      mul_nonneg hCσ (LocalCalibration.meshOdd_pos m).le, hm.2.2.2.2.2.2.1, hTm⟩
  -- `hK → 0` and `τ_{k+2} → 0`
  obtain ⟨Cτ, hCτ⟩ := hτm.bound
  have hβ2 : 2 * β < 1 := by
    have hk4 : (8 : ℝ) ≤ k + 4 := by
      have : (4 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have : β * (k + 4) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hβk
    nlinarith
  obtain ⟨hhK, hτ0⟩ := rate_tendsto (β := β) (c₂ := c₂) (Cτ := Cτ) (h := meshOdd) (K := Kh)
    (τm := fun m => tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y)) hβ2
    tendsto_meshOdd (by
      filter_upwards [hKh, hCτ] with m hKm hm
      have hτ0 : 0 ≤ tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y) :=
        TrigInterp.tau_nonneg _ (by linarith [hKm.1]) _ _
      refine ⟨hKm.1, hKm.2.2, hτ0, ?_⟩
      rw [Real.norm_of_nonneg hτ0] at hm
      refine hm.trans (le_of_eq ?_)
      rw [Real.norm_of_nonneg (by have := LocalCalibration.meshOdd_pos m; positivity)])
  -- `K_h → ∞`
  have hKinf : Tendsto Kh atTop atTop := by
    have hpow : Tendsto (fun m => c₁ * meshOdd m ^ (-β)) atTop atTop := by
      have h1 : Tendsto (fun m => meshOdd m ^ (-β)) atTop atTop :=
        (tendsto_rpow_neg_nhdsGT_zero (by linarith : -β < 0)).comp tendsto_meshOdd
      exact h1.const_mul_atTop hc₁
    exact tendsto_atTop_mono' atTop (hKh.mono fun m hm => hm.2.1) hpow
  -- the actual tuples converge
  set z : ℕ → STuple M := fun m =>
    recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) zs with hzdef
  have htc : TupleCN (k + 3) atTop z zs :=
    tupleCN_of_fields hδ (cn_dilField hrec0 t₀) hT (by
      filter_upwards [hTev] with m hm
      exact ⟨hm, recTuple_eq M hδ t₀ zs hm⟩)
  have hMC : MetCompact zs := metCompact_toTuple hδ hT
  have hi := init_tendsto (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ)
    (slabT_pos h01) (htc.mono (M := k + 1) (by omega)) hMC
  have hγ := harm_tendsto (toSMData M δ) (slabX M) eY eYD (toSMData_smooth M hδ)
    (slabT_pos h01) htc hMC hex
  have hD := (hi.add hγ).add hF
  rw [add_zero, add_zero] at hD
  -- `thm:native-closure`
  obtain ⟨C, τs', hC, hτs', H⟩ := native_closure_unconditional M hδ eY eYD hKec hKedet A hk hCk
    hb h0 h1 h01 hKr hKO hR₁
  have hcl := H atTop oddN (fun m => samp (n := oddN m) (meshOdd m) Y) Kh
    (fun m => Cσ * meshOdd m) zs hzsR hrec hhK (hτ0.eventually (ge_mem_nhds hτs')) hD
  refine ⟨δ, hδ, hT, Ke, A, Cσ, C, Kr, R₁, hKec, hKedet, hCσ, hC, hKr, hKO, hR₁, hex, hzsR, hrec,
    hhK, hKinf, hτ0, hi, hγ, hF, hcl, ?_⟩
  have hup : Tendsto (fun m => C * (‖(slabMod M hδ eY eYD k h01).init (z m) -
      (slabMod M hδ eY eYD k h01).init zs‖ + (slabMod M hδ eY eYD k h01).harm (z m) +
      forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
        (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
        (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y)))) atTop (𝓝 0) := by
    simpa using hD.const_mul C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun m => dist_nonneg) hcl

/-- **A suitable cutoff exists** (`K_h ≍ h^{-β}`, the choice of the manuscript's proof): the family
`K_h = h^{-β}` satisfies the cutoff hypothesis of `local_calibration_nonempty` with `c₁ = c₂ = 1`
and `K_h → ∞`. -/
theorem rpow_cutoff_admissible {β : ℝ} (hβ : 0 < β) :
    (∀ᶠ m in atTop, 1 ≤ meshOdd m ^ (-β) ∧ 1 * meshOdd m ^ (-β) ≤ meshOdd m ^ (-β) ∧
      meshOdd m ^ (-β) ≤ 1 * meshOdd m ^ (-β)) ∧
    Tendsto (fun m => meshOdd m ^ (-β)) atTop atTop := by
  have hh1 : ∀ᶠ m in atTop, meshOdd m ≤ 1 :=
    (tendsto_meshOdd.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds one_pos)
  refine ⟨?_, (tendsto_rpow_neg_nhdsGT_zero (by linarith : -β < 0)).comp tendsto_meshOdd⟩
  filter_upwards [hh1] with m hm
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos (LocalCalibration.meshOdd_pos m) hm
    (by linarith), by rw [one_mul], by rw [one_mul]⟩

end RenewalGeometry.LocalCalibrationClosed

end
