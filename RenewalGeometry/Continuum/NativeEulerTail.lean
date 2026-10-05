/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.DiscreteEulerRowDifference
import RenewalGeometry.Continuum.NativeTailTransferBounds

/-!
# The finite Euler-row tail transfer (`eq:native-Euler-tail`)

Einstein–Standard-Model action-closure manuscript, `lem:native-tail-transfer`, second display:
`‖E_h^{raw}(u_h) - E_h^{raw}(𝖲_h z_h^lo)‖_{0,h;Q'} ≤ C K² τ_{h,2}`.

The record `u_h` on `(ℤ/n)⁴` (`n` odd, `h = 2π/n`) is the sample of its reconstruction
`z_h = 𝓘_h^trig u_h` (`TrigInterp.recon_gpos`); the raw Euler row of the unchanged local action
`S_h^{loc}` (`NativeDensity.localAction`) is `K²` times the Euler row of the normalised shifted
first-jet action at mesh `ρ = hK` (`eulerRow_local_eq_scaled`, `lem:native-scaling`), and the
difference of the normalised rows of `z̃` and `z̃^lo` is bounded by the mean-value estimate
`EulerRowDiff.norm_eulerRow_sub_le` in terms of the first two normalised derivatives of
`z̃ - z̃^lo`, i.e. by `τ_{h,2}`.

* **`native_euler_tail`**: for a compact coframe chart `K_e`, an amplitude bound `A`, there are
  `C`, `c_res > 0`, `τ_* > 0` such that for every odd `n`, record `u_h`, `K ≥ 1` with `hK ≤ c_res`,
  `τ_{h,3}(K) ≤ τ_*`, full and low fields with coframe values in `K_e` and `|z^lo| ≤ A`,
  `‖E_h^{raw}(u_h)(x) - E_h^{raw}(𝖲_h z^lo)(x)‖ ≤ C K² τ_{h,2}` at every node, hence the mass norm
  `h⁴ Σ_x ‖…‖² ≤ ((2π)² C K² τ_{h,2})²` over the periodic box.
* **`native_tail_hyps_const`** (non-vacuity): a constant record has zero tail and constant full
  and low heads (`tau_const`, `recon_const`, `reconLow_const`, via the residue orthogonality
  `sum_cexp_phase_zmod`), so all record hypotheses of `native_euler_tail` and
  `native_source_tail` are satisfiable.
-/

open Finset Filter Topology Metric Set NormedSpace MeasureTheory
open scoped ContDiff

namespace RenewalGeometry.NativeTail

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency
open TrigInterp (recon reconLow tau)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- **`lem:native-scaling` on raw Euler rows**: on the chart, the raw Euler row of the local
action at mesh `h` is `K²` times the Euler row of the normalised first-jet action at `ρ = hK`. -/
theorem eulerRow_local_eq_scaled {n : ℕ} [NeZero n] {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    {y : Grid n → Field 𝔄 𝓗 𝓢} (hdet' : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) (x : Grid n) :
    eulerRow (localAction D h) h y x =
      K ^ 2 • eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (h * K, ξ))) (h * K)
        (shiftVec n)) (h * K) y x := by
  have hρ0 : 0 < h * K := mul_pos hh hK
  have e1 : eulerRow (localAction D h) h y x =
      eulerRow (action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n)) h y x := by
    unfold eulerRow
    erw [fderiv_localAction_eq D hh.ne' hdet' hlog]
    rfl
  rw [e1, eulerRow_smul_action (fun y' => action_firstJet_eq_scaled D hh.ne' hK.ne' y') y x
    hρ0.ne' hh.ne']
  congr 1
  field_simp

theorem eulerRow_local_eq_scaled_apply {n : ℕ} [NeZero n] {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    {y : Grid n → Field 𝔄 𝓗 𝓢} (hdet' : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) (x : Grid n)
    (v : Field 𝔄 𝓗 𝓢) :
    eulerRow (localAction D h) h y x v =
      K ^ 2 * eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (h * K, ξ))) (h * K)
        (shiftVec n)) (h * K) y x v :=
  (congrArg (fun T => T v) (eulerRow_local_eq_scaled D hh hK hdet' hlog x)).trans rfl

/-- The reconstruction of a record is `2π`-periodic in every coordinate. -/
theorem isPeriodic_tp {S : Finset (Fin 4 → ℤ)} (c : VecTrig.Coef 4 (Field 𝔄 𝓗 𝓢)) :
    IsPeriodic (2 * Real.pi) (VecTrig.tp S c) := fun z μ => TrigInterp.tp_periodic S c z μ


variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- The normalised first derivative of the rescaled low head is bounded by `240 A`. -/
theorem norm_jet1_resc_low_snd_le {n : ℕ} [NeZero n] (u : (Fin 4 → ZMod n) → Field 𝔄 𝓗 𝓢)
    {K A : ℝ} (hK : 1 ≤ K) (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (z : R4) :
    ‖(jet1 (resc K (reconLow n K u)) z).2‖ ≤ 240 * A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro μ
  have h1 := resc_reconLow_bound u hK hA 1 z
  have h2 := (iteratedFDeriv ℝ 1 (resc K (reconLow n K u)) z).le_opNorm (fun _ => evec μ)
  rw [iteratedFDeriv_one_apply] at h2
  simp only [norm_evec, Finset.prod_const_one, mul_one] at h2
  refine le_trans h2 ?_
  have : (240 : ℝ) ^ 1 * A = 240 * A := by ring
  linarith


/-! ### Pieces of the Euler-tail estimate -/

section Pieces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean-value bound `EulerRowDiff.norm_eulerRow_sub_le` for two fields sampled at mesh `h`,
read through their `K`-rescalings `z ↦ Y(K⁻¹ z)` sampled at the normalised mesh `hK`. -/
theorem row_diff_le_of_resc (σZ : ι → Fin 4 → ℤ) {F : ℝ × Jet ι V → ℝ} {S : Set (Jet ι V)}
    {δ M₂ M₃ : ℝ} (hF : DensityReg F S δ M₂ M₃) {n : ℕ} [NeZero n] {h K B t₂ t₃ s : ℝ}
    (hh : 0 < h) (hK : 0 < K) {Y₀ Y₁ : R4 → V}
    (hpY₀ : IsPeriodic ((n : ℝ) * h) Y₀) (hpY₁ : IsPeriodic ((n : ℝ) * h) Y₁)
    (hY : FieldBound (fun z => Y₀ (K⁻¹ • z)) B B B)
    (hW : FieldBound (fun z => Y₁ (K⁻¹ • z) - Y₀ (K⁻¹ • z)) t₂ t₂ t₃)
    (hW0 : ∀ z, ‖Y₁ (K⁻¹ • z) - Y₀ (K⁻¹ • z)‖ ≤ t₂)
    (hS : ∀ z, cmap (jet1 (fun z => Y₀ (K⁻¹ • z)) z) ∈ S) (hs0 : 0 ≤ s)
    (hs : ∀ i μ, |(σZ i μ : ℝ)| ≤ s) (hδ : h * K * (1 + cJet B B s) + (t₂ + t₂) < δ)
    (x : Grid n) :
    ‖eulerRow (action (fun ξ => F (h * K, ξ)) (h * K) (fun i => castVec (σZ i))) (h * K)
        (samp h Y₁) x -
      eulerRow (action (fun ξ => F (h * K, ξ)) (h * K) (fun i => castVec (σZ i))) (h * K)
        (samp h Y₀) x‖ ≤
      Fintype.card ι * (M₂ * (t₂ + t₂)) +
        Fintype.card (ι × Fin 4) * (M₃ * (t₂ + t₂) * (B + B + (t₂ + t₂)) + M₂ * (t₂ + t₂)) := by
  have hL : (n : ℝ) * (h * K) = K * ((n : ℝ) * h) := by ring
  have hpt₀ : IsPeriodic ((n : ℝ) * (h * K)) (fun z => Y₀ (K⁻¹ • z)) := by
    rw [hL]; exact hpY₀.rescale hK.ne'
  have hpt₁ : IsPeriodic ((n : ℝ) * (h * K)) (fun z => Y₁ (K⁻¹ • z)) := by
    rw [hL]; exact hpY₁.rescale hK.ne'
  have hpW : IsPeriodic ((n : ℝ) * (h * K)) (fun z => Y₁ (K⁻¹ • z) - Y₀ (K⁻¹ • z)) :=
    fun z μ => congrArg₂ (· - ·) (hpt₁ z μ) (hpt₀ z μ)
  have e₁ : (samp h Y₁ : Grid n → V) =
      samp (h * K) ((fun z => Y₀ (K⁻¹ • z)) + fun z => Y₁ (K⁻¹ • z) - Y₀ (K⁻¹ • z)) := by
    rw [← samp_rescale (Y := Y₁) hK.ne']
    congr 1
    funext z
    simp
  have e₀ : (samp h Y₀ : Grid n → V) = samp (h * K) (fun z => Y₀ (K⁻¹ • z)) :=
    (samp_rescale hK.ne').symm
  rw [e₁, e₀]
  exact EulerRowDiff.norm_eulerRow_sub_le hF hY hW hW0 hS hs0 hs (mul_pos hh hK) hpt₀ hpW hδ x

end Pieces

/-- Elementary arithmetic of the tail constant. -/
theorem tail_arith {a b M₂ M₃ B t C : ℝ} (hb : 0 ≤ b) (hM₃ : 0 ≤ M₃) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (hC : a * (M₂ * 2) + b * (M₃ * 2 * (2 * B + 2) + M₂ * 2) ≤ C) :
    a * (M₂ * (t + t)) + b * (M₃ * (t + t) * (B + B + (t + t)) + M₂ * (t + t)) ≤ C * t := by
  have hin : M₃ * (t + t) * (B + B + (t + t)) ≤ M₃ * 2 * (2 * B + 2) * t := by
    have h1 : B + B + (t + t) ≤ 2 * B + 2 := by linarith
    have h2 : 0 ≤ M₃ * t := mul_nonneg hM₃ ht
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hin hb
  have h4 := mul_le_mul_of_nonneg_right hC ht
  nlinarith

/-- Elementary arithmetic of the mesh/tail smallness. -/
theorem delta_arith {ρ c t δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hρ : ρ ≤ δ / (4 * (1 + c)))
    (ht : t ≤ δ / 8) : ρ * (1 + c) + (t + t) < δ := by
  have h2 : ρ * (1 + c) ≤ δ / 4 := by
    calc ρ * (1 + c) ≤ δ / (4 * (1 + c)) * (1 + c) := mul_le_mul_of_nonneg_right hρ (by linarith)
      _ = δ / 4 := by field_simp
  linarith

/-- The raw Euler-row difference of the local action is `K²` times the difference of the
normalised rows (`lem:native-scaling` applied to both fields). -/
theorem norm_eulerRow_local_sub_le {n : ℕ} [NeZero n] {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    {y₁ y₀ : Grid n → Field 𝔄 𝓗 𝓢} (hdet₁ : ∀ x, 0 < (coframe y₁ x).det)
    (hlog₁ : ∀ x μ ν, ‖cartanPlaquette h (coframe y₁) x μ ν - 1‖ < 1)
    (hdet₀ : ∀ x, 0 < (coframe y₀ x).det)
    (hlog₀ : ∀ x μ ν, ‖cartanPlaquette h (coframe y₀) x μ ν - 1‖ < 1) (x : Grid n) :
    ‖eulerRow (localAction D h) h y₁ x - eulerRow (localAction D h) h y₀ x‖ ≤
      K ^ 2 * ‖eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (h * K, ξ))) (h * K)
          (fun i => castVec (shiftZ i))) (h * K) y₁ x -
        eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (h * K, ξ))) (h * K)
          (fun i => castVec (shiftZ i))) (h * K) y₀ x‖ := by
  rw [castVec_shiftZ]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.sub_apply, eulerRow_local_eq_scaled_apply D hh hK hdet₁ hlog₁ x v,
    eulerRow_local_eq_scaled_apply D hh hK hdet₀ hlog₀ x v, ← mul_sub, norm_mul,
    Real.norm_of_nonneg (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← ContinuousLinearMap.sub_apply]
  exact ContinuousLinearMap.le_opNorm _ v

/-- The compact jet set of the low heads. -/
def lowJetSet (Ke : Set Mat) (A B : ℝ) : Set (DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) :=
  (fun wp => cmap wp) '' (({w : Field 𝔄 𝓗 𝓢 | w.1 ∈ Ke} ∩ closedBall 0 A) ×ˢ
    closedBall (0 : Fin 4 → Field 𝔄 𝓗 𝓢) B)

theorem isCompact_lowJetSet {Ke : Set Mat} (hKe : IsCompact Ke) (A B : ℝ) :
    IsCompact (lowJetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B) :=
  (((isCompact_closedBall _ _).inter_left (hKe.isClosed.preimage continuous_fst)).prod
    (isCompact_closedBall _ _)).image cmap.continuous

theorem contDiffAt_lowJetSet {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) (A B : ℝ) :
    ∀ θ ∈ Icc (0 : ℝ) 1, ∀ c ∈ lowJetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B,
      ContDiffAt ℝ 3 (scaledDensity D) (θ, ((0 : ℝ), c)) := by
  rintro θ - c ⟨wp, hwp, rfl⟩
  refine (contDiffAt_scaledDensity D (fun s => ?_)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (hdet _ hwp.1.1).ne'

section Record

variable {n : ℕ} [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢) {K : ℝ}

theorem fieldBound_resc_low (hK : 1 ≤ K) {A B : ℝ} (hA : ∀ y, ‖reconLow n K u y‖ ≤ A)
    (hB : 240 ^ 3 * A ≤ B) : FieldBound (fun z => reconLow n K u (K⁻¹ • z)) B B B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hb : ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j (resc K (reconLow n K u)) z‖ ≤ B := by
    intro j hj z
    refine (resc_reconLow_bound u hK hA j z).trans ?_
    have h240 : (240 : ℝ) ^ j ≤ 240 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
    have := mul_le_mul_of_nonneg_right h240 hA0
    linarith
  exact fieldBound_of_iteratedFDeriv (((contDiff_reconLow u K).comp
    (contDiff_const_smul K⁻¹)).of_le (ContEulerBounds.natCast_le_infty 3))
    (hb 1 (by norm_num)) (hb 2 (by norm_num)) (hb 3 le_rfl)

theorem fieldBound_resc_tail (hK : 1 ≤ K) :
    FieldBound (fun z => recon n u (K⁻¹ • z) - reconLow n K u (K⁻¹ • z))
      (tau n K 2 u) (tau n K 2 u) (tau n K 3 u) := by
  have hsm : ContDiff ℝ 3 (resc K (recon n u) - resc K (reconLow n K u)) :=
    (((contDiff_recon u).comp (contDiff_const_smul K⁻¹)).sub
      ((contDiff_reconLow u K).comp (contDiff_const_smul K⁻¹))).of_le
        (ContEulerBounds.natCast_le_infty 3)
  exact fieldBound_of_iteratedFDeriv hsm (fun z => resc_tail_bound u hK (by norm_num) z)
    (fun z => resc_tail_bound u hK le_rfl z) (fun z => resc_tail_bound u hK le_rfl z)

theorem norm_resc_tail_le (hK : 1 ≤ K) (z : R4) :
    ‖recon n u (K⁻¹ • z) - reconLow n K u (K⁻¹ • z)‖ ≤ tau n K 2 u := by
  have := resc_tail_bound u hK (p := 0) (m := 2) (by norm_num) z
  rwa [norm_iteratedFDeriv_zero] at this

theorem cmap_jet1_resc_low_mem {Ke : Set Mat} (hK : 1 ≤ K) {A B : ℝ}
    (hKe : ∀ x, (reconLow n K u x).1 ∈ Ke) (hA : ∀ y, ‖reconLow n K u y‖ ≤ A)
    (hB : 240 * A ≤ B) (z : R4) :
    cmap (jet1 (fun z => reconLow n K u (K⁻¹ • z)) z) ∈
      lowJetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A B := by
  refine ⟨jet1 (resc K (reconLow n K u)) z, ⟨⟨hKe _, ?_⟩, ?_⟩, rfl⟩
  · rw [mem_closedBall, dist_zero_right]; exact hA _
  · rw [mem_closedBall, dist_zero_right]
    exact (norm_jet1_resc_low_snd_le u hK hA z).trans hB

end Record

-- the assembly carries the hypotheses of the consistency and mean-value estimates
set_option maxHeartbeats 1000000 in
/-- **`eq:native-Euler-tail`** (`lem:native-tail-transfer`, second display). -/
theorem native_euler_tail {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) :
    ∃ C c_res τs : ℝ, 0 ≤ C ∧ 0 < c_res ∧ 0 < τs ∧ ∀ (n : ℕ) [NeZero n], Odd n →
      ∀ (u : Grid n → Field 𝔄 𝓗 𝓢) (K : ℝ), 1 ≤ K → (2 * Real.pi / n) * K ≤ c_res →
      tau n K 3 u ≤ τs → (∀ x, (reconLow n K u x).1 ∈ Ke) → (∀ x, ‖reconLow n K u x‖ ≤ A) →
      (∀ x, (recon n u x).1 ∈ Ke) →
      (∀ x : Grid n, ‖eulerRow (localAction D (2 * Real.pi / n)) (2 * Real.pi / n) u x -
          eulerRow (localAction D (2 * Real.pi / n)) (2 * Real.pi / n)
            (samp (2 * Real.pi / n) (reconLow n K u)) x‖ ≤ C * K ^ 2 * tau n K 2 u) ∧
      (2 * Real.pi / n) ^ 4 * ∑ x : Grid n,
          ‖eulerRow (localAction D (2 * Real.pi / n)) (2 * Real.pi / n) u x -
            eulerRow (localAction D (2 * Real.pi / n)) (2 * Real.pi / n)
              (samp (2 * Real.pi / n) (reconLow n K u)) x‖ ^ 2 ≤
        ((2 * Real.pi) ^ 2 * (C * K ^ 2 * tau n K 2 u)) ^ 2 := by
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max A 0 := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := hA₀ ▸ le_max_right _ _
  have hAA₀ : A ≤ A₀ := hA₀ ▸ le_max_left _ _
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ, Bp = 240 ^ 3 * (A₀ + 1) := ⟨_, rfl⟩
  have hBp0 : 0 ≤ Bp := by rw [hBp]; positivity
  have hBpA : 240 ^ 3 * (A₀ + 1) ≤ Bp := hBp.ge
  have hBpA' : 240 * (A₀ + 1) ≤ Bp := by rw [hBp]; nlinarith
  obtain ⟨C₀, c₀, hc₀, hnc⟩ := native_consistency D hKe hdet (A₀ + 1) Bp
  obtain ⟨δ, hδ, M₂, M₃, hreg⟩ := exists_densityReg (scaledDensity D) isCompact_Icc
    (isCompact_lowJetSet hKe (A₀ + 1) Bp) (contDiffAt_lowJetSet D hdet (A₀ + 1) Bp)
  have hM₂ : 0 ≤ M₂ := (hreg 0 ⟨le_rfl, zero_le_one⟩).M₂_nonneg
  have hM₃ : 0 ≤ M₃ := (hreg 0 ⟨le_rfl, zero_le_one⟩).M₃_nonneg
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = cJet Bp Bp 1 := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; unfold cJet; positivity
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = Fintype.card Shift * (M₂ * 2) +
      Fintype.card (Shift × Fin 4) * (M₃ * 2 * (2 * Bp + 2) + M₂ * 2) := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  refine ⟨Cc, min c₀ (δ / (4 * (1 + c₁))), min 1 (δ / 8), hCc0, lt_min hc₀ (by positivity),
    lt_min one_pos (by positivity), ?_⟩
  intro n _ hn u K hK hhK hτ hKel hAl hKef
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ, h = 2 * Real.pi / n := ⟨_, rfl⟩
  rw [← hhdef] at hhK ⊢
  have hh : 0 < h := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    rw [hhdef]; positivity
  have hK0 : 0 < K := by linarith
  have hnh : (n : ℝ) * h = 2 * Real.pi := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [hhdef]; field_simp
  have hτ1 : tau n K 3 u ≤ 1 := hτ.trans (min_le_left _ _)
  have hτδ : tau n K 3 u ≤ δ / 8 := hτ.trans (min_le_right _ _)
  have hτ23 : tau n K 2 u ≤ tau n K 3 u := TrigInterp.tau_mono n hK0 (by norm_num) u
  have hτ20 : 0 ≤ tau n K 2 u := TrigInterp.tau_nonneg n hK0 2 u
  have hτ30 : 0 ≤ tau n K 3 u := TrigInterp.tau_nonneg n hK0 3 u
  have hAl' : ∀ y, ‖reconLow n K u y‖ ≤ A₀ := fun y => (hAl y).trans hAA₀
  have hY₀s : ContDiff ℝ ∞ (reconLow n K u) := contDiff_reconLow u K
  have hY₁s : ContDiff ℝ ∞ (recon n u) := contDiff_recon u
  have hpY₀ : IsPeriodic ((n : ℝ) * h) (reconLow n K u) := by rw [hnh]; exact isPeriodic_tp _
  have hpY₁ : IsPeriodic ((n : ℝ) * h) (recon n u) := by rw [hnh]; exact isPeriodic_tp _
  -- the record is the sample of its reconstruction
  have hu : (samp h (recon n u) : Grid n → Field 𝔄 𝓗 𝓢) = u := by
    funext x
    rw [hhdef]
    exact TrigInterp.recon_gpos n hn u x
  -- growing-band bounds of the unscaled fields
  have hlo : ∀ j : ℕ, ∀ z, ‖iteratedFDeriv ℝ j (reconLow n K u) z‖ ≤ 240 ^ j * K ^ j * A₀ := by
    intro j z
    have := TrigInterp.norm_iteratedFDeriv_reconLow_le n hK0.le u hAl' j z
    calc ‖iteratedFDeriv ℝ j (reconLow n K u) z‖ ≤ (60 * (4 : ℕ) * K) ^ j * A₀ := this
      _ = 240 ^ j * K ^ j * A₀ := by push_cast; rw [mul_pow]; norm_num
  have htail : ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j (fun x => recon n u x - reconLow n K u x) z‖ ≤
      K ^ j * tau n K 3 u :=
    fun j hj z => TrigInterp.norm_iteratedFDeriv_tail_le n hK0 u hj z
  have hfu : ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j (recon n u) z‖ ≤
      240 ^ j * K ^ j * A₀ + K ^ j * tau n K 3 u := by
    intro j hj z
    have e : recon n u = reconLow n K u + fun x => recon n u x - reconLow n K u x := by
      funext x; simp
    have hj' := ContEulerBounds.natCast_le_infty j
    rw [e, iteratedFDeriv_add_apply (f := reconLow n K u)
      (g := fun x => recon n u x - reconLow n K u x)
      (hY₀s.of_le hj').contDiffAt ((hY₁s.sub hY₀s).of_le hj').contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hlo j z) (htail j hj z))
  have hband : ∀ (Y : R4 → Field 𝔄 𝓗 𝓢), (∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤
      240 ^ j * K ^ j * A₀ + K ^ j * tau n K 3 u) → ∀ j, 1 ≤ j → j ≤ 3 → ∀ z,
        ‖iteratedFDeriv ℝ j Y z‖ ≤ Bp * K ^ j := by
    intro Y hY j _ hj3 z
    refine (hY j hj3 z).trans ?_
    have hKj : 0 ≤ K ^ j := by positivity
    have h240 : (240 : ℝ) ^ j ≤ 240 ^ 3 := pow_le_pow_right₀ (by norm_num) hj3
    have : 240 ^ j * A₀ + tau n K 3 u ≤ Bp := by
      rw [hBp]
      have : (240 : ℝ) ^ j * A₀ ≤ 240 ^ 3 * A₀ := mul_le_mul_of_nonneg_right h240 hA₀0
      have : (1 : ℝ) ≤ 240 ^ 3 := by norm_num
      nlinarith
    calc 240 ^ j * K ^ j * A₀ + K ^ j * tau n K 3 u = K ^ j * (240 ^ j * A₀ + tau n K 3 u) := by
          ring
      _ ≤ K ^ j * Bp := mul_le_mul_of_nonneg_left this hKj
      _ = Bp * K ^ j := by ring
  have hlo3 : ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j (reconLow n K u) z‖ ≤
      240 ^ j * K ^ j * A₀ + K ^ j * tau n K 3 u := fun j _ z => by
    have := hlo j z
    have : 0 ≤ K ^ j * tau n K 3 u := by positivity
    linarith
  -- the charts of the samples (`prop:native-consistency`, first two clauses)
  have hchart : ∀ (Y : R4 → Field 𝔄 𝓗 𝓢), ContDiff ℝ ∞ Y → IsPeriodic ((n : ℝ) * h) Y →
      (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A₀ + 1) →
      (∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ 240 ^ j * K ^ j * A₀ + K ^ j * tau n K 3 u) →
      (∀ x, 0 < (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢) x).det) ∧
        (∀ x μ ν, ‖cartanPlaquette h (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢)) x μ ν - 1‖ < 1) := by
    intro Y hYs hpY hYe hYA hYb
    have h3 := ContEulerBounds.natCast_le_infty 3
    have := hnc K hK h hh (hhK.trans (min_le_left _ _)) n Y (hYs.of_le h3) hpY hYe hYA
      (fun z => by simpa using hband Y hYb 1 le_rfl (by norm_num) z) (fun z => hband Y hYb 2 (by norm_num)
        (by norm_num) z) (fun z => hband Y hYb 3 (by norm_num) le_rfl z)
    exact ⟨this.1, this.2.1⟩
  have hA₀1 : ∀ z, ‖reconLow n K u z‖ ≤ A₀ + 1 := fun z => (hAl' z).trans (by linarith)
  have hA₁1 : ∀ z, ‖recon n u z‖ ≤ A₀ + 1 := by
    intro z
    have h0 := htail 0 (by norm_num) z
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h0
    have e : recon n u z = reconLow n K u z + (recon n u z - reconLow n K u z) := by abel
    rw [e]
    calc ‖reconLow n K u z + (recon n u z - reconLow n K u z)‖
        ≤ ‖reconLow n K u z‖ + ‖recon n u z - reconLow n K u z‖ := norm_add_le _ _
      _ ≤ A₀ + 1 := add_le_add (hAl' z) (h0.trans hτ1)
  obtain ⟨hdet₀, hlog₀⟩ := hchart (reconLow n K u) hY₀s hpY₀ hKel hA₀1 hlo3
  obtain ⟨hdet₁, hlog₁⟩ := hchart (recon n u) hY₁s hpY₁ hKef hA₁1 hfu
  rw [hu] at hdet₁ hlog₁
  -- the pointwise estimate
  have hν : K⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩
  have hδ' : h * K * (1 + cJet Bp Bp 1) + (tau n K 2 u + tau n K 2 u) < δ := by
    rw [← hc₁]
    exact delta_arith hc₁0 hδ (hhK.trans (min_le_right _ _)) (hτ23.trans hτδ)
  have hfin := tail_arith (a := (Fintype.card Shift : ℝ)) (b := (Fintype.card (Shift × Fin 4) : ℝ))
    (by positivity) hM₃ hτ20 (hτ23.trans hτ1) hCc.ge
  have hpt : ∀ x : Grid n, ‖eulerRow (localAction D h) h u x -
      eulerRow (localAction D h) h (samp h (reconLow n K u)) x‖ ≤ Cc * K ^ 2 * tau n K 2 u := by
    intro x
    have hred := norm_eulerRow_local_sub_le D hh hK0 hdet₁ hlog₁ hdet₀ hlog₀ x
    have hdiff := row_diff_le_of_resc (F := fun q => scaledDensity D (K⁻¹, q)) shiftZ
      (hreg K⁻¹ hν) hh hK0 (n := n) hpY₀ hpY₁
      (fieldBound_resc_low u hK hA₀1 hBpA) (fieldBound_resc_tail u hK)
      (norm_resc_tail_le u hK) (cmap_jet1_resc_low_mem u hK hKel hA₀1 hBpA') zero_le_one
      (fun s μ => abs_shiftZ_le s μ) hδ' x
    rw [hu] at hdiff
    refine hred.trans ?_
    exact (mul_le_mul_of_nonneg_left (hdiff.trans hfin) (sq_nonneg K)).trans_eq (by ring)
  refine ⟨hpt, ?_⟩
  -- the mass norm over the box
  have hC0 : 0 ≤ Cc * K ^ 2 * tau n K 2 u := by positivity
  calc h ^ 4 * ∑ x : Grid n, ‖eulerRow (localAction D h) h u x -
        eulerRow (localAction D h) h (samp h (reconLow n K u)) x‖ ^ 2
      ≤ h ^ 4 * ∑ _x : Grid n, (Cc * K ^ 2 * tau n K 2 u) ^ 2 := by
        gcongr with x
        exact hpt x
    _ = ((n : ℝ) * h) ^ 4 * (Cc * K ^ 2 * tau n K 2 u) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [ShiftedJetAction.Grid, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast
        ring
    _ = ((2 * Real.pi) ^ 2 * (Cc * K ^ 2 * tau n K 2 u)) ^ 2 := by rw [hnh]; ring

/-! ### Non-vacuity: constant records have no tail -/

section ConstRecord

open TrigInterp VecTrig in
/-- One-dimensional orthogonality over the residues: `Σ_{t ∈ ℤ/n} e^{2πi t k/n} = 0` for
`0 < |k| < n`, `n` odd. -/
theorem sum_cexp_zmod {n : ℕ} [NeZero n] (hn : Odd n) (k : ℤ) (hk : |k| < n) (hk0 : k ≠ 0) :
    ∑ t : ZMod n, Complex.exp (((t.val : ℕ) : ℂ) * (2 * Real.pi * k / n : ℝ) * Complex.I) = 0 := by
  obtain ⟨M, rfl⟩ := hn
  set θ : ℝ := 2 * Real.pi * k / (2 * M + 1 : ℕ)
  set r : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hterm : ∀ m : ℕ, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) = r ^ m := by
    intro m
    rw [← Complex.exp_nat_mul]; congr 1; ring
  have hfin : ∑ t : ZMod (2 * M + 1), Complex.exp (((t.val : ℕ) : ℂ) * (θ : ℂ) * Complex.I) =
      ∑ i ∈ Finset.range (2 * M + 1), r ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => r ^ i) (2 * M + 1)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hterm]
    rfl
  rw [hfin]
  have hrn : r ^ (2 * M + 1) = 1 := by
    have e : ((2 * M + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [θ]; push_cast
      have : (2 * (M : ℂ) + 1) ≠ 0 := by exact_mod_cast (by positivity : (2 * (M : ℝ) + 1) ≠ 0)
      field_simp
    rw [← Complex.exp_nat_mul, e, Complex.exp_int_mul_two_pi_mul_I]
  have hr1 : r ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨N, hN⟩ := h
    have hpos : (0 : ℝ) < 2 * M + 1 := by positivity
    have h2 : (θ : ℂ) = (N : ℂ) * (2 * Real.pi) := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have := hN
      rw [show (N : ℂ) * (2 * Real.pi * Complex.I) = ((N : ℂ) * (2 * Real.pi)) * Complex.I by ring]
        at this
      exact mul_right_cancel₀ hI this
    have h3 : θ = N * (2 * Real.pi) := by exact_mod_cast h2
    simp only [θ] at h3
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have h4 : (k : ℝ) = N * (2 * M + 1) := by
      push_cast at h3
      field_simp at h3
      nlinarith [h3]
    have h5 : k = N * (2 * M + 1) := by exact_mod_cast h4
    have : N = 0 := by
      push_cast at hk
      have h6 : |k| = |N| * (2 * M + 1) := by
        rw [h5, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 * M + 1)]
      have h7 : |N| < 1 := by nlinarith [abs_nonneg N]
      have := abs_lt.mp h7; omega
    rw [this, zero_mul] at h5
    exact hk0 h5
  rw [geom_sum_eq hr1, hrn, sub_self, zero_div]

/-- `d`-dimensional orthogonality over the residues for a nonzero represented frequency. -/
theorem sum_cexp_phase_zmod {d n : ℕ} [NeZero n] (hn : Odd n) (ℓ : Fin d → ℤ)
    (hℓ : ℓ ∈ TrigInterp.box n d) (hℓ0 : ℓ ≠ 0) :
    ∑ y : Fin d → ZMod n,
      Complex.exp ((VecTrig.phase ℓ (TrigInterp.gpos n y) : ℂ) * Complex.I) = 0 := by
  have hprod : ∀ y : Fin d → ZMod n,
      Complex.exp ((VecTrig.phase ℓ (TrigInterp.gpos n y) : ℂ) * Complex.I) =
        ∏ μ, Complex.exp ((((y μ).val : ℕ) : ℂ) * (2 * Real.pi * ℓ μ / n : ℝ) * Complex.I) := by
    intro y
    rw [← Complex.exp_sum]
    congr 1
    simp only [VecTrig.phase, TrigInterp.gpos, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  simp_rw [hprod]
  have e : ∑ y : Fin d → ZMod n, ∏ μ, Complex.exp ((((y μ).val : ℕ) : ℂ) *
      (2 * Real.pi * ℓ μ / n : ℝ) * Complex.I) = ∏ μ, ∑ t : ZMod n,
        Complex.exp (((t.val : ℕ) : ℂ) * (2 * Real.pi * ℓ μ / n : ℝ) * Complex.I) :=
    (Fintype.prod_sum (fun μ (t : ZMod n) =>
      Complex.exp (((t.val : ℕ) : ℂ) * (2 * Real.pi * ℓ μ / n : ℝ) * Complex.I))).symm
  rw [e]
  obtain ⟨μ, hμ⟩ : ∃ μ, ℓ μ ≠ 0 := by
    by_contra h; simp only [not_exists, ne_eq, not_not] at h; exact hℓ0 (funext h)
  refine Finset.prod_eq_zero (Finset.mem_univ μ) (sum_cexp_zmod hn (ℓ μ) ?_ hμ)
  have hm := Fintype.mem_piFinset.mp hℓ μ
  rw [Finset.mem_Icc] at hm
  have hh : (TrigInterp.half n : ℤ) < n := by
    unfold TrigInterp.half
    have := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  rw [abs_lt]; constructor <;> omega

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coefOf_const_of_ne {d n : ℕ} [NeZero n] (hn : Odd n) (w : V) (ℓ : Fin d → ℤ)
    (hℓ : ℓ ∈ TrigInterp.box n d) (hℓ0 : ℓ ≠ 0) :
    TrigInterp.coefOf n (fun _ : Fin d → ZMod n => w) ℓ = (0, 0) := by
  have hc := sum_cexp_phase_zmod hn ℓ hℓ hℓ0
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  rw [Complex.re_sum] at hre
  rw [Complex.im_sum] at him
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.zero_re,
    Complex.zero_im] at hre him
  simp only [TrigInterp.coefOf, ← Finset.sum_smul, hre, him, zero_smul, smul_zero]

theorem coefOf_const_zero {d n : ℕ} [NeZero n] (w : V) :
    TrigInterp.coefOf n (fun _ : Fin d → ZMod n => w) 0 = (w, 0) := by
  have hph : ∀ y : Fin d → ZMod n, VecTrig.phase 0 (TrigInterp.gpos n y) = 0 := by
    intro y; simp [VecTrig.phase]
  have hn0 : ((n : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne n)
  simp only [TrigInterp.coefOf, hph, Real.cos_zero, Real.sin_zero, one_smul, zero_smul,
    Finset.sum_const_zero, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ hn0, one_smul]

theorem zero_mem_box {d n : ℕ} [NeZero n] : (0 : Fin d → ℤ) ∈ TrigInterp.box n d := by
  rw [TrigInterp.box, Fintype.mem_piFinset]
  intro μ; simp

/-- A constant record has no tail: `τ_{h,j}(K) = 0`. -/
theorem tau_const {d n : ℕ} [NeZero n] (hn : Odd n) (w : V) {K : ℝ} (hK : 0 ≤ K) (j : ℕ) :
    TrigInterp.tau n K j (fun _ : Fin d → ZMod n => w) = 0 := by
  refine Finset.sum_eq_zero fun ℓ hℓ => ?_
  rw [TrigInterp.tailBox, Finset.mem_filter] at hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl; exact hℓ.2 fun μ => by simpa using hK
  rw [VecTrig.cn, coefOf_const_of_ne hn w ℓ hℓ.1 hℓ0]
  simp

theorem tp_const {d n : ℕ} [NeZero n] (hn : Odd n) (w : V) {S : Finset (Fin d → ℤ)}
    (hS : S ⊆ TrigInterp.box n d) (h0 : (0 : Fin d → ℤ) ∈ S) (x : Fin d → ℝ) :
    VecTrig.tp S (TrigInterp.coefOf n (fun _ : Fin d → ZMod n => w)) x = w := by
  rw [VecTrig.tp, Finset.sum_eq_single (0 : Fin d → ℤ)]
  · rw [coefOf_const_zero]; simp [VecTrig.phase]
  · intro ℓ hℓ hℓ0
    rw [coefOf_const_of_ne hn w ℓ (hS hℓ) hℓ0]; simp
  · intro h; exact absurd h0 h

/-- The full and low reconstructions of a constant record are constant. -/
theorem recon_const {d n : ℕ} [NeZero n] (hn : Odd n) (w : V) (x : Fin d → ℝ) :
    TrigInterp.recon n (fun _ : Fin d → ZMod n => w) x = w :=
  tp_const hn w subset_rfl zero_mem_box x

theorem reconLow_const {d n : ℕ} [NeZero n] (hn : Odd n) (w : V) {K : ℝ} (hK : 0 ≤ K)
    (x : Fin d → ℝ) : TrigInterp.reconLow n K (fun _ : Fin d → ZMod n => w) x = w :=
  tp_const hn w (Finset.filter_subset _ _)
    (Finset.mem_filter.mpr ⟨zero_mem_box, fun μ => by simpa using hK⟩) x

end ConstRecord

/-- **Non-vacuity of `native_euler_tail` / `native_source_tail`**: a constant record whose coframe
value lies in `K_e` satisfies every record hypothesis (zero tail, low and full heads equal to the
constant), for every odd `n` and every `K ≥ 0`; the mesh condition `(2π/n) K ≤ c_res` holds for
`n` large. -/
theorem native_tail_hyps_const (w : Field 𝔄 𝓗 𝓢) {Ke : Set Mat} (hw : w.1 ∈ Ke) {n : ℕ} [NeZero n]
    (hn : Odd n) {K : ℝ} (hK : 0 ≤ K) (j : ℕ) :
    tau n K j (fun _ : Grid n => w) = 0 ∧
      (∀ x, (reconLow n K (fun _ : Grid n => w) x).1 ∈ Ke) ∧
      (∀ x, ‖reconLow n K (fun _ : Grid n => w) x‖ ≤ ‖w‖) ∧
      (∀ x, (recon n (fun _ : Grid n => w) x).1 ∈ Ke) :=
  ⟨tau_const hn w hK j, fun x => by rw [reconLow_const hn w hK x]; exact hw,
    fun x => by rw [reconLow_const hn w hK x], fun x => by rw [recon_const hn w x]; exact hw⟩

example (c : ℝ) (hc : 0 < c) : ∃ n : ℕ, Odd n ∧ 2 * Real.pi / n * 1 ≤ c := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Real.pi / c)
  refine ⟨2 * m + 1, odd_two_mul_add_one m, ?_⟩
  have hπ := Real.pi_pos
  have hpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [mul_one, div_le_iff₀ hpos]
  rw [div_lt_iff₀ hc] at hm
  push_cast
  nlinarith

end

end RenewalGeometry.NativeTail
