/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeClosureClosed

/-!
# `cor:native-rate` for native records: general rates, the example, residuals, dyadic chains

Einstein–Standard-Model action-closure manuscript, `cor:native-rate` (all clauses), on top of
`RecordTuple.native_closure` / `native_rate`.

* `rate_tendsto` — the rate hypotheses `1 ≤ K_h ≤ c₂h^{-β}`, `τ_{h,k+2} ≤ C_τhK_h²`, `2β < 1` give
  `hK_h → 0` and `τ_{h,k+2} → 0` (the resolution/threshold conditions of `thm:native-source`).
* **`native_closure_isBigO`** — any rate `g → 0` with `i_{h,k} + γ_{h,k} = O(g)` and `F_{h,k} = O(g)`
  is inherited by the state, curvature and stress distances.
* **`native_rate_example`** — `eq:native-example-rate`: `k = 4`, `K_h ≤ c₂h^{-1/18}`,
  `eq:native-tail-rate`, `i_{h,4} + γ_{h,4} = O(h^{1/2})` give `O(h^{1/2})` state, curvature and
  stress convergence.
* **`native_rate_residuals`** — the zero-order physical residuals are `O(h^{1-3β})` and the
  literal Cartan discrepancy is eventually `≤ C h^{1-3β}` (`O(h^{5/6})` for `β = 1/18`).
* **`summable_rate_of_dyadic`**, **`native_rate_dyadic`** — along a chain with
  `c₁2^{-j} ≤ h_j ≤ c₂2^{-j}` (odd grids: `h_j = 2π/n_j`, e.g. `n_j = 2^j + 1`) the adjacent state,
  curvature and stress differences are summable (cofinal transport).
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped Real ContDiff Nat

namespace RenewalGeometry.RecordTuple

open DiscreteEulerConsistency (R4)
open NativeScaling (Mat)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing ActualJetBridge CoupledBootstrap ActualJetSmooth
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Generic rate facts -/

/-- **The rate hypotheses force `hK → 0` and `τ_{h,m} → 0`.** -/
theorem rate_tendsto {ι : Type*} {l : Filter ι} {h K τm : ι → ℝ} {β c₂ Cτ : ℝ}
    (hβ : 2 * β < 1) (hh : Tendsto h l (𝓝[>] 0))
    (hev : ∀ᶠ i in l, 1 ≤ K i ∧ K i ≤ c₂ * h i ^ (-β) ∧ 0 ≤ τm i ∧
      τm i ≤ Cτ * (h i * K i ^ 2)) :
    Tendsto (fun i => h i * K i) l (𝓝 0) ∧ Tendsto τm l (𝓝 0) := by
  have hpos : ∀ᶠ i in l, 0 < h i := (tendsto_nhdsWithin_iff.1 hh).2
  have hβ1 : 0 < 1 - β := by linarith
  have hr1 := tendsto_rpow_of_nhdsGT hh hβ1
  have hr2 := tendsto_rpow_of_nhdsGT hh (show 0 < 1 - 2 * β by linarith)
  refine ⟨?_, ?_⟩
  · have hup : Tendsto (fun i => c₂ * h i ^ (1 - β)) l (𝓝 0) := by
      simpa using hr1.const_mul c₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev, hpos] with i hi hp
      exact mul_nonneg hp.le (by linarith [hi.1])
    · filter_upwards [hev, hpos] with i hi hp
      exact mul_le_rpow_of_le hp hi.2.1
  · have hup : Tendsto (fun i => |Cτ| * (c₂ ^ 2 * h i ^ (1 - 2 * β))) l (𝓝 0) := by
      simpa using (hr2.const_mul (c₂ ^ 2)).const_mul |Cτ|
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with i hi
      exact hi.2.2.1
    · filter_upwards [hev, hpos] with i hi hp
      have hm : 0 ≤ h i * K i ^ 2 := by positivity
      calc τm i ≤ Cτ * (h i * K i ^ 2) := hi.2.2.2
        _ ≤ |Cτ| * (h i * K i ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self _) hm
        _ ≤ |Cτ| * (c₂ ^ 2 * h i ^ (1 - 2 * β)) :=
            mul_le_mul_of_nonneg_left
              (mul_sq_le_rpow_of_le hp (by linarith [hi.1]) hi.2.1) (abs_nonneg _)

/-- `h^{5/9}(1+|log h|)^5 = O(h^{1/2})` as `h → 0⁺`. -/
theorem example_rate_isBigO {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝[>] 0)) :
    (fun i => h i ^ (1 - 1 / 18 * ((4 : ℕ) + 4 : ℝ)) * (1 + |Real.log (h i)|) ^ (4 + 1)) =O[l]
      fun i => h i ^ (1 / 2 : ℝ) := by
  have hpos : ∀ᶠ i in l, 0 < h i := (tendsto_nhdsWithin_iff.1 hh).2
  have ht := (NativeRate.tendsto_rpow_mul_one_add_abs_log_pow (ρ := 1 / 18) (by norm_num)
    (4 + 1)).comp hh
  have hb : ∀ᶠ i in l, h i ^ (1 / 18 : ℝ) * (1 + |Real.log (h i)|) ^ (4 + 1) ≤ 1 :=
    ht.eventually (ge_mem_nhds one_pos)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hpos, hb] with i hp hbi
  have e : h i ^ (1 - 1 / 18 * ((4 : ℕ) + 4 : ℝ)) =
      h i ^ (1 / 2 : ℝ) * h i ^ (1 / 18 : ℝ) := by
    rw [← Real.rpow_add hp]; norm_num
  have h0 : 0 ≤ h i ^ (1 / 2 : ℝ) := Real.rpow_nonneg hp.le _
  have h1 : 0 ≤ h i ^ (1 / 18 : ℝ) * (1 + |Real.log (h i)|) ^ (4 + 1) := by positivity
  rw [Real.norm_of_nonneg (by rw [e]; positivity), Real.norm_of_nonneg h0, e, one_mul, mul_assoc]
  exact mul_le_of_le_one_right h0 hbi

/-! ### Dyadic chains -/

/-- **Summability of the rate along a dyadic-comparable chain** `c₁2^{-j} ≤ h_j ≤ c₂2^{-j}`. -/
theorem summable_rate_of_dyadic {ρ : ℝ} (hρ : 0 < ρ) (p : ℕ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    {hs : ℕ → ℝ} (hlo : ∀ j, c₁ * (1 / 2) ^ j ≤ hs j) (hup : ∀ j, hs j ≤ c₂ * (1 / 2) ^ j) :
    Summable (fun j => hs j ^ ρ * (1 + |Real.log (hs j)|) ^ p) := by
  have hpos : ∀ j, 0 < hs j := fun j => lt_of_lt_of_le (by positivity) (hlo j)
  have hc₂ : 0 < c₂ := by
    have := (hpos 0).trans_le (hup 0); simpa using this
  set r : ℝ := (1 / 2 : ℝ) ^ ρ with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hρ
  set B : ℝ := 1 + |Real.log c₁| + |Real.log c₂| + Real.log 2 with hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 : 0 ≤ B := by positivity
  -- the logarithm along the chain
  have hlog : ∀ j : ℕ, 1 + |Real.log (hs j)| ≤ B * (1 + j) := by
    intro j
    have hlj : Real.log ((1 / 2 : ℝ) ^ j) = -(j * Real.log 2) := by
      rw [Real.log_pow, one_div, Real.log_inv]; ring
    have hlo' : Real.log c₁ - j * Real.log 2 ≤ Real.log (hs j) := by
      have := Real.log_le_log (by positivity) (hlo j)
      rwa [Real.log_mul hc₁.ne' (by positivity), hlj, ← sub_eq_add_neg] at this
    have hup' : Real.log (hs j) ≤ Real.log c₂ - j * Real.log 2 := by
      have := Real.log_le_log (hpos j) (hup j)
      rwa [Real.log_mul hc₂.ne' (by positivity), hlj, ← sub_eq_add_neg] at this
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have habs : |Real.log (hs j)| ≤ |Real.log c₁| + |Real.log c₂| + j * Real.log 2 := by
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log c₁)
        nlinarith [abs_nonneg (Real.log c₂)]
      · have := le_abs_self (Real.log c₂)
        nlinarith [abs_nonneg (Real.log c₁)]
    have : 1 + |Real.log (hs j)| ≤ B + j * Real.log 2 := by linarith
    calc 1 + |Real.log (hs j)| ≤ B + j * Real.log 2 := this
      _ ≤ B + j * B := by
          gcongr
          rw [hB]
          have := abs_nonneg (Real.log c₁)
          have := abs_nonneg (Real.log c₂)
          linarith
      _ = B * (1 + j) := by ring
  -- the power
  have hpow : ∀ j : ℕ, hs j ^ ρ ≤ c₂ ^ ρ * r ^ j := by
    intro j
    calc hs j ^ ρ ≤ (c₂ * (1 / 2) ^ j) ^ ρ := Real.rpow_le_rpow (hpos j).le (hup j) hρ.le
      _ = c₂ ^ ρ * r ^ j := by
          rw [Real.mul_rpow hc₂.le (by positivity), hr, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num), mul_comm (j : ℝ) ρ, Real.rpow_mul (by norm_num),
            Real.rpow_natCast]
  -- comparison with `(1 + j)^p r^j ≤ 2^p (1 + j^p) r^j`
  have hsum : Summable (fun j : ℕ => c₂ ^ ρ * B ^ p * (2 ^ p * (r ^ j + (j : ℝ) ^ p * r ^ j))) := by
    have h1 : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
    have h2 : Summable (fun j : ℕ => (j : ℝ) ^ p * r ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one p (by rwa [Real.norm_of_nonneg hr0])
    exact ((h1.add h2).mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun j => by
    have := hpos j; positivity) (fun j => ?_) hsum
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpj : (1 + (j : ℝ)) ^ p ≤ 2 ^ p * (1 + (j : ℝ) ^ p) := by
    rcases le_total (j : ℝ) 1 with hj | hj
    · calc (1 + (j : ℝ)) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
        _ ≤ 2 ^ p * (1 + (j : ℝ) ^ p) := le_mul_of_one_le_right (by positivity)
            (by have := pow_nonneg hj0 p; linarith)
    · calc (1 + (j : ℝ)) ^ p ≤ (2 * j) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
        _ = 2 ^ p * (j : ℝ) ^ p := mul_pow _ _ _
        _ ≤ 2 ^ p * (1 + (j : ℝ) ^ p) := by gcongr; linarith
  have hlogp : (1 + |Real.log (hs j)|) ^ p ≤ B ^ p * (2 ^ p * (1 + (j : ℝ) ^ p)) := by
    calc (1 + |Real.log (hs j)|) ^ p ≤ (B * (1 + j)) ^ p :=
          pow_le_pow_left₀ (by positivity) (hlog j) p
      _ = B ^ p * (1 + (j : ℝ)) ^ p := mul_pow _ _ _
      _ ≤ B ^ p * (2 ^ p * (1 + (j : ℝ) ^ p)) := mul_le_mul_of_nonneg_left hpj (by positivity)
  calc hs j ^ ρ * (1 + |Real.log (hs j)|) ^ p
      ≤ (c₂ ^ ρ * r ^ j) * (B ^ p * (2 ^ p * (1 + (j : ℝ) ^ p))) :=
        mul_le_mul (hpow j) hlogp (by positivity) (by positivity)
    _ = c₂ ^ ρ * B ^ p * (2 ^ p * (r ^ j + (j : ℝ) ^ p * r ^ j)) := by ring

/-! ### Record-level consequences -/

section Records

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- **Rates are inherited** (`thm:native-closure` in `O`-form): if `g → 0`,
`i_{h,k} + γ_{h,k} = O(g)` and `F_{h,k} = O(g)`, the state, curvature and stress distances are
`O(g)`. -/
theorem native_closure_isBigO {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ τs : ℝ, 0 < τs ∧ ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ g : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i)) →
      Tendsto (fun i => 2 * π / N i * K i) l (𝓝 0) →
      (∀ᶠ i in l, tau (N i) (K i) (k + 2) (u i) ≤ τs) →
      Tendsto g l (𝓝 0) →
      (fun i =>
        ‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l] g →
      (fun i => forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) =O[l] g →
      (fun i => dist ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l] g := by
  obtain ⟨C, τs, hC, hτs, H⟩ := native_closure M hδ eX eY eYD hAsym hKe hdet A hk hCk hb h0 h1
    h01 hKr hKO hR₁
  refine ⟨τs, hτs, fun {ι} l N _ u K σ g zs hzs hrec hhK hτ hg hig hF => ?_⟩
  have hD := hig.add hF
  have hev := H l N u K σ zs hzs hrec hhK hτ (hD.trans_tendsto hg)
  refine (IsBigO.of_bound C ?_).trans hD
  filter_upwards [hev] with i hi
  rw [Real.norm_of_nonneg dist_nonneg]
  exact hi.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

/-- **`eq:native-example-rate`**: `k = 4`, `1 ≤ K_h ≤ c₂h^{-1/18}`, `σ_h ≤ C_σh`,
`eq:native-tail-rate` and `i_{h,4} + γ_{h,4} = O(h^{1/2})` give `O(h^{1/2})` state, curvature and
Standard-Model stress convergence. -/
theorem native_rate_example {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ)
    {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {c₂ Cσ Cτ : ℝ} (hCσ : 0 ≤ Cσ) :
    ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) eX 4 (slabT t₀ t₁) Kr R₁,
      Tendsto (fun i => 2 * π / N i) l (𝓝[>] 0) →
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i) ∧
        K i ≤ c₂ * (2 * π / N i) ^ (-(1 / 18 : ℝ)) ∧ σ i ≤ Cσ * (2 * π / N i) ∧
        tau (N i) (K i) 2 (u i) ≤ Cτ * (2 * π / N i * K i) ∧
        tau (N i) (K i) (4 + 2) (u i) ≤ Cτ * (2 * π / N i * K i ^ 2)) →
      (fun i =>
        ‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) →
      (fun i => dist ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) 4
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) 4 (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l] (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) := by
  obtain ⟨τs, hτs, H⟩ := native_closure_isBigO M hδ eX eY eYD hAsym hKe hdet A le_rfl hCk hb
    h0 h1 h01 hKr hKO hR₁
  intro ι l N _ u K σ zs hzs hh hev hig
  have hpos : ∀ i, 0 < 2 * π / N i := fun i => by
    have : (0 : ℝ) < N i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (N i))
    positivity
  obtain ⟨hhK, hτ0⟩ := rate_tendsto (β := 1 / 18) (c₂ := c₂) (Cτ := Cτ)
    (h := fun i => 2 * π / N i) (K := K) (τm := fun i => tau (N i) (K i) (4 + 2) (u i))
    (by norm_num) hh (by
      filter_upwards [hev] with i hi
      exact ⟨hi.1.one_le, hi.2.1, TrigInterp.tau_nonneg _ (by linarith [hi.1.one_le]) _ _,
        hi.2.2.2.2⟩)
  have hh1 : ∀ᶠ i in l, 2 * π / N i ≤ 1 :=
    (tendsto_nhdsWithin_iff.1 hh).1.eventually (ge_mem_nhds one_pos)
  have hF := NativeRate.forcingBudget_isBigO (l := l) (h := fun i => 2 * π / N i) (K := K)
    (σ := σ) (τ₂ := fun i => tau (N i) (K i) 2 (u i))
    (τm := fun i => tau (N i) (K i) (4 + 2) (u i)) 4 hCk.le (β := 1 / 18) (c₂ := c₂)
    (Cσ := Cσ) (Cτ := Cτ) (by norm_num) hCσ (by
      filter_upwards [hev, hh1] with i hi hi1
      have hK0 : 0 < K i := by linarith [hi.1.one_le]
      exact ⟨hpos i, hi1, hi.1.one_le, hi.2.1, hi.1.sigma_nonneg, hi.2.2.1,
        TrigInterp.tau_nonneg _ hK0 _ _, hi.2.2.2.1, TrigInterp.tau_nonneg _ hK0 _ _,
        hi.2.2.2.2⟩)
  have hg : Tendsto (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) l (𝓝 0) :=
    tendsto_rpow_of_nhdsGT hh (by norm_num)
  exact H l N u K σ (fun i => (2 * π / N i) ^ (1 / 2 : ℝ)) zs hzs (hev.mono fun i hi => hi.1)
    hhK (hτ0.eventually (ge_mem_nhds hτs)) hg hig (hF.trans (example_rate_isBigO hh))

open Classical in
/-- **Zero-order physical residuals and the literal Cartan discrepancy along the rate family**
(`cor:native-rate`, `ε^phys(z_h) = O(h^{1-3β})`; `O(h^{5/6})` for `β = 1/18`). -/
theorem native_rate_residuals {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A : ℝ) {k : ℕ} (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b)
    (h0 : b < t₀) (h1 : t₁ + b ≤ 2 * π) {β c₂ Cσ Cτ : ℝ} (hβ : 0 ≤ β) (hβ2 : 2 * β < 1)
    (hCσ : 0 ≤ Cσ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      Tendsto (fun i => 2 * π / N i) l (𝓝[>] 0) →
      (∀ᶠ i in l, Odd (N i) ∧ 1 ≤ K i ∧ (∀ x, (reconLow (N i) (K i) (u i) x).1 ∈ Ke) ∧
        (∀ x, ‖reconLow (N i) (K i) (u i) x‖ ≤ A) ∧ (∀ x, (recon (N i) (u i) x).1 ∈ Ke) ∧
        (∀ x, ‖recon (N i) (u i) x‖ ≤ A) ∧ 0 ≤ σ i ∧
        (2 * π / N i) ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid (N i) =>
          pos (2 * π / N i) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
          ‖(eulerRow (localAction M.toData (2 * π / N i)) (2 * π / N i) (u i) x).comp
            (NativeTail.physF M.πg)‖ ^ 2 ≤ σ i ^ 2 ∧
        K i ≤ c₂ * (2 * π / N i) ^ (-β) ∧ σ i ≤ Cσ * (2 * π / N i) ∧
        tau (N i) (K i) (k + 2) (u i) ≤ Cτ * (2 * π / N i * K i ^ 2)) →
      (fun i => NativeTail.sobX 0 (NativeSlab.slab t₀ t₁)
          (NativeTail.RBP M.toData M.πg (recon (N i) (u i))) +
          NativeTail.sobX 0 (NativeSlab.slab t₀ t₁) (NativeTail.RD M.toData (recon (N i) (u i))))
        =O[l] (fun i => (2 * π / N i) ^ (1 - 3 * β)) ∧
      ∀ᶠ i in l, ∀ (x : Grid (N i)) (z : R4), ‖z - pos (2 * π / N i) x‖ ≤ 2 * π / N i →
        ∀ μ ν : Fin 4,
        ‖cartanCurvature (2 * π / N i) (coframe (u i)) x μ ν -
          matToOp ((recon (N i) (u i) z).1 *
            NativeEulerConsistency.riemMat (fun z => (recon (N i) (u i) z).1) z μ ν *
            ((recon (N i) (u i) z).1)⁻¹)‖ ≤ C * |c₂| ^ 3 * (2 * π / N i) ^ (1 - 3 * β) := by
  obtain ⟨C, cr, τs, hC, hcr, hτs, H⟩ :=
    NativeSourceThm.native_source_phys M.toData M.πg hKe hdet A k hk hCk hb h0 h1
  refine ⟨C, hC, fun {ι} l N _ u K σ hh hev => ?_⟩
  have hpos : ∀ i, 0 < 2 * π / N i := fun i => by
    have : (0 : ℝ) < N i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (N i))
    positivity
  obtain ⟨hhK, hτ0⟩ := rate_tendsto (β := β) (c₂ := c₂) (Cτ := Cτ)
    (h := fun i => 2 * π / N i) (K := K) (τm := fun i => tau (N i) (K i) (k + 2) (u i))
    hβ2 hh (by
      filter_upwards [hev] with i hi
      exact ⟨hi.2.1, hi.2.2.2.2.2.2.2.2.1,
        TrigInterp.tau_nonneg _ (by linarith [hi.2.1]) _ _, hi.2.2.2.2.2.2.2.2.2.2⟩)
  have hh1 : ∀ᶠ i in l, 2 * π / N i ≤ 1 :=
    (tendsto_nhdsWithin_iff.1 hh).1.eventually (ge_mem_nhds one_pos)
  refine ⟨?_, ?_⟩
  · refine NativeRate.physical_isBigO_of_le (σ := σ) (h := fun i => 2 * π / N i) (K := K) (C := C) ?_
      (NativeRate.eps0_isBigO (c₂ := c₂) hβ hCσ ?_)
    · filter_upwards [hev, hhK.eventually (ge_mem_nhds hcr), hτ0.eventually (ge_mem_nhds hτs)]
        with i hi hc ht
      refine (le_of_eq (Real.norm_of_nonneg
        (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).trans ?_
      exact (H (N i) hi.1 (u i) (K i) (σ i) hi.2.1 hc ht hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1
        hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.1 hi.2.2.2.2.2.2.2.1).1
    · filter_upwards [hev, hh1] with i hi hi1
      exact ⟨hpos i, hi1, by linarith [hi.2.1], hi.2.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.1,
        hi.2.2.2.2.2.2.2.2.2.1⟩
  · filter_upwards [hev, hhK.eventually (ge_mem_nhds hcr), hτ0.eventually (ge_mem_nhds hτs)]
      with i hev_i hc ht x z hz μ ν
    have hi := H (N i) hev_i.1 (u i) (K i) (σ i) hev_i.2.1 hc ht hev_i.2.2.1 hev_i.2.2.2.1
      hev_i.2.2.2.2.1 hev_i.2.2.2.2.2.1 hev_i.2.2.2.2.2.2.1 hev_i.2.2.2.2.2.2.2.1
    have hK0 : 0 ≤ K i := by linarith [hev_i.2.1]
    have hKup := hev_i.2.2.2.2.2.2.2.2.1
    have hp := hpos i
    have hKa : K i ≤ |c₂| * (2 * π / N i) ^ (-β) :=
      hKup.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _))
    have e : (2 * π / N i) ^ (1 - 3 * β) = (2 * π / N i) * ((2 * π / N i) ^ (-β)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, sub_eq_add_neg, Real.rpow_add hp,
        Real.rpow_one]
      congr 2; push_cast; ring
    have hK3 : K i ^ 3 ≤ (|c₂| * (2 * π / N i) ^ (-β)) ^ 3 := pow_le_pow_left₀ hK0 hKa 3
    refine (hi.2.2 x z hz μ ν).trans ?_
    rw [e]
    calc C * (2 * π / N i) * K i ^ 3 ≤ C * (2 * π / N i) * (|c₂| * (2 * π / N i) ^ (-β)) ^ 3 :=
          mul_le_mul_of_nonneg_left hK3 (mul_nonneg hC hp.le)
      _ = C * |c₂| ^ 3 * ((2 * π / N i) * ((2 * π / N i) ^ (-β)) ^ 3) := by ring

/-- **Cofinal summability along dyadic-comparable chains** (`cor:native-rate`, last sentence):
for records indexed by `j` with `c₁2^{-j} ≤ h_j = 2π/n_j ≤ c₂'2^{-j}`, under the rate hypotheses
and `i + γ = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the adjacent state, curvature and stress differences
are summable. -/
theorem native_rate_dyadic {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {β c₂ Cσ Cτ : ℝ} (hβ : 0 ≤ β)
    (hβk : β < 1 / (k + 4)) (hCσ : 0 ≤ Cσ) {c₁ c₂' : ℝ} (hc₁ : 0 < c₁) :
    ∀ (N : ℕ → ℕ) [∀ j, NeZero (N j)] (u : ∀ j, Grid (N j) → Field 𝔄 𝓗 𝓢) (K σ : ℕ → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
      (∀ j, c₁ * (1 / 2) ^ j ≤ 2 * π / N j ∧ 2 * π / N j ≤ c₂' * (1 / 2) ^ j) →
      (∀ᶠ j in atTop, RecordHyp M δ Ke A t₀ t₁ b (N j) (u j) (K j) (σ j) ∧
        K j ≤ c₂ * (2 * π / N j) ^ (-β) ∧ σ j ≤ Cσ * (2 * π / N j) ∧
        tau (N j) (K j) 2 (u j) ≤ Cτ * (2 * π / N j * K j) ∧
        tau (N j) (K j) (k + 2) (u j) ≤ Cτ * (2 * π / N j * K j ^ 2)) →
      (fun j =>
        ‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N j) (u j) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N j) (u j) zs)) =O[atTop]
        (fun j => (2 * π / N j) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N j)|) ^ (k + 1)) →
      Summable (fun j => dist
        ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs (recTuple M hδ t₀ (N (j + 1)) (u (j + 1)) zs))
        ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs (recTuple M hδ t₀ (N j) (u j) zs))) := by
  intro N _ u K σ zs hzs hdy hev hig
  have hpos : ∀ j, 0 < 2 * π / N j := fun j => by
    have : (0 : ℝ) < N j := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (N j))
    positivity
  have hh : Tendsto (fun j => 2 * π / N j) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hpos⟩
    have hgeo : Tendsto (fun j : ℕ => c₂' * (1 / 2 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul c₂'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo
      (fun j => (hpos j).le) (fun j => (hdy j).2)
  have hO := native_rate M hδ eX eY eYD hAsym hKe hdet A hk hCk hb h0 h1 h01 hKr hKO hR₁ hβ hβk
    hCσ atTop N u K σ zs hzs hh hev hig
  have hk4 : (0 : ℝ) < k + 4 := by positivity
  have hρ : 0 < 1 - β * (k + 4) := by
    have := (lt_div_iff₀ hk4).1 hβk; linarith
  have hsum := summable_rate_of_dyadic hρ (k + 1) hc₁ (fun j => (hdy j).1) (fun j => (hdy j).2)
  obtain ⟨c, hc⟩ := hO.bound
  set d : ℕ → ℝ := fun j => dist
    ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).obs (recTuple M hδ t₀ (N j) (u j) zs))
    ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).obs zs) with hd
  have hds : Summable d := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun j => c * ((2 * π / N j) ^
      (1 - β * (k + 4)) * (1 + |Real.log (2 * π / N j)|) ^ (k + 1))) (hsum.mul_left c) ?_
    filter_upwards [hc] with j hj
    refine hj.trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (by have := hpos j; positivity)]
  refine Summable.of_nonneg_of_le (fun j => dist_nonneg) (fun j => ?_)
    (((summable_nat_add_iff 1).2 hds).add hds)
  exact dist_triangle_right _ _ _

end Records

end

end RenewalGeometry.RecordTuple
