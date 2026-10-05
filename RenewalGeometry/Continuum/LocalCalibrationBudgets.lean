/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSourceTheorem
import RenewalGeometry.Continuum.TrigInterpolationConvergence

/-!
# Sampled smooth solutions: seam-local row bound and vanishing forcing budget
  (`cor:local-calibration-nonempty`, budget clause, source part)

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty`: "Nodal
sampling followed by trigonometric reconstruction yields records for `S_h^loc` with `σ_h = O(h)`
and with the budgets of `thm:native-closure` tending to zero for a suitable `K_h → ∞`."

The setting is the manuscript's: a smooth field tuple `Y = (e, A, H, Ψ, Ψ̄)` on `ℝ⁴`, the smooth
periodic extension (period `2π` in every coordinate, `Σ = 𝕋³`) of a solution on a compact slab,
with coframe values in a compact `K_e ⊂ {det e > 0}`; it solves the continuum Euler equations
`𝓔₀(Y) = 0` only on the buffered comparison slab `Q'` (the temporal seam of the periodic
extension lies outside `Q'`).  The records are the nodal samples `u_h = 𝖲_h Y` on the odd grid
`(ℤ/n)⁴`, `h = 2π/n`.

## Main results

* `exists_bound_iteratedFDeriv`: a smooth periodic field has uniformly bounded derivatives of
  every order.
* **`native_sigma_seam`** (`σ_h = O(h)`, seam-local form of
  `NativeEulerConsistency.native_sigma_of_solution`): at every node of `Q'` the raw Euler row of
  the samples is `≤ C h`, hence the finite-action covector norm on `Q'` satisfies
  `σ_h² = h⁴ Σ_{x ∈ Q'_h} ‖E_h^raw(u_h)(x)‖² ≤ ((2π)² C h)²`.
* `norm_recon_sub_le`: the trigonometric reconstruction of the samples is uniformly `O(h)`-close
  to `Y` (interpolation at the nodes plus a uniform derivative bound from the sharp tail).
* **`sampled_native_source`**: for `K_h ≍ h^{-β}`, `0 < β < 1/(k+4)`, eventually (odd `n → ∞`)
  the sampled records satisfy every record hypothesis of `thm:native-source`
  (`NativeSourceThm.native_source`: calibrated chart and amplitude for the complete record and
  its low head, `hK ≤ c_res`, `τ_{h,k+2}(K) ≤ τ_*`, the row bound on `Q'`), with `σ_h = O(h)`,
  `τ_{h,2} = O(hK)`, `τ_{h,k+2} = O(hK²)` (`eq:native-tail-rate`), and the forcing budget
  `F_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1}) → 0`; hence by `thm:native-source` the strong
  physical source `𝒴_k(z_h) ≤ C F_{h,k} → 0`.

Not covered here (see the ledger note of the corollary): the initial and harmonic mismatches
`i_{h,k}`, `γ_{h,k}` are defined on the actual-jet state of the reconstruction as an actual field
tuple (`ActualJetBridge.Tuple`), whose identification with the native record is the open bridge
of `thm:native-closure`.
-/

open Finset Filter Topology Set Metric Asymptotics
open scoped Real ContDiff

noncomputable section

namespace RenewalGeometry.LocalCalibration

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency NativeEulerConsistency
open TrigInterp (recon reconLow tau)
open NativeTail (RB RD)
open TrigConv

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


/-! ### `σ_h = O(h)`: the seam-local row bound -/

section Sigma

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

open Classical in
/-- **`σ_h = O(h)` for sampled solutions, seam-local form** (`cor:local-calibration-nonempty`;
`native_sigma_of_solution` with the Euler equations imposed only on the comparison region `Q'`).
For a compact coframe chart `K_e ⊂ {det e > 0}`, an amplitude bound `A` and a derivative bound
`B` there are `C`, `c_res > 0` such that for every grid size `n` with `h = 2π/n ≤ c_res`, every
`C³` field `Y` of period `2π` with coframe values in `K_e`, `|Y| ≤ A`, `‖D^jY‖ ≤ B`
(`j = 1, 2, 3`), and every region `Q'` on which `𝓔₀(Y) = 0`:
the raw Euler row of the samples is `≤ C h` at every node of `Q'`, and
`h⁴ Σ_{x ∈ Q'_h} ‖E_h^raw(𝖲_h Y)(x)‖² ≤ ((2π)² C h)²`. -/
theorem native_sigma_seam {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A B : ℝ) :
    ∃ C c_res : ℝ, 0 ≤ C ∧ 0 < c_res ∧ ∀ (n : ℕ) [NeZero n], 2 * π / n ≤ c_res →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ 3 Y → IsPeriodic (2 * π) Y → (∀ z, (Y z).1 ∈ Ke) →
        (∀ z, ‖Y z‖ ≤ A) → (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B) →
        (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B) → (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B) →
        ∀ Q' : Set R4, (∀ z ∈ Q', contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y z = 0) →
        (∀ x : Grid n, pos (2 * π / n) x ∈ Q' →
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) (samp (2 * π / n) Y) x‖ ≤
            C * (2 * π / n)) ∧
        (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖eulerRow (localAction D (2 * π / n)) (2 * π / n) (samp (2 * π / n) Y) x‖ ^ 2 ≤
            ((2 * π) ^ 2 * C * (2 * π / n)) ^ 2 := by
  obtain ⟨C, c_res, hc, hmain⟩ := native_consistency D hKe hdet A B
  refine ⟨max C 0, c_res, le_max_right _ _, hc, fun n _ hhc Y hYs hper hYe hYA h1 h2 h3 Q' hsol =>
    ?_⟩
  set h : ℝ := 2 * π / n with hh
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hper' : IsPeriodic ((n : ℝ) * h) Y := by rw [hh, mul_div_cancel₀ _ hn0]; exact hper
  have hK := hmain 1 le_rfl h hh0 (by simpa using hhc) n Y hYs hper' hYe hYA
    (fun z => by simpa using h1 z) (fun z => by simpa using h2 z) (fun z => by simpa using h3 z)
  have hpt : ∀ x : Grid n, pos h x ∈ Q' →
      ‖eulerRow (localAction D h) h (samp h Y) x‖ ≤ max C 0 * h := by
    intro x hx
    have := hK.2.2 x
    rw [hsol _ hx, sub_zero, one_pow, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hh0.le)
  refine ⟨hpt, ?_⟩
  have hC0 : 0 ≤ max C 0 * h := mul_nonneg (le_max_right _ _) hh0.le
  calc h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
        ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2
      ≤ h ^ 4 * ∑ _x : Grid n, (max C 0 * h) ^ 2 := by
        gcongr
        calc ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
              ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2
            ≤ ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'), (max C 0 * h) ^ 2 :=
              Finset.sum_le_sum fun x hx =>
                pow_le_pow_left₀ (norm_nonneg _) (hpt x (Finset.mem_filter.mp hx).2) 2
          _ ≤ ∑ _x : Grid n, (max C 0 * h) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => sq_nonneg _
    _ = ((2 * π) ^ 2 * max C 0 * h) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [ShiftedJetAction.Grid, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast
        rw [hh]
        field_simp

end Sigma


/-! ### Budget algebra -/

section Budget

open NativeRate

/-- The forcing budget dominates `hK` and `τ_{h,k+2}` (`K ≥ 1`, `L_{h,k} ≥ 1`). -/
theorem le_forcingBudget (k : ℕ) {Ck σ h K τ₂ τm : ℝ} (hCk : 0 ≤ Ck) (hσ : 0 ≤ σ) (hh : 0 < h)
    (hK : 1 ≤ K) (hτ₂ : 0 ≤ τ₂) (hτm : 0 ≤ τm) :
    h * K ≤ forcingBudget k Ck σ h K τ₂ τm ∧ τm ≤ forcingBudget k Ck σ h K τ₂ τm := by
  have hK0 : 0 < K := by linarith
  have he : h * K ^ 3 ≤ epsc σ h K τ₂ := le_epsc hσ hτ₂
  have he0 : 0 < epsc σ h K τ₂ := lt_of_lt_of_le (by positivity) he
  have hL1 : 1 ≤ logFactor k Ck K (epsc σ h K τ₂) := by
    unfold logFactor
    have : 0 ≤ Ck * K ^ (k + 5) / epsc σ h K τ₂ := by positivity
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Ck * K ^ (k + 5) / epsc σ h K τ₂ by linarith)
    linarith
  have hKp : ∀ p : ℕ, 1 ≤ K ^ p := fun p => one_le_pow₀ hK
  have hhK : h * K ≤ h * K ^ 3 := by
    have : K ≤ K ^ 3 := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * K ^ 2 := mul_le_mul_of_nonneg_left (hKp 2) hK0.le
        _ = K ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left this hh.le
  have hT1 : epsc σ h K τ₂ ≤ epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) := by
    have h1 := hKp (k + 1)
    have h2 : 1 ≤ logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) := one_le_pow₀ hL1
    calc epsc σ h K τ₂ = epsc σ h K τ₂ * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hT2 : τm ≤ K ^ (k + 2) * τm := le_mul_of_one_le_left hτm (hKp _)
  have hT10 : 0 ≤ epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) := by
    have : 0 ≤ logFactor k Ck K (epsc σ h K τ₂) := by linarith
    positivity
  unfold forcingBudget
  constructor
  · have : 0 ≤ K ^ (k + 2) * τm := by positivity
    linarith
  · linarith

/-- `K ≥ c₁ h^{-β}`, `0 < h ≤ 1`, `βp ≥ 1` give `K^{-p} ≤ c₁^{-p} h`. -/
theorem rpow_neg_le_of_lower {h K c₁ β p : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hc₁ : 0 < c₁)
    (hK : c₁ * h ^ (-β) ≤ K) (hp : 0 ≤ p) (hβp : 1 ≤ β * p) : K ^ (-p) ≤ c₁ ^ (-p) * h := by
  have hlow : 0 < c₁ * h ^ (-β) := mul_pos hc₁ (Real.rpow_pos_of_pos hh0 _)
  calc K ^ (-p) ≤ (c₁ * h ^ (-β)) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos hlow hK (by linarith)
    _ = c₁ ^ (-p) * h ^ (β * p) := by
        rw [Real.mul_rpow hc₁.le (Real.rpow_pos_of_pos hh0 _).le, ← Real.rpow_mul hh0.le]
        congr 2; ring
    _ ≤ c₁ ^ (-p) * h ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hh0 hh1 hβp)
          (Real.rpow_pos_of_pos hc₁ _).le
    _ = c₁ ^ (-p) * h := by rw [Real.rpow_one]

end Budget

/-! ### The sampled records satisfy the hypotheses of `thm:native-source` -/

section Main

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- The odd grid sizes `n_m = 2m + 1`. -/
abbrev oddN (m : ℕ) : ℕ := 2 * m + 1

/-- The mesh `h_m = 2π/(2m+1)`. -/
def meshOdd (m : ℕ) : ℝ := 2 * π / (oddN m : ℕ)

theorem meshOdd_pos (m : ℕ) : 0 < meshOdd m := by unfold meshOdd; positivity

theorem tendsto_meshOdd : Tendsto meshOdd atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall meshOdd_pos⟩
  have h1 : Tendsto (fun m : ℕ => ((oddN m : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_atTop_mono (fun m => by simp only [id, oddN]; omega) tendsto_id
  have := h1.const_div_atTop (2 * π)
  exact this

open NativeRate in
open Classical in
set_option maxHeartbeats 3200000 in
/-- **`cor:local-calibration-nonempty`, source part of the budget clause.**  Let `Y` be the smooth
`2π`-periodic extension of a solution (`𝓔₀(Y) = 0` on the buffered slab
`Q' = [t₀-δ, t₁+δ) × [0,2π)³`), with coframe values in a compact `K_e⁰ ⊂ {det e > 0}`.  Fix
`k ≥ 1`, `C_k > 0`, `0 < β < 1/(k+4)` and cutoffs `K_h` with `1 ≤ K_h`,
`c₁ h^{-β} ≤ K_h ≤ c₂ h^{-β}`.  Then there are a compact chart `K_e ⊇ K_e⁰` inside `{det e > 0}`,
an amplitude `A`, constants `C, C_σ ≥ 0` and the margins `c_res, τ_* > 0` of `thm:native-source`
such that, along the odd grids `n = 2m+1` (`h = 2π/n`), the sampled records `u_h = 𝖲_h Y` with
`σ_h = C_σ h`:
1. eventually satisfy every record hypothesis of `NativeSourceThm.native_source` (complete record
   and low head in `K_e` with amplitude `≤ A`, `hK_h ≤ c_res`, `τ_{h,k+2}(K_h) ≤ τ_*`,
   `h⁴ Σ_{Q'_h} ‖E_h^raw(u_h)‖² ≤ σ_h²`), and hence the strong source bound
   `‖𝓡_B(z_h)‖_{L²H^k(Q)} + ‖𝓡_D(z_h)‖_{L²H^{k+1}(Q)} ≤ C F_{h,k}`;
2. have `τ_{h,2}(K_h) = O(hK_h)`, `τ_{h,k+2}(K_h) = O(hK_h²)` (`eq:native-tail-rate`) and
   `F_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, so `F_{h,k} → 0`. -/
theorem sampled_native_source {Ke₀ : Set Mat} (hKe₀ : IsCompact Ke₀)
    (hdet₀ : ∀ e ∈ Ke₀, 0 < e.det) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hper : IsPeriodic (2 * π) Y) (hYe : ∀ z, (Y z).1 ∈ Ke₀) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ}
    (hCk : 0 < Ck) {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π)
    (hsol : ∀ z ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ),
      contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y z = 0)
    {β c₁ c₂ : ℝ} (hβ : 0 < β) (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
    (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β)) :
    ∃ (Ke : Set Mat) (A C Cσ c_res τs : ℝ), IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧ Ke₀ ⊆ Ke ∧
      0 ≤ C ∧ 0 ≤ Cσ ∧ 0 < c_res ∧ 0 < τs ∧
      (∀ᶠ m in atTop,
        meshOdd m * Kh m ≤ c_res ∧
        tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y) ≤ τs ∧
        (∀ x, (reconLow (oddN m) (Kh m) (samp (n := oddN m) (meshOdd m) Y) x).1 ∈ Ke) ∧
        (∀ x, ‖reconLow (oddN m) (Kh m) (samp (n := oddN m) (meshOdd m) Y) x‖ ≤ A) ∧
        (∀ x, (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y) x).1 ∈ Ke) ∧
        (∀ x, ‖recon (oddN m) (samp (n := oddN m) (meshOdd m) Y) x‖ ≤ A) ∧
        meshOdd m ^ 4 * ∑ x ∈ Finset.univ.filter
            (fun x : Grid (oddN m) => pos (meshOdd m) x ∈
              NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
            ‖eulerRow (localAction D (meshOdd m)) (meshOdd m)
              (samp (n := oddN m) (meshOdd m) Y) x‖ ^ 2 ≤ (Cσ * meshOdd m) ^ 2 ∧
        NativeTail.sobX k (NativeSlab.slab t₀ t₁)
            (RB D (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y))) +
          NativeTail.sobX (k + 1) (NativeSlab.slab t₀ t₁)
            (RD D (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y))) ≤
          C * forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
            (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
            (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) ∧
      (fun m => tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y)) =O[atTop]
        (fun m => meshOdd m * Kh m) ∧
      (fun m => tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y)) =O[atTop]
        (fun m => meshOdd m * Kh m ^ 2) ∧
      (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) =O[atTop]
        (fun m => meshOdd m ^ (1 - β * (k + 4)) * (1 + |Real.log (meshOdd m)|) ^ (k + 1)) ∧
      Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) atTop (𝓝 0) := by
  -- the order `q` of the derivative reserve
  set q : ℕ := k + 5 + ⌈1 / β⌉₊ with hq
  have hβq1 : 1 ≤ β * ((q : ℝ) - 1) := by
    have hc := Nat.le_ceil (1 / β)
    have : (1 : ℝ) / β ≤ (q : ℝ) - 1 := by
      rw [hq]; push_cast; linarith
    rw [div_le_iff₀ hβ] at this; linarith
  have hβq : 1 ≤ β * (q : ℝ) := by nlinarith
  have hq2 : ((k + 2 : ℕ) : ℝ) + 2 < q := by rw [hq]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈1 / β⌉₊]
  have hq2' : ((2 : ℕ) : ℝ) + 2 < q := by rw [hq]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈1 / β⌉₊]
  -- derivative bounds of the smooth periodic field
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv hY (by positivity) hper q
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hYA : ∀ z, ‖Y z‖ ≤ M := fun z => by
    have := hM 0 (Nat.zero_le _) z; rwa [norm_iteratedFDeriv_zero] at this
  have hq3 : 3 ≤ q := by omega
  -- the chart thickening
  have hopen : IsOpen {e : Mat | 0 < e.det} :=
    isOpen_lt continuous_const (continuous_id.matrix_det)
  obtain ⟨ε, hε, hεsub⟩ := hKe₀.exists_cthickening_subset_open hopen (fun e he => hdet₀ e he)
  set Ke : Set Mat := cthickening ε Ke₀ with hKe
  have hKec : IsCompact Ke := hKe₀.cthickening
  have hKedet : ∀ e ∈ Ke, 0 < e.det := fun e he => hεsub he
  set A : ℝ := M + 1 with hA
  -- constants
  obtain ⟨C, c_res, τs, hC, hc_res, hτs, hsrc⟩ :=
    NativeSourceThm.native_source D hKec hKedet A k hk hCk hδ h0 h1
  obtain ⟨Cσ', c_res', hCσ', hc_res', hsig⟩ := native_sigma_seam D hKec hKedet A M
  set Cσ : ℝ := (2 * π) ^ 2 * Cσ' with hCσ
  obtain ⟨C₂, hC₂, htail2⟩ := SampledTail.tau_samp_le (V := Field 𝔄 𝓗 𝓢) 2 q hq2'
  obtain ⟨Cm, hCm, htailm⟩ := SampledTail.tau_samp_le (V := Field 𝔄 𝓗 𝓢) (k + 2) q hq2
  obtain ⟨C₄, hC₄, htail1⟩ := SampledTail.tau_samp_le (V := Field 𝔄 𝓗 𝓢) 1 4 (by norm_num)
  set Cτ : ℝ := max (C₂ * M * c₁ ^ (-((q : ℝ) - 1))) (Cm * M * c₁ ^ (-(q : ℝ))) with hCτ
  have hCτ0 : 0 ≤ Cτ := le_trans (by positivity) (le_max_left _ _)
  have hM4 : ∀ r ≤ 4, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M := fun r hr z => hM r (by omega) z
  -- abbreviations
  set u : ∀ m : ℕ, Grid (oddN m) → Field 𝔄 𝓗 𝓢 := fun m => samp (n := oddN m) (meshOdd m) Y
    with hu
  set τ₂ : ℕ → ℝ := fun m => tau (oddN m) (Kh m) 2 (u m) with hτ₂
  set τm : ℕ → ℝ := fun m => tau (oddN m) (Kh m) (k + 2) (u m) with hτm
  set F : ℕ → ℝ := fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m) (τ₂ m) (τm m)
    with hF
  have hmesh2π : ∀ m, meshOdd m = 2 * π / (oddN m : ℕ) := fun m => rfl
  -- eventually `h ≤ 1`
  have hh1 : ∀ᶠ m in atTop, meshOdd m ≤ 1 :=
    (tendsto_meshOdd.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds one_pos)
  -- the tail rates
  have htail_rates : ∀ᶠ m in atTop, τ₂ m ≤ Cτ * (meshOdd m * Kh m) ∧
      τm m ≤ Cτ * (meshOdd m * Kh m ^ 2) := by
    filter_upwards [hKh, hh1] with m ⟨hK1, hKlo, _⟩ hm1
    have hK0 : 0 < Kh m := by linarith
    have hm0 := meshOdd_pos m
    have t2 := htail2 (oddN m) Y M hY hper hM (Kh m) hK1
    have tm := htailm (oddN m) Y M hY hper hM (Kh m) hK1
    have r1 := rpow_neg_le_of_lower hm0 hm1 hc₁ hKlo (p := (q : ℝ) - 1) (by
      have : (3 : ℝ) ≤ q := by exact_mod_cast hq3
      linarith) hβq1
    have r2 := rpow_neg_le_of_lower hm0 hm1 hc₁ hKlo (p := (q : ℝ)) (Nat.cast_nonneg _) hβq
    have e1 : Kh m ^ (2 - (q : ℝ)) = Kh m ^ (-((q : ℝ) - 1)) * Kh m := by
      rw [show (2 - (q : ℝ)) = -((q : ℝ) - 1) + 1 by ring, Real.rpow_add hK0, Real.rpow_one]
    have e2 : Kh m ^ (2 - (q : ℝ)) = Kh m ^ (-(q : ℝ)) * Kh m ^ 2 := by
      rw [show (2 - (q : ℝ)) = -(q : ℝ) + 2 by ring, Real.rpow_add hK0]
      norm_cast
    constructor
    · show tau (oddN m) (Kh m) 2 (u m) ≤ _
      calc tau (oddN m) (Kh m) 2 (u m) ≤ C₂ * M * Kh m ^ (2 - (q : ℝ)) := t2
        _ = C₂ * M * Kh m ^ (-((q : ℝ) - 1)) * Kh m := by rw [e1]; ring
        _ ≤ C₂ * M * (c₁ ^ (-((q : ℝ) - 1)) * meshOdd m) * Kh m := by gcongr
        _ = (C₂ * M * c₁ ^ (-((q : ℝ) - 1))) * (meshOdd m * Kh m) := by ring
        _ ≤ Cτ * (meshOdd m * Kh m) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · show tau (oddN m) (Kh m) (k + 2) (u m) ≤ _
      calc tau (oddN m) (Kh m) (k + 2) (u m) ≤ Cm * M * Kh m ^ (2 - (q : ℝ)) := tm
        _ = Cm * M * Kh m ^ (-(q : ℝ)) * Kh m ^ 2 := by rw [e2]; ring
        _ ≤ Cm * M * (c₁ ^ (-(q : ℝ)) * meshOdd m) * Kh m ^ 2 := by gcongr
        _ = (Cm * M * c₁ ^ (-(q : ℝ))) * (meshOdd m * Kh m ^ 2) := by ring
        _ ≤ Cτ * (meshOdd m * Kh m ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  -- the budget rate
  have hev : ∀ᶠ m in atTop, 0 < meshOdd m ∧ meshOdd m ≤ 1 ∧ 1 ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β) ∧ 0 ≤ Cσ * meshOdd m ∧ Cσ * meshOdd m ≤ Cσ * meshOdd m ∧
      0 ≤ τ₂ m ∧ τ₂ m ≤ Cτ * (meshOdd m * Kh m) ∧ 0 ≤ τm m ∧
      τm m ≤ Cτ * (meshOdd m * Kh m ^ 2) := by
    filter_upwards [hKh, hh1, htail_rates] with m ⟨hK1, _, hKup⟩ hm1 ⟨ht2, htm⟩
    have hK0 : 0 < Kh m := by linarith
    exact ⟨meshOdd_pos m, hm1, hK1, hKup, by have := meshOdd_pos m; positivity, le_rfl,
      TrigInterp.tau_nonneg _ hK0 _ _, ht2, TrigInterp.tau_nonneg _ hK0 _ _, htm⟩
  have hFO : F =O[atTop]
      (fun m => meshOdd m ^ (1 - β * (k + 4)) * (1 + |Real.log (meshOdd m)|) ^ (k + 1)) :=
    forcingBudget_isBigO k hCk.le hβ.le (by positivity) hev
  have hρ : 0 < 1 - β * (k + 4) := by
    have hk4 : (0 : ℝ) < k + 4 := by positivity
    rw [lt_div_iff₀ hk4] at hβk; linarith
  have hrate : Tendsto (fun m => meshOdd m ^ (1 - β * (k + 4)) *
      (1 + |Real.log (meshOdd m)|) ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_one_add_abs_log_pow hρ (k + 1)).comp tendsto_meshOdd
  have hFt : Tendsto F atTop (𝓝 0) := hFO.trans_tendsto hrate
  -- the τ rates as big-O
  have hτ2O : τ₂ =O[atTop] (fun m => meshOdd m * Kh m) := by
    refine IsBigO.of_bound Cτ ?_
    filter_upwards [htail_rates, hKh] with m ⟨ht2, _⟩ ⟨hK1, _, _⟩
    have hK0 : 0 < Kh m := by linarith
    have := meshOdd_pos m
    rw [Real.norm_of_nonneg (TrigInterp.tau_nonneg _ hK0 _ _), Real.norm_of_nonneg (by positivity)]
    exact ht2
  have hτmO : τm =O[atTop] (fun m => meshOdd m * Kh m ^ 2) := by
    refine IsBigO.of_bound Cτ ?_
    filter_upwards [htail_rates, hKh] with m ⟨_, htm⟩ ⟨hK1, _, _⟩
    have hK0 : 0 < Kh m := by linarith
    have := meshOdd_pos m
    rw [Real.norm_of_nonneg (TrigInterp.tau_nonneg _ hK0 _ _), Real.norm_of_nonneg (by positivity)]
    exact htm
  -- smallness from `F → 0`
  set c₀ : ℝ := 649 * M + C₄ * M with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set η : ℝ := min (min ε 1 / (2 * (1 + c₀))) (min (min c_res c_res') τs) with hη
  have hη0 : 0 < η := lt_min (by positivity) (lt_min (lt_min hc_res hc_res') hτs)
  have hFsmall : ∀ᶠ m in atTop, F m < η := hFt.eventually (gt_mem_nhds hη0)
  refine ⟨Ke, A, C, Cσ, c_res, τs, hKec, hKedet, self_subset_cthickening _, hC,
    by positivity, hc_res, hτs, ?_, hτ2O, hτmO, hFO, hFt⟩
  filter_upwards [hFsmall, hev] with m hFm ⟨hm0, hm1, hK1, hKup, hσ0, _, ht20, ht2, htm0, htm⟩
  have hK0 : 0 < Kh m := by linarith
  obtain ⟨hhK, hτF⟩ := le_forcingBudget k hCk.le hσ0 hm0 hK1 ht20 htm0
  have hFη : F m ≤ η := hFm.le
  have hηc : η ≤ c_res := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηc' : η ≤ c_res' := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hητ : η ≤ τs := (min_le_right _ _).trans (min_le_right _ _)
  have hηε : η ≤ min ε 1 / (2 * (1 + c₀)) := min_le_left _ _
  -- mesh and tail smallness
  have hhK' : meshOdd m * Kh m ≤ η := hhK.trans hFη
  have hh_le : meshOdd m ≤ η := by
    calc meshOdd m = meshOdd m * 1 := (mul_one _).symm
      _ ≤ meshOdd m * Kh m := mul_le_mul_of_nonneg_left hK1 hm0.le
      _ ≤ η := hhK'
  have hτm_le : τm m ≤ η := hτF.trans hFη
  -- closeness of the reconstructions
  have hY1 : ∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ M := hM 1 (by omega)
  have hτ1 : tau (oddN m) 1 1 (samp (n := oddN m) (2 * π / ((oddN m : ℕ) : ℝ)) Y) ≤ C₄ * M := by
    have := htail1 (oddN m) Y M hY hper hM4 1 le_rfl
    rw [Real.one_rpow, mul_one] at this
    exact this
  have hodd : Odd (oddN m) := ⟨m, rfl⟩
  have hrec : ∀ z, ‖recon (oddN m) (u m) z - Y z‖ ≤ c₀ * meshOdd m := by
    intro z
    have := norm_recon_sub_le hodd (hY.of_le (by exact_mod_cast le_top)) hper hYA hY1 z
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hm0.le)
    rw [hc₀]; linarith
  have hlow : ∀ z, ‖reconLow (oddN m) (Kh m) (u m) z - recon (oddN m) (u m) z‖ ≤ τm m := by
    intro z
    rw [norm_sub_rev]
    exact (TrigInterp.norm_recon_sub_reconLow_le (oddN m) hK0 (u m) 0 z).trans
      (TrigInterp.tau_mono (oddN m) hK0 (Nat.zero_le _) (u m))
  have hsmall : (1 + c₀) * η ≤ min ε 1 / 2 := by
    have h2 : 0 < 2 * (1 + c₀) := by positivity
    calc (1 + c₀) * η ≤ (1 + c₀) * (min ε 1 / (2 * (1 + c₀))) :=
          mul_le_mul_of_nonneg_left hηε (by positivity)
      _ = min ε 1 / 2 := by field_simp
  have hmin : min ε 1 / 2 < min ε 1 := by have := lt_min hε one_pos; linarith
  have hrecY : ∀ z, ‖recon (oddN m) (u m) z - Y z‖ < min ε 1 := by
    intro z
    have : c₀ * meshOdd m ≤ (1 + c₀) * η := by nlinarith
    linarith [hrec z]
  have hlowY : ∀ z, ‖reconLow (oddN m) (Kh m) (u m) z - Y z‖ < min ε 1 := by
    intro z
    have e : reconLow (oddN m) (Kh m) (u m) z - Y z =
        (reconLow (oddN m) (Kh m) (u m) z - recon (oddN m) (u m) z) +
          (recon (oddN m) (u m) z - Y z) := by abel
    rw [e]
    have : τm m + c₀ * meshOdd m ≤ (1 + c₀) * η := by nlinarith
    calc ‖(reconLow (oddN m) (Kh m) (u m) z - recon (oddN m) (u m) z) +
          (recon (oddN m) (u m) z - Y z)‖
        ≤ τm m + c₀ * meshOdd m := (norm_add_le _ _).trans (add_le_add (hlow z) (hrec z))
      _ < min ε 1 := by linarith
  -- chart and amplitude from closeness
  have hchart : ∀ w : Field 𝔄 𝓗 𝓢, ∀ z, ‖w - Y z‖ < min ε 1 → w.1 ∈ Ke ∧ ‖w‖ ≤ A := by
    intro w z hw
    constructor
    · refine mem_cthickening_of_dist_le w.1 (Y z).1 ε Ke₀ (hYe z) ?_
      rw [dist_eq_norm]
      have : ‖w.1 - (Y z).1‖ ≤ ‖w - Y z‖ := by
        rw [← Prod.fst_sub]; exact norm_fst_le _
      linarith [min_le_left ε 1]
    · have := norm_le_insert' w (Y z)
      have h1 : ‖w‖ ≤ ‖Y z‖ + ‖w - Y z‖ := by
        calc ‖w‖ = ‖Y z + (w - Y z)‖ := by congr 1; abel
          _ ≤ ‖Y z‖ + ‖w - Y z‖ := norm_add_le _ _
      linarith [hYA z, min_le_right ε 1]
  have hKcl : ∀ x, (reconLow (oddN m) (Kh m) (u m) x).1 ∈ Ke := fun x => (hchart _ x (hlowY x)).1
  have hAl : ∀ x, ‖reconLow (oddN m) (Kh m) (u m) x‖ ≤ A := fun x => (hchart _ x (hlowY x)).2
  have hKcf : ∀ x, (recon (oddN m) (u m) x).1 ∈ Ke := fun x => (hchart _ x (hrecY x)).1
  have hAf : ∀ x, ‖recon (oddN m) (u m) x‖ ≤ A := fun x => (hchart _ x (hrecY x)).2
  -- the seam-local row bound
  have hmesh' : 2 * π / ((oddN m : ℕ) : ℝ) ≤ c_res' := by
    rw [← hmesh2π]; exact hh_le.trans hηc'
  obtain ⟨-, hσsum⟩ := hsig (oddN m) hmesh' Y (hY.of_le (ContEulerBounds.natCast_le_infty 3)) hper
    (fun z => self_subset_cthickening Ke₀ (hYe z))
    (fun z => (hYA z).trans (by rw [hA]; linarith)) (hM 1 (by omega)) (hM 2 (by omega)) (hM 3 (by omega))
    (NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)) hsol
  have hσsum' : meshOdd m ^ 4 * ∑ x ∈ Finset.univ.filter
      (fun x : Grid (oddN m) => pos (meshOdd m) x ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ)),
      ‖eulerRow (localAction D (meshOdd m)) (meshOdd m) (u m) x‖ ^ 2 ≤ (Cσ * meshOdd m) ^ 2 := by
    have e : (2 * π) ^ 2 * Cσ' * meshOdd m = Cσ * meshOdd m := by rw [hCσ]
    rw [← e]
    exact hσsum
  refine ⟨hhK'.trans hηc, hτm_le.trans hητ, hKcl, hAl, hKcf, hAf, hσsum', ?_⟩
  -- `thm:native-source`
  have hS := hsrc (oddN m) hodd (u m) (Kh m) (Cσ * meshOdd m) hK1 (by
      rw [← hmesh2π]; exact hhK'.trans hηc) (hτm_le.trans hητ) hKcl hAl hKcf hAf hσ0 (by
      rw [← hmesh2π]; exact hσsum')
  have := hS.2.1
  rw [← hmesh2π] at this
  exact this

end Main

/-! ### Non-vacuity -/

section NonVacuity

/-- A coefficient bank with vanishing couplings (`κ = Λ = λ_H = 0`, zero invariant forms, gamma
matrices and Yukawa map): its local density vanishes identically, so every field solves the
continuum Euler equations.  Used only to show that the hypotheses of `sampled_native_source` are
jointly satisfiable. -/
def zeroData : Data ℝ ℝ ℝ where
  κ := 0
  Λ := 0
  lamH := 0
  vH := 0
  ipA := 0
  hermH := 0
  ρH := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρH_cont := (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap.continuous_of_finiteDimensional
  ρS := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρS_cont := (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap.continuous_of_finiteDimensional
  σ := 0
  γ := 0
  yukawa := 0

theorem firstJetDensity_zeroData (q : ℝ × NativeDensity.Jet (Field ℝ ℝ ℝ)) :
    firstJetDensity zeroData q = 0 := by
  simp [firstJetDensity, gravFirstJet, pal, dqPal, normYM, normHiggs, normD, potential, gammaMu,
    zeroData]

theorem contEuler_zeroData (Y : R4 → Field ℝ ℝ ℝ) (z : R4) :
    contEuler (limDensity (ι := Shift) (firstJetDensity zeroData)) Y z = 0 := by
  have hL : limDensity (ι := Shift) (firstJetDensity zeroData) = fun _ => 0 := by
    funext wp; exact firstJetDensity_zeroData _
  rw [hL]
  simp [contEuler]

/-- **Non-vacuity of `sampled_native_source`**: for the vanishing coefficient bank, the flat
constant field (identity coframe, all other fields zero) with the chart `{1}` and the cutoffs
`K_h = h^{-β}` (`c₁ = c₂ = 1`) satisfies every hypothesis, for every `k ≥ 1`, `0 < β < 1/(k+4)`
and every buffered slab inside one period. -/
theorem sampled_native_source_hyps (β : ℝ) (hβ : 0 < β) :
    let Y : R4 → Field ℝ ℝ ℝ := fun _ => ((1 : Mat), 0)
    ContDiff ℝ ∞ Y ∧ IsPeriodic (2 * π) Y ∧ (∀ z, (Y z).1 ∈ ({1} : Set Mat)) ∧
      IsCompact ({1} : Set Mat) ∧ (∀ e ∈ ({1} : Set Mat), 0 < e.det) ∧
      (∀ (Q' : Set R4), ∀ z ∈ Q',
        contEuler (limDensity (ι := Shift) (firstJetDensity zeroData)) Y z = 0) ∧
      (∀ᶠ m in atTop, 1 ≤ meshOdd m ^ (-β) ∧ 1 * meshOdd m ^ (-β) ≤ meshOdd m ^ (-β) ∧
        meshOdd m ^ (-β) ≤ 1 * meshOdd m ^ (-β)) := by
  intro Y
  refine ⟨contDiff_const, fun z μ => rfl, fun z => rfl, isCompact_singleton, fun e he => ?_,
    fun Q' z _ => contEuler_zeroData Y z, ?_⟩
  · rw [mem_singleton_iff] at he; subst he; simp
  · have hh1 : ∀ᶠ m in atTop, meshOdd m ≤ 1 :=
      (tendsto_meshOdd.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds one_pos)
    filter_upwards [hh1] with m hm
    refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos (meshOdd_pos m) hm (by linarith), ?_, ?_⟩
    · rw [one_mul]
    · rw [one_mul]

example (k : ℕ) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β) (hβk : β < 1 / (k + 4)) :
    ∃ (Ke : Set Mat) (A C Cσ c_res τs : ℝ), IsCompact Ke ∧ (∀ e ∈ Ke, 0 < e.det) ∧
      ({1} : Set Mat) ⊆ Ke ∧ 0 ≤ C ∧ 0 ≤ Cσ ∧ 0 < c_res ∧ 0 < τs ∧
      Tendsto (fun m => NativeRate.forcingBudget k 1 (Cσ * meshOdd m) (meshOdd m)
          (meshOdd m ^ (-β))
          (tau (oddN m) (meshOdd m ^ (-β)) 2
            (samp (n := oddN m) (meshOdd m) (fun _ : R4 => (((1 : Mat), 0) : Field ℝ ℝ ℝ))))
          (tau (oddN m) (meshOdd m ^ (-β)) (k + 2)
            (samp (n := oddN m) (meshOdd m) (fun _ : R4 => (((1 : Mat), 0) : Field ℝ ℝ ℝ)))))
        atTop (𝓝 0) := by
  obtain ⟨hY, hper, hYe, hKc, hdet, hsol, hKh⟩ := sampled_native_source_hyps β hβ
  have hδ : (0 : ℝ) < 1 := one_pos
  obtain ⟨Ke, A, C, Cσ, c_res, τs, hKec, hKedet, hsub, hC, hCσ, hc, hτ, -, -, -, -, hF⟩ :=
    sampled_native_source zeroData hKc hdet hY hper hYe k hk one_pos (t₀ := 2) (t₁ := 3)
      hδ (by norm_num) (by linarith [Real.pi_gt_three]) (hsol _) hβ hβk one_pos
      (fun m => meshOdd m ^ (-β)) hKh
  exact ⟨Ke, A, C, Cσ, c_res, τs, hKec, hKedet, hsub, hC, hCσ, hc, hτ, hF⟩

end NonVacuity

end RenewalGeometry.LocalCalibration
