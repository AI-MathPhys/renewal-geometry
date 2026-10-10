/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.LocalCalibrationBudgets
import RenewalGeometry.Continuum.NativeSourcePhys

/-!
# Sampled smooth solutions of the physical native Euler equations
  (`cor:local-calibration-nonempty`, budget clause, source part; gauge rows in `𝔤`)

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty`: "Nodal
sampling followed by trigonometric reconstruction yields records for `S_h^loc` with `σ_h = O(h)`
and with the budgets of `thm:native-closure` tending to zero for a suitable `K_h → ∞`."

Corrected encoding (gauge sector in the gauge Lie algebra `𝔤`): the solution is assumed to solve
the native Euler equations on the **physical** directions only, `𝓔₀(Y) ∘ physF P_𝔤 = 0` (for a slab
model `P_𝔤 = πg`, the projection onto `𝔤`: coframe, `𝔤`-gauge, Higgs, spinor and co-spinor
directions), and the budgets read only the physical rows.  This is what the manuscript's
solutions satisfy; the rows in the non-gauge directions of `𝔄` (e.g. the unit, whose row is
`-2v g^{σν}⟨H, ∂_νH⟩`) are not part of the Euler equations of the manuscript.

* **`native_sigma_seam_phys`** — `σ_h = O(h)` for the physical raw rows of the samples;
* **`sampled_native_source_phys`** — the physical form of `LocalCalibration.sampled_native_source`:
  the sampled records eventually satisfy every record hypothesis of
  `NativeSourceThm.native_source_phys`, with `σ_h = C_σh`, the tail rates and
  `F_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1}) → 0`.
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

section Phys

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

open Classical in
/-- **`σ_h = O(h)` for the physical rows of sampled solutions, seam-local form**: as
`native_sigma_seam`, for solutions of the physical Euler equations `𝓔₀(Y) ∘ physF P_𝔤 = 0` on `Q'`
and the physical raw rows `E_h^raw(𝖲_hY) ∘ physF P_𝔤`. -/
theorem native_sigma_seam_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A B : ℝ) :
    ∃ C c_res : ℝ, 0 ≤ C ∧ 0 < c_res ∧ ∀ (n : ℕ) [NeZero n], 2 * π / n ≤ c_res →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ 3 Y → IsPeriodic (2 * π) Y → (∀ z, (Y z).1 ∈ Ke) →
        (∀ z, ‖Y z‖ ≤ A) → (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B) →
        (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B) → (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B) →
        ∀ Q' : Set R4, (∀ z ∈ Q', (contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y z).comp
          (NativeTail.physF Pg) = 0) →
        (∀ x : Grid n, pos (2 * π / n) x ∈ Q' →
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) (samp (2 * π / n) Y) x).comp
            (NativeTail.physF Pg)‖ ≤ C * (2 * π / n)) ∧
        (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos (2 * π / n) x ∈ Q'),
          ‖(eulerRow (localAction D (2 * π / n)) (2 * π / n) (samp (2 * π / n) Y) x).comp
            (NativeTail.physF Pg)‖ ^ 2 ≤ ((2 * π) ^ 2 * C * (2 * π / n)) ^ 2 := by
  obtain ⟨C, c_res, hc, hmain⟩ := native_consistency D hKe hdet A B
  set Lp := ContEulerBounds.preL (NativeTail.physF (𝓗 := 𝓗) (𝓢 := 𝓢) Pg) with hLp
  set cP : ℝ := ‖Lp‖ with hcP
  have hcP0 : 0 ≤ cP := by rw [hcP]; exact ContinuousLinearMap.opNorm_nonneg _
  set C' : ℝ := cP * max C 0 with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hcP0 (le_max_right _ _)
  refine ⟨C', c_res, hC'0, hc, fun n _ hhc Y hYs hper hYe hYA h1 h2 h3 Q' hsol => ?_⟩
  set h : ℝ := 2 * π / n with hh
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hper' : IsPeriodic ((n : ℝ) * h) Y := by rw [hh, mul_div_cancel₀ _ hn0]; exact hper
  have hK := hmain 1 le_rfl h hh0 (by simpa using hhc) n Y hYs hper' hYe hYA
    (fun z => by simpa using h1 z) (fun z => by simpa using h2 z) (fun z => by simpa using h3 z)
  have hpt : ∀ x : Grid n, pos h x ∈ Q' →
      ‖(eulerRow (localAction D h) h (samp h Y) x).comp (NativeTail.physF Pg)‖ ≤ C' * h := by
    intro x hx
    have hx' := hK.2.2 x
    rw [one_pow, mul_one] at hx'
    have e : (eulerRow (localAction D h) h (samp h Y) x).comp (NativeTail.physF Pg) =
        Lp (eulerRow (localAction D h) h (samp h Y) x -
          contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y (pos h x)) := by
      rw [map_sub]
      show _ = (eulerRow (localAction D h) h (samp h Y) x).comp (NativeTail.physF Pg) -
        (contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y (pos h x)).comp
          (NativeTail.physF Pg)
      rw [hsol _ hx, sub_zero]
    rw [e]
    refine (Lp.le_opNorm _).trans ?_
    calc cP * ‖eulerRow (localAction D h) h (samp h Y) x -
          contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y (pos h x)‖
        ≤ cP * (max C 0 * h) :=
          mul_le_mul_of_nonneg_left (hx'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
            hh0.le)) hcP0
      _ = C' * h := by rw [hC']; ring
  refine ⟨hpt, ?_⟩
  have hC0 : 0 ≤ C' * h := mul_nonneg hC'0 hh0.le
  calc h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
        ‖(eulerRow (localAction D h) h (samp h Y) x).comp (NativeTail.physF Pg)‖ ^ 2
      ≤ h ^ 4 * ∑ _x : Grid n, (C' * h) ^ 2 := by
        gcongr
        calc ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
              ‖(eulerRow (localAction D h) h (samp h Y) x).comp (NativeTail.physF Pg)‖ ^ 2
            ≤ ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'), (C' * h) ^ 2 :=
              Finset.sum_le_sum fun x hx =>
                pow_le_pow_left₀ (norm_nonneg _) (hpt x (Finset.mem_filter.mp hx).2) 2
          _ ≤ ∑ _x : Grid n, (C' * h) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => sq_nonneg _
    _ = ((2 * π) ^ 2 * C' * h) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [ShiftedJetAction.Grid, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast
        rw [hh]
        field_simp

open NativeRate in
open Classical in
set_option maxHeartbeats 3200000 in
/-- **`cor:local-calibration-nonempty`, source part of the budget clause, physical rows** (gauge
rows in `𝔤`, through a continuous linear map `P_𝔤 : 𝔄 → 𝔄`, for a slab model the projection
`πg` onto the gauge Lie algebra).  Let `Y` be the smooth `2π`-periodic extension of a solution of
the **physical** native Euler equations (`𝓔₀(Y) ∘ physF P_𝔤 = 0` on the buffered slab
`Q' = [t₀-δ, t₁+δ) × [0,2π)³`), with coframe values in a compact `K_e⁰ ⊂ {det e > 0}`.  Fix
`k ≥ 1`, `C_k > 0`, `0 < β < 1/(k+4)` and cutoffs `K_h` with `1 ≤ K_h`,
`c₁ h^{-β} ≤ K_h ≤ c₂ h^{-β}`.  Then there are a compact chart `K_e ⊇ K_e⁰` inside `{det e > 0}`,
an amplitude `A`, constants `C, C_σ ≥ 0` and the margins `c_res, τ_* > 0` of `thm:native-source`
such that, along the odd grids `n = 2m+1` (`h = 2π/n`), the sampled records `u_h = 𝖲_h Y` with
`σ_h = C_σ h`:
1. eventually satisfy every record hypothesis of `NativeSourceThm.native_source_phys` (complete
   record and low head in `K_e` with amplitude `≤ A`, `hK_h ≤ c_res`, `τ_{h,k+2}(K_h) ≤ τ_*`,
   `h⁴ Σ_{Q'_h} ‖E_h^raw(u_h) ∘ physF P_𝔤‖² ≤ σ_h²`), and hence the strong source bound
   `‖𝓡_B^𝔤(z_h)‖_{L²H^k(Q)} + ‖𝓡_D(z_h)‖_{L²H^{k+1}(Q)} ≤ C F_{h,k}`;
2. have `τ_{h,2}(K_h) = O(hK_h)`, `τ_{h,k+2}(K_h) = O(hK_h²)` (`eq:native-tail-rate`) and
   `F_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, so `F_{h,k} → 0`. -/
theorem sampled_native_source_phys (Pg : 𝔄 →L[ℝ] 𝔄) {Ke₀ : Set Mat} (hKe₀ : IsCompact Ke₀)
    (hdet₀ : ∀ e ∈ Ke₀, 0 < e.det) {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hper : IsPeriodic (2 * π) Y) (hYe : ∀ z, (Y z).1 ∈ Ke₀) (k : ℕ) (hk : 1 ≤ k) {Ck : ℝ}
    (hCk : 0 < Ck) {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (h0 : δ < t₀) (h1 : t₁ + δ ≤ 2 * π)
    (hsol : ∀ z ∈ NativeZeroSource.bufSlab (t₀ - δ) (t₁ + δ),
      (contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y z).comp (NativeTail.physF Pg) = 0)
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
            ‖(eulerRow (localAction D (meshOdd m)) (meshOdd m)
              (samp (n := oddN m) (meshOdd m) Y) x).comp (NativeTail.physF Pg)‖ ^ 2 ≤
              (Cσ * meshOdd m) ^ 2 ∧
        NativeTail.sobX k (NativeSlab.slab t₀ t₁)
            (NativeTail.RBP D Pg (recon (oddN m) (samp (n := oddN m) (meshOdd m) Y))) +
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
    NativeSourceThm.native_source_phys D Pg hKec hKedet A k hk hCk hδ h0 h1
  obtain ⟨Cσ', c_res', hCσ', hc_res', hsig⟩ := native_sigma_seam_phys D Pg hKec hKedet A M
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
      ‖(eulerRow (localAction D (meshOdd m)) (meshOdd m) (u m) x).comp (NativeTail.physF Pg)‖ ^ 2 ≤
        (Cσ * meshOdd m) ^ 2 := by
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

end Phys

end RenewalGeometry.LocalCalibration
