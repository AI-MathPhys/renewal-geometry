/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.DyadicRateAsymptotics
import RenewalGeometry.Analysis.PeriodicTrigInterpolation

/-!
# Composition bounds for record coefficients and monotonicity of the forcing budget

Generic infrastructure for the source-budget comparison of `thm:native-closure`
(Einstein–Standard-Model action-closure manuscript, `eq:native-forcing-budget`).

* **`exists_comp_bound`** — Faà di Bruno on a compact subset of an open chart: if `g` is smooth on
  an open `U ⊇ K` (`K` compact), there is `C` such that for every smooth `f` with values in `K`
  and `‖D^i f(x)‖ ≤ D^i` (`1 ≤ i ≤ n`), `‖D^n(g ∘ f)(x)‖ ≤ n! C D^n`.
* **`norm_iteratedFDeriv_clm_recon_le`** — the derivatives of a (contracted) trigonometric
  reconstruction: `‖D^i(L ∘ z)(x)‖ ≤ (240(A + τ + 1)K)^i` for `1 ≤ i ≤ j`, from
  `‖z^{lo}‖ ≤ A`, `τ_j(K) ≤ τ`, `‖L‖ ≤ 1`.
* **`pow_mul_forcingBudget_le`** — `K^l F_{h,k'} ≤ F_{h,k}` for `k' + l = k` (`τ_{k'+2} ≤ τ_{k+2}`);
  **`pow_mul_eps0_le`** — `K^l ε_{0,h} ≤ F_{h,k}` for `l ≤ k + 1`.
-/

open Finset Set
open scoped ContDiff Nat

namespace RenewalGeometry.SourceCompare

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Faà di Bruno on a compact subset of a chart -/

section Comp

variable {X G E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_iteratedFDerivWithin_bound {g : X → G} {U : Set X} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i ≤ n, ‖iteratedFDerivWithin ℝ i g U y‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ i g U y‖ ≤ C := fun i =>
    hK.exists_bound_of_continuousOn ((hg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast le_top) hU.uniqueDiffOn).mono hKU)
  choose Cf hCf using hb
  refine ⟨∑ i ∈ range (n + 1), |Cf i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun y hy i hi => ?_⟩
  refine (hCf i y hy).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun i => |Cf i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- **Faà di Bruno on a compact subset of a chart.** -/
theorem exists_comp_bound {g : X → G} {U : Set X} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → X), ContDiff ℝ ∞ f → (∀ x, f x ∈ K) → ∀ (D : ℝ) (x : E),
      (∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) →
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ j ! * C * D ^ j := by
  obtain ⟨C, hC0, hC⟩ := exists_iteratedFDerivWithin_bound hU hg hK hKU n
  refine ⟨C, hC0, fun f hf hfK D x hD j hj => ?_⟩
  refine norm_iteratedFDeriv_comp_le' (t := U) ?_ hU.uniqueDiffOn hg hf
    (by exact_mod_cast le_top) x (fun i hi => hC _ (hfK x) i (hi.trans hj))
    (fun i h1 h2 => hD i h1 (h2.trans hj))
  rintro _ ⟨y, rfl⟩
  exact hKU (hfK y)

end Comp

/-! ### Derivatives of a trigonometric reconstruction -/

section Recon

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X]
  [NormedSpace ℝ X]
variable {n : ℕ} [NeZero n]

/-- **Derivative bound for a contracted reconstruction**: for `1 ≤ i ≤ j`,
`‖D^i(L ∘ z)(x)‖ ≤ (240(A + τ + 1)K)^i` when `‖L‖ ≤ 1`, `K ≥ 1`, `‖z^{lo}‖ ≤ A`,
`τ_j(K) ≤ τ`. -/
theorem norm_iteratedFDeriv_clm_recon_le (L : V →L[ℝ] X) (hL : ‖L‖ ≤ 1)
    (u : (Fin 4 → ZMod n) → V) {K A τ : ℝ} (hK : 1 ≤ K)
    (hA : ∀ y, ‖TrigInterp.reconLow n K u y‖ ≤ A) {i j : ℕ} (hij : i ≤ j)
    (hτ : TrigInterp.tau n K j u ≤ τ) (hi : 1 ≤ i) (x : Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i (fun ξ => L (TrigInterp.recon n u ξ)) x‖ ≤
      (240 * (A + τ + 1) * K) ^ i := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hτ0 : 0 ≤ τ := (TrigInterp.tau_nonneg n hK0 j u).trans hτ
  have hz : ContDiff ℝ ∞ (TrigInterp.recon n u) := VecTrig.contDiff_tp _ _
  have hzl : ContDiff ℝ ∞ (TrigInterp.reconLow n K u) := VecTrig.contDiff_tp _ _
  have h1 : ‖iteratedFDeriv ℝ i (fun ξ => L (TrigInterp.recon n u ξ)) x‖ ≤
      ‖iteratedFDeriv ℝ i (TrigInterp.recon n u) x‖ := by
    have := L.norm_iteratedFDeriv_comp_left (n := i) (x := x) hz.contDiffAt
      (by exact_mod_cast le_top)
    refine this.trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hL
  have hsplit : TrigInterp.recon n u = TrigInterp.reconLow n K u +
      fun ξ => TrigInterp.recon n u ξ - TrigInterp.reconLow n K u ξ := by
    funext ξ; simp only [Pi.add_apply]; abel
  have ht : ContDiff ℝ ∞ (fun ξ => TrigInterp.recon n u ξ - TrigInterp.reconLow n K u ξ) :=
    hz.sub hzl
  have h2 : ‖iteratedFDeriv ℝ i (TrigInterp.recon n u) x‖ ≤
      (60 * ((4 : ℕ) : ℝ) * K) ^ i * A + K ^ i * TrigInterp.tau n K j u := by
    rw [hsplit, iteratedFDeriv_add_apply (hzl.contDiffAt.of_le (by exact_mod_cast le_top))
      (ht.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact TrigInterp.norm_iteratedFDeriv_reconLow_le n hK0.le u hA i x
    · exact TrigInterp.norm_iteratedFDeriv_tail_le n hK0 u hij x
  have e4 : (60 * ((4 : ℕ) : ℝ) * K) = 240 * K := by norm_num
  rw [e4] at h2
  have hKi : K ^ i ≤ (240 * K) ^ i := pow_le_pow_left₀ hK0.le (by linarith) i
  have hp : A + τ ≤ (A + τ + 1) ^ i := by
    calc A + τ ≤ A + τ + 1 := by linarith
      _ = (A + τ + 1) ^ 1 := (pow_one _).symm
      _ ≤ (A + τ + 1) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc ‖iteratedFDeriv ℝ i (fun ξ => L (TrigInterp.recon n u ξ)) x‖
      ≤ (240 * K) ^ i * A + K ^ i * TrigInterp.tau n K j u := h1.trans h2
    _ ≤ (240 * K) ^ i * A + (240 * K) ^ i * τ :=
        add_le_add le_rfl (mul_le_mul hKi hτ (TrigInterp.tau_nonneg n hK0 j u) (by positivity))
    _ = (240 * K) ^ i * (A + τ) := by ring
    _ ≤ (240 * K) ^ i * (A + τ + 1) ^ i := by gcongr
    _ = (240 * (A + τ + 1) * K) ^ i := by rw [← mul_pow]; ring

end Recon

/-! ### Monotonicity of the forcing budget -/

section Budget

open NativeRate

variable {Ck σ h K τ₂ : ℝ}

theorem one_le_logFactor (k : ℕ) (hCk : 0 ≤ Ck) (hK : 0 ≤ K) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ logFactor k Ck K e := by
  unfold logFactor
  have : 0 ≤ Ck * K ^ (k + 5) / e := by positivity
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Ck * K ^ (k + 5) / e by linarith)
  linarith

theorem logFactor_mono {k' k : ℕ} (hkk : k' ≤ k) (hCk : 0 ≤ Ck) (hK : 1 ≤ K) {e : ℝ}
    (he : 0 ≤ e) : logFactor k' Ck K e ≤ logFactor k Ck K e := by
  unfold logFactor
  have hp : K ^ (k' + 5) ≤ K ^ (k + 5) := pow_le_pow_right₀ hK (by omega)
  have h1 : Ck * K ^ (k' + 5) / e ≤ Ck * K ^ (k + 5) / e := by
    gcongr
  have h0 : 0 ≤ Ck * K ^ (k' + 5) / e := by
    have : (0 : ℝ) ≤ K := by linarith
    positivity
  have := Real.log_le_log (by linarith) (show 2 + Ck * K ^ (k' + 5) / e ≤
    2 + Ck * K ^ (k + 5) / e by linarith)
  linarith

theorem epsc_nonneg (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hK : 0 ≤ K) (hτ₂ : 0 ≤ τ₂) :
    0 ≤ epsc σ h K τ₂ := by
  unfold epsc eps0; positivity

/-- **`K^l F_{h,k'} ≤ F_{h,k}`** for `k' + l = k` and `τ' ≤ τ_m`. -/
theorem pow_mul_forcingBudget_le {k' l k : ℕ} (hk : k' + l = k) (hCk : 0 ≤ Ck) (hσ : 0 ≤ σ)
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hτ₂ : 0 ≤ τ₂) {τ' τm : ℝ} (hττ : τ' ≤ τm) :
    K ^ l * forcingBudget k' Ck σ h K τ₂ τ' ≤ forcingBudget k Ck σ h K τ₂ τm := by
  have hK0 : 0 ≤ K := by linarith
  have he := epsc_nonneg hσ hh hK0 hτ₂
  set e := epsc σ h K τ₂
  have hL1 := one_le_logFactor k' hCk hK0 he
  have hLm := logFactor_mono (show k' ≤ k by omega) hCk hK he
  have hLp : logFactor k' Ck K e ^ (k' + 1) ≤ logFactor k Ck K e ^ (k + 1) :=
    calc logFactor k' Ck K e ^ (k' + 1) ≤ logFactor k Ck K e ^ (k' + 1) :=
          pow_le_pow_left₀ (by linarith) hLm _
      _ ≤ logFactor k Ck K e ^ (k + 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
  unfold forcingBudget
  have e1 : K ^ l * (e * K ^ (k' + 1) * logFactor k' Ck K e ^ (k' + 1) + K ^ (k' + 2) * τ') =
      e * K ^ (k + 1) * logFactor k' Ck K e ^ (k' + 1) + K ^ (k + 2) * τ' := by
    rw [← hk]; ring
  rw [e1]
  have hKp : 0 ≤ K ^ (k + 1) := by positivity
  have hKq : 0 ≤ K ^ (k + 2) := by positivity
  gcongr

/-- **`K^l ε_{0,h} ≤ F_{h,k}`** for `l ≤ k + 1`. -/
theorem pow_mul_eps0_le {l k : ℕ} (hl : l ≤ k + 1) (hCk : 0 ≤ Ck) (hσ : 0 ≤ σ) (hh : 0 ≤ h)
    (hK : 1 ≤ K) (hτ₂ : 0 ≤ τ₂) {τm : ℝ} (hτm : 0 ≤ τm) :
    K ^ l * eps0 σ h K ≤ forcingBudget k Ck σ h K τ₂ τm := by
  have hK0 : 0 ≤ K := by linarith
  have he := epsc_nonneg hσ hh hK0 hτ₂
  have h0 : 0 ≤ eps0 σ h K := by unfold eps0; positivity
  have hle : eps0 σ h K ≤ epsc σ h K τ₂ := by unfold epsc; nlinarith [sq_nonneg K]
  have hL1 := one_le_logFactor k hCk hK0 he
  have hLp : 1 ≤ logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) := one_le_pow₀ hL1
  have hKl : K ^ l ≤ K ^ (k + 1) := pow_le_pow_right₀ hK hl
  unfold forcingBudget
  have hKq : 0 ≤ K ^ (k + 2) * τm := by positivity
  calc K ^ l * eps0 σ h K ≤ K ^ (k + 1) * epsc σ h K τ₂ := by gcongr
    _ = epsc σ h K τ₂ * K ^ (k + 1) * 1 := by ring
    _ ≤ epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) := by
        gcongr
    _ ≤ _ := le_add_of_nonneg_right hKq

theorem forcingBudget_nonneg (k : ℕ) (hCk : 0 ≤ Ck) (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hK : 1 ≤ K)
    (hτ₂ : 0 ≤ τ₂) {τm : ℝ} (hτm : 0 ≤ τm) : 0 ≤ forcingBudget k Ck σ h K τ₂ τm := by
  have h0 : 0 ≤ eps0 σ h K := by
    have : (0 : ℝ) ≤ K := by linarith
    unfold eps0; positivity
  have := pow_mul_eps0_le (l := 0) (k := k) (by omega) hCk hσ hh hK hτ₂ hτm
  rw [pow_zero, one_mul] at this
  linarith

end Budget

end

end RenewalGeometry.SourceCompare
