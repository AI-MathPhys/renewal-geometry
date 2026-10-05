/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.SameRecordSourceSelectionExact
import RenewalGeometry.Analysis.DyadicRateAsymptotics

/-!
# Same-source selected finite-action closure (`thm:native-selected-closure`)

Einstein–Standard-Model action-closure manuscript, `thm:native-selected-closure`
(`eq:selected-reader-general`, `eq:selected-composed-budget`, `eq:selected-closure`) and its
Borel–Cantelli clause.

## Main results

* `reader_tail_le` — `eq:selected-reader-general` on the selected record: `τ ≤ t + c√V` and
  `V ≤ R²` give `τ ≤ T = t + cR`.
* `mul_one_add_log_pow_le` (generic) — quasi-monotonicity of `x ↦ x(1 + log(2 + A/x))^p`:
  for `0 < x ≤ y`, `x(1 + log(2 + A/x))^p ≤ e·p!·y(1 + log(2 + A/y))^p`.
* **`forcingBudget_le_of_le`** — the forcing budget of `eq:native-forcing-budget` with the actual
  tails is at most `e (k+1)!` times the composed budget `F̄_{h,k}` of
  `eq:selected-composed-budget` built from the upper bounds `T_{h,2}`, `T_{h,k+2}`
  (`ε̄_{c,h} = s_h + hK³ + K²T_{h,2}`, `L̄_{h,k}`, `F̄_{h,k}`): this is the step "apply
  `thm:native-source` with these upper budgets" (the logarithmic factor decreases in `ε`, so plain
  monotonicity fails; the factor `e (k+1)!` is uniform).
* `selected_closure_composition` — the composition of the selected budgets with the conclusion of
  `prop:coupled-bootstrap` (the open input of `thm:native-closure`, as in
  `NativeClosure.native_closure_composition`), uniformly over the successful records: if
  `D̄_h = α_h + F̄_h → 0`, then eventually every successful record satisfies
  `(state + curvature + stress difference) ≤ C D̄_h` (`eq:selected-closure`).
* **`native_selected_closure`** — one cutoff: the selection failure bound
  `eq:source-selection-failure` (`selection_failure_le`, `thm:source-selection`) together with the
  deterministic closure bound on every successful outcome once `D̄_h` is below the bootstrap radius.
* **`selected_borel_cantelli`** — the Borel–Cantelli clause: under any common coupling (a measure
  `μ` whose `n`-th failure event has probability at most the summable bound `p_n`), almost surely
  the
  selected record eventually succeeds, and if the successful records are within `C D̄_n` of the
  common reference with `Σ D̄_n < ∞`, the adjacent differences are summable
  (`MeasureTheory.ae_eventually_notMem`, the first Borel–Cantelli lemma).  No independence between
  cutoffs is used.

The deterministic closure inherits `thm:native-closure`, whose only open input is
`prop:coupled-bootstrap`; its stated conclusion is a hypothesis here (strict corollary policy: the
record stays conditional).
-/

open Filter Topology MeasureTheory Finset
open scoped Nat ENNReal

namespace RenewalGeometry.SelectedClosure

open NativeRate SourceSelection

noncomputable section

/-! ### The reader certificate on the selected record -/

/-- `eq:selected-reader-general` on a selected record with `V ≤ R²`:
`τ ≤ t + c√V ≤ t + cR = T_{h,j}`. -/
theorem reader_tail_le {τ t c V R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) (hτ : τ ≤ t + c * Real.sqrt V)
    (hV : V ≤ R ^ 2) : τ ≤ t + c * R := by
  have : Real.sqrt V ≤ R := by
    calc Real.sqrt V ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hV
      _ = R := Real.sqrt_sq hR
  nlinarith

/-! ### Quasi-monotonicity of the forcing budget -/

/-- **Quasi-monotonicity of `x(1 + log(2 + A/x))^p`** (generic): for `0 < x ≤ y` and `A ≥ 0`,
`x(1 + log(2 + A/x))^p ≤ e·p!·y(1 + log(2 + A/y))^p`.  Proof: with `u = log(y/x) ≥ 0`,
`log(2 + A/x) ≤ log(2 + A/y) + u`, so `1 + log(2 + A/x) ≤ L_y(1 + u)` (`L_y ≥ 1`), and
`(1+u)^p ≤ p! e^{1+u} = e·p!·y/x`. -/
theorem mul_one_add_log_pow_le {x y A : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hA : 0 ≤ A) (p : ℕ) :
    x * (1 + Real.log (2 + A / x)) ^ p ≤
      Real.exp 1 * p ! * (y * (1 + Real.log (2 + A / y)) ^ p) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  set u := Real.log (y / x) with hu
  have hyx : 1 ≤ y / x := by rw [le_div_iff₀ hx]; linarith
  have hu0 : 0 ≤ u := Real.log_nonneg hyx
  have hAy : 0 ≤ A / y := div_nonneg hA hy.le
  have hAx : 0 ≤ A / x := div_nonneg hA hx.le
  set Ly := 1 + Real.log (2 + A / y) with hLy
  have hLy1 : 1 ≤ Ly := by
    have : 0 ≤ Real.log (2 + A / y) := Real.log_nonneg (by linarith)
    linarith
  -- step 1: `log(2 + A/x) ≤ log(2 + A/y) + u`
  have hstep1 : Real.log (2 + A / x) ≤ Real.log (2 + A / y) + u := by
    rw [hu, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have e : (2 + A / y) * (y / x) = 2 * (y / x) + A / x := by field_simp
    rw [e]; nlinarith
  -- step 2: `L_x ≤ L_y (1 + u)`
  have hLx0 : 0 ≤ 1 + Real.log (2 + A / x) := by
    have : 0 ≤ Real.log (2 + A / x) := Real.log_nonneg (by linarith)
    linarith
  have hstep2 : 1 + Real.log (2 + A / x) ≤ Ly * (1 + u) := by nlinarith
  -- step 3: powers
  have hstep3 : (1 + Real.log (2 + A / x)) ^ p ≤ Ly ^ p * (1 + u) ^ p := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hLx0 hstep2 p
  -- step 4: `(1 + u)^p ≤ p! e^{1+u} = e p! (y/x)`
  have hstep4 : (1 + u) ^ p ≤ p ! * (Real.exp 1 * (y / x)) := by
    have h := Real.pow_div_factorial_le_exp (1 + u) (by linarith) p
    have hf : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
    rw [div_le_iff₀ hf] at h
    rw [Real.exp_add, hu, Real.exp_log (by positivity)] at h
    linarith
  have hLyp : 0 ≤ Ly ^ p := pow_nonneg (by linarith) p
  calc x * (1 + Real.log (2 + A / x)) ^ p ≤ x * (Ly ^ p * (1 + u) ^ p) :=
        mul_le_mul_of_nonneg_left hstep3 hx.le
    _ ≤ x * (Ly ^ p * (p ! * (Real.exp 1 * (y / x)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep4 hLyp) hx.le
    _ = Real.exp 1 * p ! * (y * Ly ^ p) := by field_simp

/-- **Forcing budget with upper tail budgets** (`eq:selected-composed-budget`): for `σ ≥ 0`,
`h > 0`, `K > 0`, `C_k ≥ 0`, `0 ≤ τ₂ ≤ T₂`, `0 ≤ τ_m ≤ T_m`,
`F_{h,k}(σ, τ₂, τ_m) ≤ e (k+1)! F̄_{h,k}` with `F̄_{h,k} = F_{h,k}(σ, T₂, T_m)` built from
`ε̄_{c,h} = σ + hK³ + K²T₂`, `L̄_{h,k} = 1 + log(2 + C_kK^{k+5}/ε̄_{c,h})`. -/
theorem forcingBudget_le_of_le (k : ℕ) {Ck σ h K τ₂ τm T₂ Tm : ℝ} (hCk : 0 ≤ Ck) (hσ : 0 ≤ σ)
    (hh : 0 < h) (hK : 0 < K) (hτ₂ : 0 ≤ τ₂) (hτ₂T : τ₂ ≤ T₂) (hτm : 0 ≤ τm) (hτmT : τm ≤ Tm) :
    forcingBudget k Ck σ h K τ₂ τm ≤
      Real.exp 1 * (k + 1)! * forcingBudget k Ck σ h K T₂ Tm := by
  have hx : 0 < epsc σ h K τ₂ := lt_of_lt_of_le (by positivity) (le_epsc (h := h) (K := K) hσ hτ₂)
  have hxy : epsc σ h K τ₂ ≤ epsc σ h K T₂ := by
    unfold epsc; nlinarith [sq_nonneg K]
  have hA : 0 ≤ Ck * K ^ (k + 5) := by positivity
  have hmain := mul_one_add_log_pow_le hx hxy hA (k + 1)
  have hE : 1 ≤ Real.exp 1 * ((k + 1)! : ℝ) := by
    have h1 : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h2 : (1 : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.factorial_pos (k + 1)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hKp : 0 ≤ K ^ (k + 1) := by positivity
  have hKq : 0 ≤ K ^ (k + 2) := by positivity
  have hTm : 0 ≤ Tm := hτm.trans hτmT
  unfold forcingBudget logFactor
  have e1 : epsc σ h K τ₂ * K ^ (k + 1) * (1 + Real.log (2 + Ck * K ^ (k + 5) / epsc σ h K τ₂))
      ^ (k + 1) = K ^ (k + 1) * (epsc σ h K τ₂ *
        (1 + Real.log (2 + Ck * K ^ (k + 5) / epsc σ h K τ₂)) ^ (k + 1)) := by ring
  have e2 : epsc σ h K T₂ * K ^ (k + 1) * (1 + Real.log (2 + Ck * K ^ (k + 5) / epsc σ h K T₂))
      ^ (k + 1) = K ^ (k + 1) * (epsc σ h K T₂ *
        (1 + Real.log (2 + Ck * K ^ (k + 5) / epsc σ h K T₂)) ^ (k + 1)) := by ring
  rw [e1, e2]
  have t1 := mul_le_mul_of_nonneg_left hmain hKp
  have t2 : K ^ (k + 2) * τm ≤ K ^ (k + 2) * Tm := mul_le_mul_of_nonneg_left hτmT hKq
  have t3 : K ^ (k + 2) * Tm ≤ Real.exp 1 * ((k + 1)! : ℝ) * (K ^ (k + 2) * Tm) :=
    le_mul_of_one_le_left (mul_nonneg hKq hTm) hE
  nlinarith

/-! ### The deterministic composition on successful records -/

/-- **Composition of the selected budgets with the conclusion of `prop:coupled-bootstrap`**
(proof of `thm:native-selected-closure`; the uniform-in-records form of
`NativeClosure.native_closure_composition`).  Along any filter of cutoffs `h`, with records
`x : 𝒳 h` and a success predicate: if every successful record has alignment
`i_{h,k} + γ_{h,k} ≤ α_h` and strong source `𝒴_k ≤ C₁ F̄_h`, the bootstrap gives
`S ≤ C_*(i + γ + 𝒴)` whenever `i + γ + 𝒴 ≤ d_*`, and `D̄_h = α_h + F̄_h → 0` (nonnegative), then
eventually every successful record satisfies `S ≤ C_* max(1, C₁) D̄_h` (`eq:selected-closure`). -/
theorem selected_closure_composition {ι : Type*} {l : Filter ι} {𝒳 : ι → Type*}
    (al Y S : ∀ h, 𝒳 h → ℝ) (Succ : ∀ h, 𝒳 h → Prop) (α F : ι → ℝ) {C₁ Cst dst : ℝ}
    (hdst : 0 < dst) (hCst : 0 ≤ Cst) (hα : ∀ h, 0 ≤ α h)
    (hF : ∀ h, 0 ≤ F h) (hD : Tendsto (fun h => α h + F h) l (𝓝 0))
    (hsα : ∀ h x, Succ h x → al h x ≤ α h) (hsY : ∀ h x, Succ h x → Y h x ≤ C₁ * F h)
    (hboot : ∀ h x, al h x + Y h x ≤ dst → S h x ≤ Cst * (al h x + Y h x)) :
    ∀ᶠ h in l, ∀ x, Succ h x → S h x ≤ Cst * max 1 C₁ * (α h + F h) := by
  set K := max 1 C₁ with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hev : ∀ᶠ h in l, α h + F h < dst / K := hD.eventually (gt_mem_nhds (div_pos hdst hK0))
  filter_upwards [hev] with h hh x hx
  have hdY : al h x + Y h x ≤ K * (α h + F h) := by
    have h1 : C₁ * F h ≤ K * F h := mul_le_mul_of_nonneg_right (le_max_right _ _) (hF h)
    have h2 : α h ≤ K * α h := le_mul_of_one_le_left (hα h) hK1
    nlinarith [hsα h x hx, hsY h x hx]
  have hsmall : al h x + Y h x ≤ dst := by
    calc al h x + Y h x ≤ K * (α h + F h) := hdY
      _ ≤ K * (dst / K) := mul_le_mul_of_nonneg_left hh.le hK0.le
      _ = dst := by field_simp
  calc S h x ≤ Cst * (al h x + Y h x) := hboot h x hsmall
    _ ≤ Cst * (K * (α h + F h)) := mul_le_mul_of_nonneg_left hdY hCst
    _ = Cst * K * (α h + F h) := by ring

variable {Ω 𝒳 : Type*} [Fintype Ω] [Fintype 𝒳] [DecidableEq 𝒳] [DecidableEq Ω]

/-- **`thm:native-selected-closure` at one cutoff** (conditional on the conclusion of the open
`prop:coupled-bootstrap`, the remaining input of `thm:native-closure`, carried as `hboot`).

Selection data: the signed-drift hypotheses of `thm:source-selection` on the finite accepted
process, a selector minimising `g²/s² + V/R² + W/α²` with `W = (i_{h,k} + γ_{h,k})²`.  Deterministic
data on every legal record `x` (legality includes the common slab, temporal gauge and the buffered
chart conditions of `thm:native-source`): the reader certificate `τ_j ≤ t_j + c_j√V`
(`eq:selected-reader-general`, `j = 2, k+2`), the output of `thm:native-source` with any row bound
`σ ≥ g` (`hsrc`: `𝒴_k ≤ C₁ F_{h,k}(σ, τ₂, τ_m)`), and the bootstrap.  If
`D̄_h = α + e(k+1)! F̄_{h,k}`-small (`hsmall`), then (1) the failure probability is at most
`eq:source-selection-failure`, and (2) on every successful outcome the selected record satisfies
`S ≤ C_* max(1, C₁)(α + e(k+1)! F̄_{h,k})` (`eq:selected-closure`). -/
theorem native_selected_closure (proc : FiniteAcceptedProcess Ω 𝒳)
    (a g V W : 𝒳 → ℝ) (rr : ℕ → 𝒳 → ℝ) {Am Ap κ δ sh Rr α : ℝ}
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (hκ : 0 < κ) (hδ : 0 < δ) (hsh : 0 < sh) (hRr : 0 < Rr)
    (hα : 0 < α) (hg : ∀ x, 0 ≤ g x) (hV : ∀ x, 0 ≤ V x) (J : ℕ) (hJ : 0 < J)
    (hdrift : ∀ j < J, ∀ x, 0 < proc.survivingMass j x →
      proc.actionDrift a j x ≤ -(κ * δ) * g x ^ 2 + δ * rr j x)
    (sel : Ω → ℕ)
    (hsel : ∀ ω ∈ proc.S J, sel ω < J ∧ ∀ j < J,
      FiniteAcceptedProcess.score g V (fun x => W x) sh Rr α (proc.X (sel ω) ω) ≤
        FiniteAcceptedProcess.score g V (fun x => W x) sh Rr α (proc.X j ω))
    -- the alignment readout `i_{h,k} + γ_{h,k}` and `W = (i + γ)²`
    (al : 𝒳 → ℝ) (hal : ∀ x, 0 ≤ al x) (hW : ∀ x, W x = al x ^ 2)
    -- reader certificate
    (k : ℕ) {h K Ck t₂ c₂ tm cm C₁ Cst dst : ℝ} (τ₂ τm : 𝒳 → ℝ)
    (hτ₂0 : ∀ x, 0 ≤ τ₂ x) (hτm0 : ∀ x, 0 ≤ τm x) (hc₂ : 0 ≤ c₂) (hcm : 0 ≤ cm)
    (hr₂ : ∀ x, τ₂ x ≤ t₂ + c₂ * Real.sqrt (V x)) (hrm : ∀ x, τm x ≤ tm + cm * Real.sqrt (V x))
    -- the output of `thm:native-source` with the row bound `s_h`
    (Ysrc : 𝒳 → ℝ) (hCk : 0 ≤ Ck) (hh : 0 < h) (hK : 0 < K) (hC₁ : 0 ≤ C₁)
    (hsrc : ∀ x, g x ≤ sh → Ysrc x ≤ C₁ * forcingBudget k Ck sh h K (τ₂ x) (τm x))
    -- the conclusion of `prop:coupled-bootstrap`
    (Sx : 𝒳 → ℝ) (hCst : 0 ≤ Cst)
    (hboot : ∀ x, al x + Ysrc x ≤ dst → Sx x ≤ Cst * (al x + Ysrc x))
    (hsmall : α + C₁ * (Real.exp 1 * (k + 1)! *
      forcingBudget k Ck sh h K (t₂ + c₂ * Rr) (tm + cm * Rr)) ≤ dst) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J ∨
        ¬ (g (proc.X (sel ω) ω) ≤ sh ∧ V (proc.X (sel ω) ω) ≤ Rr ^ 2 ∧
          W (proc.X (sel ω) ω) ≤ α ^ 2)), proc.P ω
      ≤ proc.exitProbability J + (Ap - Am) / (κ * δ * J * sh ^ 2)
        + proc.occupation J rr / (κ * sh ^ 2)
        + proc.occupation J (fun _ x => V x) / Rr ^ 2
        + proc.occupation J (fun _ x => W x) / α ^ 2) ∧
    ∀ ω ∈ proc.S J, g (proc.X (sel ω) ω) ≤ sh → V (proc.X (sel ω) ω) ≤ Rr ^ 2 →
      W (proc.X (sel ω) ω) ≤ α ^ 2 →
      Sx (proc.X (sel ω) ω) ≤ Cst * (α + C₁ * (Real.exp 1 * (k + 1)! *
        forcingBudget k Ck sh h K (t₂ + c₂ * Rr) (tm + cm * Rr))) := by
  have hW0 : ∀ x, 0 ≤ W x := fun x => by rw [hW]; positivity
  refine ⟨proc.selection_failure_le a g V W rr Am Ap κ δ sh Rr α ha hκ hδ hsh hRr hα hg hV hW0
    J hJ hdrift sel hsel, ?_⟩
  intro ω _ hgx hVx hWx
  set x := proc.X (sel ω) ω
  have halx : al x ≤ α := by
    rw [hW] at hWx; exact (pow_le_pow_iff_left₀ (hal x) hα.le (by norm_num)).mp hWx
  have hT₂ := reader_tail_le hc₂ hRr.le (hr₂ x) hVx
  have hTm := reader_tail_le hcm hRr.le (hrm x) hVx
  have hF := forcingBudget_le_of_le k hCk hsh.le hh hK (hτ₂0 x) hT₂ (hτm0 x) hTm
  have hY : Ysrc x ≤ C₁ * (Real.exp 1 * (k + 1)! *
      forcingBudget k Ck sh h K (t₂ + c₂ * Rr) (tm + cm * Rr)) :=
    (hsrc x hgx).trans (mul_le_mul_of_nonneg_left hF hC₁)
  have hd : al x + Ysrc x ≤ α + C₁ * (Real.exp 1 * (k + 1)! *
      forcingBudget k Ck sh h K (t₂ + c₂ * Rr) (tm + cm * Rr)) := add_le_add halx hY
  exact (hboot x (hd.trans hsmall)).trans (mul_le_mul_of_nonneg_left hd hCst)

/-! ### The Borel–Cantelli clause -/

/-- **Borel–Cantelli clause of `thm:native-selected-closure`** (generic).  Let `μ` be any common
coupling of the selection stages along a cofinal chain, `Fail n` the failure event at stage `n` with
`μ(Fail n) ≤ p_n`, `Σ p_n < ∞`.  Then almost surely the selected record eventually succeeds.  If
moreover every successful stage-`n` record has comparison observable within `C D̄_n` of the common
reference `x₀` and `Σ D̄_n < ∞`, then almost surely the adjacent differences are summable. -/
theorem selected_borel_cantelli {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {E : Type*} [PseudoMetricSpace E] (Fail : ℕ → Set Ω') (p : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (hμ : ∀ n, μ (Fail n) ≤ ENNReal.ofReal (p n))
    (x : ℕ → Ω' → E) (x₀ : E) (D : ℕ → ℝ) (hD : Summable D) (C : ℝ)
    (hsucc : ∀ n ω, ω ∉ Fail n → dist (x n ω) x₀ ≤ C * D n) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, ω ∉ Fail n) ∧
      Summable (fun n => dist (x (n + 1) ω) (x n ω)) := by
  have hsum : (∑' n, μ (Fail n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμ)
    rw [← ENNReal.ofReal_tsum_of_nonneg hp0 hp]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  refine ⟨hω, ?_⟩
  have hg : Summable (fun n => C * D (n + 1) + C * D n) :=
    (((summable_nat_add_iff 1).mpr hD).mul_left C).add (hD.mul_left C)
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hω1 : ∀ᶠ n in atTop, ω ∉ Fail (n + 1) := (tendsto_add_atTop_nat 1).eventually hω
  filter_upwards [hω, hω1] with n hn hn1
  rw [Real.norm_of_nonneg dist_nonneg]
  calc dist (x (n + 1) ω) (x n ω) ≤ dist (x (n + 1) ω) x₀ + dist (x n ω) x₀ :=
        dist_triangle_right _ _ _
    _ ≤ C * D (n + 1) + C * D n := add_le_add (hsucc _ _ hn1) (hsucc _ _ hn)

end

end RenewalGeometry.SelectedClosure
