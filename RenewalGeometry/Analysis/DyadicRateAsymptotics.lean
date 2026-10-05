/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Forcing-budget asymptotics and dyadic summability (`cor:native-rate`, self-contained part)

Real-analysis content of `cor:native-rate` of the Einstein–Standard-Model action-closure
manuscript: the forcing budget of `eq:native-forcing-budget`,

* `ε_{0,h} = σ_h + h K³`, `ε_{c,h} = ε_{0,h} + K² τ_{h,2}`,
* `L_{h,k} = 1 + log(2 + C_k K^{k+5}/ε_{c,h})`,
* `F_{h,k} = ε_{c,h} K^{k+1} L_{h,k}^{k+1} + K^{k+2} τ_{h,k+2}`

(`eps0`, `epsc`, `logFactor`, `forcingBudget`), under the rate hypotheses `σ_h = O(h)`,
`1 ≤ K_h ≲ h^{-β}`, `τ_{h,2} = O(hK)`, `τ_{h,k+2} = O(hK²)` (`eq:native-tail-rate`).

* `epsc_le`, `le_epsc`: `h K³ ≤ ε_{c,h} ≤ C h K³` ("the hypotheses give `ε_{c,h} = O(hK³)`").
* `logFactor_le`: `L_{h,k} ≤ C_L (1 + |log h|)` ("`L_{h,k} = O(1 + |log h|)`").
* `forcingBudget_le`, **`forcingBudget_isBigO`**:
  `F_{h,k} = O(h^{1-β(k+4)} (1 + |log h|)^{k+1})`.
* `eps0_le`, **`eps0_isBigO`**: `ε_{0,h} = O(h^{1-3β})`; `physical_isBigO_of_le` transfers it to
  `ε^phys` under the zero-order estimate `ε^phys ≤ C ε_{0,h}` of `thm:native-source`.
* `tendsto_rpow_mul_one_add_abs_log_pow`: `h^ρ (1+|log h|)^p → 0` as `h → 0⁺` for `ρ > 0`, so
  `F_{h,k} → 0` for `β < 1/(k+4)` (`forcingBudget_tendsto_zero`).
* **`summable_dyadic`**: along a dyadic sequence `h_n = h₀ 2^{-n}`,
  `Σ_n h_n^ρ (1 + |log h_n|)^p < ∞` for `ρ > 0`; `summable_adjacent_of_le` gives the summability
  of adjacent differences `‖x_{n+1} - x_n‖` from bounds `‖x_n - x_*‖ ≤ a_n` with `Σ a_n < ∞`
  (comparison of adjacent records through the same reference).
* `native_rate_example_exponents`: for `k = 4`, `β = 1/18`: `1 - β(k+4) = 5/9`, `1 - 3β = 5/6`,
  `β < 1/(k+4)`.

The remaining assertion of `cor:native-rate` (state, curvature and stress convergence) inherits
`thm:native-closure` and is not proved here.
-/

open Filter Topology Asymptotics
open scoped Real

namespace RenewalGeometry.NativeRate

noncomputable section

/-! ### The forcing budget `eq:native-forcing-budget` -/

/-- `ε_{0,h} = σ_h + h K³`. -/
def eps0 (σ h K : ℝ) : ℝ := σ + h * K ^ 3

/-- `ε_{c,h} = ε_{0,h} + K² τ_{h,2}`. -/
def epsc (σ h K τ₂ : ℝ) : ℝ := eps0 σ h K + K ^ 2 * τ₂

/-- `L_{h,k} = 1 + log(2 + C_k K^{k+5}/ε_{c,h})`. -/
def logFactor (k : ℕ) (Ck K e : ℝ) : ℝ := 1 + Real.log (2 + Ck * K ^ (k + 5) / e)

/-- `F_{h,k} = ε_{c,h} K^{k+1} L_{h,k}^{k+1} + K^{k+2} τ_{h,k+2}`. -/
def forcingBudget (k : ℕ) (Ck σ h K τ₂ τm : ℝ) : ℝ :=
  epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) + K ^ (k + 2) * τm

/-! ### Pointwise bounds -/

section Pointwise

variable {σ h K τ₂ τm Cσ Cτ : ℝ}

/-- `h K³ ≤ ε_{c,h}` (nonnegative row norm and tail). -/
theorem le_epsc (hσ0 : 0 ≤ σ) (hτ0 : 0 ≤ τ₂) : h * K ^ 3 ≤ epsc σ h K τ₂ := by
  unfold epsc eps0
  have : 0 ≤ K ^ 2 * τ₂ := mul_nonneg (sq_nonneg K) hτ0
  linarith

/-- **`ε_{c,h} = O(hK³)`**: `ε_{c,h} ≤ (C_σ + 1 + C_τ) h K³`. -/
theorem epsc_le (hh : 0 ≤ h) (hK : 1 ≤ K) (hσ : σ ≤ Cσ * h) (hτ : τ₂ ≤ Cτ * (h * K))
    (hCσ : 0 ≤ Cσ) : epsc σ h K τ₂ ≤ (Cσ + 1 + Cτ) * (h * K ^ 3) := by
  unfold epsc eps0
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have h1 : Cσ * h ≤ Cσ * (h * K ^ 3) := by
    have : h ≤ h * K ^ 3 := le_mul_of_one_le_right hh hK3
    exact mul_le_mul_of_nonneg_left this hCσ
  have h2 : K ^ 2 * τ₂ ≤ Cτ * (h * K ^ 3) := by
    have := mul_le_mul_of_nonneg_left hτ (sq_nonneg K)
    calc K ^ 2 * τ₂ ≤ K ^ 2 * (Cτ * (h * K)) := this
      _ = Cτ * (h * K ^ 3) := by ring
  nlinarith

/-- **`ε_{0,h} = O(h^{1-3β})`** pointwise: `ε_{0,h} ≤ (C_σ + c₂³) h^{1-3β}` for `0 < h ≤ 1`,
`0 ≤ K ≤ c₂ h^{-β}`, `β ≥ 0`. -/
theorem eps0_le {β c₂ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hK0 : 0 ≤ K)
    (hKup : K ≤ c₂ * h ^ (-β)) (hβ : 0 ≤ β) (hσ : σ ≤ Cσ * h) (hCσ : 0 ≤ Cσ) :
    eps0 σ h K ≤ (Cσ + c₂ ^ 3) * h ^ (1 - 3 * β) := by
  unfold eps0
  have hc₂ : 0 ≤ c₂ := by
    have := Real.rpow_pos_of_pos hh0 (-β)
    by_contra hc; push_neg at hc; nlinarith
  have hpow : h ≤ h ^ (1 - 3 * β) := by
    calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
      _ ≤ h ^ (1 - 3 * β) := Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by linarith)
  have hK3 : K ^ 3 ≤ c₂ ^ 3 * h ^ (-(3 * β)) := by
    calc K ^ 3 ≤ (c₂ * h ^ (-β)) ^ 3 := pow_le_pow_left₀ hK0 hKup 3
      _ = c₂ ^ 3 * h ^ (-(3 * β)) := by
        rw [mul_pow, ← Real.rpow_natCast (h ^ (-β)), ← Real.rpow_mul hh0.le]; ring_nf
  have hhK : h * K ^ 3 ≤ c₂ ^ 3 * h ^ (1 - 3 * β) := by
    calc h * K ^ 3 ≤ h * (c₂ ^ 3 * h ^ (-(3 * β))) := mul_le_mul_of_nonneg_left hK3 hh0.le
      _ = c₂ ^ 3 * (h ^ (1 : ℝ) * h ^ (-(3 * β))) := by rw [Real.rpow_one]; ring
      _ = c₂ ^ 3 * h ^ (1 - 3 * β) := by rw [← Real.rpow_add hh0]; ring_nf
  have : Cσ * h ≤ Cσ * h ^ (1 - 3 * β) := mul_le_mul_of_nonneg_left hpow hCσ
  nlinarith

/-- **`L_{h,k} = O(1 + |log h|)`**: for `0 < h ≤ 1`, `1 ≤ K ≤ c₂ h^{-β}`, `C_k ≥ 0` and
`ε ≥ h K³`, `L_{h,k} ≤ C_L (1 + |log h|)` with
`C_L = 1 + log(2 + C_k c₂^{k+2}) + β(k+2) + 1`. -/
theorem logFactor_le (k : ℕ) {Ck e β c₂ : ℝ} (hCk : 0 ≤ Ck) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hKup : K ≤ c₂ * h ^ (-β)) (hβ : 0 ≤ β) (he : h * K ^ 3 ≤ e) :
    logFactor k Ck K e ≤
      (1 + Real.log (2 + Ck * c₂ ^ (k + 2)) + (β * (k + 2) + 1)) * (1 + |Real.log h|) := by
  unfold logFactor
  have hK0 : 0 < K := by linarith
  have hhK : 0 < h * K ^ 3 := by positivity
  have he0 : 0 < e := lt_of_lt_of_le hhK he
  set P : ℝ := β * (k + 2) + 1
  have hP : 1 ≤ P := by have : 0 ≤ β * (k + 2) := by positivity
                        linarith
  have hc₂ : 0 ≤ c₂ := by
    have := Real.rpow_pos_of_pos hh0 (-β)
    by_contra hc; push_neg at hc; nlinarith
  -- `C_k K^{k+5}/e ≤ C_k c₂^{k+2} h^{-P}`
  have hKk : K ^ (k + 2) ≤ c₂ ^ (k + 2) * h ^ (-(β * (k + 2))) := by
    calc K ^ (k + 2) ≤ (c₂ * h ^ (-β)) ^ (k + 2) := pow_le_pow_left₀ hK0.le hKup _
      _ = c₂ ^ (k + 2) * h ^ (-(β * (k + 2))) := by
        rw [mul_pow, ← Real.rpow_natCast (h ^ (-β)), ← Real.rpow_mul hh0.le]
        push_cast; ring_nf
  have hq : Ck * K ^ (k + 5) / e ≤ Ck * c₂ ^ (k + 2) * h ^ (-P) := by
    rw [div_le_iff₀ he0]
    have e1 : K ^ (k + 5) = K ^ (k + 2) * K ^ 3 := by rw [← pow_add]
    have e2 : h ^ (-P) * h = h ^ (-(β * (k + 2))) := by
      rw [← Real.rpow_add_one hh0.ne']; simp only [P]; ring_nf
    calc Ck * K ^ (k + 5) = Ck * K ^ (k + 2) * K ^ 3 := by rw [e1]; ring
      _ ≤ Ck * (c₂ ^ (k + 2) * h ^ (-(β * (k + 2)))) * K ^ 3 := by gcongr
      _ = Ck * c₂ ^ (k + 2) * h ^ (-P) * (h * K ^ 3) := by rw [← e2]; ring
      _ ≤ Ck * c₂ ^ (k + 2) * h ^ (-P) * e := by
          gcongr
  have hhP : 1 ≤ h ^ (-P) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hh1 (by linarith)
  set Q : ℝ := 2 + Ck * c₂ ^ (k + 2)
  have hQ : 2 ≤ Q := by have : 0 ≤ Ck * c₂ ^ (k + 2) := by positivity
                        linarith
  have harg : 2 + Ck * K ^ (k + 5) / e ≤ Q * h ^ (-P) := by
    have : 0 ≤ Ck * c₂ ^ (k + 2) := by positivity
    nlinarith
  have hpos : 0 < 2 + Ck * K ^ (k + 5) / e := by
    have : 0 ≤ Ck * K ^ (k + 5) / e := by positivity
    linarith
  have hlog : Real.log (2 + Ck * K ^ (k + 5) / e) ≤ Real.log Q + P * |Real.log h| := by
    calc Real.log (2 + Ck * K ^ (k + 5) / e) ≤ Real.log (Q * h ^ (-P)) :=
          Real.log_le_log hpos harg
      _ = Real.log Q + (-P) * Real.log h := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow hh0]
      _ = Real.log Q + P * |Real.log h| := by
          rw [abs_of_nonpos (Real.log_nonpos hh0.le hh1)]; ring
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hlh : 0 ≤ |Real.log h| := abs_nonneg _
  nlinarith

/-- **`F_{h,k} = O(h^{1-β(k+4)} (1+|log h|)^{k+1})`**, pointwise form with an explicit constant
depending only on `k, β, c₂, C_k, C_σ, C_τ`. -/
theorem forcingBudget_le (k : ℕ) {Ck β c₂ : ℝ} (hCk : 0 ≤ Ck) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hKup : K ≤ c₂ * h ^ (-β)) (hβ : 0 ≤ β) (hσ0 : 0 ≤ σ) (hσ : σ ≤ Cσ * h)
    (hCσ : 0 ≤ Cσ) (hτ0 : 0 ≤ τ₂) (hτ : τ₂ ≤ Cτ * (h * K)) (hτm : τm ≤ Cτ * (h * K ^ 2)) :
    forcingBudget k Ck σ h K τ₂ τm ≤
      ((Cσ + 1 + Cτ) * (1 + Real.log (2 + Ck * c₂ ^ (k + 2)) + (β * (k + 2) + 1)) ^ (k + 1) +
          Cτ) * c₂ ^ (k + 4) * (h ^ (1 - β * (k + 4)) * (1 + |Real.log h|) ^ (k + 1)) := by
  unfold forcingBudget
  have hK0 : 0 < K := by linarith
  have hCτ : 0 ≤ Cτ := by
    have : 0 < h * K := by positivity
    by_contra hc; push_neg at hc; nlinarith
  have hc₂ : 0 ≤ c₂ := by
    have := Real.rpow_pos_of_pos hh0 (-β)
    by_contra hc; push_neg at hc; nlinarith
  set CL := 1 + Real.log (2 + Ck * c₂ ^ (k + 2)) + (β * (k + 2) + 1)
  set Λ := 1 + |Real.log h|
  have hΛ : 1 ≤ Λ := by have := abs_nonneg (Real.log h); simp only [Λ]; linarith
  have hE := epsc_le hh0.le hK hσ hτ hCσ
  have hE0 : 0 ≤ epsc σ h K τ₂ := (by positivity : (0 : ℝ) ≤ h * K ^ 3).trans (le_epsc hσ0 hτ0)
  have hL := logFactor_le k hCk hh0 hh1 hK hKup hβ (le_epsc hσ0 hτ0)
  have hL0 : 0 ≤ logFactor k Ck K (epsc σ h K τ₂) := by
    unfold logFactor
    have : 0 ≤ Ck * K ^ (k + 5) / epsc σ h K τ₂ := by positivity
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + Ck * K ^ (k + 5) / epsc σ h K τ₂)
    linarith
  -- `h K^{k+4} ≤ c₂^{k+4} h^{1-β(k+4)}`
  have hKk : h * K ^ (k + 4) ≤ c₂ ^ (k + 4) * h ^ (1 - β * (k + 4)) := by
    have h1 : K ^ (k + 4) ≤ c₂ ^ (k + 4) * h ^ (-(β * (k + 4))) := by
      calc K ^ (k + 4) ≤ (c₂ * h ^ (-β)) ^ (k + 4) := pow_le_pow_left₀ hK0.le hKup _
        _ = c₂ ^ (k + 4) * h ^ (-(β * (k + 4))) := by
          rw [mul_pow, ← Real.rpow_natCast (h ^ (-β)), ← Real.rpow_mul hh0.le]
          push_cast; ring_nf
    calc h * K ^ (k + 4) ≤ h * (c₂ ^ (k + 4) * h ^ (-(β * (k + 4)))) :=
          mul_le_mul_of_nonneg_left h1 hh0.le
      _ = c₂ ^ (k + 4) * (h ^ (1 : ℝ) * h ^ (-(β * (k + 4)))) := by rw [Real.rpow_one]; ring
      _ = c₂ ^ (k + 4) * h ^ (1 - β * (k + 4)) := by rw [← Real.rpow_add hh0]; ring_nf
  have hΛk : 1 ≤ Λ ^ (k + 1) := one_le_pow₀ hΛ
  have hCL : 0 ≤ CL := by
    have : 0 ≤ Real.log (2 + Ck * c₂ ^ (k + 2)) := Real.log_nonneg (by
      have : 0 ≤ Ck * c₂ ^ (k + 2) := by positivity
      linarith)
    have : 0 ≤ β * (k + 2) := by positivity
    simp only [CL]; linarith
  have t1 : epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) ≤
      (Cσ + 1 + Cτ) * CL ^ (k + 1) * (h * K ^ (k + 4)) * Λ ^ (k + 1) := by
    calc epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1)
        ≤ ((Cσ + 1 + Cτ) * (h * K ^ 3)) * K ^ (k + 1) * (CL * Λ) ^ (k + 1) := by
          gcongr
      _ = (Cσ + 1 + Cτ) * CL ^ (k + 1) * (h * K ^ (k + 4)) * Λ ^ (k + 1) := by
          rw [mul_pow, show k + 4 = 3 + (k + 1) by ring, pow_add]; ring
  have t2 : K ^ (k + 2) * τm ≤ Cτ * (h * K ^ (k + 4)) * Λ ^ (k + 1) := by
    have : K ^ (k + 2) * τm ≤ Cτ * (h * K ^ (k + 4)) := by
      calc K ^ (k + 2) * τm ≤ K ^ (k + 2) * (Cτ * (h * K ^ 2)) :=
            mul_le_mul_of_nonneg_left hτm (by positivity)
        _ = Cτ * (h * K ^ (k + 4)) := by rw [show k + 4 = (k + 2) + 2 by ring, pow_add]; ring
    have h0 : 0 ≤ Cτ * (h * K ^ (k + 4)) := by positivity
    nlinarith
  have hhK0 : 0 ≤ h * K ^ (k + 4) := by positivity
  calc epsc σ h K τ₂ * K ^ (k + 1) * logFactor k Ck K (epsc σ h K τ₂) ^ (k + 1) + K ^ (k + 2) * τm
      ≤ ((Cσ + 1 + Cτ) * CL ^ (k + 1) + Cτ) * (h * K ^ (k + 4)) * Λ ^ (k + 1) := by
        nlinarith
    _ ≤ ((Cσ + 1 + Cτ) * CL ^ (k + 1) + Cτ) * (c₂ ^ (k + 4) * h ^ (1 - β * (k + 4))) *
          Λ ^ (k + 1) := by
        gcongr
    _ = _ := by ring

end Pointwise

/-! ### Asymptotic forms along a filter -/

section Filter

variable {ι : Type*} {l : Filter ι} {h K σ τ₂ τm : ι → ℝ}

/-- **`F_{h,k} = O(h^{1-β(k+4)} (1+|log h|)^{k+1})`** (`cor:native-rate`, first claim) along any
filter, under `0 < h ≤ 1`, `1 ≤ K ≤ c₂ h^{-β}`, `σ = O(h)`, `τ_{h,2} = O(hK)`,
`τ_{h,k+2} = O(hK²)` (nonnegative row norm and tails), eventually. -/
theorem forcingBudget_isBigO (k : ℕ) {Ck β c₂ Cσ Cτ : ℝ} (hCk : 0 ≤ Ck) (hβ : 0 ≤ β)
    (hCσ : 0 ≤ Cσ)
    (hev : ∀ᶠ i in l, 0 < h i ∧ h i ≤ 1 ∧ 1 ≤ K i ∧ K i ≤ c₂ * h i ^ (-β) ∧ 0 ≤ σ i ∧
      σ i ≤ Cσ * h i ∧ 0 ≤ τ₂ i ∧ τ₂ i ≤ Cτ * (h i * K i) ∧ 0 ≤ τm i ∧
      τm i ≤ Cτ * (h i * K i ^ 2)) :
    (fun i => forcingBudget k Ck (σ i) (h i) (K i) (τ₂ i) (τm i)) =O[l]
      fun i => h i ^ (1 - β * (k + 4)) * (1 + |Real.log (h i)|) ^ (k + 1) := by
  refine IsBigO.of_bound
    (|((Cσ + 1 + Cτ) * (1 + Real.log (2 + Ck * c₂ ^ (k + 2)) + (β * (k + 2) + 1)) ^ (k + 1) +
      Cτ) * c₂ ^ (k + 4)|) ?_
  filter_upwards [hev] with i ⟨h0, h1, hK, hKup, hσ0, hσ, hτ0, hτ, hτm0, hτm⟩
  have hB := forcingBudget_le k hCk h0 h1 hK hKup hβ hσ0 hσ hCσ hτ0 hτ hτm
  have hF0 : 0 ≤ forcingBudget k Ck (σ i) (h i) (K i) (τ₂ i) (τm i) := by
    unfold forcingBudget
    have hKp : 0 ≤ K i := by linarith
    have hE0 : 0 ≤ epsc (σ i) (h i) (K i) (τ₂ i) :=
      (by positivity : (0 : ℝ) ≤ h i * K i ^ 3).trans (le_epsc hσ0 hτ0)
    have hL0 : 0 ≤ logFactor k Ck (K i) (epsc (σ i) (h i) (K i) (τ₂ i)) := by
      unfold logFactor
      have : 0 ≤ Ck * K i ^ (k + 5) / epsc (σ i) (h i) (K i) (τ₂ i) := by positivity
      have := Real.log_nonneg
        (by linarith : (1 : ℝ) ≤ 2 + Ck * K i ^ (k + 5) / epsc (σ i) (h i) (K i) (τ₂ i))
      linarith
    positivity
  have hg0 : 0 ≤ h i ^ (1 - β * (k + 4)) * (1 + |Real.log (h i)|) ^ (k + 1) := by
    have := Real.rpow_nonneg h0.le (1 - β * (k + 4))
    have : 0 ≤ 1 + |Real.log (h i)| := by have := abs_nonneg (Real.log (h i)); linarith
    positivity
  rw [Real.norm_of_nonneg hF0, Real.norm_of_nonneg hg0]
  exact hB.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hg0)

end Filter

/-! ### The zero-order budget, vanishing of the forcing, and dyadic summability -/

section Filter2

variable {ι : Type*} {l : Filter ι} {h K σ τ₂ τm : ι → ℝ}

/-- **`ε_{0,h} = O(h^{1-3β})`** along any filter. -/
theorem eps0_isBigO {β c₂ Cσ : ℝ} (hβ : 0 ≤ β) (hCσ : 0 ≤ Cσ)
    (hev : ∀ᶠ i in l, 0 < h i ∧ h i ≤ 1 ∧ 0 ≤ K i ∧ K i ≤ c₂ * h i ^ (-β) ∧ 0 ≤ σ i ∧
      σ i ≤ Cσ * h i) :
    (fun i => eps0 (σ i) (h i) (K i)) =O[l] fun i => h i ^ (1 - 3 * β) := by
  refine IsBigO.of_bound (Cσ + c₂ ^ 3) ?_
  filter_upwards [hev] with i ⟨h0, h1, hK0, hKup, hσ0, hσ⟩
  have hB := eps0_le h0 h1 hK0 hKup hβ hσ hCσ
  have hE0 : 0 ≤ eps0 (σ i) (h i) (K i) := by unfold eps0; positivity
  have hg0 : 0 ≤ h i ^ (1 - 3 * β) := Real.rpow_nonneg h0.le _
  rw [Real.norm_of_nonneg hE0, Real.norm_of_nonneg hg0]
  exact hB

/-- Transfer to the physical residual: if `ε^phys ≤ C ε_{0,h}` (the zero-order estimate
`eq:native-zero-source` of `thm:native-source`, taken as a hypothesis) then
`ε^phys = O(h^{1-3β})`. -/
theorem physical_isBigO_of_le {E : ι → ℝ} {C β : ℝ}
    (hE : ∀ᶠ i in l, ‖E i‖ ≤ C * eps0 (σ i) (h i) (K i))
    (h0 : (fun i => eps0 (σ i) (h i) (K i)) =O[l] fun i => h i ^ (1 - 3 * β)) :
    E =O[l] fun i => h i ^ (1 - 3 * β) := by
  refine (IsBigO.of_bound |C| ?_).trans h0
  filter_upwards [hE] with i hi
  rw [Real.norm_eq_abs (eps0 (σ i) (h i) (K i))]
  exact hi.trans ((le_abs_self _).trans_eq (abs_mul _ _))

/-- `h^ρ (1 + |log h|)^p → 0` as `h → 0⁺`, for `ρ > 0`. -/
theorem tendsto_rpow_mul_one_add_abs_log_pow {ρ : ℝ} (hρ : 0 < ρ) (p : ℕ) :
    Tendsto (fun x : ℝ => x ^ ρ * (1 + |Real.log x|) ^ p) (𝓝[>] 0) (𝓝 0) := by
  have ho := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (p : ℝ) (neg_lt_zero.mpr hρ)
  have ht := ho.tendsto_div_nhds_zero
  have ht' : Tendsto (fun x : ℝ => 2 ^ p * (|Real.log x| ^ (p : ℝ) / x ^ (-ρ))) (𝓝[>] 0)
      (𝓝 0) := by simpa using ht.const_mul (2 ^ p)
  refine squeeze_zero' ?_ ?_ ht'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have := Real.rpow_nonneg hx0.le ρ
    have : 0 ≤ 1 + |Real.log x| := by have := abs_nonneg (Real.log x); linarith
    positivity
  · have hsmall : Set.Ioo (0 : ℝ) (Real.exp (-1)) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (Real.exp_pos _)
    filter_upwards [hsmall] with x hx
    have hx0 : 0 < x := hx.1
    have hlog : Real.log x < -1 := by
      rw [Real.log_lt_iff_lt_exp hx0]; exact hx.2
    have habs : 1 ≤ |Real.log x| := by rw [abs_of_neg (by linarith)]; linarith
    have h1 : 1 + |Real.log x| ≤ 2 * |Real.log x| := by linarith
    have h2 : (1 + |Real.log x|) ^ p ≤ 2 ^ p * |Real.log x| ^ p := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 p
    rw [Real.rpow_natCast, Real.rpow_neg hx0.le, div_inv_eq_mul]
    have hxr := Real.rpow_nonneg hx0.le ρ
    calc x ^ ρ * (1 + |Real.log x|) ^ p ≤ x ^ ρ * (2 ^ p * |Real.log x| ^ p) :=
          mul_le_mul_of_nonneg_left h2 hxr
      _ = 2 ^ p * (|Real.log x| ^ p * x ^ ρ) := by ring

/-- **`F_{h,k} → 0` for `β < 1/(k+4)`** along any filter with `h → 0⁺`. -/
theorem forcingBudget_tendsto_zero (k : ℕ) {Ck β c₂ Cσ Cτ : ℝ} (hCk : 0 ≤ Ck) (hβ : 0 ≤ β)
    (hβk : β < 1 / (k + 4)) (hCσ : 0 ≤ Cσ) (hh : Tendsto h l (𝓝[>] 0))
    (hev : ∀ᶠ i in l, 0 < h i ∧ h i ≤ 1 ∧ 1 ≤ K i ∧ K i ≤ c₂ * h i ^ (-β) ∧ 0 ≤ σ i ∧
      σ i ≤ Cσ * h i ∧ 0 ≤ τ₂ i ∧ τ₂ i ≤ Cτ * (h i * K i) ∧ 0 ≤ τm i ∧
      τm i ≤ Cτ * (h i * K i ^ 2)) :
    Tendsto (fun i => forcingBudget k Ck (σ i) (h i) (K i) (τ₂ i) (τm i)) l (𝓝 0) := by
  have hρ : 0 < 1 - β * (k + 4) := by
    have hk : (0 : ℝ) < k + 4 := by positivity
    rw [lt_div_iff₀ hk] at hβk; linarith
  exact (forcingBudget_isBigO k hCk hβ hCσ hev).trans_tendsto
    ((tendsto_rpow_mul_one_add_abs_log_pow hρ (k + 1)).comp hh)

end Filter2

/-- **Dyadic summability**: along `h_n = h₀ 2^{-n}`, `Σ_n h_n^ρ (1 + |log h_n|)^p < ∞` for
`ρ > 0`. -/
theorem summable_dyadic {h₀ ρ : ℝ} (hh₀ : 0 < h₀) (hρ : 0 < ρ) (p : ℕ) :
    Summable (fun n : ℕ => (h₀ * (1 / 2) ^ n) ^ ρ * (1 + |Real.log (h₀ * (1 / 2) ^ n)|) ^ p) := by
  set r : ℝ := (1 / 2 : ℝ) ^ ρ
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hρ
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  set A : ℝ := |Real.log h₀| + 2
  have hA : 0 ≤ A := by positivity
  -- bound on each term
  have hterm : ∀ n : ℕ, (h₀ * (1 / 2) ^ n) ^ ρ * (1 + |Real.log (h₀ * (1 / 2) ^ n)|) ^ p ≤
      h₀ ^ ρ * A ^ p * r⁻¹ * (((n + 1 : ℕ) : ℝ) ^ p * r ^ (n + 1)) := by
    intro n
    have hpow : (h₀ * (1 / 2) ^ n) ^ ρ = h₀ ^ ρ * r ^ n := by
      rw [Real.mul_rpow hh₀.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_comm (n : ℝ) ρ, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hlog : |Real.log (h₀ * (1 / 2) ^ n)| ≤ |Real.log h₀| + n := by
      rw [Real.log_mul hh₀.ne' (by positivity), Real.log_pow]
      have hl2 : |Real.log (1 / 2)| ≤ 1 := by
        rw [one_div, Real.log_inv, abs_neg, abs_of_pos (Real.log_pos (by norm_num))]
        have := Real.log_two_lt_d9; linarith
      calc |Real.log h₀ + n * Real.log (1 / 2)| ≤ |Real.log h₀| + |n * Real.log (1 / 2)| :=
            abs_add_le _ _
        _ = |Real.log h₀| + n * |Real.log (1 / 2)| := by
            rw [abs_mul, Nat.abs_cast]
        _ ≤ |Real.log h₀| + n * 1 := by gcongr
        _ = |Real.log h₀| + n := by ring
    have h1 : 1 + |Real.log (h₀ * (1 / 2) ^ n)| ≤ A * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      have := abs_nonneg (Real.log h₀)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp only [A]; nlinarith
    have h2 : (1 + |Real.log (h₀ * (1 / 2) ^ n)|) ^ p ≤ A ^ p * ((n + 1 : ℕ) : ℝ) ^ p := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by have := abs_nonneg (Real.log (h₀ * (1 / 2) ^ n)); linarith) h1 p
    rw [hpow]
    have hh0r := Real.rpow_nonneg hh₀.le ρ
    calc h₀ ^ ρ * r ^ n * (1 + |Real.log (h₀ * (1 / 2) ^ n)|) ^ p
        ≤ h₀ ^ ρ * r ^ n * (A ^ p * ((n + 1 : ℕ) : ℝ) ^ p) := by gcongr
      _ = h₀ ^ ρ * A ^ p * r⁻¹ * (((n + 1 : ℕ) : ℝ) ^ p * r ^ (n + 1)) := by
          rw [pow_succ]; field_simp
  have hs : Summable (fun n : ℕ => ((n : ℕ) : ℝ) ^ p * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p (by rw [Real.norm_of_nonneg hr0]; exact hr1)
  have hs1 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ p * r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (fun n => ?_) hterm (hs1.mul_left _)
  have : 0 ≤ 1 + |Real.log (h₀ * (1 / 2) ^ n)| := by
    have := abs_nonneg (Real.log (h₀ * (1 / 2) ^ n)); linarith
  have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ h₀ * (1 / 2) ^ n) ρ
  positivity

/-- **Adjacent differences are summable** (comparison of adjacent records through the same
reference): if `‖x_n - x_*‖ ≤ a_n` with `Σ a_n < ∞`, then `Σ ‖x_{n+1} - x_n‖ < ∞`, and `x_n` is
Cauchy. -/
theorem summable_adjacent_of_le {E : Type*} [SeminormedAddCommGroup E] (x : ℕ → E) (x₀ : E)
    {a : ℕ → ℝ} (ha : Summable a) (hx : ∀ n, ‖x n - x₀‖ ≤ a n) :
    Summable (fun n => ‖x (n + 1) - x n‖) ∧ CauchySeq x := by
  have hs : Summable (fun n => a (n + 1) + a n) := ((summable_nat_add_iff 1).mpr ha).add ha
  have hle : ∀ n, ‖x (n + 1) - x n‖ ≤ a (n + 1) + a n := by
    intro n
    calc ‖x (n + 1) - x n‖ = ‖(x (n + 1) - x₀) - (x n - x₀)‖ := by congr 1; abel
      _ ≤ ‖x (n + 1) - x₀‖ + ‖x n - x₀‖ := norm_sub_le _ _
      _ ≤ a (n + 1) + a n := add_le_add (hx _) (hx _)
  have hsum : Summable (fun n => ‖x (n + 1) - x n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  refine ⟨hsum, cauchySeq_of_summable_dist ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hsum

/-- The worked example `eq:native-example-rate`: `k = 4`, `β = 1/18` gives the strong-forcing
exponent `1 - β(k+4) = 5/9`, the zero-order exponent `1 - 3β = 5/6`, and `β < 1/(k+4)`. -/
theorem native_rate_example_exponents :
    (1 : ℝ) - 1 / 18 * ((4 : ℕ) + 4) = 5 / 9 ∧ (1 : ℝ) - 3 * (1 / 18) = 5 / 6 ∧
      (1 / 18 : ℝ) < 1 / ((4 : ℕ) + 4) := by
  norm_num

/-- Non-vacuity of the rate hypotheses: `h = 1/n`, `K = h^{-1/18}`, `σ = h`, `τ₂ = hK`,
`τ_{k+2} = hK²` satisfy them eventually along `n → ∞`, so the forcing budget tends to zero. -/
example (Ck : ℝ) (hCk : 0 ≤ Ck) :
    Tendsto (fun n : ℕ => forcingBudget 4 Ck (1 / (n + 1 : ℝ)) (1 / (n + 1 : ℝ))
      ((1 / (n + 1 : ℝ)) ^ (-(1 / 18 : ℝ))) ((1 / (n + 1 : ℝ)) * (1 / (n + 1 : ℝ)) ^ (-(1 / 18 : ℝ)))
      ((1 / (n + 1 : ℝ)) * ((1 / (n + 1 : ℝ)) ^ (-(1 / 18 : ℝ))) ^ 2)) atTop (𝓝 0) := by
  refine forcingBudget_tendsto_zero 4 (β := 1 / 18) (Cσ := 1) (Cτ := 1) (c₂ := 1)
    (h := fun n : ℕ => 1 / (n + 1 : ℝ)) hCk (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => by
      simp only [Set.mem_Ioi]; positivity⟩
    exact (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  · refine Eventually.of_forall fun n => ?_
    have h0 : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have h1 : 1 / (n + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hK : 1 ≤ (1 / (n + 1 : ℝ)) ^ (-(1 / 18 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by norm_num)
    refine ⟨h0, h1, hK, by rw [one_mul], h0.le, by rw [one_mul], by positivity, by rw [one_mul],
      by positivity, by rw [one_mul]⟩

end

end RenewalGeometry.NativeRate
