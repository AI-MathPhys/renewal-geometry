/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeSelectedClosure

/-!
# An explicit polynomial selected-source regime (`cor:selected-polynomial`)

Einstein–Standard-Model action-closure manuscript, `cor:selected-polynomial`
(`eq:selected-polynomial-source`, `eq:selected-polynomial-thresholds`,
`eq:selected-polynomial-window`, `eq:selected-polynomial-rate`) and its proof
`app:native-polynomial-proof`.

## Exponent arithmetic (standalone, proved)

* `failure_terms_le` — the five terms of `eq:source-selection-failure` under
  `eq:selected-polynomial-source` with `s_h = h^b`, `R_h = h^{-a}`, `α_h = h^c` are respectively
  `O(h^{2ε})` (exit), `O(h^{2ε})` (action span), `O(h^{2ε})` (work), `O(h^{2a})` (native energy) and
  `O(h^{2ε})` (alignment); `failure_le` — the failure probability is `O(h^{2a} + h^{2ε})`.
* `reader_budget_le` — the Sobolev reader (`cor:native-reader-sobolev`: `t_{h,j}, c_{h,j} ≤ C
K^{2-q}`)
  gives `T_{h,j} = t_{h,j} + c_{h,j}R_h ≤ 2C h^{-a}K^{2-q}` (`eq:app-polynomial-tail`).
* `rpow_le_of_window` — `K ≍ h^{-β}` gives `K^e ≤ C h^{-βe}` for exponents of either sign.
* `budget_rate_le` — with `ρ = min{c, b - β(k+1), 1 - β(k+4), β(q-k-5) - a}`:
  `α_h + F̄_{h,k} ≤ C h^ρ (1 + |log h|)^{k+1}`; the four terms of `F̄_{h,k}` have orders
  `h^bK^{k+1}`, `hK^{k+4}`, `h^{-a}K^{k+5-q}`, `h^{-a}K^{k+4-q}` (`fourth_exponent_eq`: the fourth
  exponent exceeds the third by `β`).
* `rho_pos` — the window `eq:selected-polynomial-window` and `c > 0` give `ρ > 0`.

## Composition

* `selected_polynomial_borel_cantelli` — along `h_n = h₀2^{-n}`: the failure bounds
  `C(h_n^{2a} + h_n^{2ε})` and the rates `h_n^ρ(1 + |log h_n|)^{k+1}` are summable
  (`NativeRate.summable_dyadic`), so under any common coupling the successful selected branch is
  eventually almost sure with summable adjacent differences
  (`SelectedClosure.selected_borel_cantelli`).
  The closure bound on success is the conclusion of `thm:native-selected-closure`
  (`SelectedClosure.native_selected_closure`), conditional on the open `prop:coupled-bootstrap`.
-/

open Filter Topology MeasureTheory
open scoped Nat ENNReal

namespace RenewalGeometry.SelectedPolynomial

open NativeRate SelectedClosure

noncomputable section

/-! ### Elementary power algebra -/

theorem rpow_sq {h b : ℝ} (hh : 0 < h) : (h ^ b) ^ 2 = h ^ (2 * b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; ring_nf

/-- `h^e ≤ h^ρ` for `0 < h ≤ 1` and `ρ ≤ e`. -/
theorem rpow_le_rpow_rho {h e ρ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hρ : ρ ≤ e) : h ^ e ≤ h ^ ρ :=
  Real.rpow_le_rpow_of_exponent_ge hh0 hh1 hρ

/-- **`K ≍ h^{-β}` controls every real power of `K`**: if `0 < c₁`, `c₁h^{-β} ≤ K ≤ c₂h^{-β}`
and `h > 0`, then `K^e ≤ max(c₁^e, c₂^e) h^{-βe}` for every real `e`. -/
theorem rpow_le_of_window {h K β c₁ c₂ : ℝ} (hh : 0 < h) (hc₁ : 0 < c₁)
    (hlo : c₁ * h ^ (-β) ≤ K) (hup : K ≤ c₂ * h ^ (-β)) (e : ℝ) :
    K ^ e ≤ max (c₁ ^ e) (c₂ ^ e) * h ^ (-β * e) := by
  have hhb : 0 < h ^ (-β) := Real.rpow_pos_of_pos hh _
  have hlo0 : 0 < c₁ * h ^ (-β) := mul_pos hc₁ hhb
  have hc₂ : 0 ≤ c₂ := by
    by_contra hneg; push Not at hneg
    have : c₂ * h ^ (-β) < 0 := mul_neg_of_neg_of_pos hneg hhb
    linarith
  have hpow : ∀ c, 0 ≤ c → (c * h ^ (-β)) ^ e = c ^ e * h ^ (-β * e) := by
    intro c hc
    rw [Real.mul_rpow hc hhb.le, ← Real.rpow_mul hh.le]
  rcases le_or_gt 0 e with he | he
  · calc K ^ e ≤ (c₂ * h ^ (-β)) ^ e := Real.rpow_le_rpow (hlo0.le.trans hlo) hup he
      _ = c₂ ^ e * h ^ (-β * e) := hpow c₂ hc₂
      _ ≤ max (c₁ ^ e) (c₂ ^ e) * h ^ (-β * e) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hh.le _)
  · calc K ^ e ≤ (c₁ * h ^ (-β)) ^ e := Real.rpow_le_rpow_of_nonpos hlo0 hlo he.le
      _ = c₁ ^ e * h ^ (-β * e) := hpow c₁ hc₁.le
      _ ≤ max (c₁ ^ e) (c₂ ^ e) * h ^ (-β * e) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hh.le _)

/-! ### The five failure terms -/

/-- **The five terms of `eq:source-selection-failure`** in the polynomial regime
(`app:native-polynomial-proof`).  For `0 < h`, `κ > 0`, `δ_h ≥ c_δh^d`, `D_h^A ≤ Ch^{-d_A}`,
`J_h ≥ c_Jh^{-(d+d_A+2b+2ε)}`, `ℛ_{h,J} ≤ Ch^{2b+2ε}`, `M_{h,J} ≤ C`, `A_{h,J} ≤ Ch^{2c+2ε}`,
`p_h^exit ≤ Ch^{2ε}` and thresholds `s_h = h^b`, `R_h = h^{-a}`, `α_h = h^c`, the terms are bounded
by `Ch^{2ε}`, `C/(κc_δc_J) h^{2ε}`, `C/κ h^{2ε}`, `Ch^{2a}`, `Ch^{2ε}`. -/
theorem failure_terms_le {h κ δ DA J Rw M Aocc pex C cδ cJ a b c d dA ε : ℝ} (hh : 0 < h)
    (hκ : 0 < κ) (hcδ : 0 < cδ) (hcJ : 0 < cJ) (hC : 0 ≤ C)
    (hδ : cδ * h ^ d ≤ δ) (hDA : DA ≤ C * h ^ (-dA)) (hJ : cJ * h ^ (-(d + dA + 2 * b + 2 * ε)) ≤ J)
    (hRw : Rw ≤ C * h ^ (2 * b + 2 * ε)) (hM : M ≤ C) (hA : Aocc ≤ C * h ^ (2 * c + 2 * ε))
    (hpex : pex ≤ C * h ^ (2 * ε)) :
    pex ≤ C * h ^ (2 * ε) ∧
      DA / (κ * δ * J * (h ^ b) ^ 2) ≤ C / (κ * cδ * cJ) * h ^ (2 * ε) ∧
      Rw / (κ * (h ^ b) ^ 2) ≤ C / κ * h ^ (2 * ε) ∧
      M / (h ^ (-a)) ^ 2 ≤ C * h ^ (2 * a) ∧
      Aocc / (h ^ c) ^ 2 ≤ C * h ^ (2 * ε) := by
  have hp : ∀ e : ℝ, 0 < h ^ e := fun e => Real.rpow_pos_of_pos hh e
  refine ⟨hpex, ?_, ?_, ?_, ?_⟩
  · -- action-span term
    have hden0 : 0 < κ * (cδ * h ^ d) * (cJ * h ^ (-(d + dA + 2 * b + 2 * ε))) * (h ^ b) ^ 2 := by
      have := hp d; have := hp (-(d + dA + 2 * b + 2 * ε)); have := hp b; positivity
    have hden : κ * (cδ * h ^ d) * (cJ * h ^ (-(d + dA + 2 * b + 2 * ε))) * (h ^ b) ^ 2 ≤
        κ * δ * J * (h ^ b) ^ 2 := by
      have := hp d; have := hp (-(d + dA + 2 * b + 2 * ε))
      have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ
      gcongr
    have hid : C / (κ * cδ * cJ) * h ^ (2 * ε) *
        (κ * (cδ * h ^ d) * (cJ * h ^ (-(d + dA + 2 * b + 2 * ε))) * (h ^ b) ^ 2) =
        C * h ^ (-dA) := by
      rw [rpow_sq hh]
      have e1 : h ^ (2 * ε) * h ^ d * h ^ (-(d + dA + 2 * b + 2 * ε)) * h ^ (2 * b) =
          h ^ (-dA) := by
        rw [← Real.rpow_add hh, ← Real.rpow_add hh, ← Real.rpow_add hh]; ring_nf
      have hne : κ * cδ * cJ ≠ 0 := by positivity
      calc C / (κ * cδ * cJ) * h ^ (2 * ε) *
            (κ * (cδ * h ^ d) * (cJ * h ^ (-(d + dA + 2 * b + 2 * ε))) * h ^ (2 * b))
          = C * (h ^ (2 * ε) * h ^ d * h ^ (-(d + dA + 2 * b + 2 * ε)) * h ^ (2 * b)) *
              ((κ * cδ * cJ) / (κ * cδ * cJ)) := by ring
        _ = C * h ^ (-dA) := by rw [e1, div_self hne, mul_one]
    rw [div_le_iff₀ (lt_of_lt_of_le hden0 hden)]
    calc DA ≤ C * h ^ (-dA) := hDA
      _ = C / (κ * cδ * cJ) * h ^ (2 * ε) *
          (κ * (cδ * h ^ d) * (cJ * h ^ (-(d + dA + 2 * b + 2 * ε))) * (h ^ b) ^ 2) := hid.symm
      _ ≤ C / (κ * cδ * cJ) * h ^ (2 * ε) * (κ * δ * J * (h ^ b) ^ 2) :=
          mul_le_mul_of_nonneg_left hden (by have := hp (2 * ε); positivity)
  · -- work term
    rw [rpow_sq hh, div_le_iff₀ (by have := hp (2 * b); positivity)]
    have e1 : h ^ (2 * ε) * h ^ (2 * b) = h ^ (2 * b + 2 * ε) := by
      rw [← Real.rpow_add hh]; ring_nf
    calc Rw ≤ C * h ^ (2 * b + 2 * ε) := hRw
      _ = C / κ * h ^ (2 * ε) * (κ * h ^ (2 * b)) := by
          rw [← e1]; field_simp
  · -- native-energy term
    rw [rpow_sq hh, div_le_iff₀ (hp _)]
    have e1 : h ^ (2 * a) * h ^ (2 * -a) = 1 := by
      rw [← Real.rpow_add hh]; ring_nf; exact Real.rpow_zero h
    calc M ≤ C := hM
      _ = C * h ^ (2 * a) * h ^ (2 * -a) := by rw [mul_assoc, e1, mul_one]
  · -- alignment term
    rw [rpow_sq hh, div_le_iff₀ (hp _)]
    have e1 : h ^ (2 * ε) * h ^ (2 * c) = h ^ (2 * c + 2 * ε) := by
      rw [← Real.rpow_add hh]; ring_nf
    calc Aocc ≤ C * h ^ (2 * c + 2 * ε) := hA
      _ = C * h ^ (2 * ε) * h ^ (2 * c) := by rw [← e1]; ring

/-- **The failure probability is `O(h^{2a} + h^{2ε})`** (`cor:selected-polynomial`): the boxed
bound `eq:source-selection-failure` is at most
`C(1 + 1/(κc_δc_J) + 1/κ + 1 + 1)(h^{2a} + h^{2ε})`. -/
theorem failure_le {h κ δ DA J Rw M Aocc pex C cδ cJ a b c d dA ε : ℝ} (hh : 0 < h)
    (hκ : 0 < κ) (hcδ : 0 < cδ) (hcJ : 0 < cJ) (hC : 0 ≤ C)
    (hδ : cδ * h ^ d ≤ δ) (hDA : DA ≤ C * h ^ (-dA)) (hJ : cJ * h ^ (-(d + dA + 2 * b + 2 * ε)) ≤ J)
    (hRw : Rw ≤ C * h ^ (2 * b + 2 * ε)) (hM : M ≤ C) (hA : Aocc ≤ C * h ^ (2 * c + 2 * ε))
    (hpex : pex ≤ C * h ^ (2 * ε)) :
    pex + DA / (κ * δ * J * (h ^ b) ^ 2) + Rw / (κ * (h ^ b) ^ 2) + M / (h ^ (-a)) ^ 2 +
        Aocc / (h ^ c) ^ 2 ≤
      (C + C / (κ * cδ * cJ) + C / κ + C + C) * (h ^ (2 * a) + h ^ (2 * ε)) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := failure_terms_le (a := a) hh hκ hcδ hcJ hC hδ hDA hJ hRw hM
    hA hpex
  have ha : 0 ≤ h ^ (2 * a) := Real.rpow_nonneg hh.le _
  have he : 0 ≤ h ^ (2 * ε) := Real.rpow_nonneg hh.le _
  have h1 : 0 ≤ C / (κ * cδ * cJ) := by positivity
  have h2 : 0 ≤ C / κ := by positivity
  nlinarith [mul_nonneg hC ha, mul_nonneg hC he, mul_nonneg h1 ha, mul_nonneg h2 ha]


/-! ### The reader budget and the rate -/

/-- **`eq:app-polynomial-tail`**: the Sobolev reader of `cor:native-reader-sobolev`
(`τ_{h,j} ≤ C_q K^{2-q}(1 + √V)`, i.e. `t_{h,j}, c_{h,j} ≤ C_q K^{2-q}`) with `R_h = h^{-a}`,
`0 < h ≤ 1`, `a ≥ 0` gives `T_{h,j} = t_{h,j} + c_{h,j}R_h ≤ 2C_q h^{-a} K^{2-q}`. -/
theorem reader_budget_le {h K a q Cq t c : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : 0 ≤ a)
    (hCq : 0 ≤ Cq) (hK : 0 < K) (ht : t ≤ Cq * K ^ (2 - q)) (hc : c ≤ Cq * K ^ (2 - q)) :
    t + c * h ^ (-a) ≤ 2 * Cq * h ^ (-a) * K ^ (2 - q) := by
  have h1 : 1 ≤ h ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hh1 (by linarith)
  have hKq : 0 ≤ Cq * K ^ (2 - q) := mul_nonneg hCq (Real.rpow_nonneg hK.le _)
  have h2 : c * h ^ (-a) ≤ Cq * K ^ (2 - q) * h ^ (-a) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  nlinarith

/-- One term of the composed budget: `h^u K^e ≤ max(c₁^e, c₂^e) h^ρ` whenever `ρ ≤ u - βe`,
`0 < h ≤ 1` and `c₁h^{-β} ≤ K ≤ c₂h^{-β}`. -/
theorem term_le {h K β c₁ c₂ u e ρ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hc₁ : 0 < c₁)
    (hlo : c₁ * h ^ (-β) ≤ K) (hup : K ≤ c₂ * h ^ (-β)) (hρ : ρ ≤ u + -β * e) :
    h ^ u * K ^ e ≤ max (c₁ ^ e) (c₂ ^ e) * h ^ ρ := by
  have hm : 0 ≤ max (c₁ ^ e) (c₂ ^ e) := le_max_of_le_left (Real.rpow_nonneg hc₁.le _)
  calc h ^ u * K ^ e ≤ h ^ u * (max (c₁ ^ e) (c₂ ^ e) * h ^ (-β * e)) :=
        mul_le_mul_of_nonneg_left (rpow_le_of_window hh0 hc₁ hlo hup e) (Real.rpow_nonneg hh0.le _)
    _ = max (c₁ ^ e) (c₂ ^ e) * h ^ (u + -β * e) := by rw [Real.rpow_add hh0]; ring
    _ ≤ max (c₁ ^ e) (c₂ ^ e) * h ^ ρ :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_rho hh0 hh1 hρ) hm

/-- The rate exponent `ρ = min{c, b - β(k+1), 1 - β(k+4), β(q-k-5) - a}` of
`eq:selected-polynomial-rate`. -/
def rho (k : ℕ) (q a b c β : ℝ) : ℝ :=
  min (min c (b - β * (k + 1))) (min (1 - β * (k + 4)) (β * (q - k - 5) - a))

/-- **`ρ > 0`** under the window `eq:selected-polynomial-window`
(`0 < β < min{b/(k+1), 1/(k+4)}`, `0 < a < β(q-k-5)`) and `c > 0`. -/
theorem rho_pos (k : ℕ) {q a b c β : ℝ} (hc : 0 < c) (hβb : β < b / (k + 1))
    (hβk : β < 1 / (k + 4)) (ha : a < β * (q - k - 5)) : 0 < rho k q a b c β := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk4 : (0 : ℝ) < k + 4 := by positivity
  rw [lt_div_iff₀ hk1] at hβb
  rw [lt_div_iff₀ hk4] at hβk
  unfold rho
  refine lt_min (lt_min hc ?_) (lt_min ?_ ?_) <;> linarith

/-- The fourth exponent of `app:native-polynomial-proof` exceeds the third by `β`:
`(β(q-k-4) - a) - (β(q-k-5) - a) = β`. -/
theorem fourth_exponent_eq (k : ℕ) (q a β : ℝ) :
    (β * (q - k - 4) - a) - (β * (q - k - 5) - a) = β := by ring

theorem npow_eq_rpow (K : ℝ) (n : ℕ) : K ^ n = K ^ (n : ℝ) := (Real.rpow_natCast K n).symm

/-- **The polynomial rate** (`eq:selected-polynomial-rate`, `app:native-polynomial-proof`).  Fix
`k`, `q`, `a`, `b`, `c`, `β ≥ 0`, window constants `0 < c₁`, `c₂`, the reader constant `C_T ≥ 0`
and `C_k ≥ 0`.  There is `C` such that for every `0 < h ≤ 1`, `1 ≤ K` with
`c₁h^{-β} ≤ K ≤ c₂h^{-β}` (`K_h ≍ h^{-β}`) and tail budgets `0 ≤ T₂`, `T₂, T_m ≤ C_Th^{-a}K^{2-q}`
(`eq:app-polynomial-tail`), with `s_h = h^b`, `α_h = h^c`:
`D̄_{h,k} = α_h + F̄_{h,k} ≤ C h^ρ (1 + |log h|)^{k+1}`.  (The four terms of `F̄_{h,k}` have orders
`h^bK^{k+1}`, `hK^{k+4}`, `h^{-a}K^{k+5-q}`, `h^{-a}K^{k+4-q}` up to the logarithmic factor.) -/
theorem budget_rate_le (k : ℕ) {q a b c β c₁ c₂ CT Ck : ℝ} (hc₁ : 0 < c₁) (hCT : 0 ≤ CT)
    (hCk : 0 ≤ Ck) (hβ : 0 ≤ β) :
    ∃ C : ℝ, ∀ h K T₂ Tm : ℝ, 0 < h → h ≤ 1 → 1 ≤ K → c₁ * h ^ (-β) ≤ K → K ≤ c₂ * h ^ (-β) →
      0 ≤ T₂ → T₂ ≤ CT * h ^ (-a) * K ^ (2 - q) → Tm ≤ CT * h ^ (-a) * K ^ (2 - q) →
      h ^ c + forcingBudget k Ck (h ^ b) h K T₂ Tm ≤
        C * (h ^ rho k q a b c β * (1 + |Real.log h|) ^ (k + 1)) := by
  set ρ := rho k q a b c β with hρdef
  set M1 := max (c₁ ^ ((k : ℝ) + 1)) (c₂ ^ ((k : ℝ) + 1))
  set M2 := max (c₁ ^ ((k : ℝ) + 4)) (c₂ ^ ((k : ℝ) + 4))
  set M3 := max (c₁ ^ ((k : ℝ) + 5 - q)) (c₂ ^ ((k : ℝ) + 5 - q))
  set M4 := max (c₁ ^ ((k : ℝ) + 4 - q)) (c₂ ^ ((k : ℝ) + 4 - q))
  set CL := 1 + Real.log (2 + Ck * c₂ ^ (k + 2)) + (β * (k + 2) + 1)
  have hM1 : 0 ≤ M1 := le_max_of_le_left (Real.rpow_nonneg hc₁.le _)
  have hM2 : 0 ≤ M2 := le_max_of_le_left (Real.rpow_nonneg hc₁.le _)
  have hM3 : 0 ≤ M3 := le_max_of_le_left (Real.rpow_nonneg hc₁.le _)
  have hM4 : 0 ≤ M4 := le_max_of_le_left (Real.rpow_nonneg hc₁.le _)
  refine ⟨1 + (M1 + M2 + CT * M3) * CL ^ (k + 1) + CT * M4, ?_⟩
  intro h K T₂ Tm hh0 hh1 hK hlo hup hT₂0 hT₂ hTm
  have hK0 : 0 < K := by linarith
  have hP : 0 ≤ h ^ ρ := Real.rpow_nonneg hh0.le _
  set Lg := (1 + |Real.log h|) ^ (k + 1) with hLg
  have hLg1 : 1 ≤ Lg := one_le_pow₀ (by have := abs_nonneg (Real.log h); linarith)
  -- exponent facts
  have hρc : ρ ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hρb : ρ ≤ b - β * (k + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 - β * (k + 4) := (min_le_right _ _).trans (min_le_left _ _)
  have hρq : ρ ≤ β * (q - k - 5) - a := (min_le_right _ _).trans (min_le_right _ _)
  -- the five terms
  have t0 : h ^ c ≤ h ^ ρ := rpow_le_rpow_rho hh0 hh1 hρc
  have t1 : h ^ b * K ^ (k + 1) ≤ M1 * h ^ ρ := by
    rw [npow_eq_rpow, show (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    exact term_le hh0 hh1 hc₁ hlo hup (by linarith)
  have t2 : h * K ^ (k + 4) ≤ M2 * h ^ ρ := by
    rw [npow_eq_rpow, show (((k + 4 : ℕ)) : ℝ) = (k : ℝ) + 4 by push_cast; ring]
    have := term_le (u := 1) (e := (k : ℝ) + 4) hh0 hh1 hc₁ hlo hup (ρ := ρ) (by linarith)
    rwa [Real.rpow_one] at this
  have t3 : K ^ (k + 3) * T₂ ≤ CT * (M3 * h ^ ρ) := by
    have hk3 : 0 ≤ K ^ (k + 3) := by positivity
    calc K ^ (k + 3) * T₂ ≤ K ^ (k + 3) * (CT * h ^ (-a) * K ^ (2 - q)) :=
          mul_le_mul_of_nonneg_left hT₂ hk3
      _ = CT * (h ^ (-a) * K ^ ((k : ℝ) + 5 - q)) := by
          have e : K ^ ((k : ℝ) + 5 - q) = K ^ (k + 3) * K ^ (2 - q) := by
            rw [npow_eq_rpow, ← Real.rpow_add hK0]; congr 1; push_cast; ring
          rw [e]; ring
      _ ≤ CT * (M3 * h ^ ρ) :=
          mul_le_mul_of_nonneg_left (term_le hh0 hh1 hc₁ hlo hup (by linarith)) hCT
  have t4 : K ^ (k + 2) * Tm ≤ CT * (M4 * h ^ ρ) := by
    have hk2 : 0 ≤ K ^ (k + 2) := by positivity
    calc K ^ (k + 2) * Tm ≤ K ^ (k + 2) * (CT * h ^ (-a) * K ^ (2 - q)) :=
          mul_le_mul_of_nonneg_left hTm hk2
      _ = CT * (h ^ (-a) * K ^ ((k : ℝ) + 4 - q)) := by
          have e : K ^ ((k : ℝ) + 4 - q) = K ^ (k + 2) * K ^ (2 - q) := by
            rw [npow_eq_rpow, ← Real.rpow_add hK0]; congr 1; push_cast; ring
          rw [e]; ring
      _ ≤ CT * (M4 * h ^ ρ) :=
          mul_le_mul_of_nonneg_left (term_le hh0 hh1 hc₁ hlo hup (by nlinarith)) hCT
  -- the logarithmic factor
  have hb0 : 0 ≤ h ^ b := Real.rpow_nonneg hh0.le _
  have he : h * K ^ 3 ≤ epsc (h ^ b) h K T₂ := le_epsc hb0 hT₂0
  have hL := logFactor_le k hCk hh0 hh1 hK hup hβ he
  have hepos : 0 < epsc (h ^ b) h K T₂ := lt_of_lt_of_le (by positivity) he
  have hL0 : 0 ≤ logFactor k Ck K (epsc (h ^ b) h K T₂) := by
    unfold logFactor
    have hq : 0 ≤ Ck * K ^ (k + 5) / epsc (h ^ b) h K T₂ := by positivity
    have : 0 ≤ Real.log (2 + Ck * K ^ (k + 5) / epsc (h ^ b) h K T₂) :=
      Real.log_nonneg (by linarith)
    linarith
  have hLp : logFactor k Ck K (epsc (h ^ b) h K T₂) ^ (k + 1) ≤ CL ^ (k + 1) * Lg := by
    rw [hLg, ← mul_pow]; exact pow_le_pow_left₀ hL0 hL _
  -- `ε̄ K^{k+1}` expanded
  have hEK : epsc (h ^ b) h K T₂ * K ^ (k + 1) =
      h ^ b * K ^ (k + 1) + h * K ^ (k + 4) + K ^ (k + 3) * T₂ := by
    unfold epsc eps0; ring
  have hE : epsc (h ^ b) h K T₂ * K ^ (k + 1) ≤ (M1 + M2 + CT * M3) * h ^ ρ := by
    rw [hEK]; nlinarith
  have hprod : epsc (h ^ b) h K T₂ * K ^ (k + 1) * logFactor k Ck K (epsc (h ^ b) h K T₂) ^ (k + 1)
      ≤ (M1 + M2 + CT * M3) * h ^ ρ * (CL ^ (k + 1) * Lg) :=
    mul_le_mul hE hLp (pow_nonneg hL0 _) (by positivity)
  unfold forcingBudget
  have hPL : h ^ ρ ≤ h ^ ρ * Lg := le_mul_of_one_le_right hP hLg1
  have hCT4 : 0 ≤ CT * M4 := mul_nonneg hCT hM4
  have hCT4' : CT * (M4 * h ^ ρ) ≤ CT * M4 * (h ^ ρ * Lg) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hPL hCT4
  have hfin : (M1 + M2 + CT * M3) * h ^ ρ * (CL ^ (k + 1) * Lg) =
      (M1 + M2 + CT * M3) * CL ^ (k + 1) * (h ^ ρ * Lg) := by ring
  calc h ^ c + (epsc (h ^ b) h K T₂ * K ^ (k + 1) *
        logFactor k Ck K (epsc (h ^ b) h K T₂) ^ (k + 1) + K ^ (k + 2) * Tm)
      ≤ h ^ ρ * Lg + ((M1 + M2 + CT * M3) * CL ^ (k + 1) * (h ^ ρ * Lg) +
          CT * M4 * (h ^ ρ * Lg)) := by linarith
    _ = (1 + (M1 + M2 + CT * M3) * CL ^ (k + 1) + CT * M4) * (h ^ ρ * Lg) := by ring


/-! ### Dyadic summability and the almost-sure clause -/

/-- `h_n^e` is summable along `h_n = h₀2^{-n}` for `e > 0`. -/
theorem summable_dyadic_rpow {h₀ e : ℝ} (hh₀ : 0 < h₀) (he : 0 < e) :
    Summable (fun n : ℕ => (h₀ * (1 / 2) ^ n) ^ e) := by
  simpa using summable_dyadic hh₀ he 0

/-- **The dyadic clause of `cor:selected-polynomial`** (the closure bound on success is the
conclusion of `thm:native-selected-closure`, conditional on the open `prop:coupled-bootstrap`, and
enters as `hsucc`).  Along `h_n = h₀2^{-n}` (`0 < h₀ ≤ 1`), let `μ` be any common coupling of the
selection stages whose `n`-th failure event has probability at most the boxed bound
`eq:source-selection-failure` with the polynomial thresholds `s = h^b`, `R = h^{-a}`, `α = h^c` and
the polynomial source hypotheses `eq:selected-polynomial-source`; let `K_n ≍ h_n^{-β}` and the
reader
budgets satisfy `eq:app-polynomial-tail`; assume the window `eq:selected-polynomial-window`, and
that
every successful stage-`n` record is within `C_s(α_n + F̄_{h_n,k})` of the common reference.  Then
almost surely the selected branch eventually succeeds and has summable adjacent differences. -/
theorem selected_polynomial_borel_cantelli (k : ℕ) {Ω' : Type*} [MeasurableSpace Ω']
    (μ : Measure Ω') {E : Type*} [PseudoMetricSpace E] {h₀ q a b c β ε d dA c₁ c₂ CT Ck κ cδ cJ C
      Cs : ℝ}
    (hh₀ : 0 < h₀) (hh₀1 : h₀ ≤ 1) (hc : 0 < c) (hε : 0 < ε) (ha0 : 0 < a)
    (hβ0 : 0 < β) (hβb : β < b / (k + 1)) (hβk : β < 1 / (k + 4)) (ha : a < β * (q - k - 5))
    (hc₁ : 0 < c₁) (hCT : 0 ≤ CT) (hCk : 0 ≤ Ck) (hκ : 0 < κ) (hcδ : 0 < cδ) (hcJ : 0 < cJ)
    (hC : 0 ≤ C)
    -- the selection stages
    (Fail : ℕ → Set Ω') (δ DA J Rw M Aocc pex : ℕ → ℝ)
    (hδ : ∀ n, cδ * (h₀ * (1 / 2) ^ n) ^ d ≤ δ n)
    (hDA : ∀ n, DA n ≤ C * (h₀ * (1 / 2) ^ n) ^ (-dA))
    (hJ : ∀ n, cJ * (h₀ * (1 / 2) ^ n) ^ (-(d + dA + 2 * b + 2 * ε)) ≤ J n)
    (hRw : ∀ n, Rw n ≤ C * (h₀ * (1 / 2) ^ n) ^ (2 * b + 2 * ε)) (hM : ∀ n, M n ≤ C)
    (hA : ∀ n, Aocc n ≤ C * (h₀ * (1 / 2) ^ n) ^ (2 * c + 2 * ε))
    (hpex : ∀ n, pex n ≤ C * (h₀ * (1 / 2) ^ n) ^ (2 * ε))
    (hμ : ∀ n, μ (Fail n) ≤ ENNReal.ofReal (pex n +
      DA n / (κ * δ n * J n * ((h₀ * (1 / 2) ^ n) ^ b) ^ 2) +
      Rw n / (κ * ((h₀ * (1 / 2) ^ n) ^ b) ^ 2) + M n / ((h₀ * (1 / 2) ^ n) ^ (-a)) ^ 2 +
      Aocc n / ((h₀ * (1 / 2) ^ n) ^ c) ^ 2))
    -- the cutoffs and reader budgets
    (K T₂ Tm : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (hKlo : ∀ n, c₁ * (h₀ * (1 / 2) ^ n) ^ (-β) ≤ K n)
    (hKup : ∀ n, K n ≤ c₂ * (h₀ * (1 / 2) ^ n) ^ (-β)) (hT₂0 : ∀ n, 0 ≤ T₂ n)
    (hT₂ : ∀ n, T₂ n ≤ CT * (h₀ * (1 / 2) ^ n) ^ (-a) * K n ^ (2 - q))
    (hTm : ∀ n, Tm n ≤ CT * (h₀ * (1 / 2) ^ n) ^ (-a) * K n ^ (2 - q))
    -- the closure bound on success
    (x : ℕ → Ω' → E) (x₀ : E) (hCs : 0 ≤ Cs)
    (hsucc : ∀ n ω, ω ∉ Fail n → dist (x n ω) x₀ ≤ Cs * ((h₀ * (1 / 2) ^ n) ^ c +
      forcingBudget k Ck ((h₀ * (1 / 2) ^ n) ^ b) (h₀ * (1 / 2) ^ n) (K n) (T₂ n) (Tm n))) :
    ∀ᵐ ω ∂μ, (∀ᶠ n in atTop, ω ∉ Fail n) ∧
      Summable (fun n => dist (x (n + 1) ω) (x n ω)) := by
  set hn : ℕ → ℝ := fun n => h₀ * (1 / 2) ^ n with hhn
  have hn0 : ∀ n, 0 < hn n := fun n => by simp only [hhn]; positivity
  have hn1 : ∀ n, hn n ≤ 1 := fun n => by
    simp only [hhn]
    calc h₀ * (1 / 2) ^ n ≤ 1 * 1 :=
          mul_le_mul hh₀1 (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  -- the rate
  obtain ⟨Cr, hCr⟩ := budget_rate_le k (q := q) (a := a) (b := b) (c := c) (c₂ := c₂) hc₁ hCT hCk
    hβ0.le
  have hρ : 0 < rho k q a b c β := rho_pos k hc hβb hβk ha
  set Cf := C + C / (κ * cδ * cJ) + C / κ + C + C
  refine selected_borel_cantelli μ Fail (fun n => Cf * (hn n ^ (2 * a) + hn n ^ (2 * ε)))
    (fun n => by
      have : 0 ≤ Cf := by positivity
      have := Real.rpow_nonneg (hn0 n).le (2 * a)
      have := Real.rpow_nonneg (hn0 n).le (2 * ε)
      positivity)
    (((summable_dyadic_rpow hh₀ (by linarith)).add
      (summable_dyadic_rpow hh₀ (by linarith))).mul_left
      Cf)
    (fun n => (hμ n).trans (ENNReal.ofReal_le_ofReal
      (failure_le (hn0 n) hκ hcδ hcJ hC (hδ n) (hDA n) (hJ n) (hRw n) (hM n) (hA n) (hpex n))))
    x x₀ (fun n => Cr * (hn n ^ rho k q a b c β * (1 + |Real.log (hn n)|) ^ (k + 1)))
    ((summable_dyadic hh₀ hρ (k + 1)).mul_left Cr) Cs (fun n ω hω => ?_)
  calc dist (x n ω) x₀ ≤ Cs * (hn n ^ c +
        forcingBudget k Ck (hn n ^ b) (hn n) (K n) (T₂ n) (Tm n)) := hsucc n ω hω
    _ ≤ Cs * (Cr * (hn n ^ rho k q a b c β * (1 + |Real.log (hn n)|) ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left (hCr (hn n) (K n) (T₂ n) (Tm n) (hn0 n) (hn1 n) (hK n) (hKlo n)
          (hKup n) (hT₂0 n) (hT₂ n) (hTm n)) hCs

end

end RenewalGeometry.SelectedPolynomial
