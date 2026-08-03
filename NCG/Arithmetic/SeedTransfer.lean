/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quantitative seed transfer and the natural rough carrier
  (`thm:v003-seed-transfer`, `cor:v003-natural-rough-carrier`,
   arithmetic manuscript)

Finite-carrier rendering of the two conditional transfer theorems
on top of the Li–Liu prime–semiprime seeds:

* `seed_prime_target_bound` / `seed_semiprime_target_bound`: the
  per-candidate arithmetic — a prime target contributes
  `≥ c₁²·L` and a semiprime target `rq` with `log p ≥ c₁L`,
  `log r ≥ c₂ > 0`, `log q ≥ c₃L` contributes `≥ c₁c₂c₃` to the
  weighted degree-`≤2` correlation `(log p)·(log r·log q/L²)`;
* `seed_mass_transfer`: summing the per-candidate bound over the
  seed multiplies by the seed count — any count lower bound `M`
  transfers to the correlation lower bound `c·M`
  (the boxed `≫ Sing·x/log²x` scale);
* `seed_transfer_onelog`: under the additional rough lower bound
  `log r ≥ αL` the per-candidate contribution improves by one
  logarithm to `≥ c₁·α·c₃·L`;
* `rough_support_contribution`: on the support-retaining carrier
  (`log r ≥ L/13`, `log q ≥ L/2`), every target contributes
  `≥ (c₁/26)·L`;
* `natural_rough_carrier`: since the rough weight satisfies
  `0 ≤ 𝒲 ≤ 4`, the support count is at least one quarter of the
  weighted mass — the boxed `≫ Sing(2)·x/log x` carrier bound.

Rendering disclosed: the seed counts (Assumption
`ass:v003-quant-seeds`, external Li–Liu inputs) and the identities
`log p ≍ L`, `log q ≥ L/(1+a)` (the proved
`prop:v003-ratio-conversion` record) enter as the displayed
per-candidate hypotheses; the singular-series normalization
`M = c·Sing·x/L²` names the transferred count.
-/

namespace NCG

/-- Per-candidate bound, prime target: `(log p)(log n)/L ≥ c₁²L`. -/
theorem seed_prime_target_bound (L lp ln c1 : ℝ) (hL : 0 < L)
    (h1 : 0 < c1) (hp : c1 * L ≤ lp) (hn : c1 * L ≤ ln) :
    c1 ^ 2 * L ≤ lp * ln / L := by
  rw [le_div_iff₀ hL]
  have hlp : (0:ℝ) ≤ lp := le_trans (by positivity) hp
  nlinarith [mul_le_mul hp hn (by positivity : (0:ℝ) ≤ c1 * L)
    hlp]

/-- Per-candidate bound, semiprime target:
`(log p)(log r · log q)/L² ≥ c₁c₂c₃`. -/
theorem seed_semiprime_target_bound (L lp lr lq c1 c2 c3 : ℝ)
    (hL : 0 < L) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3)
    (hp : c1 * L ≤ lp) (hr : c2 ≤ lr) (hq : c3 * L ≤ lq) :
    c1 * c2 * c3 ≤ lp * (lr * lq / L ^ 2) := by
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hlp : (0:ℝ) ≤ lp := le_trans (by positivity) hp
  have key : c1 * L * (c2 * (c3 * L)) ≤ lp * (lr * lq) :=
    mul_le_mul hp (mul_le_mul hr hq (by positivity)
      (le_trans h2.le hr)) (by positivity) hlp
  nlinarith [key]

/-- `thm:v003-seed-transfer`, summation step: a per-candidate
lower bound `c` and a seed count `M` transfer to the boxed mass
bound `c·M`. -/
theorem seed_mass_transfer (S : Finset ℕ) (w : ℕ → ℝ)
    (c M : ℝ) (hc : 0 ≤ c) (hw : ∀ p ∈ S, c ≤ w p)
    (hM : M ≤ (S.card : ℝ)) :
    c * M ≤ ∑ p ∈ S, w p := by
  calc c * M ≤ c * S.card := by nlinarith
    _ = ∑ _p ∈ S, c := by rw [Finset.sum_const, nsmul_eq_mul,
        mul_comm]
    _ ≤ ∑ p ∈ S, w p := Finset.sum_le_sum hw

/-- One-logarithm improvement: the rough lower bound
`log r ≥ αL` upgrades the semiprime contribution to `≥ c₁αc₃·L`. -/
theorem seed_transfer_onelog (L lp lr lq c1 al c3 : ℝ)
    (hL : 0 < L) (h1 : 0 < c1) (hal : 0 < al) (h3 : 0 < c3)
    (hp : c1 * L ≤ lp) (hr : al * L ≤ lr) (hq : c3 * L ≤ lq) :
    c1 * al * c3 * L ≤ lp * (lr * lq / L ^ 2) := by
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hlp : (0:ℝ) ≤ lp := le_trans (by positivity) hp
  have key : c1 * L * (al * L * (c3 * L)) ≤ lp * (lr * lq) :=
    mul_le_mul hp (mul_le_mul hr hq (by positivity)
      (le_trans (by positivity) hr)) (by positivity) hlp
  nlinarith [key]

/-- Supported-carrier contribution: with `log r ≥ L/13` and
`log q ≥ L/2`, every supported target contributes `≥ (c₁/26)L`. -/
theorem rough_support_contribution (L lp lr lq c1 : ℝ)
    (hL : 0 < L) (h1 : 0 < c1) (hp : c1 * L ≤ lp)
    (hr : L / 13 ≤ lr) (hq : L / 2 ≤ lq) :
    c1 / 26 * L ≤ lp * (lr * lq / L ^ 2) := by
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hlp : (0:ℝ) ≤ lp := le_trans (by positivity) hp
  have key : c1 * L * (L / 13 * (L / 2)) ≤ lp * (lr * lq) :=
    mul_le_mul hp (mul_le_mul hr hq (by positivity)
      (le_trans (by positivity) hr)) (by positivity) hlp
  nlinarith [key]

/-- `cor:v003-natural-rough-carrier`, support count: the rough
weight is bounded by `4`, so the support count is at least a
quarter of the weighted mass. -/
theorem natural_rough_carrier (S : Finset ℕ) (w : ℕ → ℝ)
    (M : ℝ) (hub : ∀ p ∈ S, w p ≤ 4)
    (hlb : M ≤ ∑ p ∈ S, w p) :
    M / 4 ≤ (S.card : ℝ) := by
  have h1 : ∑ p ∈ S, w p ≤ 4 * S.card := by
    calc ∑ p ∈ S, w p ≤ ∑ _p ∈ S, (4:ℝ) :=
        Finset.sum_le_sum hub
      _ = 4 * S.card := by rw [Finset.sum_const, nsmul_eq_mul,
          mul_comm]
  linarith

end NCG
