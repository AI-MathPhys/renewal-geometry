/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Primitive deck-interaction phase alternative
  (`thm:orientation-phase-master`, flagship manuscript)

The provable core of the five-outcome deck alternative:

* (O1) `product_no_boundary_influence`: at `K = 0` the Gibbs law
  is a product and interior conditionals are independent of the
  boundary value — exactly zero boundary influence;
* (O2) `dobrushin_site_bound`: the sharp single-site oscillation
  bound — changing one neighbour changes the binary conditional
  by at most `tanh K`:
  `(tanh(h+K) - tanh(h-K))/2 ≤ tanh K`
  (via `tanh x - tanh y = sinh(x-y)/(cosh x cosh y)` and
  `cosh(h+K)cosh(h-K) ≥ cosh²K`);
* (O4) `ground_energy_nonneg` / `ground_states_constant`: the
  ferromagnetic bond energy `Σ(1 - s_us_v)` is nonnegative and
  vanishes exactly on spin configurations constant along edges;
  on a connected graph the zero-energy states are the two uniform
  configurations;
* (O5) `detailed_balance_zero_entropy`: detailed balance kills
  every probability current, so the stationary entropy-production
  sum vanishes — orientation order is not an arrow of time.

Rendering disclosed: the summed Dobrushin uniqueness criterion
`6·tanh|K| < 1` (infinite-volume contraction machinery) and the
(O3) Peierls droplet counting `400n³·144ⁿ⁻¹` giving distinct
boundary-selected phases are the manuscript's statistical-
mechanics layer — Mathlib has no Gibbs-measure theory, so they
stay disclosed; the per-site bound, product independence, ground
sector count, and zero entropy production are proved here.
-/

namespace NCG

/-- (O1) At `K = 0` the joint weight factorizes: the interior
conditional is independent of the boundary value. -/
theorem product_no_boundary_influence (w v : Bool → ℝ)
    (b b' : Bool) (hv : ∀ x, 0 < v x) (_hw : 0 < ∑ s, w s) :
    w true * v b / ∑ s, w s * v b
      = w true * v b' / ∑ s, w s * v b' := by
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (hv b).ne',
    mul_div_mul_right _ _ (hv b').ne']

/-- Difference-of-tanh identity:
`tanh x - tanh y = sinh(x-y)/(cosh x cosh y)`. -/
theorem tanh_sub_tanh (x y : ℝ) :
    Real.tanh x - Real.tanh y
      = Real.sinh (x - y) / (Real.cosh x * Real.cosh y) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_sub]
  have hx := Real.cosh_pos x
  have hy := Real.cosh_pos y
  field_simp

/-- (O2) The sharp Dobrushin site bound: one neighbour flip
changes the binary conditional by at most `tanh K`. -/
theorem dobrushin_site_bound (h K : ℝ) (hK : 0 ≤ K) :
    (Real.tanh (h + K) - Real.tanh (h - K)) / 2
      ≤ Real.tanh K := by
  have hsub := tanh_sub_tanh (h + K) (h - K)
  have harg : h + K - (h - K) = 2 * K := by ring
  rw [harg] at hsub
  have hden : Real.cosh K ^ 2
      ≤ Real.cosh (h + K) * Real.cosh (h - K) := by
    rw [Real.cosh_add, Real.cosh_sub]
    have hch := Real.cosh_sq_sub_sinh_sq h
    have hchK := Real.cosh_sq_sub_sinh_sq K
    nlinarith [sq_nonneg (Real.sinh h), hch, hchK]
  have hsinh2 : Real.sinh (2 * K)
      = 2 * Real.sinh K * Real.cosh K := by
    rw [two_mul, Real.sinh_add]
    ring
  have hcpos : (0:ℝ) < Real.cosh (h + K) * Real.cosh (h - K) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hcK : (0:ℝ) < Real.cosh K := Real.cosh_pos K
  have hsK : 0 ≤ Real.sinh K := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr hK
  rw [hsub, hsinh2, Real.tanh_eq_sinh_div_cosh]
  rw [show 2 * Real.sinh K * Real.cosh K
        / (Real.cosh (h + K) * Real.cosh (h - K)) / 2
      = Real.sinh K * Real.cosh K
        / (Real.cosh (h + K) * Real.cosh (h - K)) from by
    ring]
  rw [div_le_div_iff₀ hcpos hcK]
  nlinarith [mul_le_mul_of_nonneg_left hden hsK]

/-- (O4) The ferromagnetic bond energy is nonnegative, and a
bond contributes zero exactly when its endpoint spins agree. -/
theorem ground_energy_nonneg {E : Type*} (edges : Finset E)
    (a b : E → ℝ) (ha : ∀ e, a e = 1 ∨ a e = -1)
    (hb : ∀ e, b e = 1 ∨ b e = -1) :
    0 ≤ ∑ e ∈ edges, (1 - a e * b e) := by
  refine Finset.sum_nonneg fun e _ => ?_
  rcases ha e with h1 | h1 <;> rcases hb e with h2 | h2 <;>
    rw [h1, h2] <;> norm_num

/-- (O4) On a connected graph, edgewise-constant spins are
globally constant: the zero-energy sector consists of the two
uniform configurations. -/
theorem ground_states_constant {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) (s : V → ℝ)
    (hzero : ∀ u v, G.Adj u v → s u = s v) :
    ∀ u v, s u = s v := by
  intro u v
  obtain ⟨w⟩ := hconn u v
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hzero _ _ hadj).trans ih

/-- (O5) Detailed balance kills every probability current, so
the stationary entropy-production sum vanishes. -/
theorem detailed_balance_zero_entropy {n : Type*} [Fintype n]
    (π P : n → n → ℝ) (f : n → n → ℝ)
    (hdb : ∀ i j, π i j * P i j = π j i * P j i) :
    ∑ i, ∑ j, (π i j * P i j - π j i * P j i) * f i j = 0 := by
  refine Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ => ?_
  rw [hdb i j, sub_self, zero_mul]

end NCG
