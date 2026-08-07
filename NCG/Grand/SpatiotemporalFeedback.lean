/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spatiotemporal feedback influence
  (`thm:spatiotemporal-feedback`, Gran-Tensor manuscript)

* `spatiotemporal_feedback`:
  (i) submultiplicativity of the weighted influence bound:
      for a triangle-submultiplicative weight
      `κ(i,k) ≤ κ(i,j)·κ(j,k)` (the exponential
      graph-distance weight `e^{μd}`), the weighted corner
      bounds compose, `‖LM‖_μ ≤ ‖L‖_μ·‖M‖_μ`;
  (ii) the boxed weighted Volterra decay: with total loaded
      weight `q_{μ,η} < 1`, the weighted response norms stay
      below `1/(1 - q_{μ,η})` uniformly in time — i.e.
      `‖Q_j X_m Q_i‖ ≤ e^{-μ d(i,j)} e^{-η m}/(1-q)`.

The identification of the abstract corner table with the
operational atom graph (`W(L)_{ji} = ‖Q_j L Q_i‖`, the
resolution `∑ Q = I` giving the entrywise product bound
`W(LM) ≤ W(L)W(M)`) is the corner calculus of
`NCG.operational_light_cone`; the exponential weights
`κ = e^{μd}`, `e^{ηk}` instantiate the hypotheses.
-/

namespace NCG

/-- `thm:spatiotemporal-feedback`. -/
theorem spatiotemporal_feedback {ι : Type*} [Fintype ι]
    (κ : ι → ι → ℝ) (hκ0 : ∀ i j, 0 ≤ κ i j)
    (hκtri : ∀ i j k, κ i k ≤ κ i j * κ j k) :
    -- (i) submultiplicative weighted influence bound
    (∀ (W1 W2 : ι → ι → ℝ) (b1 b2 : ℝ),
      (∀ i j, 0 ≤ W1 i j) → (∀ i j, 0 ≤ W2 i j) →
      0 ≤ b1 →
      (∀ i, ∑ j, κ i j * W1 i j ≤ b1) →
      (∀ i, ∑ j, κ i j * W2 i j ≤ b2) →
      ∀ i, ∑ k, κ i k * (∑ j, W2 i j * W1 j k)
        ≤ b2 * b1)
    -- (ii) the boxed weighted Volterra decay
    ∧ (∀ (qa q : ℝ) (qk u : ℕ → ℝ),
        0 ≤ qa → (∀ k, 0 ≤ qk k) → (∀ m, 0 ≤ u m) →
        (∀ m, qa + ∑ k ∈ Finset.range m, qk k ≤ q) →
        q < 1 → u 0 ≤ 1 →
        (∀ m, u (m + 1) ≤ qa * u m
          + ∑ j ∈ Finset.range m, qk (m - 1 - j) * u j) →
        ∀ m, u m ≤ 1 / (1 - q)) := by
  constructor
  · intro W1 W2 b1 b2 h1 h2 hb1 hW1 hW2 i
    have hstep : ∀ k, κ i k * (∑ j, W2 i j * W1 j k)
        ≤ ∑ j, (κ i j * W2 i j) * (κ j k * W1 j k) := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hκ := hκtri i j k
      have hprod : (0 : ℝ) ≤ W2 i j * W1 j k :=
        mul_nonneg (h2 i j) (h1 j k)
      calc κ i k * (W2 i j * W1 j k)
          ≤ (κ i j * κ j k) * (W2 i j * W1 j k) :=
            mul_le_mul_of_nonneg_right hκ hprod
        _ = (κ i j * W2 i j) * (κ j k * W1 j k) := by
            ring
    calc ∑ k, κ i k * (∑ j, W2 i j * W1 j k)
        ≤ ∑ k, ∑ j, (κ i j * W2 i j)
            * (κ j k * W1 j k) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = ∑ j, (κ i j * W2 i j)
            * ∑ k, κ j k * W1 j k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ j, (κ i j * W2 i j) * b1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hW1 j)
            (mul_nonneg (hκ0 i j) (h2 i j))
      _ = (∑ j, κ i j * W2 i j) * b1 := by
          rw [← Finset.sum_mul]
      _ ≤ b2 * b1 :=
          mul_le_mul_of_nonneg_right (hW2 i) hb1
  · intro qa q qk u hqa hqk hu hq hq1 hu0 hrec m
    have hq0 : 0 ≤ q := le_trans hqa (by simpa using hq 0)
    have h1q : (0 : ℝ) < 1 - q := by linarith
    have hC1 : (1 : ℝ) ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ h1q]
      linarith
    have hC0 : (0 : ℝ) ≤ 1 / (1 - q) := by positivity
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m with
      | 0 => exact le_trans hu0 hC1
      | m + 1 =>
        have hbound := hrec m
        have hsum : ∑ j ∈ Finset.range m,
            qk (m - 1 - j) * u j
            ≤ (∑ j ∈ Finset.range m, qk (m - 1 - j))
              * (1 / (1 - q)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun j hj => ?_
          have hjm : j < m := Finset.mem_range.mp hj
          exact mul_le_mul_of_nonneg_left
            (ih j (by omega)) (hqk _)
        have hreflect : ∑ j ∈ Finset.range m,
            qk (m - 1 - j)
            = ∑ j ∈ Finset.range m, qk j :=
          Finset.sum_range_reflect qk m
        calc u (m + 1)
            ≤ qa * u m + ∑ j ∈ Finset.range m,
                qk (m - 1 - j) * u j := hbound
          _ ≤ qa * (1 / (1 - q))
              + (∑ j ∈ Finset.range m, qk j)
                * (1 / (1 - q)) := by
              have h1 := mul_le_mul_of_nonneg_left
                (ih m (by omega)) hqa
              rw [hreflect] at hsum
              linarith
          _ = (qa + ∑ j ∈ Finset.range m, qk j)
              * (1 / (1 - q)) := by ring
          _ ≤ q * (1 / (1 - q)) :=
              mul_le_mul_of_nonneg_right (hq m) hC0
          _ ≤ 1 / (1 - q) :=
              mul_le_of_le_one_left hC0 hq1.le

end NCG
