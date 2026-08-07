/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fast loaded feedback collapses to a local generator
  (`thm:fast-feedback-collapse`, Gran-Tensor manuscript)

* `power_comparison_bound`: the discrete-Duhamel core of the
  boxed sup-convergence — for two step maps bounded by `M`,
  `‖Aⁿ⁺¹ - Eⁿ⁺¹‖ ≤ (n+1)·Mⁿ·‖A - E‖`, so an `O(h²)` per-step
  defect stays `O(h)` uniformly on `0 ≤ nh ≤ T`;
* `geometric_feedback_resummation`: the boxed factored branch
  `R = B(I - D₀)⁻¹C` — for `‖D₀‖ < 1` the resummed feedback
  `∑ₖ B·D₀ᵏ·C` equals `B·(∑ₖ D₀ᵏ)·C` with
  `(1 - D₀)·(∑ₖ D₀ᵏ) = 1`, exhibiting the geometric sum as the
  exact Neumann inverse;
* `feedback_tail_summable`: the loading hypothesis
  `∑ₖ (k+1)‖Rₖ‖ < ∞` holds automatically on the factored branch
  `‖D₀ᵏ‖ ≤ M·rᵏ` with `r < 1`.

Rendering disclosed: the full telescoping of the delayed
recursion `X_{n+1,h} = A_h X_{n,h} + Σ K_{k,h} X_{n-1-k,h}`
against the exponential `e^{nh(G+R)}` (the discrete Duhamel sum
with the two vanishing-rate hypotheses) and the `o(h)`
disappearing branch are the manuscript's limit bookkeeping; the
uniform power comparison, the exact Neumann resummation, and the
tail summability are proved here.
-/

open Matrix

namespace NCG

section PowerComparison

variable {A : Type*} [NormedRing A]

/-- Discrete-Duhamel power comparison: step maps bounded by `M`
satisfy `‖Aⁿ⁺¹ - Eⁿ⁺¹‖ ≤ (n+1)·Mⁿ·‖A - E‖`. -/
theorem power_comparison_bound (X E : A) (M : ℝ)
    (hX : ‖X‖ ≤ M) (hE : ‖E‖ ≤ M) :
    ∀ n : ℕ, ‖X ^ (n + 1) - E ^ (n + 1)‖
      ≤ (n + 1 : ℝ) * M ^ n * ‖X - E‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg X) hX
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : X ^ (n + 2) - E ^ (n + 2)
        = X * (X ^ (n + 1) - E ^ (n + 1))
          + (X - E) * E ^ (n + 1) := by
      rw [mul_sub, sub_mul, pow_succ' X (n + 1),
        pow_succ' E (n + 1)]
      abel
    have hEpow : ‖E ^ (n + 1)‖ ≤ M ^ (n + 1) := by
      calc ‖E ^ (n + 1)‖ ≤ ‖E‖ ^ (n + 1) :=
            norm_pow_le' E n.succ_pos
        _ ≤ M ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg E) hE _
    calc ‖X ^ (n + 2) - E ^ (n + 2)‖
        ≤ ‖X * (X ^ (n + 1) - E ^ (n + 1))‖
          + ‖(X - E) * E ^ (n + 1)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖X‖ * ‖X ^ (n + 1) - E ^ (n + 1)‖
          + ‖X - E‖ * ‖E ^ (n + 1)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * ((n + 1 : ℝ) * M ^ n * ‖X - E‖)
          + ‖X - E‖ * M ^ (n + 1) := by
          refine add_le_add (mul_le_mul hX ih (norm_nonneg _)
            hM) ?_
          exact mul_le_mul_of_nonneg_left hEpow (norm_nonneg _)
      _ = ((n + 1 : ℕ) + 1 : ℝ) * M ^ (n + 1) * ‖X - E‖ := by
          push_cast
          ring

end PowerComparison

section Resummation

variable {A : Type*} [NormedRing A] [CompleteSpace A]

/-- Boxed factored branch: for `‖D‖ < 1` the resummed feedback
is the exact Neumann composite — `∑ₖ B·Dᵏ·C = B·(∑ₖ Dᵏ)·C` and
`(1 - D)·(∑ₖ Dᵏ) = 1`, i.e. `R = B(I - D)⁻¹C`. -/
theorem geometric_feedback_resummation (B D C : A)
    (hD : ‖D‖ < 1) :
    (1 - D) * (∑' k : ℕ, D ^ k) = 1
      ∧ (∑' k : ℕ, B * D ^ k * C)
        = B * (∑' k : ℕ, D ^ k) * C := by
  have hsum : Summable fun k : ℕ => D ^ k :=
    summable_geometric_of_norm_lt_one hD
  refine ⟨mul_neg_geom_series D hD, ?_⟩
  have hsumC : Summable fun k : ℕ => D ^ k * C := hsum.mul_right C
  calc (∑' k : ℕ, B * D ^ k * C)
      = ∑' k : ℕ, B * (D ^ k * C) := by
        refine tsum_congr fun k => ?_
        rw [mul_assoc]
    _ = B * ∑' k : ℕ, D ^ k * C := hsumC.tsum_mul_left B
    _ = B * ((∑' k : ℕ, D ^ k) * C) := by
        rw [hsum.tsum_mul_right C]
    _ = B * (∑' k : ℕ, D ^ k) * C := by rw [mul_assoc]

end Resummation

/-- Loading summability on the factored branch: the weighted
tail `∑ₖ (k+1)·M·rᵏ` converges for `r < 1`. -/
theorem feedback_tail_summable (M r : ℝ) (hr : |r| < 1) :
    Summable fun k : ℕ => (k + 1 : ℝ) * M * r ^ k := by
  have h1 : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := r) (by simpa using hr)
  have h2 : Summable fun k : ℕ => r ^ k :=
    summable_geometric_of_abs_lt_one hr
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1) * r ^ k := by
    have := h1.add h2
    refine this.congr fun k => ?_
    ring
  have := hsum.mul_right M
  refine this.congr fun k => ?_
  ring

end NCG
