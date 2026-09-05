/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpatiotemporalExponentialWeights

/-!
# Exact spatiotemporal feedback decay

This closes the last assembly step of `thm:spatiotemporal-feedback`: the
scalar weighted Volterra estimate is applied to every spatial row, then the
exponential weights are removed to obtain the displayed corner estimate.
-/

namespace NCG

/-- The spatial-and-temporal weighted row of a response corner table. -/
noncomputable def weightedResponseRow {ι : Type*} [Fintype ι]
    (d : ι → ι → ℝ) (μ η : ℝ)
    (W : ℕ → ι → ι → ℝ) (m : ℕ) (i : ι) : ℝ :=
  Real.exp (η * m) * ∑ j, Real.exp (μ * d i j) * W m i j

/-- Exact final display: a loaded Volterra recursion for every weighted row
implies simultaneous exponential decay in graph distance and delay. -/
theorem spatiotemporal_feedback_decay_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j k, d i k ≤ d i j + d j k)
    (μ η qa q : ℝ) (hμ : 0 ≤ μ)
    (qk : ℕ → ℝ) (hqa : 0 ≤ qa) (hqk : ∀ k, 0 ≤ qk k)
    (hqtotal : ∀ m, qa + ∑ k ∈ Finset.range m, qk k ≤ q)
    (hq : q < 1)
    (W : ℕ → ι → ι → ℝ) (hW : ∀ m i j, 0 ≤ W m i j)
    (hinitial : ∀ i, weightedResponseRow d μ η W 0 i ≤ 1)
    (hrec : ∀ i m,
      weightedResponseRow d μ η W (m + 1) i
        ≤ qa * weightedResponseRow d μ η W m i
          + ∑ j ∈ Finset.range m,
              qk (m - 1 - j) * weightedResponseRow d μ η W j i) :
    ∀ m i j,
      W m i j ≤ Real.exp (-(μ * d i j))
        * Real.exp (-(η * m)) / (1 - q) := by
  have hvolterra := (spatiotemporal_feedback (ι := ι)
    (fun _ _ => (1 : ℝ)) (by intro i j; positivity)
    (by intro i j k; norm_num)).2
  have hrow : ∀ m i,
      ∑ j, Real.exp (μ * d i j) * W m i j
        ≤ Real.exp (-(η * m)) / (1 - q) := by
    intro m i
    have hu : weightedResponseRow d μ η W m i ≤ 1 / (1 - q) :=
      hvolterra qa q qk (fun n => weightedResponseRow d μ η W n i)
        hqa hqk
        (fun n => mul_nonneg (Real.exp_nonneg _)
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (Real.exp_nonneg _) (hW n i j)))
        hqtotal hq (hinitial i) (hrec i) m
    let x : ℝ := η * m
    have hinv : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      ∑ j, Real.exp (μ * d i j) * W m i j
          = Real.exp (-x) * weightedResponseRow d μ η W m i := by
              rw [weightedResponseRow, show η * (m : ℝ) = x from rfl,
                ← mul_assoc, hinv, one_mul]
      _ ≤ Real.exp (-x) * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
      _ = Real.exp (-(η * m)) / (1 - q) := by
        dsimp [x]
        ring
  exact (spatiotemporal_exponential_weights d hd μ η q hμ hq W hW hrow).2

end NCG
