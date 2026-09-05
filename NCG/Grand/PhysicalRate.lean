/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Physical-time rate, dense-cycle comparison, and Lyapunov
  tightness
  (`thm:renewal-physical-rate` and
  `thm:renewal-Lyapunov-tightness`, Gran-Tensor manuscript)

* `renewal_physical_rate` (l2 operator norm):
  (i) rate transfer: `‖T·V‖ ≤ ‖V·W‖ + ‖T·V - V·W‖` — the
      target rate survives whenever the Ward residual is
      below the rate gap;
  (ii) the boxed dense-cycle comparison
      `‖Tⁿ·V - V·Wⁿ‖ ≤ n·‖T·V - V·W‖` for contractions
      `‖T‖ ≤ 1`, `‖W‖ ≤ 1` — `o(τ)` residuals give agreement
      of ambient and action-model dynamics on compact
      physical-time windows.

* `renewal_lyapunov_tightness` (scalar drift clauses, applied
  to `x = ω(V)` by stationarity of the state):
  (i) the boxed stationary bound
      `x ≤ bτ/(1 - e^{-κτ})` from the drift inequality;
  (ii) the uniform bound `bτ/(1-e^{-κτ}) ≤ (b/κ)e^{κτmax}`;
  (iii) the screen bound `ω(I-P) ≤ ω(V)/ψ(R)`.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `thm:renewal-physical-rate`. -/
theorem renewal_physical_rate {H E : Type*} [Fintype H]
    [Fintype E] [DecidableEq H] [DecidableEq E]
    (T : Matrix H H ℂ) (V : Matrix H E ℂ)
    (W : Matrix E E ℂ) (hT : ‖T‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    -- (i) rate transfer through the residual
    ‖T * V‖ ≤ ‖V * W‖ + ‖T * V - V * W‖
    -- (ii) the dense-cycle comparison
    ∧ ∀ n : ℕ,
        ‖T ^ n * V - V * W ^ n‖ ≤ n * ‖T * V - V * W‖ := by
  have hone : ‖(1 : Matrix E E ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty E with hE | hE
    · rw [Subsingleton.elim (1 : Matrix E E ℂ) 0, norm_zero]
      norm_num
    · exact le_of_eq CStarRing.norm_one
  have hWk : ∀ k : ℕ, ‖W ^ k‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ j ihj =>
        rw [pow_succ]
        calc ‖W ^ j * W‖ ≤ ‖W ^ j‖ * ‖W‖ :=
              Matrix.l2_opNorm_mul _ _
          _ ≤ 1 * 1 :=
              mul_le_mul ihj hW (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
  constructor
  · calc ‖T * V‖ = ‖V * W + (T * V - V * W)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖V * W‖ + ‖T * V - V * W‖ := norm_add_le _ _
  · intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hsplit : T ^ (k + 1) * V - V * W ^ (k + 1)
            = T * (T ^ k * V - V * W ^ k)
              + (T * V - V * W) * W ^ k := by
          rw [pow_succ' T, pow_succ' W]
          simp only [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_assoc]
          abel
        calc ‖T ^ (k + 1) * V - V * W ^ (k + 1)‖
            = ‖T * (T ^ k * V - V * W ^ k)
                + (T * V - V * W) * W ^ k‖ := by
              rw [hsplit]
          _ ≤ ‖T * (T ^ k * V - V * W ^ k)‖
              + ‖(T * V - V * W) * W ^ k‖ :=
              norm_add_le _ _
          _ ≤ ‖T‖ * ‖T ^ k * V - V * W ^ k‖
              + ‖T * V - V * W‖ * ‖W ^ k‖ :=
              add_le_add (Matrix.l2_opNorm_mul _ _)
                (Matrix.l2_opNorm_mul _ _)
          _ ≤ 1 * (k * ‖T * V - V * W‖)
              + ‖T * V - V * W‖ * 1 := by
              apply add_le_add
              · apply mul_le_mul hT ih (norm_nonneg _)
                  zero_le_one
              · apply mul_le_mul_of_nonneg_left (hWk k)
                  (norm_nonneg _)
          _ = (k + 1 : ℕ) * ‖T * V - V * W‖ := by
              push_cast
              ring

/-- `thm:renewal-Lyapunov-tightness`. -/
theorem renewal_lyapunov_tightness (κ b τ τmax x : ℝ)
    (hκ : 0 < κ) (hτ : 0 < τ) (hττ : τ ≤ τmax) (hb : 0 ≤ b)
    (hdrift : x ≤ Real.exp (-(κ * τ)) * x + b * τ) :
    -- (i) the boxed stationary bound
    x ≤ b * τ / (1 - Real.exp (-(κ * τ)))
    -- (ii) uniform in the cutoff
    ∧ b * τ / (1 - Real.exp (-(κ * τ)))
        ≤ b * Real.exp (κ * τmax) / κ
    -- (iii) the finite-rank screen bound
    ∧ (∀ z ψ : ℝ, 0 < ψ → ψ * z ≤ x → z ≤ x / ψ) := by
  have hgap : 0 < 1 - Real.exp (-(κ * τ)) := by
    have h1 : Real.exp (-(κ * τ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 < κ * τ := mul_pos hκ hτ
      linarith
    linarith
  have hfloor : κ * τ * Real.exp (-(κ * τ))
      ≤ 1 - Real.exp (-(κ * τ)) := by
    have h1 : κ * τ + 1 ≤ Real.exp (κ * τ) :=
      Real.add_one_le_exp (κ * τ)
    have h2 : (κ * τ + 1) * Real.exp (-(κ * τ))
        ≤ Real.exp (κ * τ) * Real.exp (-(κ * τ)) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    rw [← Real.exp_add] at h2
    simp only [add_neg_cancel, Real.exp_zero] at h2
    nlinarith [Real.exp_nonneg (-(κ * τ))]
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hgap]
    nlinarith
  · have hpos : 0 < κ * τ * Real.exp (-(κ * τ)) := by
      positivity
    calc b * τ / (1 - Real.exp (-(κ * τ)))
        ≤ b * τ / (κ * τ * Real.exp (-(κ * τ))) := by
          gcongr
      _ = b * Real.exp (κ * τ) / κ := by
          rw [Real.exp_neg]
          field_simp
      _ ≤ b * Real.exp (κ * τmax) / κ := by
          gcongr
  · intro z ψ hψ hz
    rw [le_div_iff₀ hψ]
    linarith [hz, mul_comm ψ z]

end NCG
