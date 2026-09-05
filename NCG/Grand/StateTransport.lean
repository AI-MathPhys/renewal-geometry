/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unique stationary states and cutoff transport from cycle
  mixing
  (`thm:renewal-state-transport`, Gran-Tensor manuscript)

* `renewal_state_transport`, on the space of zero-mass
  functional differences with the cycle precomposition `T`
  contracting by `q < 1`:
  (i) uniqueness: two stationary states have zero difference;
  (ii) the boxed perturbation bound
      `‖ω_Y∘ι - ω_X‖ ≤ δ/(1-q)` from the intertwining
      defect `‖e - T e‖ ≤ δ`;
  (iii) exact intertwining gives exact transport
      (`δ = 0 ⇒ ω_Y∘ι = ω_X`).

The summable-chain limit clause is the proved
`summable_state_correction` layer applied to these bounds.
-/

namespace NCG

/-- `thm:renewal-state-transport`. -/
theorem renewal_state_transport {V : Type*}
    [NormedAddCommGroup V] (T : V → V) (q δ : ℝ)
    (hq : q < 1) (e : V)
    (hcontr : ‖T e‖ ≤ q * ‖e‖)
    (hdef : ‖e - T e‖ ≤ δ) :
    -- (ii) the boxed perturbation bound
    ‖e‖ ≤ δ / (1 - q)
    -- (iii) exact intertwining gives exact transport
    ∧ (δ = 0 → e = 0)
    -- (i) uniqueness: a fixed zero-mass difference vanishes
    ∧ (T e = e → 0 ≤ ‖e‖ → ‖e‖ = 0) := by
  have hgap : 0 < 1 - q := by linarith
  have hbound : ‖e‖ ≤ q * ‖e‖ + δ := by
    calc ‖e‖ = ‖T e + (e - T e)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖T e‖ + ‖e - T e‖ := norm_add_le _ _
      _ ≤ q * ‖e‖ + δ := add_le_add hcontr hdef
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hgap]
    nlinarith
  · intro h0
    rw [h0] at hbound
    have hle : ‖e‖ * (1 - q) ≤ 0 := by nlinarith
    have hnn : 0 ≤ ‖e‖ := norm_nonneg e
    have : ‖e‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  · intro hfix _
    have h := hcontr
    rw [hfix] at h
    have hnn : 0 ≤ ‖e‖ := norm_nonneg e
    nlinarith

end NCG
