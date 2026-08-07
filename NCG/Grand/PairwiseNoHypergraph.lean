/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pairwise panels do not determine interaction support
  (`cth:pairwise-no-hypergraph`, Gran-Tensor manuscript)

* `pairwise_no_hypergraph`: for the three-bit family
  `p_θ(x) = (1 + θ·x₁x₂x₃)/8` on `{±1}³`:
  (i)–(iii) every two-variable marginal equals `1/4`
      independently of `θ` (hence every one- and two-variable
      marginal is `θ`-free);
  (iv) the laws are normalized;
  (v) the three-body correlation reads
      `E_θ[x₁x₂x₃] = θ`.

Hence every pairwise connected panel may vanish while a
three-body hyperedge survives.
-/

set_option linter.unusedSimpArgs false

namespace NCG

private def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `cth:pairwise-no-hypergraph`. -/
theorem pairwise_no_hypergraph (θ : ℝ) :
    -- (i)–(iii) all pair marginals are θ-free
    (∀ b1 b2 : Bool, ∑ b3 : Bool,
      (1 + θ * sgn b1 * sgn b2 * sgn b3) / 8 = 1/4)
    ∧ (∀ b1 b3 : Bool, ∑ b2 : Bool,
        (1 + θ * sgn b1 * sgn b2 * sgn b3) / 8 = 1/4)
    ∧ (∀ b2 b3 : Bool, ∑ b1 : Bool,
        (1 + θ * sgn b1 * sgn b2 * sgn b3) / 8 = 1/4)
    -- (iv) normalization
    ∧ (∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
        (1 + θ * sgn b1 * sgn b2 * sgn b3) / 8 = 1)
    -- (v) the three-body correlation reads θ
    ∧ (∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
        (sgn b1 * sgn b2 * sgn b3)
          * ((1 + θ * sgn b1 * sgn b2 * sgn b3) / 8) = θ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b1 b2
    cases b1 <;> cases b2 <;>
      · simp [Fintype.sum_bool, sgn]
        ring
  · intro b1 b3
    cases b1 <;> cases b3 <;>
      · simp [Fintype.sum_bool, sgn]
        ring
  · intro b2 b3
    cases b2 <;> cases b3 <;>
      · simp [Fintype.sum_bool, sgn]
        ring
  · simp [Fintype.sum_bool, sgn]
    ring
  · simp [Fintype.sum_bool, sgn]
    ring

end NCG
