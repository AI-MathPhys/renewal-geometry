/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minimal recurrent-root experiment and the historical
  boundary (`thm:dimension-recurrent-root-table`,
  Gran-Tensor manuscript)

* `dimension_recurrent_root_table`: for the joint table
  `J(s,α,s')` with faithful source marginal
  `μ(s) = ∑_{α,s'} J`,
  (i) the boxed DS.10 reconstruction — the normalized
      kernel `P = μ⁻¹J` recovers the table exactly
      (`μ(s)·P = J`);
  (ii) row minimality — two distinct tables with the same
      faithful marginal have distinct normalized kernels;
  (iii) pairwise marginals do not suffice: the parity
      construction on three binary variables gives two
      distinct joint laws with identical pairwise
      marginals;
  (iv) the DS.11 slip bridge
      `B = (1-3b)I + b(𝟙𝟙ᵀ - I)` is stochastic
      (rows sum to one), is the identity exactly at
      `b = 0`, and at `b > 0` every off-diagonal overlap
      is positive (the overlap graph is complete, hence
      connected).

The `S₄`-covariance uniqueness of the bridge form (only
diagonal and off-diagonal orbits on `X × X`), the sharp
factor statement, and the commutant-reduced assemblage
remark are the manuscript's covariance layer.
-/

open Finset

namespace NCG

/-- `thm:dimension-recurrent-root-table`
(DS.9–DS.11). -/
theorem dimension_recurrent_root_table :
    -- (i) the boxed DS.10 exact reconstruction
    (∀ {S A : Type} [Fintype S] [Fintype A]
      (J : S → A → S → ℝ),
      (∀ s, (∑ a, ∑ s', J s a s') ≠ 0) →
      ∀ s a s', (∑ b, ∑ t', J s b t')
          * ((∑ b, ∑ t', J s b t')⁻¹ * J s a s')
        = J s a s')
    -- (ii) row minimality: same faithful marginal +
    -- equal kernels ⟹ equal tables
    ∧ (∀ {S A : Type} [Fintype S] [Fintype A]
      (J J' : S → A → S → ℝ),
      (∀ s, (∑ a, ∑ s', J s a s') ≠ 0) →
      (∀ s, ∑ a, ∑ s', J s a s'
        = ∑ a, ∑ s', J' s a s') →
      (∀ s a s', (∑ b, ∑ t', J s b t')⁻¹ * J s a s'
        = (∑ b, ∑ t', J' s b t')⁻¹ * J' s a s') →
      J = J')
    -- (iii) pairwise marginals do not suffice (parity
    -- construction)
    ∧ (∃ p q : Fin 2 × Fin 2 × Fin 2 → ℝ,
        (∀ x1 x2, ∑ x3, p (x1, x2, x3)
          = ∑ x3, q (x1, x2, x3))
        ∧ (∀ x1 x3, ∑ x2, p (x1, x2, x3)
          = ∑ x2, q (x1, x2, x3))
        ∧ (∀ x2 x3, ∑ x1, p (x1, x2, x3)
          = ∑ x1, q (x1, x2, x3))
        ∧ p ≠ q)
    -- (iv) the DS.11 slip bridge
    ∧ (∀ b : ℝ,
        (∀ i : Fin 4, (∑ j, ((1 - 3*b)
            * (if i = j then (1:ℝ) else 0)
          + b * (1 - if i = j then 1 else 0))) = 1)
        ∧ (b = 0 → ∀ i j : Fin 4, ((1 - 3*b)
            * (if i = j then (1:ℝ) else 0)
          + b * (1 - if i = j then 1 else 0))
          = if i = j then 1 else 0)
        ∧ (0 < b → ∀ i j : Fin 4, i ≠ j →
          0 < ((1 - 3*b)
            * (if i = j then (1:ℝ) else 0)
          + b * (1 - if i = j then 1 else 0)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S A _ _ J hfaith s a s'
    rw [← mul_assoc, mul_inv_cancel₀ (hfaith s),
      one_mul]
  · intro S A _ _ J J' hfaith hmarg hker
    funext s a s'
    have h := hker s a s'
    rw [← hmarg s] at h
    have h2 := congrArg (fun x =>
      (∑ b, ∑ t', J s b t') * x) h
    simp only at h2
    rw [← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (hfaith s), one_mul, one_mul]
      at h2
    exact h2
  · -- parity construction: uniform on even vs odd
    -- parity triples
    refine ⟨fun x => if ((x.1 : ℕ) + (x.2.1 : ℕ)
        + (x.2.2 : ℕ)) % 2 = 0 then 1/4 else 0,
      fun x => if ((x.1 : ℕ) + (x.2.1 : ℕ)
        + (x.2.2 : ℕ)) % 2 = 1 then 1/4 else 0,
      ?_, ?_, ?_, ?_⟩
    · intro x1 x2
      fin_cases x1 <;> fin_cases x2 <;>
        norm_num [Fin.sum_univ_two]
    · intro x1 x3
      fin_cases x1 <;> fin_cases x3 <;>
        norm_num [Fin.sum_univ_two]
    · intro x2 x3
      fin_cases x2 <;> fin_cases x3 <;>
        norm_num [Fin.sum_univ_two]
    · intro hcontra
      have h := congrFun hcontra (0, 0, 0)
      norm_num at h
  · intro b
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [Fin.sum_univ_four]
      fin_cases i <;> norm_num [Fin.ext_iff] <;> ring
    · rintro rfl i j
      norm_num
    · intro hb i j hij
      rw [if_neg hij]
      norm_num
      linarith

end NCG
