/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Objectivity from redundant records
  (`prop:objectivity`, wavefunction)

If a sector label is redundantly encoded in `N` fragments, each
inferring the label correctly except on an event of probability at
most `ε`, then all observers agree on the sector except on an event
of probability at most `Nε` — agreement with probability approaching
one as the per-fragment error decays with growing redundancy:

* `union_bound` — the finite union bound
  `μ(∃ k, failure_k) ≤ Σ_k μ(failure_k)`;
* `redundant_agreement` — `μ(all fragments agree) ≥ 1 - Nε`.

The identification of the fragment-inference failure events inside
the quantum record model (spectrum-broadcast structure) is the
declared modeling step.
-/

namespace NCG

/-- Finite union bound: the probability that some fragment fails is
at most the sum of the individual failure probabilities. -/
theorem union_bound {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hnn : ∀ w, 0 ≤ p w)
    {N : ℕ} (bad : Fin N → Ω → Prop) [∀ k w, Decidable (bad k w)] :
    (∑ w ∈ Finset.univ.filter (fun w => ∃ k, bad k w), p w)
      ≤ ∑ k, ∑ w ∈ Finset.univ.filter (fun w => bad k w), p w := by
  classical
  have hpoint : ∀ w ∈ Finset.univ.filter (fun w => ∃ k, bad k w),
      p w ≤ ∑ k, if bad k w then p w else 0 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨k0, hk0⟩ := hw.2
    calc p w = if bad k0 w then p w else 0 := by rw [if_pos hk0]
    _ ≤ ∑ k, if bad k w then p w else 0 := by
        apply Finset.single_le_sum (f := fun k =>
          if bad k w then p w else 0)
          (fun k _ => by
            by_cases hb : bad k w
            · rw [if_pos hb]
              exact hnn w
            · rw [if_neg hb])
          (Finset.mem_univ k0)
  calc (∑ w ∈ Finset.univ.filter (fun w => ∃ k, bad k w), p w)
      ≤ ∑ w ∈ Finset.univ.filter (fun w => ∃ k, bad k w),
          ∑ k, if bad k w then p w else 0 :=
        Finset.sum_le_sum hpoint
  _ ≤ ∑ w, ∑ k, if bad k w then p w else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro w _ _
        apply Finset.sum_nonneg
        intro k _
        by_cases hb : bad k w
        · rw [if_pos hb]
          exact hnn w
        · rw [if_neg hb]
  _ = ∑ k, ∑ w, if bad k w then p w else 0 := Finset.sum_comm
  _ = ∑ k, ∑ w ∈ Finset.univ.filter (fun w => bad k w), p w := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_filter]

/-- `prop:objectivity` (quantitative core): if each of `N` fragments
infers the true sector label except on probability at most `ε`, then
all observers condition on the same sector except on probability at
most `Nε` — agreement with probability approaching one as redundancy
grows with decaying per-fragment error. -/
theorem redundant_agreement {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hnn : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1)
    {N : ℕ} {I : Type*} [DecidableEq I]
    (infer : Fin N → Ω → I) (label : Ω → I)
    (eps : ℝ)
    (herr : ∀ k, (∑ w ∈ Finset.univ.filter
      (fun w => infer k w ≠ label w), p w) ≤ eps) :
    1 - N * eps ≤ ∑ w ∈ Finset.univ.filter
      (fun w => ∀ k, infer k w = label w), p w := by
  classical
  have hub := union_bound p hnn (fun k w => infer k w ≠ label w)
  have hcompl : Finset.univ.filter
        (fun w => ¬ ∀ k, infer k w = label w)
      = Finset.univ.filter (fun w => ∃ k, infer k w ≠ label w) := by
    apply Finset.filter_congr
    intro w _
    simp [not_forall]
  have hsplit : (∑ w ∈ Finset.univ.filter
        (fun w => ∀ k, infer k w = label w), p w)
      + (∑ w ∈ Finset.univ.filter
        (fun w => ∃ k, infer k w ≠ label w), p w) = 1 := by
    rw [← hsum, ← hcompl]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun w => ∀ k, infer k w = label w) p
  have hbadsum : (∑ w ∈ Finset.univ.filter
      (fun w => ∃ k, infer k w ≠ label w), p w) ≤ N * eps := by
    calc (∑ w ∈ Finset.univ.filter
        (fun w => ∃ k, infer k w ≠ label w), p w)
        ≤ ∑ k, ∑ w ∈ Finset.univ.filter
            (fun w => infer k w ≠ label w), p w := hub
    _ ≤ ∑ _k : Fin N, eps := Finset.sum_le_sum fun k _ => herr k
    _ = N * eps := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  linarith [hsplit, hbadsum]

end NCG
