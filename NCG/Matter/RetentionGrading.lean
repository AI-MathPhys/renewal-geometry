/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Retention selectors and Dirac-pair retention (SM_emergence, Phase 1)

* `matrix_retention`, `matrix_retention_value` —
  `thm:matrix-retention-main`: all-branch retention
  (`A ≤ 1 - σ_j` for every occupied eigenbranch) holds exactly up to
  `A* = 1 - λ_max(Σ)`; for the protected spectrum `{±2/95}` the
  maximal faithful selector is `A* = 93/95`;
* `retention_9795_fails` — `corollary:failure-of-the-97-95-branch`:
  the selector `97/95` expels the branch with threshold `93/95`;
* `dirac_retention` — `thm:dirac-retention-main`: for the chirally
  odd block with pole equation `(z - A)² = |y|²`, retention of both
  signed branches below the upper edge again gives
  `A* = 1 - |y(1)| = 93/95` — full-pair retention does not rescue
  the selector.
-/

namespace NCG

/-! ## `thm:matrix-retention-main` -/

/-- `thm:matrix-retention-main` (abstract form): every occupied
eigenbranch `σ_j` is retained (`A ≤ 1 - σ_j`) iff the selector
respects the top of the spectrum, `A ≤ 1 - λ_max`.  Hence the
maximal all-branch-faithful selector is `A* = 1 - λ_max(Σ(1))`. -/
theorem matrix_retention (sigma : Finset ℝ) (hne : sigma.Nonempty)
    (A : ℝ) :
    (∀ s ∈ sigma, A ≤ 1 - s) ↔ A ≤ 1 - sigma.max' hne := by
  constructor
  · intro h
    exact h _ (sigma.max'_mem hne)
  · intro h s hs
    have := sigma.le_max' s hs
    linarith

/-- The protected spectrum `{2/95, -2/95}`: the retention maximum is
`A* = 1 - 2/95 = 93/95`. -/
theorem matrix_retention_value :
    (1 : ℝ) - ({2/95, -(2/95)} : Finset ℝ).max'
        (by simp) = 93/95 := by
  have hmax : ({2/95, -(2/95)} : Finset ℝ).max' (by simp) = 2/95 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]
      · rw [h]
        norm_num
    · apply Finset.le_max'
      simp
  rw [hmax]
  norm_num

/-- `corollary:failure-of-the-97-95-branch`: at `A = 97/95` the
branch with threshold `93/95` is expelled — `97/95` is incompatible
with simultaneous faithfulness and all-branch retention. -/
theorem retention_9795_fails : ¬((97:ℝ)/95 ≤ 93/95) := by
  norm_num

/-! ## `thm:dirac-retention-main` -/

/-- `thm:dirac-retention-main`: for the exactly-odd protected block,
the additive pole equation `(z - A)² = |y|²` has the two signed
branches `z± = A ± |y|`; both lie below the upper edge `1` iff
`A ≤ 1 - |y|`, so the maximal selector is again `A* = 1 - |y(1)|`
(for `|y(1)| = 2/95`, `A* = 93/95`) — full-pair retention does not
rescue the `97/95` selector. -/
theorem dirac_retention (A y : ℝ) :
    (A + |y| ≤ 1 ∧ A - |y| ≤ 1) ↔ A ≤ 1 - |y| := by
  constructor
  · intro ⟨h1, _⟩
    linarith
  · intro h
    have := abs_nonneg y
    exact ⟨by linarith, by linarith⟩

end NCG
