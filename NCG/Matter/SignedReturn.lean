/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Signed return parity and the minimal signed visible return
  (`lem:signed-return-parity-consolidated`,
   `thm:minimal-signed-return-consolidated`, SM_emergence)

On the canonical anti-balanced double cover of `K₄` every traversed
edge flips the sheet, so the net sheet change after `n` steps is
`(-1)ⁿ`:

* `signed_sheet_return_iff_even` — a path returns to its initial
  signed sheet iff its length is even;
* `nb_return_length_one` / `nb_return_length_two` — nonbacktracking
  paths of length one or two cannot return to the oriented port
  `e₀ = (0,1)`;
* `nb_return_length_three` — the length-three returns are exactly
  the two triangular cycles (through `2` or `3`), which land on the
  opposite sheet since `3` is odd;
* `nb_return_length_four` — the length-four returns are exactly the
  two displayed Hamiltonian cycles `γ₋ : 0→1→2→3→0` and
  `γ₊ : 0→1→3→2→0`, so the minimal same-port, same-sheet return
  length is `n_vis = 4` with exactly two primitive histories.

Nonbacktracking on `K₄`: from the oriented edge `(x, y)` the next
vertex `z` satisfies `z ≠ x` (no backtrack) and `z ≠ y` (no loop).
-/

namespace NCG

/-- `lem:signed-return-parity-consolidated`: on the anti-balanced
double cover every edge flips the sheet, so a length-`n` path
returns to its initial signed sheet iff `n` is even. -/
theorem signed_sheet_return_iff_even (n : ℕ) :
    ((-1 : ℤ) ^ n = 1) ↔ Even n :=
  neg_one_pow_eq_one_iff_even (by norm_num)

/-- No nonbacktracking return to the oriented port `(0,1)` in one
step. -/
theorem nb_return_length_one :
    ¬∃ a2 : Fin 4, (a2 ≠ 0 ∧ a2 ≠ 1)
      ∧ ((1 : Fin 4), a2) = ((0 : Fin 4), (1 : Fin 4)) := by
  decide

/-- No nonbacktracking return to the oriented port `(0,1)` in two
steps. -/
theorem nb_return_length_two :
    ¬∃ a2 a3 : Fin 4,
      ((a2 ≠ 0 ∧ a2 ≠ 1) ∧ (a3 ≠ 1 ∧ a3 ≠ a2))
        ∧ (a2, a3) = ((0 : Fin 4), (1 : Fin 4)) := by
  decide

/-- The nonbacktracking length-three returns to `(0,1)` are exactly
the two triangular cycles, through `2` or through `3`.  Both have
odd length, hence land on the opposite signed sheet. -/
theorem nb_return_length_three (a2 a3 a4 : Fin 4) :
    ((a2 ≠ 0 ∧ a2 ≠ 1) ∧ (a3 ≠ 1 ∧ a3 ≠ a2)
        ∧ (a4 ≠ a2 ∧ a4 ≠ a3))
      ∧ (a3, a4) = ((0 : Fin 4), (1 : Fin 4))
      ↔ (a2 = 2 ∨ a2 = 3) ∧ a3 = 0 ∧ a4 = 1 := by
  decide +revert

/-- `thm:minimal-signed-return-consolidated`: the nonbacktracking
length-four returns to the oriented port `(0,1)` are exactly the
two Hamiltonian cycles `γ₋ : (a₂,a₃) = (2,3)` and
`γ₊ : (a₂,a₃) = (3,2)`.  With the parity lemma this makes
`n_vis = 4` the minimal same-port, same-sheet return length, with
exactly the two displayed primitive histories. -/
theorem nb_return_length_four (a2 a3 a4 a5 : Fin 4) :
    ((a2 ≠ 0 ∧ a2 ≠ 1) ∧ (a3 ≠ 1 ∧ a3 ≠ a2)
        ∧ (a4 ≠ a2 ∧ a4 ≠ a3) ∧ (a5 ≠ a3 ∧ a5 ≠ a4))
      ∧ (a4, a5) = ((0 : Fin 4), (1 : Fin 4))
      ↔ ((a2 = 2 ∧ a3 = 3) ∨ (a2 = 3 ∧ a3 = 2))
        ∧ a4 = 0 ∧ a5 = 1 := by
  decide +revert

end NCG
