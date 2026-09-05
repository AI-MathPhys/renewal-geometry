/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.ConnectedGram

/-!
# The Klein four-group characters on the generation carrier
(SM_emergence, Phase 2)

The `V₄`/`S₄` representation layer in its diagonalized (character)
form:

* `commute_separating_family_diag` — the general rigidity: an
  operator commuting with a family of diagonal operators whose joint
  eigenvalue patterns separate indices is itself diagonal;
* `kleinK1`, `kleinK2`, `klein_separating` —
  `proposition:klein-decomposition-of-the-carrier` (character form):
  the three joint eigenvalue patterns `(+,-)`, `(-,+)`, `(-,-)` of
  the two commuting Klein involutions on the rank-three carrier are
  distinct nontrivial characters, and they separate the three lines;
* `klein_equivariant_diagonal`, `v4_commutative_trap` —
  `thm:v4-commutative-trap-current` (completed in the character
  basis): every endomorphism commuting with the Klein involutions is
  diagonal in the three character lines, so any two such
  endomorphisms commute — a strictly democratic `V₄`-equivariant
  inventory satisfies `[Y_uY_u†, Y_dY_d†] = 0` and cannot produce
  CKM mixing or physical quark CP.
-/

namespace NCG

open Matrix

/-- **Separating-family rigidity**: an operator commuting with a
family of diagonals whose joint eigenvalue patterns separate indices
is diagonal. -/
theorem commute_separating_family_diag {n ι : Type*} [Fintype n]
    [DecidableEq n] (d : ι → n → ℂ) (X : Matrix n n ℂ)
    (hX : ∀ g, X * Matrix.diagonal (d g) = Matrix.diagonal (d g) * X)
    (hsep : ∀ i j : n, i ≠ j → ∃ g, d g i ≠ d g j) :
    X = Matrix.diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    obtain ⟨g, hg⟩ := hsep i j hij
    have h := congrFun (congrFun (hX g) i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h2 : X i j * (d g j - d g i) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3).symm hg

/-- The joint character pattern of the two Klein involutions on the
rank-three carrier: `g = 0 ↦ (+1,-1,-1)`, `g = 1 ↦ (-1,+1,-1)`. -/
def kleinPattern : Fin 2 → Fin 3 → ℂ := fun g i =>
  if (g.val = 0 ∧ i.val = 0) ∨ (g.val = 1 ∧ i.val = 1) then 1 else -1

/-- The first Klein involution on the rank-three carrier: character
pattern `(+1, -1, -1)`. -/
def kleinK1 : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (kleinPattern 0)

/-- The second Klein involution: character pattern `(-1, +1, -1)`. -/
def kleinK2 : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (kleinPattern 1)

/-- `proposition:klein-decomposition-of-the-carrier` (character
form): the joint eigenvalue patterns of the two Klein involutions
separate the three carrier lines — the three restricted characters
are distinct and nontrivial. -/
theorem klein_separating : ∀ i j : Fin 3, i ≠ j →
    ∃ g : Fin 2, kleinPattern g i ≠ kleinPattern g j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨0, by norm_num [kleinPattern]⟩
  · exact ⟨0, by norm_num [kleinPattern]⟩
  · exact ⟨0, by norm_num [kleinPattern]⟩
  · exact absurd rfl hij
  · exact ⟨1, by norm_num [kleinPattern]⟩
  · exact ⟨0, by norm_num [kleinPattern]⟩
  · exact ⟨1, by norm_num [kleinPattern]⟩
  · exact absurd rfl hij

/-- `thm:v4-commutative-trap-current` (equivariance step): every
endomorphism of the carrier commuting with the Klein involutions is
diagonal in the three character lines. -/
theorem klein_equivariant_diagonal (X : Matrix (Fin 3) (Fin 3) ℂ)
    (h1 : X * kleinK1 = kleinK1 * X) (h2 : X * kleinK2 = kleinK2 * X) :
    X = Matrix.diagonal (fun i => X i i) := by
  apply commute_separating_family_diag (d := kleinPattern)
  · intro g
    fin_cases g
    · exact h1
    · exact h2
  · exact klein_separating

/-- `thm:v4-commutative-trap-current` (**democratic commutative
trap**, completed): any two endomorphisms commuting with the Klein
involutions commute with each other — in particular
`[Y_uY_u†, Y_dY_d†] = 0` for a strictly democratic
`V₄`-equivariant inventory, which therefore cannot produce
nontrivial CKM mixing or physical quark CP. -/
theorem v4_commutative_trap (X Y : Matrix (Fin 3) (Fin 3) ℂ)
    (hX1 : X * kleinK1 = kleinK1 * X) (hX2 : X * kleinK2 = kleinK2 * X)
    (hY1 : Y * kleinK1 = kleinK1 * Y) (hY2 : Y * kleinK2 = kleinK2 * Y) :
    X * Y = Y * X := by
  rw [klein_equivariant_diagonal X hX1 hX2,
    klein_equivariant_diagonal Y hY1 hY2]
  exact diagonal_commute _ _

end NCG
