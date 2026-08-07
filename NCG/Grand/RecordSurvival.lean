/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandNullIdeal

/-!
# Record-survival theorem
  (`thm:record-survival`, Gran-Tensor manuscript)

* `nullSubmodule`: the contextual null coefficients — vanishing
  future-Gram expectation in every two-sided word context — as a
  submodule of the history algebra (the linear part of the
  proved ideal lemma `contextual_null_ideal`).
* `record_survival`: in the future quotient
  `𝒜^hist = 𝒜^proc/𝒩^fut`: (S2) a record projection survives
  (nonzero class) exactly when some contextual Read fails the
  null test on it, and (S1) two protected record values remain
  distinct exactly when some contextual Read separates their
  difference.

Rendering disclosed: writers attached to nonzero branches (S3)
survive by the same criterion applied to the writer coefficient,
and the subalgebra clause (S4) is the multiplicativity of the
quotient supplied by the two-sided-ideal property of
`contextual_null_ideal` — both are the manuscript's bookkeeping
over the criteria proved here.
-/

open Matrix

namespace NCG

/-- The contextual null coefficients form a submodule (linear
part of `contextual_null_ideal`). -/
def nullSubmodule {n : Type*} [Fintype n] (G : Matrix n n ℂ) :
    Submodule ℂ (Matrix n n ℂ) where
  carrier := {a | ∀ x y : Matrix n n ℂ,
    (G * (x * a * y)).trace = (0 : ℂ)}
  zero_mem' := by
    intro x y
    simp
  add_mem' := by
    intro a b ha hb x y
    rw [show x * (a + b) * y = x * a * y + x * b * y from by
      rw [Matrix.mul_add, Matrix.add_mul]]
    rw [Matrix.mul_add, Matrix.trace_add, ha x y, hb x y,
      add_zero]
  smul_mem' := by
    intro c a ha x y
    rw [show x * (c • a) * y = c • (x * a * y) from by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    rw [Matrix.mul_smul, Matrix.trace_smul, ha x y, smul_zero]

/-- `thm:record-survival`: survival and distinctness in the
future quotient are exactly the failure of the contextual null
tests. -/
theorem record_survival {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) :
    (∀ P : Matrix n n ℂ,
      (Submodule.Quotient.mk P :
          Matrix n n ℂ ⧸ nullSubmodule G) ≠ 0
        ↔ ∃ x y, (G * (x * P * y)).trace ≠ 0)
    ∧ (∀ P Q : Matrix n n ℂ,
      (Submodule.Quotient.mk P :
          Matrix n n ℂ ⧸ nullSubmodule G)
          ≠ Submodule.Quotient.mk Q
        ↔ ∃ x y, (G * (x * (P - Q) * y)).trace ≠ 0) := by
  constructor
  · intro P
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      by_contra hall
      apply h
      intro x y
      by_contra hxy
      exact hall ⟨x, y, hxy⟩
    · rintro ⟨x, y, hxy⟩ hmem
      exact hxy (hmem x y)
  · intro P Q
    rw [Ne, Submodule.Quotient.eq]
    constructor
    · intro h
      by_contra hall
      apply h
      intro x y
      by_contra hxy
      exact hall ⟨x, y, hxy⟩
    · rintro ⟨x, y, hxy⟩ hmem
      exact hxy (hmem x y)

end NCG
