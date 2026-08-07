/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gran-Tensor master no-overstatement boundary
  (`prop:no-overstatement`, Gran-Tensor manuscript)

The sixteen boundary clauses as non-implication schemas over
realized witness models, in the style of the proved flagship
`master_no_overstatement`:

* entrance/ideal clauses (1): a finite process need not enter
  the coherent phase — witness assignment;
* shadow clause (2): degree-one data do not determine
  multiplication — `x² = y²` admits `1, -1` (the numeric core of
  the aliasing schema);
* dimension clause (3): the primitive algebra need not be only
  `M₄(ℂ)` — a premise flag does not force the target flag;
* marginal-identity clause (4): equality of marginal data does
  not prove source identity — witness `1, -1`;
* seed clauses (5)–(7): the determinant seed does not fix
  generation number, the six-state source carries no matter
  occurrence, unmarked moments do not determine a marked
  operator — schema witnesses;
* algebra clause (8): the premise leaves the identification of
  the spacetime and gauge algebras free;
* arithmetic clauses (9)–(11): transform dualities, saturation,
  and selectors do not supply contraction, PCJM12, or prime
  mass — bridge schemas with the hypothesis dropped;
* sector clauses (12)–(15): a finite gap, a harmonic projection,
  a large dimension, and scalar determinants do not close their
  continuum/algebraicity/resource/gluing problems — witness
  assignments;
* clause (16): nothing unresolved follows from universality
  alone — the conditional-bridge schema.

Rendering disclosed: the identification of each schema premise
with the corresponding manuscript certificate is the cited
firewall prose; the non-implications over the realized witness
models are what is proved.
-/

namespace NCG

/-- A premise flag does not force a conclusion flag — the
generic entrance/dimension/algebra/sector non-implication
schema, clauses (1), (3), (8), (12)–(15). -/
theorem gt_flag_non_implication :
    ¬(∀ m : Bool × Bool, m.1 = true → m.2 = true) := by
  intro h
  exact absurd (h (true, false) rfl) (by simp)

/-- Equal quadratic marginals do not force identity — the
numeric core of the shadow and marginal-identity clauses (2),
(4). -/
theorem gt_marginal_not_identity :
    ¬(∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y) := by
  intro h
  have := h 1 (-1) (by norm_num)
  norm_num at this

/-- The premise data leave the target datum free — generation
number, marked panels, and algebra identification, clauses
(5)–(7). -/
theorem gt_premise_leaves_free :
    ∀ p : Bool, ∃ m m' : Bool × Bool,
      m.1 = p ∧ m'.1 = p ∧ m.2 ≠ m'.2 := by
  intro p
  exact ⟨(p, true), (p, false), rfl, rfl, by simp⟩

/-- A conditional bridge proves nothing once its displayed
hypothesis is dropped — the arithmetic and universality clauses
(9)–(11), (16). -/
theorem gt_no_free_conclusion :
    ¬(∀ m : Bool × Bool, (m.1 = true → m.2 = true)
      → m.2 = true) := by
  intro h
  have := h (false, false) (by simp)
  simp at this

/-- `prop:no-overstatement` (Gran-Tensor): the sixteen-clause
boundary bundle over the realized witness schemas. -/
theorem gt_no_overstatement :
    (¬(∀ m : Bool × Bool, m.1 = true → m.2 = true))
    ∧ (¬(∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y))
    ∧ (∀ p : Bool, ∃ m m' : Bool × Bool,
        m.1 = p ∧ m'.1 = p ∧ m.2 ≠ m'.2)
    ∧ ¬(∀ m : Bool × Bool, (m.1 = true → m.2 = true)
        → m.2 = true) :=
  ⟨gt_flag_non_implication, gt_marginal_not_identity,
    gt_premise_leaves_free, gt_no_free_conclusion⟩

end NCG
