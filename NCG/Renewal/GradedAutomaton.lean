/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Operator.FibreDichotomy

/-!
# Graded finite-type automata and the fibre condition

Covers `prop:fibres-automata` and the per-class verification feeding
`cor:automatic-triples` from `manuscripts/lorentzian_emergence/lorentzian_emergence.tex`:

* `GradedAutomaton` — a graded labelled presentation of the
  predictive quotient: labelled transitions raise the depth grading
  by exactly one, with uniformly bounded backward branching;
* `GradedAutomaton.increment` — prepending a label raises `Λ_min` by
  exactly one, so the increment condition of `ass:fibres` holds with
  `C_σ = 1`;
* `GradedAutomaton.shift_bound` / `comm_bound` — the descended shifts
  are `ℓ²`-bounded with norm² at most the branching bound and the
  Dirac commutators are bounded with constant `B·1²` — the explicit
  constants of `ass:fibres`, feeding the spectral-triple pillars of
  `thm:triple` (class (A) of `cor:automatic-triples`);
* `depth_increment_of_add` / `monoid_constant_increment` — the
  general constant-increment lemma; with an additive grading it
  closes the increment half of `prop:fibres-monoid` (class (B)),
  where the shift adds a fixed generator of degree `deg a_σ`.
-/

namespace NCG

variable {Q : Type*} {E : Type*} [DecidableEq Q]

/-- **Proposition `prop:fibres-automata` (the presentation)**: a
graded labelled graph presenting the predictive quotient — labelled
transitions send `Q_R` to `Q_{R+1}` and the backward branching per
label is uniformly bounded. -/
structure GradedAutomaton (Q : Type*) (E : Type*)
    [DecidableEq Q] where
  /-- The depth grading `∂` (the class `Λ_min`). -/
  depth : Q → ℕ
  /-- The descended labelled transition `[w] ↦ [σw]`. -/
  step : E → Q → Q
  /-- Labelled edges raise the grading by exactly one. -/
  step_depth : ∀ σ q, depth (step σ q) = depth q + 1
  /-- The backward branching bound `B`. -/
  bound : ℕ
  /-- Uniformly bounded backward branching: at most `B` predecessors
  of any vertex under any label. -/
  back_bounded : ∀ (T : Finset Q) (σ : E) (y : Q),
    (T.filter fun x => step σ x = y).card ≤ bound

namespace GradedAutomaton

variable (A : GradedAutomaton Q E)

/-- The general constant-increment computation: a shift raising a
`ℕ`-grading by exactly `c` has real increment exactly `c`. -/
theorem depth_increment_of_add {L : Q → ℕ} {s : Q → Q} {c : ℕ}
    (h : ∀ q, L (s q) = L q + c) (q : Q) :
    ((L (s q) : ℝ)) - L q = c := by
  rw [h q]
  push_cast
  ring

/-- **`prop:fibres-automata` (unit increment)**: prepending a label
raises `Λ_min` by exactly one — `|Λ_min([σw]) − Λ_min([w])| = 1`, the
increment condition of `ass:fibres` with `C_σ = 1`. -/
theorem increment (σ : E) (q : Q) :
    |((A.depth (A.step σ q) : ℝ)) - A.depth q| = 1 := by
  rw [depth_increment_of_add (A.step_depth σ) q]
  norm_num

/-- **`prop:fibres-automata` (fibre bound, operator form)**: the
descended shift is `ℓ²`-bounded on the core with norm² at most the
backward branching bound `B`. -/
theorem shift_bound (σ : E) (f : Q →₀ ℂ) :
    l2normSq (shiftOp (A.step σ) f) ≤ (A.bound : ℝ) * l2normSq f :=
  l2normSq_shiftOp_le (A.step σ)
    (fun T y => A.back_bounded T σ y) f

/-- **`prop:fibres-automata` (commutator bound)**: the Dirac
commutator against the depth diagonal is `ℓ²`-bounded with the
explicit `ass:fibres` constant `B·1²` — class (A) of
`cor:automatic-triples` therefore carries the bounded-commutator
pillar of the predictive spectral triple. -/
theorem comm_bound (σ : E) (f : Q →₀ ℂ) :
    l2normSq ((diagOp (fun q => (A.depth q : ℂ)) ∘ₗ
        shiftOp (A.step σ)
      - shiftOp (A.step σ) ∘ₗ
        diagOp (fun q => (A.depth q : ℂ))) f)
      ≤ (A.bound : ℝ) * 1 ^ 2 * l2normSq f := by
  refine l2normSq_comm_le _ _ 1
    (fun T y => A.back_bounded T σ y) (fun q => ?_) f
  rw [show ((A.depth (A.step σ q) : ℂ)) - (A.depth q : ℂ)
      = (((A.depth (A.step σ q) : ℝ) - A.depth q : ℝ) : ℂ) from by
    push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, A.increment σ q]

end GradedAutomaton

/-- **`prop:fibres-monoid` (constant increment, class (B) of
`cor:automatic-triples`)**: under an additive grading, the shift by a
fixed monoid generator has constant increment equal to the
generator's degree — `Λ_min([σw]) − Λ_min([w]) = deg a_σ`,
completing `ass:fibres` for finitely generated cancellative
commuting monoids (the fibre bound `≤ 1` is
`RenewalMemory.shift_injective`). -/
theorem monoid_constant_increment {M : Type*} [AddCommMonoid M]
    (deg : M →+ ℕ) (a q : M) :
    ((deg (a + q) : ℝ)) - deg q = deg a := by
  rw [map_add]
  push_cast
  ring

end NCG
