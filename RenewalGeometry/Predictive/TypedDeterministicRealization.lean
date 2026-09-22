/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cut-typed deterministic predictive realizations
  (`def:supp-predictive-realization`, emergent-spacetime manuscript)

The manuscript definition: a *reachable deterministic predictive realization*
of a cut-typed predictive law consists of finite state sets `S_{X,x}` (one per
cut type `x`), history maps `s_x : H_{X,x} → S_{X,x}`, partial updates
`u_a : S_{X,x} ⇀ S_{X,y}` for each letter `a : x → y`, and branch functions
`r_a : S_{X,x} → [0,1]`, such that on every reachable (occurring) branch

  `s_y(ha) = u_a(s_x(h))`,  `p_X(a | h) = r_a(s_x(h))`.

* `RenewalGeometry.TypedPredictiveLaw` — the input datum: the cut-typed
  one-step branch law `p_X(a | h)` with deterministic history extension
  `h ↦ ha`;
* `RenewalGeometry.TypedDeterministicRealization` — the realization itself,
  with finiteness of every state set, `Option`-valued (partial) updates, the
  `[0,1]` bound on the branch functions, reachability (every state is hit by
  some history) and the two displayed intertwining identities
  (`eq:supp-realization`), the update identity on every occurring branch.

The untyped variant with total updates and an extra future-law field is
`RenewalGeometry.DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization`;
this file supplies the literally typed object of the definition. -/

universe u v w

namespace RenewalGeometry

/-- The cut-typed one-step predictive law: histories `H_{X,x}` of cut type
`x`, letters `a : x → y`, deterministic extension `h ↦ ha : H_{X,y}` and the
branch law `p_X(a | h)` (input datum of `def:supp-predictive-realization`). -/
structure TypedPredictiveLaw (Cut : Type u) (History : Cut → Type v)
    (Letter : Cut → Cut → Type w) where
  /-- deterministic history extension `h ↦ ha` -/
  step : ∀ {x y : Cut}, History x → Letter x y → History y
  /-- the one-step branch law `p_X(a | h)` -/
  branch : ∀ {x y : Cut}, History x → Letter x y → ℝ

/-- **Definition `def:supp-predictive-realization`**: a reachable deterministic
predictive realization of the cut-typed law `P` on the state sets `State x`. -/
structure TypedDeterministicRealization {Cut : Type u} {History : Cut → Type v}
    {Letter : Cut → Cut → Type w}
    (P : TypedPredictiveLaw Cut History Letter) (State : Cut → Type*) where
  /-- every state set `S_{X,x}` is finite -/
  finite : ∀ x, Finite (State x)
  /-- the history maps `s_x : H_{X,x} → S_{X,x}` -/
  stateOf : ∀ {x : Cut}, History x → State x
  /-- the partial updates `u_a : S_{X,x} ⇀ S_{X,y}` -/
  update : ∀ {x y : Cut}, Letter x y → State x → Option (State y)
  /-- the branch functions `r_a : S_{X,x} → [0,1]` -/
  rate : ∀ {x y : Cut}, Letter x y → State x → ℝ
  rate_nonneg : ∀ {x y : Cut} (a : Letter x y) (s : State x), 0 ≤ rate a s
  rate_le_one : ∀ {x y : Cut} (a : Letter x y) (s : State x), rate a s ≤ 1
  /-- reachability: every state is the image of some history -/
  reachable : ∀ x : Cut, Function.Surjective (stateOf (x := x))
  /-- `s_y(ha) = u_a(s_x(h))` on every occurring branch -/
  state_step : ∀ {x y : Cut} (h : History x) (a : Letter x y),
    P.branch h a ≠ 0 → update a (stateOf h) = some (stateOf (P.step h a))
  /-- `p_X(a | h) = r_a(s_x(h))` -/
  branch_factor : ∀ {x y : Cut} (h : History x) (a : Letter x y),
    P.branch h a = rate a (stateOf h)

namespace TypedDeterministicRealization

variable {Cut : Type u} {History : Cut → Type v} {Letter : Cut → Cut → Type w}
  {P : TypedPredictiveLaw Cut History Letter} {State : Cut → Type*}
  (R : TypedDeterministicRealization P State)

/-- On an occurring branch the partial update is defined
(`def:supp-predictive-realization`). -/
theorem update_isSome_of_occurs {x y : Cut} (h : History x) (a : Letter x y)
    (ha : P.branch h a ≠ 0) : (R.update a (R.stateOf h)).isSome := by
  rw [R.state_step h a ha]
  rfl

/-- The branch function at a reachable state is the branch law of any history
representing that state (`def:supp-predictive-realization`). -/
theorem rate_eq_branch {x y : Cut} (s : State x) (a : Letter x y) :
    ∃ h : History x, R.stateOf h = s ∧ R.rate a s = P.branch h a := by
  obtain ⟨h, rfl⟩ := R.reachable x s
  exact ⟨h, rfl, (R.branch_factor h a).symm⟩

/-- Histories mapped to the same state have the same one-step branch law
(`def:supp-predictive-realization`). -/
theorem branch_eq_of_stateOf_eq {x y : Cut} {h h' : History x}
    (hs : R.stateOf h = R.stateOf h') (a : Letter x y) :
    P.branch h a = P.branch h' a := by
  rw [R.branch_factor h a, R.branch_factor h' a, hs]

end TypedDeterministicRealization

end RenewalGeometry
-- AXIOMCHECK
#print axioms RenewalGeometry.TypedDeterministicRealization.update_isSome_of_occurs
#print axioms RenewalGeometry.TypedDeterministicRealization.rate_eq_branch
#print axioms RenewalGeometry.TypedDeterministicRealization.branch_eq_of_stateOf_eq
