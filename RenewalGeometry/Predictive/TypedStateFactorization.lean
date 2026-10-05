/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.TypedEventGrammar
import RenewalGeometry.Predictive.TypedFinitePredictionExact

/-!
# The derived predictive state machine and the state-path factorization
  (`cor:supp-derived-state-machine`, `eq:supp-state-factorization`,
  emergent-spacetime manuscript)

For a finite typed event grammar with conditional law `P`, the minimum predictive state space
is `Z^min_{X,x} = H_{X,x}/∼_X` (`ConditionalLaw.MinimalState`), with one-step weight
`κ_{X,a}([h]) = p_X(a | h)` (`ConditionalLaw.weight`, well defined on all of `Z^min`) and
transition `T_{X,a}([h]) = [h a]` (`ConditionalLaw.transition`).

**Positive-probability-branch reading.**  `T_{X,a}([h]) = [h a]` only makes sense when `h a`
is a history, i.e. on the branch `κ_{X,a}([h]) > 0` (otherwise `h a` need not be reachable and
`h ∼ h'` need not give `h a ∼ h' a`).  We therefore run the state path in `Option Z^min`:
`z_j = T_{X,a_j}(z_{j-1})` while `κ_{X,a_j}(z_{j-1}) > 0`, and the path *stops* (`none`) at the
first vanishing weight; the factor attached to a stopped state is `0`.  With this convention the
product formula `eq:supp-state-factorization` holds for **every** typed future word, and on
positive-probability words the path never stops.

* `TypedStateMachine.transition_eq_of_project_eq`: `T_{X,a}` is well defined on classes
  (any two representatives give the same `[h a]`), on the positive-probability branch.
* `TypedStateMachine.statePath`, `TypedStateMachine.stateFactors`: the state path
  `z_0 = q_X(h)`, `z_j = T_{X,a_j}(z_{j-1})`, and the list of factors `κ_{X,a_j}(z_{j-1})`.
* `TypedStateMachine.statePath_spec`: along a positive-probability word the path is the
  class of the extended history, `z_k = q_X(h w)`; along a null word it has stopped.
* `TypedStateMachine.state_factorization` (`eq:supp-state-factorization`):
  `p_X(w | h) = ∏_{j=1}^k κ_{X,a_j}(z_{j-1})`.
-/

namespace RenewalGeometry
namespace TypedStateMachine

open FiniteTypedEventGrammar FiniteTypedEventGrammar.ConditionalLaw

variable {G : FiniteTypedEventGrammar} (P : G.ConditionalLaw)

/-- The chain law is nonnegative. -/
theorem wordProb_nonneg' {s x : G.CutType} (h : TypedWord G.Letter s x) :
    ∀ {z : G.CutType} (w : TypedWord G.Letter x z), 0 ≤ P.wordProb h w
  | _, .nil _ => by simp
  | _, .snoc w a => by
    rw [wordProb_snoc]
    exact mul_nonneg (wordProb_nonneg' h w) (P.prob_nonneg _ a)

/-- `T_{X,a}` is well defined on future-equivalence classes (positive-probability branch):
representatives of the same class give the same extended class `[h a] = [h' a]`. -/
theorem transition_eq_of_project_eq {x y : G.CutType} (a : G.Letter x y)
    {h h' : G.History x} (hh : P.project h = P.project h') (hpos : 0 < P.prob h.word a)
    (hpos' : 0 < P.prob h'.word a) :
    P.project (h.snoc a (P.admissible_of_prob_pos hpos))
      = P.project (h'.snoc a (P.admissible_of_prob_pos hpos')) := by
  rw [project_eq_iff] at hh ⊢
  exact P.futureEquivalent_snoc hh a hpos

/-- `κ_{X,a}` is well defined on future-equivalence classes. -/
theorem weight_eq_of_project_eq {x y : G.CutType} (a : G.Letter x y)
    {h h' : G.History x} (hh : P.project h = P.project h') :
    P.prob h.word a = P.prob h'.word a := by
  rw [← weight_project, ← weight_project, hh]

/-- One step of the partial state machine on `Option Z^min`: apply `T_{X,a}` on the
positive-probability branch, stop otherwise. -/
noncomputable def step {x y : G.CutType} (a : G.Letter x y) :
    Option (P.MinimalState x) → Option (P.MinimalState y)
  | none => none
  | some z => if hz : 0 < P.weight a z then some (P.transition a z hz) else none

/-- The factor `κ_{X,a}(z)` attached to a (possibly stopped) state; `0` once stopped. -/
def factor {x y : G.CutType} (a : G.Letter x y) : Option (P.MinimalState x) → ℝ
  | none => 0
  | some z => P.weight a z

/-- The state path `z_0, z_j = T_{X,a_j}(z_{j-1})` along a typed future word, evaluated at
the end of the word. -/
noncomputable def statePath {x : G.CutType} (z₀ : Option (P.MinimalState x)) :
    ∀ {z : G.CutType}, TypedWord G.Letter x z → Option (P.MinimalState z)
  | _, .nil _ => z₀
  | _, .snoc w a => step P a (statePath z₀ w)

/-- The ordered list of factors `κ_{X,a_1}(z_0), …, κ_{X,a_k}(z_{k-1})`. -/
noncomputable def stateFactors {x : G.CutType} (z₀ : Option (P.MinimalState x)) :
    ∀ {z : G.CutType}, TypedWord G.Letter x z → List ℝ
  | _, .nil _ => []
  | _, .snoc w a => stateFactors z₀ w ++ [factor P a (statePath P z₀ w)]

/-- The length of a typed word. -/
def wordLength {O : Type} {Letter : O → O → Type} {x : O} :
    ∀ {z : O}, TypedWord Letter x z → ℕ
  | _, .nil _ => 0
  | _, .snoc w _ => wordLength w + 1

/-- One factor per letter. -/
theorem stateFactors_length {x : G.CutType} (z₀ : Option (P.MinimalState x)) :
    ∀ {z : G.CutType} (w : TypedWord G.Letter x z),
      (stateFactors P z₀ w).length = wordLength w
  | _, .nil _ => rfl
  | _, .snoc w a => by
    simp [stateFactors, wordLength, stateFactors_length z₀ w]

/-- The history `h w` obtained by extending `h` along a reachable continuation. -/
def extendHistory {x z : G.CutType} (h : G.History x) (w : TypedWord G.Letter x z)
    (hr : G.Reachable (h.word.append w)) : G.History z :=
  ⟨h.1, ⟨h.word.append w, hr⟩⟩

/-- **State-path specification.**  Along a positive-probability word the path never stops and
ends at the class of the extended history, `z_k = q_X(h w)`; along a null word it has stopped. -/
theorem statePath_spec {x : G.CutType} (h : G.History x) :
    ∀ {z : G.CutType} (w : TypedWord G.Letter x z),
      (0 < P.wordProb h.word w → ∃ hr : G.Reachable (h.word.append w),
          statePath P (some (P.project h)) w = some (P.project (extendHistory h w hr))) ∧
      (P.wordProb h.word w = 0 → statePath P (some (P.project h)) w = none)
  | _, .nil _ => by
    refine ⟨fun _ => ⟨by simpa using h.reachable, ?_⟩, fun h0 => by simp at h0⟩
    simp only [statePath]
    congr 1
  | _, .snoc w a => by
    obtain ⟨ihpos, ihzero⟩ := statePath_spec h w
    rcases (wordProb_nonneg' P h.word w).lt_or_eq with hw | hw
    · obtain ⟨hr, hpath⟩ := ihpos hw
      set hw' := extendHistory h w hr with hhw'
      have hweight : P.weight a (P.project hw') = P.prob (h.word.append w) a := rfl
      rcases (P.prob_nonneg (h.word.append w) a).lt_or_eq with ha | ha
      · -- positive branch: the path continues with `T_{X,a}`
        have hprod : 0 < P.wordProb h.word (w.snoc a) := by
          rw [wordProb_snoc]; exact mul_pos hw ha
        have hpos' : 0 < P.prob hw'.word a := ha
        refine ⟨fun _ => ⟨?_, ?_⟩, fun h0 => absurd h0 hprod.ne'⟩
        · rw [TypedWord.append_snoc]; exact P.admissible_of_prob_pos ha
        · simp only [statePath, hpath, step]
          rw [dif_pos (by rw [hweight]; exact ha)]
          congr 1
          rw [transition_project P a hw' hpos']
          rfl
      · -- the letter has probability zero: the path stops
        have hprod : P.wordProb h.word (w.snoc a) = 0 := by
          rw [wordProb_snoc, ← ha, mul_zero]
        refine ⟨fun hp => absurd hprod hp.ne', fun _ => ?_⟩
        simp only [statePath, hpath, step]
        rw [dif_neg (by rw [hweight, ← ha]; exact lt_irrefl 0)]
    · -- the prefix already has probability zero: the path has stopped
      have hprod : P.wordProb h.word (w.snoc a) = 0 := by
        rw [wordProb_snoc, ← hw, zero_mul]
      refine ⟨fun hp => absurd hprod hp.ne', fun _ => ?_⟩
      simp only [statePath, ihzero hw.symm, step]

/-- **`eq:supp-state-factorization`** (`cor:supp-derived-state-machine`): for a history `h`
and a typed future word `w = a_1 ⋯ a_k`, with `z_0 = q_X(h)` and `z_j = T_{X,a_j}(z_{j-1})`
(positive-probability-branch convention: the path stops, and contributes the factor `0`, at
the first vanishing weight),
`p_X(w | h) = ∏_{j=1}^k κ_{X,a_j}(z_{j-1})`. -/
theorem state_factorization {x : G.CutType} (h : G.History x) :
    ∀ {z : G.CutType} (w : TypedWord G.Letter x z),
      P.wordProb h.word w = (stateFactors P (some (P.project h)) w).prod
  | _, .nil _ => by simp [stateFactors]
  | _, .snoc w a => by
    rw [wordProb_snoc, stateFactors, List.prod_append, List.prod_singleton,
      ← state_factorization h w]
    rcases (wordProb_nonneg' P h.word w).lt_or_eq with hw | hw
    · obtain ⟨hr, hpath⟩ := (statePath_spec P h w).1 hw
      rw [hpath]
      rfl
    · rw [← hw, zero_mul, zero_mul]

/-- On a positive-probability word every factor of the product is a genuine positive weight
`κ_{X,a_j}(z_{j-1})` of a non-stopped state. -/
theorem stateFactors_pos {x : G.CutType} (h : G.History x) {z : G.CutType}
    (w : TypedWord G.Letter x z) (hw : 0 < P.wordProb h.word w) :
    ∀ c ∈ stateFactors P (some (P.project h)) w, 0 < c := by
  induction w with
  | nil => simp [stateFactors]
  | snoc w a ih =>
    have hw0 : 0 < P.wordProb h.word w := by
      rcases (wordProb_nonneg' P h.word w).lt_or_eq with h1 | h1
      · exact h1
      · rw [wordProb_snoc, ← h1, zero_mul] at hw
        exact absurd hw (lt_irrefl 0)
    have ha : 0 < P.prob (h.word.append w) a := by
      rcases (P.prob_nonneg (h.word.append w) a).lt_or_eq with h1 | h1
      · exact h1
      · rw [wordProb_snoc, ← h1, mul_zero] at hw
        exact absurd hw (lt_irrefl 0)
    intro c hc
    rw [stateFactors, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih hw0 c hc
    · rw [List.mem_singleton] at hc
      obtain ⟨hr, hpath⟩ := (statePath_spec P h w).1 hw0
      rw [hc, hpath]
      exact ha

/-- The complete corollary: `κ_{X,a}` and `T_{X,a}` are well defined on `Z^min`
(the latter on the positive-probability branch), and every future-word probability is the
product of the one-step weights along the derived state path. -/
theorem derived_state_machine :
    (∀ {x y : G.CutType} (a : G.Letter x y) {h h' : G.History x},
        P.project h = P.project h' → P.prob h.word a = P.prob h'.word a) ∧
    (∀ {x y : G.CutType} (a : G.Letter x y) {h h' : G.History x}
        (_hh : P.project h = P.project h') (hpos : 0 < P.prob h.word a)
        (hpos' : 0 < P.prob h'.word a),
        P.project (h.snoc a (P.admissible_of_prob_pos hpos))
          = P.project (h'.snoc a (P.admissible_of_prob_pos hpos'))) ∧
    (∀ {x z : G.CutType} (h : G.History x) (w : TypedWord G.Letter x z),
        P.wordProb h.word w = (stateFactors P (some (P.project h)) w).prod) :=
  ⟨fun a _ _ hh => weight_eq_of_project_eq P a hh,
    fun a _ _ hh hpos hpos' => transition_eq_of_project_eq P a hh hpos hpos',
    fun h w => state_factorization P h w⟩

/-- Non-vacuity on a non-trivial law (the binary renewal law of
`TypedFinitePredictionCountermodel`, renewal probability `1/(n+2)` at age `n`): along the word
`(nonrenewal, renewal)` from the empty history, the product of the one-step weights along the
derived state path is `(1 - 1/2)·(1/3) = 1/6`. -/
example :
    (stateFactors TypedFinitePredictionCountermodel.law
      (some (TypedFinitePredictionCountermodel.law.project
        (TypedFinitePredictionCountermodel.nonrenewalHistory 0)))
      (((TypedWord.nil ()).snoc (z := ()) (false : Bool)).snoc (z := ()) (true : Bool) :
        TypedWord TypedFinitePredictionCountermodel.grammar.Letter () ())).prod = 1 / 6 := by
  rw [← state_factorization, wordProb_snoc, wordProb_snoc, wordProb_nil]
  simp [TypedFinitePredictionCountermodel.law, TypedFinitePredictionCountermodel.age,
    TypedFinitePredictionCountermodel.renewalProb,
    TypedFinitePredictionCountermodel.nonrenewalHistory,
    TypedFinitePredictionCountermodel.nonrenewals, History.word, TypedWord.append]
  norm_num

end TypedStateMachine
end RenewalGeometry
