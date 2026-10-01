/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.TypedEventGrammarHorizon
import RenewalGeometry.Predictive.MinimalRecordPartitionRefinementExact

/-!
# Finite predictive reconstruction on a typed event grammar
(`prop:supp-finite-prediction`, emergent-spacetime manuscript)

All statements are about a conditional operational renewal law `P` on a finite typed event
grammar `G` (`FiniteTypedEventGrammar.ConditionalLaw`, `def:supp-event-grammar`,
`def:supp-operational-datum`) and its typed future congruence `∼_X`
(`def:supp-future-signature`).

* **Bisimulation principle.** `ConditionalLaw.TypedPredictionBisimulation` is a family of
  relations on same-type histories that preserves every one-letter probability and is
  stable under every positive-probability extension;
  `ConditionalLaw.futureEquivalent_of_typedPredictionBisimulation`: related histories are
  future equivalent (equality of every finite future), proved by induction on the future
  word using the chain rule.
* **Finite-horizon clause.** `FiniteHorizonTypedEventGrammar.typedFinitePrediction_horizon`:
  with the remaining horizon included in the cut type, the future quotient is finite at
  every cut type and is a right congruence on every positive-probability branch.
* **Finite presentations and partition refinement.**
  `ConditionalLaw.TypedFinitePresentation` is a reachable finite presentation of `P` with
  `m = card Record` records (cut type, history map, branch functions, partial updates on
  the positive-probability branch).  `TypedFinitePresentation.refineOut` /
  `refineUpdate` encode the refinement algorithm of the proof: blocks are initialized by
  cut type and branch probabilities, and each round additionally requires equal successor
  blocks for every positive-probability letter (zero-probability letters are totalized by
  the identity, which does not change the partition).
  `TypedFinitePresentation.typedFinitePrediction_refinement`: every strict round happens
  before round `m - 1`, every later round equals round `m - 1`, and round `m - 1`
  identifies two records exactly when they represent future-equivalent histories (the
  coarsest predictive partition); `stable_round_futureEquivalent`: any stable round is
  sufficient for equality of all finite futures.
* **Negative clause.** `TypedFinitePredictionCountermodel`: the binary renewal process
  whose next renewal after `n` consecutive nonrenewals has probability `1/(n+2)`, on a
  grammar with one cut type and the two-letter alphabet; it admits no horizon function and
  its future quotient is infinite.
-/

namespace RenewalGeometry

namespace FiniteTypedEventGrammar

namespace ConditionalLaw

variable {G : FiniteTypedEventGrammar} (P : G.ConditionalLaw)

/-- Chain-law probabilities are nonnegative. -/
theorem typedPrediction_wordProb_nonneg {s x z : G.CutType} (h : TypedWord G.Letter s x)
    (w : TypedWord G.Letter x z) : 0 ≤ P.wordProb h w := by
  induction w with
  | nil => simp
  | snoc w a ih =>
    rw [wordProb_snoc]
    exact mul_nonneg ih (P.prob_nonneg _ _)

/-- A positive-probability continuation of a reachable history is reachable. -/
theorem typedPrediction_reachable_append {s x z : G.CutType} (h : TypedWord G.Letter s x)
    (hr : G.Reachable h) (w : TypedWord G.Letter x z) (hw : 0 < P.wordProb h w) :
    G.Reachable (h.append w) := by
  induction w with
  | nil => simpa using hr
  | snoc w a ih =>
    rw [wordProb_snoc] at hw
    have h2 := P.prob_nonneg (h.append w) a
    have hpa : 0 < P.prob (h.append w) a := by
      refine lt_of_le_of_ne h2 (fun h0 => ?_)
      rw [← h0, mul_zero] at hw
      exact lt_irrefl _ hw
    rw [TypedWord.append_snoc]
    exact P.admissible_of_prob_pos hpa

/-- The history `h w` on the positive-probability branch of the future word `w`. -/
def typedPredictionExtend {x z : G.CutType} (h : G.History x) (w : TypedWord G.Letter x z)
    (hw : 0 < P.wordProb h.word w) : G.History z :=
  ⟨h.1, ⟨h.word.append w, P.typedPrediction_reachable_append h.word h.reachable w hw⟩⟩

/-- A typed prediction bisimulation: a relation on same-type histories preserving every
one-letter probability and stable under every positive-probability extension. -/
def TypedPredictionBisimulation
    (R : ∀ {x : G.CutType}, G.History x → G.History x → Prop) : Prop :=
  ∀ {x y : G.CutType} (h h' : G.History x), R h h' → ∀ a : G.Letter x y,
    P.prob h.word a = P.prob h'.word a ∧
    ∀ (hpos : 0 < P.prob h.word a) (hpos' : 0 < P.prob h'.word a),
      R (h.snoc a (P.admissible_of_prob_pos hpos)) (h'.snoc a (P.admissible_of_prob_pos hpos'))

/-- Bisimilar histories are future equivalent: induction on the future word with the chain
rule `eq:supp-chain-law` (`prop:supp-finite-prediction`, the step "at a fixed point,
induction on word length gives equality of every finite future"). -/
theorem futureEquivalent_of_typedPredictionBisimulation
    (R : ∀ {x : G.CutType}, G.History x → G.History x → Prop)
    (hR : P.TypedPredictionBisimulation R) {x : G.CutType} (h h' : G.History x)
    (hh : R h h') : P.FutureEquivalent h h' := by
  have key : ∀ {z : G.CutType} (w : TypedWord G.Letter x z),
      P.wordProb h.word w = P.wordProb h'.word w ∧
        ∀ (hp : 0 < P.wordProb h.word w) (hp' : 0 < P.wordProb h'.word w),
          R (P.typedPredictionExtend h w hp) (P.typedPredictionExtend h' w hp') := by
    intro z w
    induction w with
    | nil => exact ⟨rfl, fun _ _ => hh⟩
    | snoc w a ih =>
      obtain ⟨heq, hrel⟩ := ih
      by_cases h0 : P.wordProb h.word w = 0
      · have h0' : P.wordProb h'.word w = 0 := heq ▸ h0
        refine ⟨by rw [wordProb_snoc, wordProb_snoc, h0, h0', zero_mul, zero_mul], ?_⟩
        intro hp _
        rw [wordProb_snoc, h0, zero_mul] at hp
        exact absurd hp (lt_irrefl _)
      · have hp : 0 < P.wordProb h.word w :=
          lt_of_le_of_ne (P.typedPrediction_wordProb_nonneg _ _) (Ne.symm h0)
        have hp' : 0 < P.wordProb h'.word w := heq ▸ hp
        obtain ⟨hprob, hstep⟩ := hR _ _ (hrel hp hp') a
        have hprob' : P.prob (h.word.append w) a = P.prob (h'.word.append w) a := hprob
        refine ⟨by rw [wordProb_snoc, wordProb_snoc, heq, hprob'], ?_⟩
        intro hq hq'
        rw [wordProb_snoc] at hq hq'
        have ha : 0 < P.prob (h.word.append w) a := by
          refine lt_of_le_of_ne (P.prob_nonneg _ _) (fun hz => ?_)
          rw [← hz, mul_zero] at hq
          exact lt_irrefl _ hq
        have ha' : 0 < P.prob (h'.word.append w) a := hprob' ▸ ha
        exact hstep ha ha'
  intro z w
  exact (key w).1

/-- Future equivalence is itself a typed prediction bisimulation
(`thm:supp-right-congruence`). -/
theorem futureEquivalent_typedPredictionBisimulation :
    P.TypedPredictionBisimulation P.FutureEquivalent := by
  intro x y h h' hh a
  refine ⟨P.prob_eq_of_futureEquivalent hh a, fun hpos _ => ?_⟩
  exact P.futureEquivalent_snoc hh a hpos

end ConditionalLaw

end FiniteTypedEventGrammar

/-! ## Finite-horizon clause -/

namespace FiniteHorizonTypedEventGrammar

/-- **`prop:supp-finite-prediction`, finite-horizon clause.**  With the remaining horizon
included in the cut type (`FiniteHorizonTypedEventGrammar`, strictly decreasing along every
letter) and the complete bank of admissible continuations, the future quotient
`Z^min_{X,x} = H_{X,x}/∼_X` is finite at every cut type, and future equivalence is a right
congruence on every positive-probability branch, so `T_{X,a}[h] = [h a]` there. -/
theorem typedFinitePrediction_horizon (G : FiniteHorizonTypedEventGrammar)
    (P : G.toFiniteTypedEventGrammar.ConditionalLaw) :
    (∀ x, Finite (P.MinimalState x)) ∧
    (∀ {x y : G.CutType} {h h' : G.toFiniteTypedEventGrammar.History x}
      (hh : P.FutureEquivalent h h') (a : G.Letter x y) (hpos : 0 < P.prob h.word a),
      P.FutureEquivalent (h.snoc a (P.admissible_of_prob_pos hpos))
        (h'.snoc a (P.admissible_of_prob_pos (P.prob_eq_of_futureEquivalent hh a ▸ hpos)))) ∧
    (∀ {x y : G.CutType} (a : G.Letter x y) (h : G.toFiniteTypedEventGrammar.History x)
      (hpos : 0 < P.prob h.word a),
      P.transition a (P.project h) (by simpa using hpos)
        = P.project (h.snoc a (P.admissible_of_prob_pos hpos))) :=
  ⟨G.finite_minimalState P, fun hh a hpos => P.futureEquivalent_snoc hh a hpos,
    fun a h hpos => P.transition_project a h hpos⟩

end FiniteHorizonTypedEventGrammar

/-! ## Finite presentations and partition refinement -/

namespace FiniteTypedEventGrammar

namespace ConditionalLaw

variable {G : FiniteTypedEventGrammar}

/-- `prop:supp-finite-prediction`: a reachable finite presentation of the typed law `P` with
`m = card Record` records.  Each record carries its cut type; histories are mapped to records
of their own cut type, every record is reached, branch probabilities factor through branch
functions, and on every positive-probability branch the partial update sends the record of
`h` to the record of `h a` (`def:supp-predictive-realization`, `eq:supp-realization`). -/
structure TypedFinitePresentation (P : G.ConditionalLaw) where
  /-- the finite record set -/
  Record : Type
  [recordFintype : Fintype Record]
  /-- the cut type of a record -/
  cutType : Record → G.CutType
  /-- the history map `s` -/
  stateOf : ∀ {x : G.CutType}, G.History x → Record
  cutType_stateOf : ∀ {x : G.CutType} (h : G.History x), cutType (stateOf h) = x
  /-- reachability: every record represents some history -/
  reachable : ∀ r : Record, ∃ (x : G.CutType) (h : G.History x), stateOf h = r
  /-- the branch functions `r_a` -/
  rate : ∀ {x y : G.CutType}, G.Letter x y → Record → ℝ
  branch_factor : ∀ {x y : G.CutType} (h : G.History x) (a : G.Letter x y),
    P.prob h.word a = rate a (stateOf h)
  /-- the partial updates `u_a` -/
  update : ∀ {x y : G.CutType}, G.Letter x y → Record → Option Record
  state_step : ∀ {x y : G.CutType} (h : G.History x) (a : G.Letter x y)
    (hpos : 0 < P.prob h.word a),
    update a (stateOf h) = some (stateOf (h.snoc a (P.admissible_of_prob_pos hpos)))

namespace TypedFinitePresentation

attribute [instance] recordFintype

variable {P : G.ConditionalLaw} (S : TypedFinitePresentation P)

/-- Untyped letters `⟨x, y, a⟩`. -/
abbrev AnyLetter (G : FiniteTypedEventGrammar) : Type := Σ x y : G.CutType, G.Letter x y

open Classical in
/-- The immediate data used to initialize the partition: the cut type of a record and its
branch probabilities. -/
noncomputable def refineOut (r : S.Record) : AnyLetter G ⊕ G.CutType → ℝ
  | Sum.inl ⟨x, _, a⟩ => if S.cutType r = x then S.rate a r else 0
  | Sum.inr o => if S.cutType r = o then 1 else 0

open Classical in
/-- The successor used by the refinement rounds: the update along a positive-probability
letter of the record's own cut type; all other letters are totalized by the identity. -/
noncomputable def refineUpdate (A : AnyLetter G) (r : S.Record) : S.Record :=
  if S.cutType r = A.1 ∧ 0 < S.rate A.2.2 r then (S.update A.2.2 r).getD r else r

theorem refineOut_stateOf {x y : G.CutType} (h : G.History x) (a : G.Letter x y) :
    S.refineOut (S.stateOf h) (Sum.inl ⟨x, y, a⟩) = P.prob h.word a := by
  simp [refineOut, S.cutType_stateOf, S.branch_factor]

theorem refineUpdate_stateOf_pos {x y : G.CutType} (h : G.History x) (a : G.Letter x y)
    (hpos : 0 < P.prob h.word a) :
    S.refineUpdate ⟨x, y, a⟩ (S.stateOf h)
      = S.stateOf (h.snoc a (P.admissible_of_prob_pos hpos)) := by
  have hrate : 0 < S.rate a (S.stateOf h) := S.branch_factor h a ▸ hpos
  simp [refineUpdate, S.cutType_stateOf, hrate, S.state_step h a hpos]

theorem refineUpdate_stateOf_not_pos {x y : G.CutType} (h : G.History x) (a : G.Letter x y)
    (hpos : ¬ 0 < P.prob h.word a) :
    S.refineUpdate ⟨x, y, a⟩ (S.stateOf h) = S.stateOf h := by
  have hrate : ¬ 0 < S.rate a (S.stateOf h) := S.branch_factor h a ▸ hpos
  simp [refineUpdate, hrate]

theorem refineUpdate_stateOf_ne {x x' y : G.CutType} (h : G.History x) (a : G.Letter x' y)
    (hx : x' ≠ x) :
    S.refineUpdate ⟨x', y, a⟩ (S.stateOf h) = S.stateOf h := by
  have : ¬ S.cutType (S.stateOf h) = x' := by rw [S.cutType_stateOf]; exact fun e => hx e.symm
  simp [refineUpdate, this]

/-- Future-equivalent histories have equal immediate data. -/
theorem refineOut_eq_of_futureEquivalent {x : G.CutType} {h h' : G.History x}
    (hh : P.FutureEquivalent h h') : S.refineOut (S.stateOf h) = S.refineOut (S.stateOf h') := by
  funext i
  rcases i with ⟨x', y, a⟩ | o
  · by_cases hx : x' = x
    · subst hx
      rw [refineOut_stateOf, refineOut_stateOf, P.prob_eq_of_futureEquivalent hh a]
    · have h1 : ¬ S.cutType (S.stateOf h) = x' := by
        rw [S.cutType_stateOf]; exact fun e => hx e.symm
      have h2 : ¬ S.cutType (S.stateOf h') = x' := by
        rw [S.cutType_stateOf]; exact fun e => hx e.symm
      simp [refineOut, h1, h2]
  · simp only [refineOut]
    rw [S.cutType_stateOf h, S.cutType_stateOf h']

/-- Future-equivalent histories are never separated by any future word of the refinement
dynamics ("future-equivalent records cannot be separated by any round"). -/
theorem wordEqv_of_futureEquivalent :
    ∀ (w : List (AnyLetter G)) {x : G.CutType} {h h' : G.History x},
      P.FutureEquivalent h h' →
        S.refineOut (MinimalRecordPartitionRefinement.run S.refineUpdate w (S.stateOf h))
          = S.refineOut (MinimalRecordPartitionRefinement.run S.refineUpdate w (S.stateOf h')) := by
  intro w
  induction w with
  | nil =>
    intro x h h' hh
    exact S.refineOut_eq_of_futureEquivalent hh
  | cons A w ih =>
    intro x h h' hh
    rw [MinimalRecordPartitionRefinement.run_cons, MinimalRecordPartitionRefinement.run_cons]
    obtain ⟨x', y, a⟩ := A
    by_cases hx : x' = x
    · subst hx
      by_cases hpos : 0 < P.prob h.word a
      · have hpos' : 0 < P.prob h'.word a := P.prob_eq_of_futureEquivalent hh a ▸ hpos
        rw [S.refineUpdate_stateOf_pos h a hpos, S.refineUpdate_stateOf_pos h' a hpos']
        exact ih (P.futureEquivalent_snoc hh a hpos)
      · have hpos' : ¬ 0 < P.prob h'.word a := P.prob_eq_of_futureEquivalent hh a ▸ hpos
        rw [S.refineUpdate_stateOf_not_pos h a hpos, S.refineUpdate_stateOf_not_pos h' a hpos']
        exact ih hh
    · rw [S.refineUpdate_stateOf_ne h a hx, S.refineUpdate_stateOf_ne h' a hx]
      exact ih hh

/-- Records whose refinement words all agree represent future-equivalent histories: the
relation is a typed prediction bisimulation. -/
theorem futureEquivalent_of_wordEqv {x : G.CutType} {h h' : G.History x}
    (hw : MinimalRecordPartitionRefinement.wordEqv S.refineOut S.refineUpdate
      (S.stateOf h) (S.stateOf h')) : P.FutureEquivalent h h' := by
  refine P.futureEquivalent_of_typedPredictionBisimulation
    (fun {x} (g g' : G.History x) =>
      MinimalRecordPartitionRefinement.wordEqv S.refineOut S.refineUpdate
        (S.stateOf g) (S.stateOf g')) ?_ h h' hw
  intro x y g g' hg a
  have h0 := congrFun (hg []) (Sum.inl ⟨x, y, a⟩)
  simp only [MinimalRecordPartitionRefinement.run_nil] at h0
  rw [refineOut_stateOf, refineOut_stateOf] at h0
  refine ⟨h0, fun hpos hpos' => ?_⟩
  intro w
  have := hg (⟨x, y, a⟩ :: w)
  rw [MinimalRecordPartitionRefinement.run_cons, MinimalRecordPartitionRefinement.run_cons,
    S.refineUpdate_stateOf_pos g a hpos, S.refineUpdate_stateOf_pos g' a hpos'] at this
  exact this

/-- Equivalence of the two descriptions on represented histories. -/
theorem wordEqv_iff_futureEquivalent {x : G.CutType} (h h' : G.History x) :
    MinimalRecordPartitionRefinement.wordEqv S.refineOut S.refineUpdate
      (S.stateOf h) (S.stateOf h') ↔ P.FutureEquivalent h h' :=
  ⟨S.futureEquivalent_of_wordEqv, fun hh w => S.wordEqv_of_futureEquivalent w hh⟩

/-- **`prop:supp-finite-prediction`, "a stable finite partition is sufficient for equality of
all finite futures".**  If round `k + 1` of the refinement equals round `k`, then two records
identified at round `k` represent future-equivalent histories. -/
theorem stable_round_futureEquivalent {k : ℕ}
    (hst : ∀ r s : S.Record,
      MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate (k + 1) r s ↔
        MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate k r s)
    {x : G.CutType} {h h' : G.History x}
    (hk : MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate k
      (S.stateOf h) (S.stateOf h')) : P.FutureEquivalent h h' := by
  apply S.futureEquivalent_of_wordEqv
  intro w
  have hprop := MinimalRecordPartitionRefinement.eqv_stable_propagates
    S.refineOut S.refineUpdate hst (max k w.length) (le_max_left _ _) (S.stateOf h)
    (S.stateOf h')
  exact (MinimalRecordPartitionRefinement.eqv_iff_sep S.refineOut S.refineUpdate _ _ _).mp
    (hprop.mpr hk) w (le_max_right _ _)

/-- **`prop:supp-finite-prediction`, unbounded-horizon clause.**  For a reachable finite
presentation with `m = card Record` records:
(i) every strict refinement round happens strictly before round `m - 1`, and every round
`j ≥ m - 1` equals round `m - 1` (at most `m - 1` strict refinements);
(ii) round `m - 1` identifies the records of two histories exactly when the histories are
future equivalent;
(iii) round `m - 1` identifies two records exactly when they represent future-equivalent
histories of the same cut type, i.e. the stable partition is the coarsest predictive
partition. -/
theorem typedFinitePrediction_refinement :
    ((∀ j, Fintype.card S.Record - 1 ≤ j → ∀ r s : S.Record,
        MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate j r s ↔
          MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate
            (Fintype.card S.Record - 1) r s) ∧
      (∀ k, (¬ ∀ r s : S.Record,
          MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate (k + 1) r s ↔
            MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate k r s) →
        k < Fintype.card S.Record - 1)) ∧
    (∀ {x : G.CutType} (h h' : G.History x),
      MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate
          (Fintype.card S.Record - 1) (S.stateOf h) (S.stateOf h') ↔
        P.FutureEquivalent h h') ∧
    (∀ r s : S.Record,
      MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate
          (Fintype.card S.Record - 1) r s ↔
        ∃ (x : G.CutType) (h h' : G.History x),
          S.stateOf h = r ∧ S.stateOf h' = s ∧ P.FutureEquivalent h h') := by
  have hpull : ∀ {x : G.CutType} (h h' : G.History x),
      MinimalRecordPartitionRefinement.eqv S.refineOut S.refineUpdate
          (Fintype.card S.Record - 1) (S.stateOf h) (S.stateOf h') ↔
        P.FutureEquivalent h h' := by
    intro x h h'
    rw [MinimalRecordPartitionRefinement.stable_eq_wordEqv]
    exact S.wordEqv_iff_futureEquivalent h h'
  refine ⟨MinimalRecordPartitionRefinement.refinement_stabilizes _ _, hpull, ?_⟩
  intro r s
  constructor
  · intro hrs
    obtain ⟨x, h, rfl⟩ := S.reachable r
    obtain ⟨x', h', rfl⟩ := S.reachable s
    have hout : S.refineOut (S.stateOf h) = S.refineOut (S.stateOf h') :=
      (MinimalRecordPartitionRefinement.stable_eq_wordEqv _ _ _ _).mp hrs []
    have htype := congrFun hout (Sum.inr x)
    simp only [refineOut] at htype
    rw [S.cutType_stateOf h, S.cutType_stateOf h'] at htype
    have hxx : x' = x := by
      by_contra hne
      simp [hne] at htype
    subst hxx
    exact ⟨x', h, h', rfl, rfl, (hpull h h').mp hrs⟩
  · rintro ⟨x, h, h', rfl, rfl, hh⟩
    exact (hpull h h').mpr hh

end TypedFinitePresentation

end ConditionalLaw

end FiniteTypedEventGrammar

/-! ## The negative clause: a finite alphabet without horizon or finite index -/

namespace TypedFinitePredictionCountermodel

/-- The binary renewal grammar: one cut type, letters `true` (renewal) and `false`
(nonrenewal), every typed word reachable, trivial (E4) data and the binary orientation
record `ℤˣ`. -/
abbrev grammar : FiniteTypedEventGrammar where
  CutType := Unit
  Letter := fun _ _ => Bool
  Reachable := fun _ => True
  reachable_nil := fun _ => trivial
  reachable_of_snoc := fun _ _ _ => trivial
  Preparation := Unit
  InterventionOutcome := Unit
  TerminalRead := Unit
  Port := Unit
  ReadOutcome := fun _ => ℤˣ
  Verdict := ℤˣ
  readPolicy := fun _ v => v
  orientationRead := ()
  orientationBinary := Equiv.refl _
  orientation_separated := by decide

/-- The age of a history: the number of consecutive nonrenewals at its end. -/
def age : ∀ {x y : Unit}, TypedWord grammar.Letter x y → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc w a => if (a : Bool) then 0 else age w + 1

/-- Renewal probability `1/(n+2)` after `n` consecutive nonrenewals. -/
noncomputable def renewalProb (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem renewalProb_pos (n : ℕ) : 0 < renewalProb n := by
  unfold renewalProb; positivity

theorem renewalProb_le_one (n : ℕ) : renewalProb n ≤ 1 := by
  unfold renewalProb
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem renewalProb_injective : Function.Injective renewalProb := by
  intro n m h
  unfold renewalProb at h
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  rw [div_eq_div_iff hn.ne' hm.ne'] at h
  exact_mod_cast (by linarith : (n : ℝ) = m)

/-- The binary renewal law: renewal with probability `1/(n+2)` at age `n`. -/
noncomputable def law : grammar.ConditionalLaw where
  prob := fun h a => if (a : Bool) then renewalProb (age h) else 1 - renewalProb (age h)
  prob_nonneg := by
    intro s x y h a
    cases a
    · simp only [Bool.false_eq_true, ite_false]
      linarith [renewalProb_le_one (age h)]
    · simp only [ite_true]
      exact (renewalProb_pos _).le
  prob_eq_zero_of_not_admissible := by
    intro s x y h a ha
    exact absurd trivial ha
  sum_prob := by
    intro s x h _
    change ∑ y : Unit, ∑ a : Bool, (if (a : Bool) then renewalProb (age h)
      else 1 - renewalProb (age h)) = 1
    simp

/-- The history of `n` consecutive nonrenewals. -/
def nonrenewals : ℕ → TypedWord grammar.Letter () ()
  | 0 => .nil ()
  | n + 1 => .snoc (nonrenewals n) (false : Bool)

theorem age_nonrenewals (n : ℕ) : age (nonrenewals n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nonrenewals, age, ih]

/-- The reachable history of `n` consecutive nonrenewals. -/
def nonrenewalHistory (n : ℕ) : grammar.History () := ⟨(), ⟨nonrenewals n, trivial⟩⟩

/-- **`prop:supp-finite-prediction`, negative clause.**  The binary renewal grammar has
finitely many cut types and finite letter sets, admits no horizon function strictly
decreasing along its letters, and its renewal law with probability `1/(n+2)` after `n`
consecutive nonrenewals has an infinite future quotient: finite alphabets without a horizon
bound or a finite-index hypothesis do not imply a finite quotient. -/
theorem typedFinitePrediction_countermodel :
    Finite grammar.CutType ∧ (∀ x y, Finite (grammar.Letter x y)) ∧
    (∀ horizon : grammar.CutType → ℕ,
      ¬ ∀ {x y : grammar.CutType} (_ : grammar.Letter x y), horizon y < horizon x) ∧
    Infinite (law.MinimalState ()) := by
  refine ⟨inferInstance, fun _ _ => inferInstance, ?_, ?_⟩
  · intro horizon hlt
    exact lt_irrefl _ (@hlt () () (true : Bool))
  · refine Infinite.of_injective (fun n => law.project (nonrenewalHistory n)) ?_
    intro n m hnm
    have h := congrArg (law.weight (x := ()) (y := ()) (true : Bool)) hnm
    simp only [FiniteTypedEventGrammar.ConditionalLaw.weight_project] at h
    change renewalProb (age (nonrenewals n)) = renewalProb (age (nonrenewals m)) at h
    rw [age_nonrenewals, age_nonrenewals] at h
    exact renewalProb_injective h

end TypedFinitePredictionCountermodel

end RenewalGeometry
