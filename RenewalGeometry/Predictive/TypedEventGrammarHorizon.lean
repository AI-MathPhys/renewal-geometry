/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.TypedEventGrammar

/-!
# Finite typed event grammars: the finiteness clause of (E3)
(`def:supp-event-grammar`, emergent-spacetime manuscript)

Clause (E3) of `def:supp-event-grammar` asks for a *finite-horizon* prefix-closed family
of reachable typed histories, with the remaining horizon included in the cut type, or,
alternatively, an unbounded family with a separately certified finite-index future
congruence.  `FiniteTypedEventGrammar` (`TypedEventGrammar.lean`) carries the
prefix-closed reachable family, typed concatenation and empty words; this file adds the
finiteness clause.

* `TypedWord.toList`, `TypedWord.toList_injective`, `TypedWord.length_add_horizon_le`,
  `TypedWord.finite_of_horizon` — a typed word is determined by its letter sequence; under
  a horizon function strictly decreasing along every letter the words from `x` to `y`
  have at most `horizon x - horizon y` letters, hence form a finite type.
* `FiniteHorizonTypedEventGrammar` — the finite-horizon branch of (E3): a finite typed
  event grammar together with the remaining horizon `horizon : CutType → ℕ` carried by the
  cut type and strictly decreasing along every event letter.
  `FiniteHorizonTypedEventGrammar.finite_history`: the reachable histories `H_{X,x}` at
  every cut type then form a finite family;
  `FiniteHorizonTypedEventGrammar.finite_minimalState`: every conditional law on it has a
  finite-index future congruence.
* `FiniteIndexTypedEventGrammar` — the alternative branch of (E3): an (unbounded)
  grammar with a conditional law whose future congruence `∼_X`
  (`def:supp-future-signature`) is certified to have finite index at every cut type.
* `FiniteTypedEventGrammar.HistoryFinitenessCertificate`,
  `CertifiedFiniteTypedEventGrammar` — `def:supp-event-grammar` in full: (E1)–(E5) with
  clause (E3) closed by one of the two admitted finiteness certificates.
-/

namespace RenewalGeometry

namespace TypedWord

variable {O : Type} {Letter : O → O → Type}

/-- The letter sequence of a typed word, each letter tagged by its source and target
cut types. -/
def toList {x y : O} : TypedWord Letter x y → List (Σ x y : O, Letter x y)
  | nil _ => []
  | snoc w a => toList w ++ [⟨_, _, a⟩]

@[simp] theorem toList_nil (x : O) : (nil x : TypedWord Letter x x).toList = [] := rfl

@[simp] theorem toList_snoc {x y z : O} (w : TypedWord Letter x y) (a : Letter y z) :
    (w.snoc a).toList = w.toList ++ [⟨y, z, a⟩] := rfl

/-- A typed word from `x` to `y` is determined by its letter sequence. -/
theorem toList_injective {x y : O} :
    Function.Injective (toList : TypedWord Letter x y → List (Σ x y : O, Letter x y)) := by
  intro w
  induction w with
  | nil =>
    intro w' h
    cases w' with
    | nil => rfl
    | snoc v a => simp at h
  | snoc v a ih =>
    intro w' h
    cases w' with
    | nil => simp at h
    | snoc v' a' =>
      simp only [toList_snoc] at h
      obtain ⟨hv, ha⟩ := List.append_inj' h rfl
      have ha' := List.singleton_inj.mp ha
      obtain ⟨rfl, ha''⟩ := Sigma.mk.inj_iff.mp ha'
      obtain ⟨-, ha'''⟩ := Sigma.mk.inj_iff.mp (eq_of_heq ha'')
      rw [ih hv, eq_of_heq ha''']

/-- Under a horizon that strictly decreases along every letter, a typed word from `x` to
`y` has at most `horizon x - horizon y` letters. -/
theorem length_add_horizon_le (horizon : O → ℕ)
    (hlt : ∀ {x y : O} (_ : Letter x y), horizon y < horizon x)
    {x y : O} (w : TypedWord Letter x y) :
    w.toList.length + horizon y ≤ horizon x := by
  induction w with
  | nil => simp
  | snoc v a ih =>
    have := hlt a
    simp only [toList_snoc, List.length_append, List.length_singleton]
    omega

/-- Under a strictly decreasing horizon, the typed words between two cut types form a
finite type. -/
theorem finite_of_horizon [Finite O] [∀ x y, Finite (Letter x y)] (horizon : O → ℕ)
    (hlt : ∀ {x y : O} (_ : Letter x y), horizon y < horizon x) (x y : O) :
    Finite (TypedWord Letter x y) := by
  have hfin : {l : List (Σ x y : O, Letter x y) | l.length ≤ horizon x}.Finite :=
    List.finite_length_le _ _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun w : TypedWord Letter x y =>
      (⟨w.toList, ?_⟩ : {l : List (Σ x y : O, Letter x y) | l.length ≤ horizon x})) ?_
  · show w.toList.length ≤ horizon x
    have := length_add_horizon_le horizon hlt w
    omega
  · intro w w' h
    exact toList_injective (congrArg Subtype.val h)

end TypedWord

/-- `def:supp-event-grammar`, clause (E3), finite-horizon branch: a finite typed event
grammar in which the remaining horizon is included in the cut type (`horizon x`) and
strictly decreases along every primitive event letter, so that the reachable histories at
every cut type form a finite family (`FiniteHorizonTypedEventGrammar.finite_history`). -/
structure FiniteHorizonTypedEventGrammar extends FiniteTypedEventGrammar where
  /-- (E3) the remaining horizon carried by each cut type. -/
  horizon : CutType → ℕ
  /-- (E3) every event letter strictly consumes horizon. -/
  horizon_lt : ∀ {x y : CutType} (_ : Letter x y), horizon y < horizon x

namespace FiniteHorizonTypedEventGrammar

variable (G : FiniteHorizonTypedEventGrammar)

/-- The typed words of a finite-horizon grammar form finite types. -/
theorem finite_typedWord (x y : G.CutType) : Finite (TypedWord G.Letter x y) :=
  TypedWord.finite_of_horizon G.horizon G.horizon_lt x y

/-- (E3): in the finite-horizon branch the reachable typed histories `H_{X,x}` ending at
each cut type form a finite family. -/
theorem finite_history (x : G.CutType) : Finite (G.toFiniteTypedEventGrammar.History x) := by
  have : ∀ s, Finite (TypedWord G.Letter s x) := fun s => G.finite_typedWord s x
  unfold FiniteTypedEventGrammar.History
  infer_instance

/-- In the finite-horizon branch every conditional law automatically has a finite-index
future congruence: the minimum predictive state space is a quotient of a finite type. -/
theorem finite_minimalState (P : G.toFiniteTypedEventGrammar.ConditionalLaw) (x : G.CutType) :
    Finite (P.MinimalState x) := by
  have := G.finite_history x
  exact Quotient.finite _

end FiniteHorizonTypedEventGrammar

/-- `def:supp-event-grammar`, clause (E3), alternative branch: an (unbounded) finite typed
event grammar together with a conditional operational renewal law whose future congruence
`∼_X` (`def:supp-future-signature`) is separately certified to have finite index at every
cut type. -/
structure FiniteIndexTypedEventGrammar where
  /-- the underlying grammar (E1), (E2), (E4), (E5) and the prefix-closed family of (E3). -/
  grammar : FiniteTypedEventGrammar
  /-- the conditional law whose future congruence is certified. -/
  law : grammar.ConditionalLaw
  /-- the certified finite-index future congruence at every cut type. -/
  finiteIndex : ∀ x : grammar.CutType, Finite (law.MinimalState x)

namespace FiniteTypedEventGrammar

/-- The two admitted certificates closing clause (E3) of `def:supp-event-grammar`: a
remaining horizon carried by the cut type and strictly decreasing along every letter, or a
conditional law with a finite-index future congruence at every cut type. -/
inductive HistoryFinitenessCertificate (G : FiniteTypedEventGrammar) : Type
  /-- finite-horizon branch. -/
  | finiteHorizon (horizon : G.CutType → ℕ)
      (horizon_lt : ∀ {x y : G.CutType} (_ : G.Letter x y), horizon y < horizon x)
  /-- unbounded branch with certified finite-index future congruence. -/
  | finiteIndex (P : G.ConditionalLaw) (hfin : ∀ x : G.CutType, Finite (P.MinimalState x))

/-- The finite-horizon certificate yields the finite-horizon grammar. -/
def HistoryFinitenessCertificate.toFiniteHorizon (G : FiniteTypedEventGrammar)
    (horizon : G.CutType → ℕ)
    (horizon_lt : ∀ {x y : G.CutType} (_ : G.Letter x y), horizon y < horizon x) :
    FiniteHorizonTypedEventGrammar :=
  { G with horizon := horizon, horizon_lt := horizon_lt }

/-- Under the finite-horizon certificate the reachable histories at every cut type are
finite. -/
theorem finite_history_of_finiteHorizon (G : FiniteTypedEventGrammar)
    (horizon : G.CutType → ℕ)
    (horizon_lt : ∀ {x y : G.CutType} (_ : G.Letter x y), horizon y < horizon x)
    (x : G.CutType) : Finite (G.History x) :=
  (HistoryFinitenessCertificate.toFiniteHorizon G horizon horizon_lt).finite_history x

end FiniteTypedEventGrammar

/-- **`def:supp-event-grammar`**: a finite typed event grammar at cutoff `X` — (E1) finite
cut types, (E2) finite letter sets, (E3) a prefix-closed family of reachable typed
histories with typed concatenation and empty words, closed by one of the two admitted
finiteness certificates, (E4) finite preparation, intervention-outcome and terminal-Read
alphabets with finite exposed operator ports, (E5) the protected binary orientation
record separated by the declared Read policy.  No state label, relation object, metric,
scheduler, connection or spacetime semantic is part of the data. -/
structure CertifiedFiniteTypedEventGrammar where
  /-- (E1), (E2), (E4), (E5) and the prefix-closed reachable family of (E3). -/
  grammar : FiniteTypedEventGrammar
  /-- the finiteness clause of (E3). -/
  certificate : grammar.HistoryFinitenessCertificate

end RenewalGeometry
