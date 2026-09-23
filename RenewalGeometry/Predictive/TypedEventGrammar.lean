/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite typed event grammars, future signatures and minimum predictive states
(`def:supp-event-grammar`, `def:supp-future-signature`, `def:supp-predictive-state`,
emergent-spacetime manuscript)

* `TypedWord Letter x y` — finite typed words `a₁ ⋯ a_k` with `a_j : x_{j-1} → x_j`, built
  by right-appending letters (`TypedWord.snoc`), with typed concatenation
  (`TypedWord.append`) and empty words (`TypedWord.nil`).
* `FiniteTypedEventGrammar` — `def:supp-event-grammar`: a finite set of cut types (E1),
  finite letter sets `Σ_X(x,y)` (E2), a prefix-closed reachability predicate on typed
  words containing the empty words (E3), finite preparation / intervention-outcome /
  terminal-Read alphabets and exposed operator ports (E4), and a distinguished
  protected binary orientation Read whose two values receive different verdicts under
  the declared Read policy (E5).  `FiniteTypedEventGrammar.History x` is `H_{X,x}`,
  the reachable histories ending at `x`; `Admissible h a` is `a ∈ Σ_{X,h}`.
* `FiniteTypedEventGrammar.ConditionalLaw` — the conditional-probability clause of
  `def:supp-operational-datum` (`eq:supp-one-step-law`), with the chain law
  `eq:supp-chain-law` as `ConditionalLaw.wordProb`.
* `ConditionalLaw.futureSignature`, `ConditionalLaw.FutureEquivalent`,
  `ConditionalLaw.futureSetoid` — `def:supp-future-signature`
  (`eq:supp-future-signature`, `eq:supp-future-equivalence`) with the complete future
  bank = all typed future words starting at the cut type of the history (words that
  are not admissible carry probability `0`, so this is the admissible bank).  Histories
  of different cut type live in different fibres and are never identified.
* `ConditionalLaw.MinimalState`, `ConditionalLaw.project`, `ConditionalLaw.weight`,
  `ConditionalLaw.transition` — `def:supp-predictive-state`
  (`eq:supp-predictive-state`, `eq:supp-predictive-transition`): `Z^min_{X,x} =
  H_{X,x}/∼_X`, `q_{X,x}`, `κ_{X,a}([h]) = p_X(a | h)` and, on the positive-probability
  branch, `T_{X,a}([h]) = [h a]` (`ConditionalLaw.transition_project`), well defined by
  the typed right congruence `ConditionalLaw.futureEquivalent_snoc`
  (`thm:supp-right-congruence`).
-/

namespace RenewalGeometry

/-- Finite typed words over a family of letter sets `Letter x y` (letters `a : x → y`),
built by appending letters on the right. -/
inductive TypedWord {O : Type} (Letter : O → O → Type) : O → O → Type
  | nil (x : O) : TypedWord Letter x x
  | snoc {x y z : O} (w : TypedWord Letter x y) (a : Letter y z) : TypedWord Letter x z

namespace TypedWord

variable {O : Type} {Letter : O → O → Type}

/-- Typed concatenation of words. -/
def append {x y : O} (w : TypedWord Letter x y) :
    ∀ {z : O}, TypedWord Letter y z → TypedWord Letter x z
  | _, nil _ => w
  | _, snoc v a => snoc (append w v) a

@[simp] theorem append_nil {x y : O} (w : TypedWord Letter x y) :
    w.append (nil y) = w := by
  simp [append]

@[simp] theorem append_snoc {x y z t : O} (w : TypedWord Letter x y)
    (v : TypedWord Letter y z) (a : Letter z t) :
    w.append (v.snoc a) = (w.append v).snoc a := by
  simp [append]

theorem nil_append {x y : O} (w : TypedWord Letter x y) :
    (nil x).append w = w := by
  induction w with
  | nil => simp
  | snoc v a ih => rw [append_snoc, ih]

theorem append_assoc {x y z t : O} (w : TypedWord Letter x y)
    (v : TypedWord Letter y z) (u : TypedWord Letter z t) :
    (w.append v).append u = w.append (v.append u) := by
  induction u with
  | nil => simp
  | snoc u a ih => rw [append_snoc, append_snoc, append_snoc, ih]

end TypedWord

/-- `def:supp-event-grammar`: a finite typed event grammar at cutoff `X`. -/
structure FiniteTypedEventGrammar where
  /-- (E1) the finite set of cut types `𝖮_X`. -/
  CutType : Type
  [cutTypeFintype : Fintype CutType]
  /-- (E2) the finite sets `Σ_X(x,y)` of primitive event letters `a : x → y`. -/
  Letter : CutType → CutType → Type
  [letterFintype : ∀ x y, Fintype (Letter x y)]
  /-- (E3) the reachable typed histories. -/
  Reachable : ∀ {x y : CutType}, TypedWord Letter x y → Prop
  /-- (E3) empty words are reachable. -/
  reachable_nil : ∀ x : CutType, Reachable (TypedWord.nil x)
  /-- (E3) prefix closure. -/
  reachable_of_snoc : ∀ {x y z : CutType} (w : TypedWord Letter x y) (a : Letter y z),
    Reachable (w.snoc a) → Reachable w
  /-- (E4) the finite preparation alphabet. -/
  Preparation : Type
  [preparationFintype : Fintype Preparation]
  /-- (E4) the finite intervention-outcome alphabet. -/
  InterventionOutcome : Type
  [interventionOutcomeFintype : Fintype InterventionOutcome]
  /-- (E4) the finite terminal-Read alphabet. -/
  TerminalRead : Type
  [terminalReadFintype : Fintype TerminalRead]
  /-- (E4) the finite exposed operator ports. -/
  Port : Type
  [portFintype : Fintype Port]
  /-- Finite outcome sets of the terminal Reads. -/
  ReadOutcome : TerminalRead → Type
  [readOutcomeFintype : ∀ r, Fintype (ReadOutcome r)]
  /-- The verdicts of the declared physical Read policy. -/
  Verdict : Type
  /-- The declared physical Read policy. -/
  readPolicy : ∀ r : TerminalRead, ReadOutcome r → Verdict
  /-- (E5) the distinguished protected orientation record. -/
  orientationRead : TerminalRead
  /-- (E5) the orientation record is binary, with values `±1`. -/
  orientationBinary : ReadOutcome orientationRead ≃ ℤˣ
  /-- (E5) the two orientation values are separated by the Read policy. -/
  orientation_separated :
    readPolicy orientationRead (orientationBinary.symm 1)
      ≠ readPolicy orientationRead (orientationBinary.symm (-1))

namespace FiniteTypedEventGrammar

attribute [instance] cutTypeFintype letterFintype preparationFintype
  interventionOutcomeFintype terminalReadFintype portFintype readOutcomeFintype

variable (G : FiniteTypedEventGrammar)

/-- `H_{X,x}`: the reachable finite typed histories ending at the cut type `x`
(`def:supp-event-grammar` (E3)). -/
def History (x : G.CutType) : Type :=
  Σ s : G.CutType, {h : TypedWord G.Letter s x // G.Reachable h}

/-- `Σ_{X,h}`: the event letters admissible after the history `h`. -/
def Admissible {s x y : G.CutType} (h : TypedWord G.Letter s x) (a : G.Letter x y) : Prop :=
  G.Reachable (h.snoc a)

variable {G}

/-- The underlying typed word of a history. -/
def History.word {x : G.CutType} (h : G.History x) : TypedWord G.Letter h.1 x := h.2.1

theorem History.reachable {x : G.CutType} (h : G.History x) : G.Reachable h.word := h.2.2

/-- Extension `h a` of a history by an admissible letter. -/
def History.snoc {x y : G.CutType} (h : G.History x) (a : G.Letter x y)
    (ha : G.Admissible h.word a) : G.History y :=
  ⟨h.1, ⟨h.word.snoc a, ha⟩⟩

variable (G) in
/-- The conditional-probability clause of `def:supp-operational-datum`: a finite
conditional operational renewal law `p_X(a | h)` (`eq:supp-one-step-law`), with
non-admissible letters carrying probability `0`. -/
structure ConditionalLaw where
  /-- `p_X(a | h)`. -/
  prob : ∀ {s x y : G.CutType}, TypedWord G.Letter s x → G.Letter x y → ℝ
  prob_nonneg : ∀ {s x y : G.CutType} (h : TypedWord G.Letter s x) (a : G.Letter x y),
    0 ≤ prob h a
  prob_eq_zero_of_not_admissible :
    ∀ {s x y : G.CutType} (h : TypedWord G.Letter s x) (a : G.Letter x y),
      ¬ G.Admissible h a → prob h a = 0
  /-- normalization over the admissible letters after every reachable history. -/
  sum_prob : ∀ {s x : G.CutType} (h : TypedWord G.Letter s x), G.Reachable h →
    ∑ y : G.CutType, ∑ a : G.Letter x y, prob h a = 1

namespace ConditionalLaw

variable (P : G.ConditionalLaw)

/-- The chain law `eq:supp-chain-law`: `p_X(w | h)` for a typed future word `w`
starting at the cut type of `h`. -/
def wordProb {s x : G.CutType} (h : TypedWord G.Letter s x) :
    ∀ {z : G.CutType}, TypedWord G.Letter x z → ℝ
  | _, .nil _ => 1
  | _, .snoc w a => wordProb h w * P.prob (h.append w) a

@[simp] theorem wordProb_nil {s x : G.CutType} (h : TypedWord G.Letter s x) :
    P.wordProb h (TypedWord.nil x) = 1 := rfl

@[simp] theorem wordProb_snoc {s x y z : G.CutType} (h : TypedWord G.Letter s x)
    (w : TypedWord G.Letter x y) (a : G.Letter y z) :
    P.wordProb h (w.snoc a) = P.wordProb h w * P.prob (h.append w) a := rfl

/-- The chain law factorizes over typed concatenation. -/
theorem wordProb_append {s x y z : G.CutType} (h : TypedWord G.Letter s x)
    (w : TypedWord G.Letter x y) (v : TypedWord G.Letter y z) :
    P.wordProb h (w.append v) = P.wordProb h w * P.wordProb (h.append w) v := by
  induction v with
  | nil => simp
  | snoc v a ih =>
    rw [TypedWord.append_snoc, wordProb_snoc, wordProb_snoc, ih, TypedWord.append_assoc]
    ring

/-- The one-letter word `a`. -/
theorem wordProb_single {s x y : G.CutType} (h : TypedWord G.Letter s x) (a : G.Letter x y) :
    P.wordProb h ((TypedWord.nil x).snoc a) = P.prob h a := by
  simp

theorem admissible_of_prob_pos {s x y : G.CutType} {h : TypedWord G.Letter s x}
    {a : G.Letter x y} (hpos : 0 < P.prob h a) : G.Admissible h a := by
  by_contra hna
  rw [P.prob_eq_zero_of_not_admissible h a hna] at hpos
  exact lt_irrefl _ hpos

/-- `eq:supp-future-signature`: the complete predictive future signature `Σ_X(h)`,
indexed by the complete bank of typed future words starting at the cut type of `h`. -/
def futureSignature {x : G.CutType} (h : G.History x) :
    (Σ z : G.CutType, TypedWord G.Letter x z) → ℝ :=
  fun w => P.wordProb h.word w.2

/-- `eq:supp-future-equivalence`: histories of the same cut type are future equivalent
when all their future-word probabilities agree. -/
def FutureEquivalent {x : G.CutType} (h h' : G.History x) : Prop :=
  ∀ (z : G.CutType) (w : TypedWord G.Letter x z), P.wordProb h.word w = P.wordProb h'.word w

theorem futureEquivalent_iff_futureSignature {x : G.CutType} (h h' : G.History x) :
    P.FutureEquivalent h h' ↔ P.futureSignature h = P.futureSignature h' := by
  constructor
  · intro hh
    funext w
    exact hh w.1 w.2
  · intro hh z w
    exact congrFun hh ⟨z, w⟩

theorem futureEquivalent_equivalence (x : G.CutType) :
    Equivalence (P.FutureEquivalent (x := x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h z w
    rfl
  · intro h h' hh z w
    exact (hh z w).symm
  · intro h₁ h₂ h₃ h₁₂ h₂₃ z w
    exact (h₁₂ z w).trans (h₂₃ z w)

/-- The typed future-equivalence setoid `∼_X` on `H_{X,x}`. -/
def futureSetoid (x : G.CutType) : Setoid (G.History x) where
  r := P.FutureEquivalent
  iseqv := P.futureEquivalent_equivalence x

/-- One-letter probabilities agree on future-equivalent histories
(`eq:supp-one-letter-equality`). -/
theorem prob_eq_of_futureEquivalent {x y : G.CutType} {h h' : G.History x}
    (hh : P.FutureEquivalent h h') (a : G.Letter x y) :
    P.prob h.word a = P.prob h'.word a := by
  have := hh y ((TypedWord.nil x).snoc a)
  simpa using this

/-- `thm:supp-right-congruence`: on the positive-probability branch, future equivalence
is a typed right congruence, `h ∼_X h' → h a ∼_X h' a`. -/
theorem futureEquivalent_snoc {x y : G.CutType} {h h' : G.History x}
    (hh : P.FutureEquivalent h h') (a : G.Letter x y) (hpos : 0 < P.prob h.word a) :
    P.FutureEquivalent (h.snoc a (P.admissible_of_prob_pos hpos))
      (h'.snoc a (P.admissible_of_prob_pos (P.prob_eq_of_futureEquivalent hh a ▸ hpos))) := by
  intro z w
  have h1 := hh z (((TypedWord.nil x).snoc a).append w)
  rw [P.wordProb_append, P.wordProb_append, wordProb_single, wordProb_single,
    P.prob_eq_of_futureEquivalent hh a] at h1
  have hpos' : 0 < P.prob h'.word a := P.prob_eq_of_futureEquivalent hh a ▸ hpos
  exact mul_left_cancel₀ hpos'.ne' h1

/-- `eq:supp-predictive-state`: the minimum predictive state space
`Z^min_{X,x} = H_{X,x} / ∼_X`. -/
abbrev MinimalState (x : G.CutType) : Type := Quotient (P.futureSetoid x)

/-- `eq:supp-predictive-state`: the canonical surjection `q_{X,x}`. -/
def project {x : G.CutType} (h : G.History x) : P.MinimalState x :=
  Quotient.mk (P.futureSetoid x) h

theorem project_surjective (x : G.CutType) : Function.Surjective (P.project (x := x)) :=
  Quotient.mk_surjective

theorem project_eq_iff {x : G.CutType} (h h' : G.History x) :
    P.project h = P.project h' ↔ P.FutureEquivalent h h' :=
  Quotient.eq (r := P.futureSetoid x)

/-- `eq:supp-predictive-transition`: the one-step weight `κ_{X,a}([h]) = p_X(a | h)`. -/
def weight {x y : G.CutType} (a : G.Letter x y) : P.MinimalState x → ℝ :=
  Quotient.lift (fun h : G.History x => P.prob h.word a)
    (fun _ _ hh => P.prob_eq_of_futureEquivalent hh a)

@[simp] theorem weight_project {x y : G.CutType} (a : G.Letter x y) (h : G.History x) :
    P.weight a (P.project h) = P.prob h.word a := rfl

/-- `eq:supp-predictive-transition`: the transition `T_{X,a}` on the
positive-probability branch, defined through a representative. -/
noncomputable def transition {x y : G.CutType} (a : G.Letter x y) (z : P.MinimalState x)
    (hz : 0 < P.weight a z) : P.MinimalState y :=
  P.project (z.out.snoc a (P.admissible_of_prob_pos (by
    have hout : P.project z.out = z := Quotient.out_eq z
    rw [← hout, weight_project] at hz
    exact hz)))

/-- `eq:supp-predictive-transition`: `T_{X,a}([h]) = [h a]` on the positive-probability
branch. -/
theorem transition_project {x y : G.CutType} (a : G.Letter x y) (h : G.History x)
    (hpos : 0 < P.prob h.word a) :
    P.transition a (P.project h) (by simpa using hpos)
      = P.project (h.snoc a (P.admissible_of_prob_pos hpos)) := by
  unfold transition
  apply Quotient.sound
  have hout : P.FutureEquivalent (P.project h).out h := Quotient.mk_out (s := P.futureSetoid x) h
  have hpos' : 0 < P.prob (P.project h).out.word a :=
    (P.prob_eq_of_futureEquivalent hout a).symm ▸ hpos
  exact P.futureEquivalent_snoc hout a hpos'

end ConditionalLaw

end FiniteTypedEventGrammar

end RenewalGeometry
