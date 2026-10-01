/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.TypedFinitePredictionExact

/-!
# Terminality and naturality of predictive reduction
(`prop:supp-predictive-category`, emergent-spacetime manuscript)

* `TypedPredictiveCategory.TypedOperationalLaw` — a typed operational law: a finite typed
  event grammar (`def:supp-event-grammar`), a conditional operational renewal law on it
  (`def:supp-operational-datum`) and terminal Reads of the histories, which are part of the
  declared future test bank and hence constant on future-equivalence classes.
* `TypedPredictiveCategory.Presentation` — a reachable predictive presentation `S`: state
  sets per cut type, history maps `s`, reads, branch functions and partial updates
  intertwining every positive-probability successor (`def:supp-predictive-realization`).
* `TypedPredictiveCategory.Hom` — morphisms `f : S → S'` with `s' = f ∘ s`, preserving
  reads and branch probabilities and intertwining every positive-probability successor;
  `TypedPredictiveCategory.instCategoryPresentation` — the resulting category.
* `TypedPredictiveCategory.minimal` — the predictive quotient `Z^min_X`
  (`def:supp-predictive-state`) as a presentation;
  `TypedPredictiveCategory.minimal_isTerminal`: `Z^min_X` is terminal.
* `TypedPredictiveCategory.TypedLawIso` — isomorphisms of typed laws (bijections of cut
  types, letters, histories and read values commuting with extension and preserving branch
  probabilities and reads), with identities and composition;
  `TypedLawIso.futureEquivalent_iff`, `TypedLawIso.minimalStateEquiv`: an isomorphism of
  laws induces bijections of the predictive quotients `Z^min_{X,x} ≃ Z^min_{X',e x}` that
  preserve weights, transitions and reads (`minimalStateEquiv_weight`,
  `minimalStateEquiv_transition`, `minimalStateEquiv_read`), compatibly with identities and
  composition (`minimalStateEquiv_refl`, `minimalStateEquiv_trans`).
-/

namespace RenewalGeometry

namespace TypedPredictiveCategory

open FiniteTypedEventGrammar

/-- A typed operational law: a finite typed event grammar, a conditional operational renewal
law on it, and terminal Reads of histories.  Reads belong to the declared future test bank,
so they are constant on future-equivalence classes (`read_congr`). -/
structure TypedOperationalLaw where
  /-- the finite typed event grammar -/
  grammar : FiniteTypedEventGrammar
  /-- the conditional operational renewal law -/
  law : grammar.ConditionalLaw
  /-- the read values -/
  ReadValue : Type
  /-- the terminal Read of a history -/
  read : ∀ {x : grammar.CutType}, grammar.History x → ReadValue
  /-- Reads are part of the future test bank. -/
  read_congr : ∀ {x : grammar.CutType} {h h' : grammar.History x},
    law.FutureEquivalent h h' → read h = read h'

variable (L : TypedOperationalLaw)

/-- A reachable predictive presentation of the typed law `L`
(`def:supp-predictive-realization`, with reads). -/
structure Presentation where
  /-- the state sets `S_{X,x}` -/
  State : L.grammar.CutType → Type
  /-- the history maps `s_x` -/
  stateOf : ∀ {x : L.grammar.CutType}, L.grammar.History x → State x
  /-- reachability -/
  reachable : ∀ x, Function.Surjective (stateOf (x := x))
  /-- the reads of states -/
  readOf : ∀ {x : L.grammar.CutType}, State x → L.ReadValue
  read_factor : ∀ {x : L.grammar.CutType} (h : L.grammar.History x),
    readOf (stateOf h) = L.read h
  /-- the branch functions `r_a` -/
  rate : ∀ {x y : L.grammar.CutType}, L.grammar.Letter x y → State x → ℝ
  branch_factor : ∀ {x y : L.grammar.CutType} (h : L.grammar.History x)
    (a : L.grammar.Letter x y), L.law.prob h.word a = rate a (stateOf h)
  /-- the partial updates `u_a` -/
  update : ∀ {x y : L.grammar.CutType}, L.grammar.Letter x y → State x → Option (State y)
  state_step : ∀ {x y : L.grammar.CutType} (h : L.grammar.History x)
    (a : L.grammar.Letter x y) (hpos : 0 < L.law.prob h.word a),
    update a (stateOf h) = some (stateOf (h.snoc a (L.law.admissible_of_prob_pos hpos)))

variable {L}

/-- A morphism of reachable predictive presentations: `s' = f ∘ s`, reads and branch
probabilities preserved, every positive-probability successor intertwined. -/
@[ext]
structure Hom (S S' : Presentation L) where
  /-- the state maps -/
  map : ∀ x, S.State x → S'.State x
  map_stateOf : ∀ {x : L.grammar.CutType} (h : L.grammar.History x),
    map x (S.stateOf h) = S'.stateOf h
  map_read : ∀ {x : L.grammar.CutType} (s : S.State x), S'.readOf (map x s) = S.readOf s
  map_rate : ∀ {x y : L.grammar.CutType} (a : L.grammar.Letter x y) (s : S.State x),
    S'.rate a (map x s) = S.rate a s
  map_update : ∀ {x y : L.grammar.CutType} (a : L.grammar.Letter x y) (s : S.State x)
    (t : S.State y), 0 < S.rate a s → S.update a s = some t →
      S'.update a (map x s) = some (map y t)

namespace Hom

/-- Reachability forces every morphism to be determined by `s' = f ∘ s`. -/
instance (S S' : Presentation L) : Subsingleton (Hom S S') := by
  constructor
  intro f g
  ext x s
  obtain ⟨h, rfl⟩ := S.reachable x s
  rw [f.map_stateOf, g.map_stateOf]

/-- A family of maps with `s' = f ∘ s` is automatically a morphism. -/
def ofStateOf {S S' : Presentation L} (m : ∀ x, S.State x → S'.State x)
    (hm : ∀ {x : L.grammar.CutType} (h : L.grammar.History x), m x (S.stateOf h) = S'.stateOf h) :
    Hom S S' where
  map := m
  map_stateOf := hm
  map_read := by
    intro x s
    obtain ⟨h, rfl⟩ := S.reachable x s
    rw [hm, S'.read_factor, S.read_factor]
  map_rate := by
    intro x y a s
    obtain ⟨h, rfl⟩ := S.reachable x s
    rw [hm, ← S'.branch_factor, ← S.branch_factor]
  map_update := by
    intro x y a s t hpos hupd
    obtain ⟨h, rfl⟩ := S.reachable x s
    have hp : 0 < L.law.prob h.word a := (S.branch_factor h a).symm ▸ hpos
    rw [S.state_step h a hp, Option.some_inj] at hupd
    subst hupd
    rw [hm, hm, S'.state_step h a hp]

/-- The identity morphism. -/
def id (S : Presentation L) : Hom S S := ofStateOf (fun _ s => s) (fun _ => rfl)

/-- Composition of morphisms. -/
def comp {S S' S'' : Presentation L} (f : Hom S S') (g : Hom S' S'') : Hom S S'' :=
  ofStateOf (fun x s => g.map x (f.map x s)) (fun h => by rw [f.map_stateOf, g.map_stateOf])

end Hom

/-- The category of reachable predictive presentations of a typed law. -/
instance instCategoryPresentation : CategoryTheory.Category (Presentation L) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- The category of presentations is thin. -/
instance (S S' : Presentation L) : Subsingleton (S ⟶ S') :=
  inferInstanceAs (Subsingleton (Hom S S'))

variable (L)

/-- The predictive quotient `Z^min_X = H_X/∼_X` (`def:supp-predictive-state`) as a reachable
predictive presentation: reads descend by `read_congr`, `κ_a[h] = p(a | h)` and, on the
positive-probability branch, `T_a[h] = [h a]`. -/
noncomputable def minimal : Presentation L where
  State := L.law.MinimalState
  stateOf := L.law.project
  reachable x := L.law.project_surjective x
  readOf := fun {x} z =>
    Quotient.lift (s := L.law.futureSetoid x) (fun h => L.read h) (fun _ _ hh => L.read_congr hh) z
  read_factor _ := rfl
  rate a z := L.law.weight a z
  branch_factor _ _ := rfl
  update a z := if hz : 0 < L.law.weight a z then some (L.law.transition a z hz) else none
  state_step h a hpos := by
    have hz : 0 < L.law.weight a (L.law.project h) := by simpa using hpos
    simp only [hz, ↓reduceDIte, Option.some_inj]
    exact L.law.transition_project a h hpos

variable {L}

/-- Histories with the same state in a presentation are future equivalent (the first step of
the proof: "if two histories have the same record in `S`, their complete futures agree"). -/
theorem futureEquivalent_of_stateOf_eq (S : Presentation L) {x : L.grammar.CutType}
    {h h' : L.grammar.History x} (hs : S.stateOf h = S.stateOf h') :
    L.law.FutureEquivalent h h' := by
  refine L.law.futureEquivalent_of_typedPredictionBisimulation
    (fun {x} (g g' : L.grammar.History x) => S.stateOf g = S.stateOf g') ?_ h h' hs
  intro x y g g' hg a
  refine ⟨by rw [S.branch_factor, S.branch_factor, hg], fun hpos hpos' => ?_⟩
  have h1 := S.state_step g a hpos
  have h2 := S.state_step g' a hpos'
  rw [hg, h2, Option.some_inj] at h1
  exact h1.symm

/-- The canonical morphism `S → Z^min_X`, `f_S(s(h)) = [h]`. -/
noncomputable def toMinimal (S : Presentation L) : Hom S (minimal L) :=
  Hom.ofStateOf (fun x s => L.law.project (Function.surjInv (S.reachable x) s)) (by
    intro x h
    apply Quotient.sound
    exact futureEquivalent_of_stateOf_eq S (Function.surjInv_eq (S.reachable x) _))

/-- **`prop:supp-predictive-category`, terminality.**  In the category of reachable predictive
presentations of a typed operational law (morphisms with `s' = f ∘ s`, preserving reads and
branch probabilities and intertwining every positive-probability successor), the predictive
quotient `Z^min_X` is terminal. -/
noncomputable def minimal_isTerminal : CategoryTheory.Limits.IsTerminal (minimal L) :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom (fun S => toMinimal S)
    (fun _ _ => Subsingleton.elim _ _)

/-- The unique morphism into `Z^min_X` is surjective on every fibre and sends `s(h)` to `[h]`. -/
theorem toMinimal_spec (S : Presentation L) :
    (∀ {x : L.grammar.CutType} (h : L.grammar.History x),
      (toMinimal S).map x (S.stateOf h) = L.law.project h) ∧
    (∀ x, Function.Surjective ((toMinimal S).map x)) ∧
    (∀ f g : S ⟶ minimal L, f = g) := by
  refine ⟨fun h => (toMinimal S).map_stateOf h, fun x z => ?_, fun f g => Subsingleton.elim f g⟩
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  exact ⟨S.stateOf h, (toMinimal S).map_stateOf h⟩

/-! ## Naturality under isomorphisms of typed laws -/

/-- An isomorphism of typed operational laws: bijections of cut types, letters, reachable
histories and read values, commuting with history extension and preserving branch
probabilities and reads. -/
structure TypedLawIso (L L' : TypedOperationalLaw) where
  /-- the bijection of cut types -/
  cut : L.grammar.CutType ≃ L'.grammar.CutType
  /-- the bijections of letters -/
  letter : ∀ x y, L.grammar.Letter x y ≃ L'.grammar.Letter (cut x) (cut y)
  /-- the bijections of reachable histories -/
  hist : ∀ x, L.grammar.History x ≃ L'.grammar.History (cut x)
  /-- the bijection of read values -/
  readEquiv : L.ReadValue ≃ L'.ReadValue
  admissible_map : ∀ {x y : L.grammar.CutType} (h : L.grammar.History x)
    (a : L.grammar.Letter x y), L.grammar.Admissible h.word a →
      L'.grammar.Admissible (hist x h).word (letter x y a)
  hist_snoc : ∀ {x y : L.grammar.CutType} (h : L.grammar.History x)
    (a : L.grammar.Letter x y) (ha : L.grammar.Admissible h.word a),
      hist y (h.snoc a ha) = (hist x h).snoc (letter x y a) (admissible_map h a ha)
  prob_map : ∀ {x y : L.grammar.CutType} (h : L.grammar.History x)
    (a : L.grammar.Letter x y), L'.law.prob (hist x h).word (letter x y a) = L.law.prob h.word a
  read_map : ∀ {x : L.grammar.CutType} (h : L.grammar.History x),
    L'.read (hist x h) = readEquiv (L.read h)

namespace TypedLawIso

/-- The identity isomorphism of a typed law. -/
def refl (L : TypedOperationalLaw) : TypedLawIso L L where
  cut := Equiv.refl _
  letter _ _ := Equiv.refl _
  hist _ := Equiv.refl _
  readEquiv := Equiv.refl _
  admissible_map _ _ ha := ha
  hist_snoc _ _ _ := rfl
  prob_map _ _ := rfl
  read_map _ := rfl

/-- Composition of isomorphisms of typed laws. -/
def trans {L₁ L₂ L₃ : TypedOperationalLaw} (e₁ : TypedLawIso L₁ L₂) (e₂ : TypedLawIso L₂ L₃) :
    TypedLawIso L₁ L₃ where
  cut := e₁.cut.trans e₂.cut
  letter x y := (e₁.letter x y).trans (e₂.letter (e₁.cut x) (e₁.cut y))
  hist x := (e₁.hist x).trans (e₂.hist (e₁.cut x))
  readEquiv := e₁.readEquiv.trans e₂.readEquiv
  admissible_map h a ha := e₂.admissible_map _ _ (e₁.admissible_map h a ha)
  hist_snoc h a ha := by
    change e₂.hist _ (e₁.hist _ (h.snoc a ha)) = _
    rw [e₁.hist_snoc, e₂.hist_snoc]
    rfl
  prob_map h a := by
    change L₃.law.prob (e₂.hist _ (e₁.hist _ h)).word (e₂.letter _ _ (e₁.letter _ _ a)) = _
    rw [e₂.prob_map, e₁.prob_map]
  read_map h := by
    change L₃.read (e₂.hist _ (e₁.hist _ h)) = e₂.readEquiv (e₁.readEquiv (L₁.read h))
    rw [e₂.read_map, e₁.read_map]

variable {L' : TypedOperationalLaw} (e : TypedLawIso L L')

/-- Future equivalence is reflected by an isomorphism of laws. -/
theorem futureEquivalent_of_map {x : L.grammar.CutType} {h h' : L.grammar.History x}
    (hh : L'.law.FutureEquivalent (e.hist x h) (e.hist x h')) : L.law.FutureEquivalent h h' := by
  refine L.law.futureEquivalent_of_typedPredictionBisimulation
    (fun {x} (g g' : L.grammar.History x) =>
      L'.law.FutureEquivalent (e.hist x g) (e.hist x g')) ?_ h h' hh
  intro x y g g' hg a
  have hp : L.law.prob g.word a = L.law.prob g'.word a := by
    rw [← e.prob_map, ← e.prob_map, L'.law.prob_eq_of_futureEquivalent hg]
  refine ⟨hp, fun hpos hpos' => ?_⟩
  have hq : 0 < L'.law.prob (e.hist x g).word (e.letter x y a) := by rw [e.prob_map]; exact hpos
  have := L'.law.futureEquivalent_snoc hg (e.letter x y a) hq
  change L'.law.FutureEquivalent (e.hist y (g.snoc a _)) (e.hist y (g'.snoc a _))
  rw [e.hist_snoc, e.hist_snoc]
  exact this

/-- Future equivalence is preserved by an isomorphism of laws: equal future signatures are
carried to equal future signatures. -/
theorem futureEquivalent_map {x : L.grammar.CutType} {h h' : L.grammar.History x}
    (hh : L.law.FutureEquivalent h h') :
    L'.law.FutureEquivalent (e.hist x h) (e.hist x h') := by
  refine L'.law.futureEquivalent_of_typedPredictionBisimulation
    (fun {x'} (g g' : L'.grammar.History x') =>
      ∃ (x : L.grammar.CutType) (hx : e.cut x = x') (h h' : L.grammar.History x),
        L.law.FutureEquivalent h h' ∧ hx ▸ e.hist x h = g ∧ hx ▸ e.hist x h' = g') ?_
    (e.hist x h) (e.hist x h') ⟨x, rfl, h, h', hh, rfl, rfl⟩
  intro x' y' g g' hg b
  obtain ⟨x, hx, h, h', hh, hgh, hgh'⟩ := hg
  subst hx
  subst hgh
  subst hgh'
  obtain ⟨y, rfl⟩ := e.cut.surjective y'
  obtain ⟨a, rfl⟩ := (e.letter x y).surjective b
  have hp : L'.law.prob (e.hist x h).word (e.letter x y a)
      = L'.law.prob (e.hist x h').word (e.letter x y a) := by
    rw [e.prob_map, e.prob_map, L.law.prob_eq_of_futureEquivalent hh]
  refine ⟨hp, fun hpos hpos' => ?_⟩
  have hq : 0 < L.law.prob h.word a := by rw [← e.prob_map]; exact hpos
  have hq' : 0 < L.law.prob h'.word a := by rw [← e.prob_map]; exact hpos'
  refine ⟨y, rfl, h.snoc a (L.law.admissible_of_prob_pos hq),
    h'.snoc a (L.law.admissible_of_prob_pos hq'), L.law.futureEquivalent_snoc hh a hq, ?_, ?_⟩
  · exact e.hist_snoc _ _ _
  · exact e.hist_snoc _ _ _

/-- An isomorphism of typed laws carries future equivalence exactly. -/
theorem futureEquivalent_iff {x : L.grammar.CutType} (h h' : L.grammar.History x) :
    L.law.FutureEquivalent h h' ↔ L'.law.FutureEquivalent (e.hist x h) (e.hist x h') :=
  ⟨e.futureEquivalent_map, e.futureEquivalent_of_map⟩

/-- **`prop:supp-predictive-category`, naturality.**  An isomorphism of typed laws induces a
bijection of the predictive quotients at every cut type. -/
def minimalStateEquiv (x : L.grammar.CutType) :
    L.law.MinimalState x ≃ L'.law.MinimalState (e.cut x) :=
  Quotient.congr (e.hist x) (fun h h' => e.futureEquivalent_iff h h')

@[simp] theorem minimalStateEquiv_project {x : L.grammar.CutType} (h : L.grammar.History x) :
    e.minimalStateEquiv x (L.law.project h) = L'.law.project (e.hist x h) := rfl

/-- The induced bijection preserves the one-step weights. -/
theorem minimalStateEquiv_weight {x y : L.grammar.CutType} (a : L.grammar.Letter x y)
    (z : L.law.MinimalState x) :
    L'.law.weight (e.letter x y a) (e.minimalStateEquiv x z) = L.law.weight a z := by
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  rw [minimalStateEquiv_project, FiniteTypedEventGrammar.ConditionalLaw.weight_project,
    FiniteTypedEventGrammar.ConditionalLaw.weight_project, e.prob_map]

/-- The induced bijection intertwines the predictive transitions. -/
theorem minimalStateEquiv_transition {x y : L.grammar.CutType} (a : L.grammar.Letter x y)
    (z : L.law.MinimalState x) (hz : 0 < L.law.weight a z) :
    e.minimalStateEquiv y (L.law.transition a z hz)
      = L'.law.transition (e.letter x y a) (e.minimalStateEquiv x z)
          (by rw [e.minimalStateEquiv_weight]; exact hz) := by
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  have hpos : 0 < L.law.prob h.word a := by simpa using hz
  have hpos' : 0 < L'.law.prob (e.hist x h).word (e.letter x y a) := by
    rw [e.prob_map]; exact hpos
  have h1 := L.law.transition_project a h hpos
  have h2 := L'.law.transition_project (e.letter x y a) (e.hist x h) hpos'
  rw [h1, minimalStateEquiv_project]
  change _ = L'.law.transition (e.letter x y a) (L'.law.project (e.hist x h)) _
  rw [h2, e.hist_snoc]

/-- The induced bijection preserves reads. -/
theorem minimalStateEquiv_read {x : L.grammar.CutType} (z : L.law.MinimalState x) :
    (minimal L').readOf (e.minimalStateEquiv x z) = e.readEquiv ((minimal L).readOf z) := by
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  rw [minimalStateEquiv_project]
  exact e.read_map h

/-- Compatibility with identities. -/
theorem minimalStateEquiv_refl (x : L.grammar.CutType) :
    (refl L).minimalStateEquiv x = Equiv.refl _ := by
  ext z
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  rfl

/-- **Compatibility with composition**: the bijection induced by a composite isomorphism is
the composite of the induced bijections. -/
theorem minimalStateEquiv_trans {L₃ : TypedOperationalLaw} (e₂ : TypedLawIso L' L₃)
    (x : L.grammar.CutType) :
    (e.trans e₂).minimalStateEquiv x
      = (e.minimalStateEquiv x).trans (e₂.minimalStateEquiv (e.cut x)) := by
  ext z
  obtain ⟨h, rfl⟩ := L.law.project_surjective x z
  rfl

end TypedLawIso

end TypedPredictiveCategory

end RenewalGeometry
