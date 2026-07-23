/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The rooted operational process system (upstream program, §2–3)

First upstream batch, covering `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:ops` — `NCG.Upstream.OperationalSystem`: a small category of
  typed processes with a root interface, a wide subcategory of
  admissible continuations (identities + composition closure), a
  structureless weight set, terminal tests, and the evaluation map;
* `def:profile` — `futureProfile` / `OpEquiv`: the future profile of a
  rooted process and operational equivalence;
* `prop:operational-equivalence` — `opEquiv_equivalence`,
  `profileQuot_injective`, `exists_separating_context`: `≈` is an
  equivalence, the profile map descends injectively to the quotient,
  and distinct classes are separated by an admissible future context;
* `cor:separated` — `opEquiv_iff_eq_of_separated`,
  `quot_factorization`: under contextual separation `≈` is equality,
  and the quotient is the separated reflection (unique factorization
  of any invariant map);
* `def:presentation` — `GeneratedPresentation` / `Hist` / `sem`:
  generated presentations, histories as free paths of elementary
  processes, and their operational meaning;
* `def:future-equivalence` — `FutureEquiv` / `Qpred`: future
  contextual equivalence of histories and the predictive quotient;
* `thm:future-congruence` — `futureEquiv_equivalence`,
  `futureEquiv_comp`: `≃₊` is an equivalence stable under every
  generated future continuation (a typed right congruence);
* `cor:quotient-action` — `Qmap`, `Qmap_nil`, `Qmap_comp`: the
  canonical predictive transition system is functorial;
* `thm:reduction-to-equality` — `futureEquiv_iff_sem_eq`: under
  contextual separation on the represented reachable processes,
  `h ≃₊ h' ↔ ⟦h⟧ = ⟦h'⟧`;
* `def:two-sided` — `CtxEquiv`: two-sided contextual equivalence.
-/

namespace NCG.Upstream

open CategoryTheory

universe u v w t

/-- **Definition `def:ops` (rooted operational process system)**: a
small category `P` of typed processes with a distinguished root
interface, a wide subcategory of admissible continuations (all
identities, closed under composition), a structureless weight set `W`,
terminal tests `T B` at each interface, and an evaluation
`ev : T B → (root ⟶ B) → W` of tests on rooted processes. -/
structure OperationalSystem (P : Type u) [Category.{v} P]
    (W : Type w) (T : P → Type t) where
  /-- The distinguished root interface `0`. -/
  root : P
  /-- The admissible continuations (a wide subcategory of `P`). -/
  Cont : ∀ {A B : P}, (A ⟶ B) → Prop
  cont_id : ∀ A : P, Cont (𝟙 A)
  cont_comp : ∀ {A B C : P} {f : A ⟶ B} {g : B ⟶ C},
    Cont f → Cont g → Cont (f ≫ g)
  /-- Evaluation of a terminal test on a rooted process. -/
  ev : ∀ {B : P}, T B → (root ⟶ B) → W

variable {P : Type u} [Category.{v} P] {W : Type w} {T : P → Type t}

/-- An admissible future context for a rooted process ending at `B`:
an admissible continuation `c : B ⟶ C` together with a terminal test
at `C`. -/
def FutureContext (O : OperationalSystem P W T) (B : P) :=
  Σ C : P, {c : B ⟶ C // O.Cont c} × T C

/-- **Definition `def:profile` (future profile)**: the function
recording every observed weight `ev(t, c ∘ p)` over all admissible
future contexts. -/
def futureProfile (O : OperationalSystem P W T) {B : P}
    (p : O.root ⟶ B) : FutureContext O B → W :=
  fun ctx => O.ev ctx.2.2 (p ≫ ctx.2.1.1)

/-- **Definition `def:profile` (operational equivalence)**:
`p ≈ q` iff their future profiles coincide. -/
def OpEquiv (O : OperationalSystem P W T) {B : P}
    (p q : O.root ⟶ B) : Prop :=
  futureProfile O p = futureProfile O q

/-- **Proposition `prop:operational-equivalence` (equivalence)**:
operational equivalence is an equivalence relation on rooted
processes. -/
theorem opEquiv_equivalence (O : OperationalSystem P W T) (B : P) :
    Equivalence (OpEquiv O (B := B)) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The profile map descended to the separation quotient. -/
def profileQuot (O : OperationalSystem P W T) (B : P) :
    Quot (OpEquiv O (B := B)) → (FutureContext O B → W) :=
  Quot.lift (futureProfile O) fun _ _ h => h

/-- **Proposition `prop:operational-equivalence` (injectivity)**: the
descended profile map embeds the separation quotient into the space of
weight functions on future contexts. -/
theorem profileQuot_injective (O : OperationalSystem P W T) (B : P) :
    Function.Injective (profileQuot O B) := by
  intro x y
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ q =>
  intro h
  exact Quot.sound h

/-- **Proposition `prop:operational-equivalence` (separation)**:
inequivalent rooted processes are separated by at least one admissible
future context. -/
theorem exists_separating_context (O : OperationalSystem P W T)
    {B : P} {p q : O.root ⟶ B} (h : ¬ OpEquiv O p q) :
    ∃ ctx : FutureContext O B,
      futureProfile O p ctx ≠ futureProfile O q ctx :=
  Function.ne_iff.mp h

/-- **Corollary `cor:separated` (separation collapses `≈` to
equality)**: under contextual separation, operational equivalence is
equality. -/
theorem opEquiv_iff_eq_of_separated (O : OperationalSystem P W T)
    {B : P}
    (hsep : ∀ p q : O.root ⟶ B,
      futureProfile O p = futureProfile O q → p = q)
    (p q : O.root ⟶ B) :
    OpEquiv O p q ↔ p = q :=
  ⟨hsep p q, fun h => h ▸ rfl⟩

/-- **Corollary `cor:separated` (separated reflection)**: every map
constant on operational-equivalence classes factors uniquely through
the separation quotient. -/
theorem quot_factorization (O : OperationalSystem P W T) {B : P}
    {α : Type*} (f : (O.root ⟶ B) → α)
    (hf : ∀ p q, OpEquiv O p q → f p = f q) :
    ∃! g : Quot (OpEquiv O (B := B)) → α,
      ∀ p, g (Quot.mk _ p) = f p := by
  refine ⟨Quot.lift f hf, fun p => rfl, ?_⟩
  intro g' hg'
  funext x
  induction x using Quot.ind with | _ p =>
  exact hg' p

/-- **Definition `def:presentation` (generated operational
presentation)**: a directed multigraph of elementary processes on the
objects of `P`, each edge denoting an admissible process — the
identity-on-objects functor from the free category is realized by the
path semantics `sem` below. -/
structure GeneratedPresentation (O : OperationalSystem P W T) where
  /-- Elementary processes: the edges of the generating multigraph. -/
  Edge : P → P → Type v
  /-- The process denoted by an elementary edge. -/
  toProc : ∀ {A B : P}, Edge A B → (A ⟶ B)
  /-- Every elementary process is an admissible continuation. -/
  adm : ∀ {A B : P} (σ : Edge A B), O.Cont (toProc σ)

variable {O : OperationalSystem P W T}

/-- **Histories** (`def:presentation`): free paths of elementary
processes — the morphisms of the free category on the generating
multigraph. -/
inductive Hist (G : GeneratedPresentation O) :
    P → P → Type (max u v) where
  | nil : (A : P) → Hist G A A
  | cons : {A B C : P} → Hist G A B → G.Edge B C → Hist G A C

namespace Hist

variable {G : GeneratedPresentation O}

/-- The operational meaning `⟦h⟧` of a history: the composite of its
elementary processes (the identity-on-objects functor `J`). -/
def sem : ∀ {A B : P}, Hist G A B → (A ⟶ B)
  | _, _, .nil A => 𝟙 A
  | _, _, .cons h σ => sem h ≫ G.toProc σ

/-- Concatenation of histories (composition in the free category). -/
def comp : ∀ {A B C : P}, Hist G A B → Hist G B C → Hist G A C
  | _, _, _, h, .nil _ => h
  | _, _, _, h, .cons k σ => .cons (comp h k) σ

@[simp] theorem comp_nil {A B : P} (h : Hist G A B) :
    h.comp (nil B) = h := by simp [comp]

@[simp] theorem sem_nil (A : P) : (nil (G := G) A).sem = 𝟙 A := by
  simp [sem]

@[simp] theorem sem_cons {A B C : P} (h : Hist G A B) (σ : G.Edge B C) :
    (cons h σ).sem = h.sem ≫ G.toProc σ := by
  simp [sem]

@[simp] theorem comp_cons {A B C D : P} (h : Hist G A B)
    (k : Hist G B C) (σ : G.Edge C D) :
    h.comp (cons k σ) = cons (h.comp k) σ := by
  simp [comp]

/-- Functoriality of the meaning: `⟦h · k⟧ = ⟦h⟧ ≫ ⟦k⟧`. -/
theorem sem_comp : ∀ {A B C : P} (h : Hist G A B) (k : Hist G B C),
    (h.comp k).sem = h.sem ≫ k.sem := by
  intro A B C h k
  induction k with
  | nil => simp
  | cons k σ ih => simp [ih]

/-- Associativity of concatenation. -/
theorem comp_assoc : ∀ {A B C D : P} (h : Hist G A B)
    (k : Hist G B C) (l : Hist G C D),
    (h.comp k).comp l = h.comp (k.comp l) := by
  intro A B C D h k l
  induction l with
  | nil => simp
  | cons l σ ih => simp [ih]

/-- The meaning of every history is an admissible continuation. -/
theorem sem_cont : ∀ {A B : P} (h : Hist G A B), O.Cont h.sem := by
  intro A B h
  induction h with
  | nil =>
      rw [sem_nil]
      exact O.cont_id _
  | cons h σ ih =>
      rw [sem_cons]
      exact O.cont_comp ih (G.adm σ)

end Hist

/-- **Definition `def:future-equivalence`**: two histories ending at
`B` are future-contextually equivalent when every generated
continuation and terminal test assigns their meanings the same
weight. -/
def FutureEquiv (G : GeneratedPresentation O) {B : P}
    (h h' : Hist G O.root B) : Prop :=
  ∀ (C : P) (c : Hist G B C) (t : T C),
    O.ev t (h.sem ≫ c.sem) = O.ev t (h'.sem ≫ c.sem)

/-- **Definition `def:future-equivalence` (predictive quotient)**:
`Q₊(B)`, the histories at `B` modulo future contextual
equivalence. -/
def Qpred (G : GeneratedPresentation O) (B : P) :=
  Quot (FutureEquiv G (B := B))

/-- **Theorem `thm:future-congruence` (equivalence)**: future
contextual equivalence is an equivalence relation on `Hist_B`. -/
theorem futureEquiv_equivalence (G : GeneratedPresentation O)
    (B : P) : Equivalence (FutureEquiv G (B := B)) :=
  ⟨fun _ _ _ _ => rfl,
   fun h C c t => (h C c t).symm,
   fun h₁ h₂ C c t => (h₁ C c t).trans (h₂ C c t)⟩

/-- **Theorem `thm:future-congruence` (right congruence)**: future
equivalence is stable under every generated future continuation —
`h ≃₊ h'` implies `k∘h ≃₊ k∘h'`.  The proof is the manuscript's:
associativity in the free category and functoriality of the semantics
convert a context after `k∘h` into the context `d∘k` after `h`. -/
theorem futureEquiv_comp {G : GeneratedPresentation O}
    {B C : P} {h h' : Hist G O.root B}
    (hE : FutureEquiv G h h') (k : Hist G B C) :
    FutureEquiv G (h.comp k) (h'.comp k) := by
  intro D d t
  have h1 : (h.comp k).sem ≫ d.sem = h.sem ≫ (k.comp d).sem := by
    rw [Hist.sem_comp, Hist.sem_comp, Category.assoc]
  have h2 : (h'.comp k).sem ≫ d.sem = h'.sem ≫ (k.comp d).sem := by
    rw [Hist.sem_comp, Hist.sem_comp, Category.assoc]
  rw [h1, h2]
  exact hE D (k.comp d) t

/-- **Corollary `cor:quotient-action` (transition maps)**: every
generated continuation induces a well-defined map of predictive
quotients. -/
def Qmap {G : GeneratedPresentation O} {B C : P}
    (k : Hist G B C) : Qpred G B → Qpred G C :=
  Quot.lift (fun h => Quot.mk _ (h.comp k))
    fun _ _ hab => Quot.sound (futureEquiv_comp hab k)

/-- **Corollary `cor:quotient-action` (identity law)**. -/
theorem Qmap_nil {G : GeneratedPresentation O} (B : P) :
    Qmap (G := G) (Hist.nil B) = id := by
  funext x
  induction x using Quot.ind with | _ h =>
  change Quot.mk _ (h.comp (Hist.nil B)) = Quot.mk _ h
  rw [Hist.comp_nil]

/-- **Corollary `cor:quotient-action` (composition law)**: `Q₊` is a
covariant functor from the generated continuation category to `Set`
on the reachable component. -/
theorem Qmap_comp {G : GeneratedPresentation O} {B C D : P}
    (k : Hist G B C) (d : Hist G C D) :
    Qmap (G := G) (k.comp d) = Qmap d ∘ Qmap k := by
  funext x
  induction x using Quot.ind with | _ h =>
  change Quot.mk _ (h.comp (k.comp d)) = Quot.mk _ ((h.comp k).comp d)
  rw [Hist.comp_assoc]

/-- **Theorem `thm:reduction-to-equality`**: if the generated future
continuations and terminal tests are contextually separating on the
represented reachable processes, then future equivalence of histories
is *exactly* equality of their accumulated meanings:
`h ≃₊ h' ↔ ⟦h⟧ = ⟦h'⟧`. -/
theorem futureEquiv_iff_sem_eq {G : GeneratedPresentation O}
    {B : P}
    (hsep : ∀ h h' : Hist G O.root B,
      (∀ (C : P) (c : Hist G B C) (t : T C),
        O.ev t (h.sem ≫ c.sem) = O.ev t (h'.sem ≫ c.sem)) →
      h.sem = h'.sem)
    (h h' : Hist G O.root B) :
    FutureEquiv G h h' ↔ h.sem = h'.sem := by
  constructor
  · intro hE
    exact hsep h h' hE
  · intro hsem C c t
    rw [hsem]

/-- **Definition `def:two-sided` (two-sided contextual
equivalence)**: processes `p, q : A ⟶ B` are two-sidedly equivalent
when every rooted preparation, admissible future continuation, and
terminal test assigns them the same weight. -/
def CtxEquiv (O : OperationalSystem P W T) {A B : P}
    (p q : A ⟶ B) : Prop :=
  ∀ (a : O.root ⟶ A) (C : P) (c : B ⟶ C), O.Cont c →
    ∀ t : T C, O.ev t (a ≫ p ≫ c) = O.ev t (a ≫ q ≫ c)

/-- **Proposition `prop:two-sided-congruence` (precomposition)**: any
rooted preparation before `p ∘ u` is the rooted preparation `u ∘ a'`
before `p`. -/
theorem ctxEquiv_precomp {O : OperationalSystem P W T} {A A' B : P}
    {p q : A ⟶ B} (hpq : CtxEquiv O p q) (u : A' ⟶ A) :
    CtxEquiv O (u ≫ p) (u ≫ q) := by
  intro a C c hc t
  have := hpq (a ≫ u) C c hc t
  simpa [Category.assoc] using this

/-- **Proposition `prop:two-sided-congruence` (postcomposition)**: any
future context after `v ∘ p` is the future context `c ∘ v` after `p`;
closure of the admissible continuations under composition finishes. -/
theorem ctxEquiv_postcomp {O : OperationalSystem P W T} {A B B' : P}
    {p q : A ⟶ B} (hpq : CtxEquiv O p q) (v : B ⟶ B')
    (hv : O.Cont v) :
    CtxEquiv O (p ≫ v) (q ≫ v) := by
  intro a C c hc t
  have := hpq a C (v ≫ c) (O.cont_comp hv hc) t
  simpa [Category.assoc] using this

/-- **Assumption `ass:monoidal` / Proposition `prop:product-ancilla`
(hypothesis, abstracted)**: an ancillary extension of rooted processes
(`p ↦ p ⊗ r` for a fixed ancilla `r`), under which every admissible
continuation after the extension is *absorbed* as an admissible
continuation before it — the strict-monoidal interchange
`c ∘ (h ⊗ r) = (c ∘ (id_B ⊗ r)) ∘ h` together with the admissibility
of `c ∘ (id_B ⊗ r)`. -/
structure AncillaryExtension (O : OperationalSystem P W T)
    (B B' : P) where
  /-- The extension `p ↦ p ⊗ r`. -/
  ext : (O.root ⟶ B) → (O.root ⟶ B')
  /-- Context absorption: strict-monoidal interchange plus closure of
  the admissible continuations. -/
  absorb : ∀ {C : P} (c : B' ⟶ C), O.Cont c →
    ∃ c' : B ⟶ C, O.Cont c' ∧ ∀ p : O.root ⟶ B, ext p ≫ c = p ≫ c'

/-- **Proposition `prop:product-ancilla`**: operational equivalence is
stable under tensoring with a fixed product ancilla — every future
context after `h ⊗ r` is absorbed into an ordinary admissible future
context after `h`. -/
theorem product_ancilla {O : OperationalSystem P W T} {B B' : P}
    (E : AncillaryExtension O B B') {p q : O.root ⟶ B}
    (hpq : OpEquiv O p q) : OpEquiv O (E.ext p) (E.ext q) := by
  funext ctx
  obtain ⟨C, ⟨c, hc⟩, t⟩ := ctx
  obtain ⟨c', hc', habs⟩ := E.absorb c hc
  have h := congrFun hpq ⟨C, ⟨c', hc'⟩, t⟩
  simpa [futureProfile, habs] using h

open MonoidalCategory in
/-- **Definition `def:complete-contextual` (completely contextual
equivalence)**: transformations are completely equivalent when every
ancillary object, every rooted preparation of the joint interface,
every admissible continuation, and every terminal test give the same
weight to `p ⊗ id_R` and `q ⊗ id_R`. -/
def CCtxEquiv [MonoidalCategory P] (O : OperationalSystem P W T)
    {A B : P} (p q : A ⟶ B) : Prop :=
  ∀ (R : P) (a : O.root ⟶ A ⊗ R) (C : P) (c : B ⊗ R ⟶ C), O.Cont c →
    ∀ t : T C,
      O.ev t (a ≫ (p ▷ R) ≫ c) = O.ev t (a ≫ (q ▷ R) ≫ c)

open MonoidalCategory in
/-- **Proposition `prop:complete-stable` (sequential stability)**:
complete contextual equivalence absorbs pre- and postcomposition, by
the same context-absorption argument as
`prop:two-sided-congruence`; postcomposition uses the closure of the
admissible continuations under whiskering (Assumption
`ass:monoidal`). -/
theorem cctxEquiv_comp [MonoidalCategory P]
    {O : OperationalSystem P W T} {A A' B B' : P} {p q : A ⟶ B}
    (hpq : CCtxEquiv O p q) (u : A' ⟶ A) (v : B ⟶ B')
    (hclosed : ∀ (R : P), O.Cont (v ▷ R)) :
    CCtxEquiv O (u ≫ p ≫ v) (u ≫ q ≫ v) := by
  intro R a C c hc t
  have habs := hpq R (a ≫ (u ▷ R)) C ((v ▷ R) ≫ c)
    (O.cont_comp (hclosed R) hc) t
  simpa [MonoidalCategory.comp_whiskerRight, Category.assoc] using habs

open MonoidalCategory in
/-- **Proposition `prop:complete-stable` (identity extension)**: a
further ancilla `R` for `p ▷ S` is the combined ancilla `S ⊗ R` for
`p` — associativity identifies the preparations and continuations
(the associator components are admissible in the strict setting,
taken here as the hypothesis `hα`). -/
theorem cctxEquiv_whiskerRight [MonoidalCategory P]
    {O : OperationalSystem P W T} {A B : P} {p q : A ⟶ B}
    (hpq : CCtxEquiv O p q) (S : P)
    (hα : ∀ (R C : P) (c : (B ⊗ S) ⊗ R ⟶ C), O.Cont c →
      O.Cont ((α_ B S R).inv ≫ c)) :
    CCtxEquiv O (p ▷ S) (q ▷ S) := by
  intro R a C c hc t
  have hkey := hpq (S ⊗ R) (a ≫ (α_ A S R).hom) C
    ((α_ B S R).inv ≫ c) (hα R C c hc) t
  have hnatp : ((p ▷ S) ▷ R) ≫ c
      = (α_ A S R).hom ≫ (p ▷ (S ⊗ R)) ≫ (α_ B S R).inv ≫ c := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← MonoidalCategory.associator_naturality_left,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hnatq : ((q ▷ S) ▷ R) ≫ c
      = (α_ A S R).hom ≫ (q ▷ (S ⊗ R)) ≫ (α_ B S R).inv ≫ c := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← MonoidalCategory.associator_naturality_left,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hnatp, hnatq]
  simpa [Category.assoc] using hkey

variable {G : GeneratedPresentation O}

/-- **Proposition `prop:quotient-factorisation` (factorization)**:
every family of maps constant on future-equivalence classes factors
uniquely through the predictive quotient. -/
theorem qpred_factorisation {Y : P → Type*}
    (f : ∀ B : P, Hist G O.root B → Y B)
    (hf : ∀ (B : P) (h h' : Hist G O.root B),
      FutureEquiv G h h' → f B h = f B h') (B : P) :
    ∃! g : Qpred G B → Y B, ∀ h, g (Quot.mk _ h) = f B h := by
  refine ⟨Quot.lift (f B) (hf B), fun h => rfl, ?_⟩
  intro g' hg'
  funext x
  induction x using Quot.ind with | _ h =>
  exact hg' h

/-- **Proposition `prop:quotient-factorisation` (naturality)**: if the
target family carries continuation maps intertwining `f`, the
descended maps intertwine the predictive transition system. -/
theorem qpred_factorisation_natural {Y : P → Type*}
    (f : ∀ B : P, Hist G O.root B → Y B)
    (hf : ∀ (B : P) (h h' : Hist G O.root B),
      FutureEquiv G h h' → f B h = f B h')
    (Ymap : ∀ {B C : P}, Hist G B C → Y B → Y C)
    (hnat : ∀ {B C : P} (c : Hist G B C) (h : Hist G O.root B),
      f C (h.comp c) = Ymap c (f B h))
    {B C : P} (c : Hist G B C) (x : Qpred G B) :
    Quot.lift (f C) (hf C) (Qmap c x)
      = Ymap c (Quot.lift (f B) (hf B) x) := by
  induction x using Quot.ind with | _ h =>
  exact hnat c h

/-! ## The canonical parallel completion (`thm:parallel-completion`) -/

open MonoidalCategory in
/-- **Theorem `thm:parallel-completion` (comparison)**: complete
contextual equivalence implies ordinary two-sided operational
equivalence, by testing with the trivial ancilla and absorbing the
right unitor into the admissible continuations. -/
theorem cctxEquiv_implies_ctxEquiv [MonoidalCategory P]
    {O : OperationalSystem P W T} {A B : P} {p q : A ⟶ B}
    (hpq : CCtxEquiv O p q)
    (hu : ∀ (C : P) (c : B ⟶ C), O.Cont c →
      O.Cont ((ρ_ B).hom ≫ c)) :
    CtxEquiv O p q := by
  intro a C c hc t
  have hkey := hpq (𝟙_ P) (a ≫ (ρ_ A).inv) C ((ρ_ B).hom ≫ c)
    (hu C c hc) t
  have hnat : ∀ r : A ⟶ B,
      (a ≫ (ρ_ A).inv) ≫ (r ▷ 𝟙_ P) ≫ (ρ_ B).hom ≫ c
        = a ≫ r ≫ c := by
    intro r
    have h1 : (r ▷ 𝟙_ P) ≫ (ρ_ B).hom = (ρ_ A).hom ≫ r :=
      MonoidalCategory.rightUnitor_naturality r
    calc (a ≫ (ρ_ A).inv) ≫ (r ▷ 𝟙_ P) ≫ (ρ_ B).hom ≫ c
        = a ≫ (ρ_ A).inv ≫ ((r ▷ 𝟙_ P) ≫ (ρ_ B).hom) ≫ c := by
          simp [Category.assoc]
      _ = a ≫ (ρ_ A).inv ≫ ((ρ_ A).hom ≫ r) ≫ c := by rw [h1]
      _ = a ≫ r ≫ c := by simp [Category.assoc]
  rw [hnat p, hnat q] at hkey
  exact hkey

open MonoidalCategory in
/-- **Theorem `thm:parallel-completion` (maximality)**: complete
contextual equivalence is the **largest** relation inside ordinary
operational equivalence that is stable under tensoring with ancilla
identities: any such relation is contained in `CCtxEquiv`.  (Together
with `cctxEquiv_comp` and `cctxEquiv_whiskerRight`, which give
sequential and monoidal stability, this is the universal
characterisation of the parallel completion.) -/
theorem cctxEquiv_maximal [MonoidalCategory P]
    {O : OperationalSystem P W T}
    (Rel : ∀ {A B : P}, (A ⟶ B) → (A ⟶ B) → Prop)
    (hR1 : ∀ {A B : P} (p q : A ⟶ B), Rel p q → CtxEquiv O p q)
    (hRten : ∀ {A B : P} (p q : A ⟶ B) (S : P),
      Rel p q → Rel (p ▷ S) (q ▷ S))
    {A B : P} (p q : A ⟶ B) (hpq : Rel p q) :
    CCtxEquiv O p q := by
  intro R a C c hc t
  exact hR1 (p ▷ R) (q ▷ R) (hRten p q R hpq) a C c hc t

end NCG.Upstream
