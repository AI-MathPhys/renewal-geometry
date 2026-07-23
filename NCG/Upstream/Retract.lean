/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.Realization

/-!
# Reduced realizations, selectors, and the renewal realization theorem

Third upstream batch, covering `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `thm:reduced-unique` — `reduced_iff_injective`,
  `reduced_iff_bijective`, `invCanonical`, `reducedHom`,
  `reducedHom_bijective`: a realization is reduced iff the canonical
  maps to `Q₊` are injective, iff they are an isomorphism; reduced
  realizations are unique up to a unique isomorphism;
* `def:predictive-rank` — `predictiveRank`, `FinitePredictiveRank`;
* `cor:finite-minimality` — `card_qpred_le`, `predictiveRank_le`,
  `reduced_iff_card_eq`: `|S(B)| ≥ |Q₊(B)|`, with equality exactly
  for reduced realizations;
* `prop:selector-existence` — `selector_exists`,
  `canonicalSelector`: type-preserving selectors exist (by choice;
  the finite case is subsumed);
* `def:selector` — `Selector`, `Selector.compress`: predictive
  selectors and the associated compression `E_s = s ∘ q`;
* `thm:exact-retract` — `Selector.compress_idem`,
  `Selector.mk_compress`, `Selector.futureEquiv_compress`,
  `Selector.range_compress`, `Selector.bijOn_mk`,
  `Selector.compress_eq_of_mem_range`: every selector yields an
  idempotent future-sufficient compression whose image maps
  bijectively onto `Q₊`;
* `def:sufficient-retract` — `IsSufficientRetract`, `ClassMinimal`;
* `thm:retract-classification` — `Selector.isSufficientRetract`,
  `Selector.classMinimal`, `selectorOfRetract`,
  `retract_eq_compress`, `Selector.compress_constant`,
  `Selector.compress_uniqueFixed`,
  `retract_eq_compress_of_constant`: minimal predictive retracts
  are exactly the selector compressions;
* `cor:retract-conjugacy` — `Selector.compress_compress`,
  `Selector.transfer_bijOn`, `Selector.transfer_inverse`,
  `Selector.transfer_unique`: the canonical conjugacies between two
  selected predictive images, their groupoid laws, and uniqueness;
* `thm:renewal-realization` — `Selector.renewal`,
  `Selector.mk_renewal`, `Selector.renewal_nil`,
  `Selector.renewal_comp`, `Selector.renewal_transfer`: "update then
  compress" is an exact action on the selected predictive image,
  conjugate over `q` to the canonical predictive action, and
  selector-independent up to the canonical conjugacies.
-/

namespace NCG.Upstream

open CategoryTheory

universe u v w t

variable {P : Type u} [Category.{v} P] {W : Type w} {T : P → Type t}
variable {O : OperationalSystem P W T} {G : GeneratedPresentation O}

/-! ## Exactness of the predictive quotient -/

/-- The future profile of a history descends to the predictive
quotient: predictive classes remember all future test statistics. -/
def qpredProfile {B : P} : Qpred G B → ∀ C : P, Hist G B C → T C → W :=
  Quot.lift (fun h => fun C c t => O.ev t (h.sem ≫ c.sem))
    (fun _ _ hE => by funext C c t; exact hE C c t)

/-- Exactness: equal predictive classes come from future-equivalent
histories (the quotient identifies *only* what the future contexts
cannot distinguish). -/
theorem futureEquiv_of_mk_eq {B : P} {h h' : Hist G O.root B}
    (hq : (Quot.mk _ h : Qpred G B) = Quot.mk _ h') :
    FutureEquiv G h h' := by
  intro C c t
  exact congrFun (congrFun (congrFun
    (congrArg (qpredProfile (G := G)) hq) C) c) t

/-! ## `thm:reduced-unique`: characterisation of reduced realizations -/

/-- **Theorem `thm:reduced-unique` ((i) ↔ (ii))**: a reachable
future-sufficient realization is reduced iff every canonical map
`π^S_B : S(B) → Q₊(B)` is injective. -/
theorem reduced_iff_injective (Rz : Realization G) :
    Rz.Reduced ↔
      ∀ B : P, Function.Injective ((toCanonical Rz).app B) := by
  constructor
  · intro hred B x y hxy
    by_contra hne
    obtain ⟨C, c, t, hsep⟩ := hred x y hne
    apply hsep
    obtain ⟨h, rfl⟩ := Rz.enc_surj B x
    obtain ⟨h', rfl⟩ := Rz.enc_surj B y
    rw [toCanonical_app_enc, toCanonical_app_enc] at hxy
    have hE := futureEquiv_of_mk_eq hxy
    rw [Rz.δ_enc, Rz.δ_enc, Rz.out_enc, Rz.out_enc,
      Hist.sem_comp, Hist.sem_comp]
    exact hE C c t
  · intro hinj B x y hne
    by_contra hcon
    push Not at hcon
    apply hne
    apply hinj B
    obtain ⟨h, rfl⟩ := Rz.enc_surj B x
    obtain ⟨h', rfl⟩ := Rz.enc_surj B y
    rw [toCanonical_app_enc, toCanonical_app_enc]
    refine Quot.sound fun C c t => ?_
    have hout := hcon C c t
    rwa [Rz.δ_enc, Rz.δ_enc, Rz.out_enc, Rz.out_enc,
      Hist.sem_comp, Hist.sem_comp] at hout

/-- **Theorem `thm:reduced-unique` ((i) ↔ (iii), bijectivity)**: since
`π^S` is always surjective, reducedness is equivalent to every
canonical map being a bijection. -/
theorem reduced_iff_bijective (Rz : Realization G) :
    Rz.Reduced ↔
      ∀ B : P, Function.Bijective ((toCanonical Rz).app B) := by
  rw [reduced_iff_injective]
  exact forall_congr' fun B =>
    ⟨fun h => ⟨h, toCanonical_surjective Rz B⟩, And.left⟩

/-- The canonical state equivalence of a reduced realization. -/
noncomputable def reducedEquiv (Rz : Realization G) (hred : Rz.Reduced)
    (B : P) : Rz.S B ≃ Qpred G B :=
  Equiv.ofBijective _ ((reduced_iff_bijective Rz).mp hred B)

/-- **Theorem `thm:reduced-unique` ((iii), inverse morphism)**: for a
reduced realization the canonical morphism has an inverse morphism of
realizations, so `π^S : S → Q₊` is an isomorphism. -/
noncomputable def invCanonical (Rz : Realization G) (hred : Rz.Reduced) :
    RealizationHom (canonicalRealization G) Rz where
  app := fun B => (reducedEquiv Rz hred B).symm
  app_enc := by
    intro B h
    exact (Equiv.symm_apply_eq (reducedEquiv Rz hred B)).mpr
      (toCanonical_app_enc Rz h).symm
  app_δ := by
    intro B C c x
    exact (Equiv.symm_apply_eq (reducedEquiv Rz hred C)).mpr
      ((congrArg ((canonicalRealization G).δ c)
          ((reducedEquiv Rz hred B).apply_symm_apply x)).symm.trans
        ((toCanonical Rz).app_δ c ((reducedEquiv Rz hred B).symm x)).symm)
  app_out := by
    intro B t x
    exact ((toCanonical Rz).app_out t
        ((reducedEquiv Rz hred B).symm x)).symm.trans
      (congrArg (fun y => (canonicalRealization G).out t y)
        ((reducedEquiv Rz hred B).apply_symm_apply x))

/-- Composition of realization morphisms. -/
def RealizationHom.comp {Rz Rz' Rz'' : Realization G}
    (f : RealizationHom Rz Rz') (g : RealizationHom Rz' Rz'') :
    RealizationHom Rz Rz'' where
  app := fun B x => g.app B (f.app B x)
  app_enc := by intro B h; rw [f.app_enc, g.app_enc]
  app_δ := by intro B C c x; rw [f.app_δ, g.app_δ]
  app_out := by intro B t x; rw [g.app_out, f.app_out]

/-- **Theorem `thm:reduced-unique` (uniqueness)**: the canonical
comparison morphism between a realization and any reduced one,
obtained by factoring through `Q₊`.  By `RealizationHom.app_eq` it is
the *unique* morphism between them. -/
noncomputable def reducedHom (Rz Rz' : Realization G)
    (hred' : Rz'.Reduced) : RealizationHom Rz Rz' :=
  (toCanonical Rz).comp (invCanonical Rz' hred')

/-- **Theorem `thm:reduced-unique` (uniqueness, bijectivity)**: the
comparison morphism between two reduced realizations is bijective —
reduced reachable realizations are unique up to a unique isomorphism
compatible with the encoded histories. -/
theorem reducedHom_bijective (Rz Rz' : Realization G)
    (hred : Rz.Reduced) (hred' : Rz'.Reduced) (B : P) :
    Function.Bijective ((reducedHom Rz Rz' hred').app B) :=
  (reducedEquiv Rz' hred' B).symm.bijective.comp
    ((reduced_iff_bijective Rz).mp hred B)

/-! ## `def:predictive-rank` and `cor:finite-minimality` -/

/-- **Definition `def:predictive-rank`**: the total number of
predictive classes over a finite set of reachable endpoint types. -/
noncomputable def predictiveRank (G : GeneratedPresentation O)
    (𝓑 : Finset P) : ℕ :=
  ∑ B ∈ 𝓑, Nat.card (Qpred G B)

/-- **Definition `def:predictive-rank` (finiteness)**: finite
predictive rank on the chosen reachable component. -/
def FinitePredictiveRank (G : GeneratedPresentation O)
    (𝓑 : Finset P) : Prop :=
  ∀ B ∈ 𝓑, Finite (Qpred G B)

/-- **Corollary `cor:finite-minimality` (lower bound)**: every
reachable future-sufficient realization has at least as many states
as predictive classes, at every endpoint. -/
theorem card_qpred_le (Rz : Realization G) (B : P)
    [Finite (Rz.S B)] :
    Nat.card (Qpred G B) ≤ Nat.card (Rz.S B) :=
  Nat.card_le_card_of_surjective _ (toCanonical_surjective Rz B)

/-- **Corollary `cor:finite-minimality` (rank bound)**: summed over a
finite family of endpoints, the predictive rank bounds the total
state count from below. -/
theorem predictiveRank_le (Rz : Realization G) (𝓑 : Finset P)
    (hfin : ∀ B : P, Finite (Rz.S B)) :
    predictiveRank G 𝓑 ≤ ∑ B ∈ 𝓑, Nat.card (Rz.S B) :=
  Finset.sum_le_sum fun B _ => by
    haveI := hfin B
    exact card_qpred_le Rz B

/-- **Corollary `cor:finite-minimality` (equality case)**: a
realization with finite state sets attains the bound at every
endpoint iff it is reduced — `Q₊` is the unique state-minimal
reachable future-sufficient realization (uniqueness by
`reducedHom_bijective` and `RealizationHom.app_eq`). -/
theorem reduced_iff_card_eq (Rz : Realization G)
    (hfin : ∀ B : P, Finite (Rz.S B)) :
    Rz.Reduced ↔
      ∀ B : P, Nat.card (Rz.S B) = Nat.card (Qpred G B) := by
  rw [reduced_iff_bijective]
  refine forall_congr' fun B => ?_
  haveI := hfin B
  rw [Nat.bijective_iff_surjective_and_card]
  exact and_iff_right (toCanonical_surjective Rz B)

/-! ## `prop:selector-existence` and `def:selector` -/

/-- **Definition `def:selector`**: a predictive selector — a
type-preserving section of the quotient map, choosing one
representative history in each predictive class. -/
structure Selector (G : GeneratedPresentation O) where
  /-- The chosen representative of each predictive class. -/
  sec : ∀ {B : P}, Qpred G B → Hist G O.root B
  sec_mk : ∀ {B : P} (x : Qpred G B),
    (Quot.mk _ (sec x) : Qpred G B) = x

/-- **Proposition `prop:selector-existence`**: a type-preserving
selector exists (choice provides one for arbitrary set-sized
quotients; the finite case is subsumed). -/
theorem selector_exists (G : GeneratedPresentation O) :
    ∃ s : ∀ B : P, Qpred G B → Hist G O.root B,
      ∀ (B : P) (x : Qpred G B), (Quot.mk _ (s B x) : Qpred G B) = x :=
  ⟨fun _ x => Quot.out x, fun _ x => Quot.out_eq x⟩

/-- **Proposition `prop:selector-existence`** (packaged): the selector
given by a choice of representatives. -/
noncomputable def canonicalSelector (G : GeneratedPresentation O) :
    Selector G where
  sec := fun x => Quot.out x
  sec_mk := fun x => Quot.out_eq x

instance : Nonempty (Selector G) := ⟨canonicalSelector G⟩

/-- **Definition `def:selector` (predictive compression)**:
`E_s = s ∘ q`, replacing each history by the chosen representative of
its predictive class. -/
def Selector.compress (s : Selector G) {B : P}
    (h : Hist G O.root B) : Hist G O.root B :=
  s.sec (Quot.mk _ h : Qpred G B)

/-! ## `thm:exact-retract` -/

/-- **Theorem `thm:exact-retract` (`q ∘ E_s = q`)**: compression does
not change the predictive class. -/
@[simp] theorem Selector.mk_compress (s : Selector G) {B : P}
    (h : Hist G O.root B) :
    (Quot.mk _ (s.compress h) : Qpred G B) = Quot.mk _ h :=
  s.sec_mk _

/-- Compression fixes the chosen representatives. -/
@[simp] theorem Selector.compress_sec (s : Selector G) {B : P}
    (x : Qpred G B) : s.compress (s.sec x) = s.sec x := by
  change s.sec (Quot.mk _ (s.sec x) : Qpred G B) = s.sec x
  rw [s.sec_mk]

/-- **Theorem `thm:exact-retract` (idempotency)**: `E_s² = E_s`. -/
theorem Selector.compress_idem (s : Selector G) {B : P}
    (h : Hist G O.root B) :
    s.compress (s.compress h) = s.compress h :=
  s.compress_sec (Quot.mk _ h : Qpred G B)

/-- **Theorem `thm:exact-retract` (future sufficiency)**:
`h ≃₊ E_s(h)` — compression preserves all future test statistics. -/
theorem Selector.futureEquiv_compress (s : Selector G) {B : P}
    (h : Hist G O.root B) : FutureEquiv G h (s.compress h) :=
  futureEquiv_of_mk_eq (s.mk_compress h).symm

/-- **Theorem `thm:exact-retract` (image)**: the image of the
compression is exactly the set of selected representatives. -/
theorem Selector.range_compress (s : Selector G) (B : P) :
    Set.range (fun h : Hist G O.root B => s.compress h)
      = Set.range (fun x : Qpred G B => s.sec x) := by
  ext h
  constructor
  · rintro ⟨h₀, rfl⟩
    exact ⟨Quot.mk _ h₀, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨s.sec x, s.compress_sec x⟩

/-- Members of the compressed image are fixed by the compression
(the inverse-bijection identity `s ∘ q = id` on `im E_s`). -/
theorem Selector.compress_eq_of_mem_range (s : Selector G) {B : P}
    {h : Hist G O.root B}
    (hh : h ∈ Set.range (fun h : Hist G O.root B => s.compress h)) :
    s.compress h = h := by
  obtain ⟨h₀, rfl⟩ := hh
  exact s.compress_idem h₀

/-- **Theorem `thm:exact-retract` (restricted bijection)**: the
quotient map restricted to the compressed image is a bijection onto
`Q₊(B)`, with inverse the selector. -/
theorem Selector.bijOn_mk (s : Selector G) (B : P) :
    Set.BijOn (fun h : Hist G O.root B => (Quot.mk _ h : Qpred G B))
      (Set.range (fun h : Hist G O.root B => s.compress h))
      Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro h₁ h₁m h₂ h₂m hq
    have hq' : (Quot.mk _ h₁ : Qpred G B) = Quot.mk _ h₂ := hq
    rw [← s.compress_eq_of_mem_range h₁m,
      ← s.compress_eq_of_mem_range h₂m]
    exact congrArg (fun x : Qpred G B => s.sec x) hq'
  · intro x _
    exact ⟨s.sec x, ⟨s.sec x, s.compress_sec x⟩, s.sec_mk x⟩

/-! ## `def:sufficient-retract` and `thm:retract-classification` -/

/-- **Definition `def:sufficient-retract`**: a type-preserving
idempotent on histories that does not change predictive classes. -/
structure IsSufficientRetract (G : GeneratedPresentation O)
    (E : ∀ B : P, Hist G O.root B → Hist G O.root B) : Prop where
  idem : ∀ (B : P) (h : Hist G O.root B), E B (E B h) = E B h
  mk_eq : ∀ (B : P) (h : Hist G O.root B),
    (Quot.mk _ (E B h) : Qpred G B) = Quot.mk _ h

/-- **Definition `def:sufficient-retract` (class-minimality)**: the
quotient map restricted to the image is a bijection onto `Q₊`. -/
def ClassMinimal (G : GeneratedPresentation O)
    (E : ∀ B : P, Hist G O.root B → Hist G O.root B) : Prop :=
  ∀ B : P,
    Set.BijOn (fun h : Hist G O.root B => (Quot.mk _ h : Qpred G B))
      (Set.range (E B)) Set.univ

/-- **Theorem `thm:retract-classification` ((i) → (ii), retract)**:
every selector compression is an idempotent future-sufficient
retract. -/
theorem Selector.isSufficientRetract (s : Selector G) :
    IsSufficientRetract G (fun B h => s.compress (B := B) h) :=
  ⟨fun _ h => s.compress_idem h, fun _ h => s.mk_compress h⟩

/-- **Theorem `thm:retract-classification` ((i) → (ii),
minimality)**: every selector compression is class-minimal. -/
theorem Selector.classMinimal (s : Selector G) :
    ClassMinimal G (fun B h => s.compress (B := B) h) :=
  fun B => s.bijOn_mk B

/-- **Theorem `thm:retract-classification` ((ii) → (i),
construction)**: a future-sufficient retract determines a selector,
`s(x) := E(some representative of x)`. -/
noncomputable def selectorOfRetract
    {E : ∀ B : P, Hist G O.root B → Hist G O.root B}
    (hE : IsSufficientRetract G E) : Selector G where
  sec := fun {B} x => E B (Quot.out x)
  sec_mk := fun {B} x => by
    rw [hE.mk_eq]
    exact Quot.out_eq x

/-- **Theorem `thm:retract-classification` ((ii) → (i))**: every
class-minimal future-sufficient retract is the compression of the
selector it determines — `E = s ∘ q`. -/
theorem retract_eq_compress
    {E : ∀ B : P, Hist G O.root B → Hist G O.root B}
    (hE : IsSufficientRetract G E) (hmin : ClassMinimal G E) :
    ∀ (B : P) (h : Hist G O.root B),
      E B h = (selectorOfRetract hE).compress h := by
  intro B h
  have hmem1 : E B h ∈ Set.range (E B) := ⟨h, rfl⟩
  have hmem2 : E B (Quot.out (Quot.mk _ h : Qpred G B))
      ∈ Set.range (E B) := ⟨_, rfl⟩
  have hq : (Quot.mk _ (E B h) : Qpred G B)
      = Quot.mk _ (E B (Quot.out (Quot.mk _ h : Qpred G B))) := by
    rw [hE.mk_eq, hE.mk_eq, Quot.out_eq]
  exact (hmin B).injOn hmem1 hmem2 hq

/-- **Theorem `thm:retract-classification` ((i) → (iii),
constancy)**: a compression is constant on each predictive class. -/
theorem Selector.compress_constant (s : Selector G) {B : P}
    {h h' : Hist G O.root B} (hE : FutureEquiv G h h') :
    s.compress h = s.compress h' :=
  congrArg (fun x : Qpred G B => s.sec x) (Quot.sound hE)

/-- **Theorem `thm:retract-classification` ((i) → (iii), fixed
points)**: a compression fixes exactly one history in each
predictive class — the selected representative. -/
theorem Selector.compress_uniqueFixed (s : Selector G) (B : P)
    (x : Qpred G B) :
    ∃! h : Hist G O.root B,
      (Quot.mk _ h : Qpred G B) = x ∧ s.compress h = h := by
  refine ⟨s.sec x, ⟨s.sec_mk x, s.compress_sec x⟩, ?_⟩
  rintro h ⟨rfl, hfix⟩
  exact hfix.symm

/-- **Theorem `thm:retract-classification` ((iii) → (i))**: a map
that is constant on predictive classes and fixes exactly one history
per class is the compression of a selector.  Minimal predictive
retracts are in bijection with choices of one representative per
class. -/
theorem retract_eq_compress_of_constant
    {E : ∀ B : P, Hist G O.root B → Hist G O.root B}
    (hconst : ∀ (B : P) (h h' : Hist G O.root B),
      FutureEquiv G h h' → E B h = E B h')
    (hfix : ∀ (B : P) (x : Qpred G B),
      ∃! h : Hist G O.root B,
        (Quot.mk _ h : Qpred G B) = x ∧ E B h = h) :
    ∃ s : Selector G,
      ∀ (B : P) (h : Hist G O.root B), E B h = s.compress h := by
  refine ⟨⟨fun {B} x => Classical.choose (hfix B x).exists,
    fun {B} x => (Classical.choose_spec (hfix B x).exists).1⟩, ?_⟩
  intro B h
  have hspec :=
    Classical.choose_spec (hfix B (Quot.mk _ h : Qpred G B)).exists
  have hEq := hconst B h
    (Classical.choose (hfix B (Quot.mk _ h : Qpred G B)).exists)
    (futureEquiv_of_mk_eq hspec.1.symm)
  rw [hEq]
  exact hspec.2

/-! ## `cor:retract-conjugacy` -/

/-- **Corollary `cor:retract-conjugacy` (cocycle law)**: composing
two compressions collapses to the outer one —
`U_{s',s''} ∘ U_{s,s'} = U_{s,s''}` on every history. -/
theorem Selector.compress_compress (s s' : Selector G) {B : P}
    (h : Hist G O.root B) :
    s'.compress (s.compress h) = s'.compress h :=
  congrArg (fun x : Qpred G B => s'.sec x) (s.mk_compress h)

/-- **Corollary `cor:retract-conjugacy` (inverse law)**: on the image
of `E_s`, the conjugacy to `s'` followed by the conjugacy back is the
identity (with `U_{s,s} = id` the case `s' = s`, which is
`Selector.compress_eq_of_mem_range`). -/
theorem Selector.transfer_inverse (s s' : Selector G) {B : P}
    {h : Hist G O.root B}
    (hmem : h ∈ Set.range (fun h : Hist G O.root B => s.compress h)) :
    s.compress (s'.compress h) = h := by
  rw [Selector.compress_compress s' s]
  exact s.compress_eq_of_mem_range hmem

/-- **Corollary `cor:retract-conjugacy` (bijection)**:
`U_{s,s'} = s' ∘ q` restricts to a bijection from the image of `E_s`
onto the image of `E_{s'}`. -/
theorem Selector.transfer_bijOn (s s' : Selector G) (B : P) :
    Set.BijOn (fun h : Hist G O.root B => s'.compress h)
      (Set.range (fun h : Hist G O.root B => s.compress h))
      (Set.range (fun h : Hist G O.root B => s'.compress h)) := by
  refine ⟨fun h _ => ⟨h, rfl⟩, ?_, ?_⟩
  · intro h₁ h₁m h₂ h₂m heq
    have hq : (Quot.mk _ h₁ : Qpred G B) = Quot.mk _ h₂ :=
      calc (Quot.mk _ h₁ : Qpred G B)
          = Quot.mk _ (s'.compress h₁) := (s'.mk_compress h₁).symm
        _ = Quot.mk _ (s'.compress h₂) :=
            congrArg (fun h => (Quot.mk _ h : Qpred G B)) heq
        _ = Quot.mk _ h₂ := s'.mk_compress h₂
    rw [← s.compress_eq_of_mem_range h₁m,
      ← s.compress_eq_of_mem_range h₂m]
    exact congrArg (fun x : Qpred G B => s.sec x) hq
  · intro h hmem
    refine ⟨s.compress h, ⟨h, rfl⟩, ?_⟩
    change s'.compress (s.compress h) = h
    rw [Selector.compress_compress s s']
    exact s'.compress_eq_of_mem_range hmem

/-- **Corollary `cor:retract-conjugacy` (uniqueness)**: `U_{s,s'}` is
the unique map into the image of `E_{s'}` that preserves predictive
classes on the image of `E_s`. -/
theorem Selector.transfer_unique (s s' : Selector G) {B : P}
    (F : Hist G O.root B → Hist G O.root B)
    (hrange : ∀ h : Hist G O.root B,
      F h ∈ Set.range (fun h : Hist G O.root B => s'.compress h))
    (hq : ∀ h : Hist G O.root B,
      (Quot.mk _ (F h) : Qpred G B) = Quot.mk _ h) :
    ∀ h ∈ Set.range (fun h : Hist G O.root B => s.compress h),
      F h = s'.compress h := by
  intro h _
  have h1 := s'.compress_eq_of_mem_range (hrange h)
  rw [← h1]
  exact congrArg (fun x : Qpred G B => s'.sec x) (hq h)

/-! ## `thm:renewal-realization` -/

/-- **Construction `constr:renewal-map`**: "update along the
continuation `c`, then return to the predictive image" —
`Φ_c^{(s)} = E_s ∘ U_c`. -/
def Selector.renewal (s : Selector G) {B C : P} (c : Hist G B C)
    (h : Hist G O.root B) : Hist G O.root C :=
  s.compress (h.comp c)

/-- The renewal maps land in the selected predictive image. -/
theorem Selector.renewal_mem_range (s : Selector G) {B C : P}
    (c : Hist G B C) (h : Hist G O.root B) :
    s.renewal c h
      ∈ Set.range (fun h : Hist G O.root C => s.compress h) :=
  ⟨h.comp c, rfl⟩

/-- **Theorem `thm:renewal-realization` (conjugacy)**:
`q ∘ Φ_c^{(s)} = Q₊(c) ∘ q` — the renewal action is conjugate to the
canonical predictive action under the quotient map. -/
theorem Selector.mk_renewal (s : Selector G) {B C : P}
    (c : Hist G B C) (h : Hist G O.root B) :
    (Quot.mk _ (s.renewal c h) : Qpred G C)
      = Qmap c (Quot.mk _ h) :=
  s.mk_compress _

/-- **Theorem `thm:renewal-realization` (identity law)**:
`Φ_{id}^{(s)} = id` on the selected predictive image. -/
theorem Selector.renewal_nil (s : Selector G) {B : P}
    {h : Hist G O.root B}
    (hmem : h ∈ Set.range (fun h : Hist G O.root B => s.compress h)) :
    s.renewal (Hist.nil B) h = h := by
  change s.compress (h.comp (Hist.nil B)) = h
  rw [Hist.comp_nil]
  exact s.compress_eq_of_mem_range hmem

/-- **Theorem `thm:renewal-realization` (composition law)**:
`Φ_d^{(s)} ∘ Φ_c^{(s)} = Φ_{d∘c}^{(s)}` — the renewal maps form an
exact action of the generated continuation category. -/
theorem Selector.renewal_comp (s : Selector G) {B C D : P}
    (c : Hist G B C) (d : Hist G C D) (h : Hist G O.root B) :
    s.renewal d (s.renewal c h) = s.renewal (c.comp d) h := by
  have h1 : (Quot.mk _ ((s.compress (h.comp c)).comp d) : Qpred G D)
      = Quot.mk _ (h.comp (c.comp d)) := by
    have h2 : (Quot.mk _ ((s.compress (h.comp c)).comp d) : Qpred G D)
        = Qmap d (Quot.mk _ (s.compress (h.comp c))) := rfl
    rw [h2, s.mk_compress]
    change Quot.mk _ ((h.comp c).comp d) = _
    rw [Hist.comp_assoc]
  exact congrArg (fun x : Qpred G D => s.sec x) h1

/-- **Theorem `thm:renewal-realization` (selector independence)**: the
canonical conjugacy `U_{s,s'} = s' ∘ q` intertwines the renewal
actions of any two selectors — the renewal realization is independent
of the selector up to the conjugacies of `cor:retract-conjugacy`. -/
theorem Selector.renewal_transfer (s s' : Selector G) {B C : P}
    (c : Hist G B C) (h : Hist G O.root B) :
    s'.compress (s.renewal c h) = s'.renewal c (s'.compress h) := by
  have h1 : (Quot.mk _ (s.renewal c h) : Qpred G C)
      = Quot.mk _ (h.comp c) := s.mk_compress _
  have h2 : (Quot.mk _ ((s'.compress h).comp c) : Qpred G C)
      = Quot.mk _ (h.comp c) := by
    have h3 : (Quot.mk _ ((s'.compress h).comp c) : Qpred G C)
        = Qmap c (Quot.mk _ (s'.compress h)) := rfl
    rw [h3, s'.mk_compress]
    rfl
  change s'.sec (Quot.mk _ (s.renewal c h) : Qpred G C)
      = s'.sec (Quot.mk _ ((s'.compress h).comp c) : Qpred G C)
  rw [h1, h2]

end NCG.Upstream
