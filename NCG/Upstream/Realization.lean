/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.Operational

/-!
# Future-sufficient realizations and the universal predictive quotient

Second upstream batch (continued), covering `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:realization` — `NCG.Upstream.Realization`: reachable
  future-sufficient realizations (surjective encoding, transitions
  intertwining continuation, outputs reproducing test statistics,
  functor laws);
* `lem:sufficient` — `Realization.sufficient`: equal encoded states
  have future-equivalent histories;
* `def:realization-morphism` — `RealizationHom` and its rigidity
  (`RealizationHom.app_eq`: the encoding condition determines a
  morphism uniquely);
* `thm:universal-quotient` — `canonicalRealization`, `toCanonical`,
  `toCanonical_app_enc`, `toCanonical_surjective`,
  `toCanonical_unique`: the canonical predictive realization on
  `Q₊` is terminal — every realization maps onto it by
  `π^S(r_B(h)) = [h]`, surjectively and uniquely;
* `def:reduced` — `Realization.Reduced`: reduced (observable)
  realizations.
-/

namespace NCG.Upstream

open CategoryTheory

universe u v w t

variable {P : Type u} [Category.{v} P] {W : Type w} {T : P → Type t}
variable {O : OperationalSystem P W T}

/-- **Definition `def:realization` (reachable future-sufficient
realization)**: state sets, a surjective encoding of histories,
transitions intertwining every generated continuation, outputs
reproducing the terminal test statistics, and the transition functor
laws. -/
structure Realization (G : GeneratedPresentation O) where
  /-- The state set at each reachable endpoint. -/
  S : P → Type (max u v)
  /-- The (surjective) encoding of histories into states. -/
  enc : ∀ {B : P}, Hist G O.root B → S B
  enc_surj : ∀ B : P, Function.Surjective (enc (B := B))
  /-- Transition along a generated continuation. -/
  δ : ∀ {B C : P}, Hist G B C → S B → S C
  δ_enc : ∀ {B C : P} (c : Hist G B C) (h : Hist G O.root B),
    δ c (enc h) = enc (h.comp c)
  /-- Output of a terminal test on a state. -/
  out : ∀ {B : P}, T B → S B → W
  out_enc : ∀ {B : P} (t : T B) (h : Hist G O.root B),
    out t (enc h) = O.ev t h.sem
  δ_id : ∀ {B : P} (x : S B), δ (Hist.nil B) x = x
  δ_comp : ∀ {B C D : P} (c : Hist G B C) (d : Hist G C D) (x : S B),
    δ (c.comp d) x = δ d (δ c x)

variable {G : GeneratedPresentation O}

/-- **Lemma `lem:sufficient`**: equality of realized states implies
predictive equivalence of the encoded histories — the encoded state
reproduces every future test statistic. -/
theorem Realization.sufficient (Rz : Realization G) {B : P}
    {h h' : Hist G O.root B} (henc : Rz.enc h = Rz.enc h') :
    FutureEquiv G h h' := by
  intro C c t
  have h1 : Rz.enc (h.comp c) = Rz.enc (h'.comp c) := by
    rw [← Rz.δ_enc, ← Rz.δ_enc, henc]
  have h2 := congrArg (Rz.out t) h1
  rwa [Rz.out_enc, Rz.out_enc, Hist.sem_comp, Hist.sem_comp] at h2

/-- **Definition `def:realization-morphism`**: a family of state maps
compatible with encodings, transitions, and outputs. -/
structure RealizationHom (Rz : Realization G)
    (Rz' : Realization G) where
  app : ∀ B : P, Rz.S B → Rz'.S B
  app_enc : ∀ {B : P} (h : Hist G O.root B),
    app B (Rz.enc h) = Rz'.enc h
  app_δ : ∀ {B C : P} (c : Hist G B C) (x : Rz.S B),
    app C (Rz.δ c x) = Rz'.δ c (app B x)
  app_out : ∀ {B : P} (t : T B) (x : Rz.S B),
    Rz'.out t (app B x) = Rz.out t x

/-- **Definition `def:realization-morphism` (rigidity)**: the encoding
condition already determines a morphism uniquely, because the
encodings are surjective. -/
theorem RealizationHom.app_eq {Rz Rz' : Realization G}
    (f g : RealizationHom Rz Rz') : f.app = g.app := by
  funext B x
  obtain ⟨h, rfl⟩ := Rz.enc_surj B x
  rw [f.app_enc, g.app_enc]

/-- **Theorem `thm:universal-quotient` (the canonical predictive
realization)**: `Q₊` with the class encoding, the transition maps of
`cor:quotient-action`, and the class outputs (well defined because
the identity continuation is among the future contexts). -/
noncomputable def canonicalRealization (G : GeneratedPresentation O) :
    Realization G where
  S := Qpred G
  enc := Quot.mk _
  enc_surj := fun _ x => Quot.exists_rep x
  δ := fun c => Qmap c
  δ_enc := fun _ _ => rfl
  out := fun t => Quot.lift (fun h => O.ev t h.sem) (by
    intro h h' hE
    have := hE _ (Hist.nil _) t
    simpa using this)
  out_enc := fun _ _ => rfl
  δ_id := fun x => congrFun (Qmap_nil _) x
  δ_comp := fun c d x => congrFun (Qmap_comp c d) x

/-- **Theorem `thm:universal-quotient` (the universal morphism)**:
`π^S_B(r_B(h)) = [h]` — well defined by `lem:sufficient`. -/
noncomputable def toCanonical (Rz : Realization G) :
    RealizationHom Rz (canonicalRealization G) where
  app := fun B x => Quot.mk _ (Classical.choose (Rz.enc_surj B x))
  app_enc := by
    intro B h
    exact Quot.sound (Rz.sufficient
      (Classical.choose_spec (Rz.enc_surj B (Rz.enc h))))
  app_δ := by
    intro B C c x
    obtain ⟨h, rfl⟩ := Rz.enc_surj B x
    have h1 : Quot.mk _ (Classical.choose (Rz.enc_surj B (Rz.enc h)))
        = (Quot.mk _ h : Qpred G B) :=
      Quot.sound (Rz.sufficient
        (Classical.choose_spec (Rz.enc_surj B (Rz.enc h))))
    rw [Rz.δ_enc]
    have h2 : Quot.mk _
        (Classical.choose (Rz.enc_surj C (Rz.enc (h.comp c))))
        = (Quot.mk _ (h.comp c) : Qpred G C) :=
      Quot.sound (Rz.sufficient
        (Classical.choose_spec (Rz.enc_surj C (Rz.enc (h.comp c)))))
    rw [h1, h2]
    rfl
  app_out := by
    intro B t x
    obtain ⟨h, rfl⟩ := Rz.enc_surj B x
    have h1 : Quot.mk _ (Classical.choose (Rz.enc_surj B (Rz.enc h)))
        = (Quot.mk _ h : Qpred G B) :=
      Quot.sound (Rz.sufficient
        (Classical.choose_spec (Rz.enc_surj B (Rz.enc h))))
    rw [h1, Rz.out_enc]
    rfl

/-- **Theorem `thm:universal-quotient` (formula)**: the universal
morphism sends every encoded history to its predictive class. -/
theorem toCanonical_app_enc (Rz : Realization G)
    {B : P} (h : Hist G O.root B) :
    (toCanonical Rz).app B (Rz.enc h) = Quot.mk _ h :=
  (toCanonical Rz).app_enc h

/-- **Theorem `thm:universal-quotient` (surjectivity)**: each
`π^S_B` is surjective — every class is the image of a reachable
state. -/
theorem toCanonical_surjective (Rz : Realization G)
    (B : P) : Function.Surjective ((toCanonical Rz).app B) := by
  intro x
  obtain ⟨h, rfl⟩ := Quot.exists_rep x
  exact ⟨Rz.enc h, toCanonical_app_enc Rz h⟩

/-- **Theorem `thm:universal-quotient` (terminality)**: any morphism
into the canonical realization agrees with `π^S` — the canonical
predictive realization is terminal. -/
theorem toCanonical_unique (Rz : Realization G)
    (f : RealizationHom Rz (canonicalRealization G)) :
    f.app = (toCanonical Rz).app :=
  RealizationHom.app_eq f (toCanonical Rz)

/-- **Definition `def:reduced` (reduced or observable realization)**:
distinct states are separated by some generated future experiment. -/
def Realization.Reduced (Rz : Realization G) : Prop :=
  ∀ {B : P} (x y : Rz.S B), x ≠ y →
    ∃ (C : P) (c : Hist G B C) (t : T C),
      Rz.out t (Rz.δ c x) ≠ Rz.out t (Rz.δ c y)

end NCG.Upstream
