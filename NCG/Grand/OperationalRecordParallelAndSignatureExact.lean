/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalRecordCompletionFunctoriality

/-!
# Parallel composition and derived signature preservation

This file closes the two gaps named by the fidelity audit of
`thm:operational-record-completion`:

* it constructs the synchronized parallel product of two word-record machines and proves
  componentwise execution, preservation of complete future signatures, and the induced
  surjective map onto its minimal completion;
* it derives preservation of the complete future signature from the concrete primitive-step
  and Read intertwining laws of a label-preserving operational morphism.  Thus cutoff descent
  no longer takes signature preservation as a separate abstract hypothesis.
-/

namespace NCG
namespace OperationalRecordParallelAndSignature

/-! ## Concrete parallel composition -/

variable {A B R S D E V W : Type*}

/-- Synchronized parallel composition: primitive labels, ledger states, Read coordinates,
and Read values are paired componentwise. -/
def parallelMachine (M : WordRecordMachine A R D V)
    (N : WordRecordMachine B S E W) :
    WordRecordMachine (A × B) (R × S) (D × E) (V × W) where
  step ab rs := (M.step ab.1 rs.1, N.step ab.2 rs.2)
  read de rs := (M.read de.1 rs.1, N.read de.2 rs.2)

/-- A parallel word executes componentwise on the two projected words. -/
theorem parallel_run
    (M : WordRecordMachine A R D V) (N : WordRecordMachine B S E W)
    (word : List (A × B)) (r : R) (s : S) :
    (parallelMachine M N).run word (r, s) =
      (M.run (word.map Prod.fst) r, N.run (word.map Prod.snd) s) := by
  induction word generalizing r s with
  | nil => rfl
  | cons ab word ih =>
      simp only [WordRecordMachine.run_cons, List.map_cons, parallelMachine]
      exact ih (M.step ab.1 r) (N.step ab.2 s)

/-- Equality of both component future signatures implies equality of the complete future
signature of the parallel product. -/
theorem parallel_future_signature_preserved
    (M : WordRecordMachine A R D V) (N : WordRecordMachine B S E W)
    {r r' : R} {s s' : S}
    (hM : M.futureSig r = M.futureSig r')
    (hN : N.futureSig s = N.futureSig s') :
    (parallelMachine M N).futureSig (r, s) =
      (parallelMachine M N).futureSig (r', s') := by
  funext query
  rcases query with ⟨word, d, e⟩
  have hM' := congrFun hM (word.map Prod.fst, d)
  have hN' := congrFun hN (word.map Prod.snd, e)
  have hMread : M.read d (M.run (word.map Prod.fst) r) =
      M.read d (M.run (word.map Prod.fst) r') := by
    simpa only [WordRecordMachine.futureSig] using hM'
  have hNread : N.read e (N.run (word.map Prod.snd) s) =
      N.read e (N.run (word.map Prod.snd) s') := by
    simpa only [WordRecordMachine.futureSig] using hN'
  change
    (M.read d ((parallelMachine M N).run word (r, s)).1,
        N.read e ((parallelMachine M N).run word (r, s)).2) =
      (M.read d ((parallelMachine M N).run word (r', s')).1,
        N.read e ((parallelMachine M N).run word (r', s')).2)
  rw [parallel_run M N word r s, parallel_run M N word r' s']
  exact Prod.ext hMread hNread

/-- The quotient by the pair of component future signatures maps canonically onto the
minimal future record of the parallel product. -/
def parallelMinimalRecordMap
    (M : WordRecordMachine A R D V) (N : WordRecordMachine B S E W) :
    MinRec (fun rs : R × S => (M.futureSig rs.1, N.futureSig rs.2)) →
      MinRec (parallelMachine M N).futureSig :=
  minimalRecordMap
    (fun rs : R × S => (M.futureSig rs.1, N.futureSig rs.2))
    (parallelMachine M N).futureSig id
    (fun h => parallel_future_signature_preserved M N
      (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Parallel completion is not merely functorial: the canonical map from paired component
future data onto the parallel minimal record is surjective. -/
theorem parallelMinimalRecordMap_surjective
    (M : WordRecordMachine A R D V) (N : WordRecordMachine B S E W) :
    Function.Surjective (parallelMinimalRecordMap M N) := by
  intro q
  induction q using Quotient.ind with
  | _ rs =>
      exact ⟨Quotient.mk
        (minRecSetoid (fun x : R × S => (M.futureSig x.1, N.futureSig x.2))) rs, rfl⟩

/-! ## Signature preservation derived from operational morphism laws -/

variable {L R₁ R₂ Q X : Type*}

/-- A label-preserving map that intertwines primitive updates and all declared Reads
automatically preserves the entire old future signature. -/
theorem future_signature_map_exact
    (M : WordRecordMachine L R₁ Q X) (N : WordRecordMachine L R₂ Q X)
    (f : R₁ → R₂)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (hread : ∀ q r, N.read q (f r) = M.read q r) (r : R₁) :
    N.futureSig (f r) = M.futureSig r := by
  funext query
  rw [WordRecordMachine.futureSig, WordRecordMachine.futureSig]
  rw [← WordRecordMachine.run_map_exact M N f hstep query.1 r]
  exact hread query.2 (M.run query.1 r)

/-- Consequently future-equivalent source records remain future equivalent after the
operational morphism; no separate signature-preservation hypothesis is needed. -/
theorem future_equivalence_preserved_of_step_and_read
    (M : WordRecordMachine L R₁ Q X) (N : WordRecordMachine L R₂ Q X)
    (f : R₁ → R₂)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (hread : ∀ q r, N.read q (f r) = M.read q r)
    {r r' : R₁} (h : M.futureSig r = M.futureSig r') :
    N.futureSig (f r) = N.futureSig (f r') := by
  rw [future_signature_map_exact M N f hstep hread r,
    future_signature_map_exact M N f hstep hread r', h]

/-- The induced minimal-record map for a genuine operational morphism, with signature
compatibility derived internally from step and Read preservation. -/
def operationalMorphismMinimalRecordMap
    (M : WordRecordMachine L R₁ Q X) (N : WordRecordMachine L R₂ Q X)
    (f : R₁ → R₂)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (hread : ∀ q r, N.read q (f r) = M.read q r) :
    MinRec M.futureSig → MinRec N.futureSig :=
  minimalRecordMap M.futureSig N.futureSig f
    (future_equivalence_preserved_of_step_and_read M N f hstep hread)

/-- The derived cutoff map intertwines every primitive update. -/
theorem operationalMorphismMinimalRecordMap_intertwines_step
    (M : WordRecordMachine L R₁ Q X) (N : WordRecordMachine L R₂ Q X)
    (f : R₁ → R₂)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (hread : ∀ q r, N.read q (f r) = M.read q r) (a : L) :
    operationalMorphismMinimalRecordMap M N f hstep hread ∘ M.quotientStep a =
      N.quotientStep a ∘
        operationalMorphismMinimalRecordMap M N f hstep hread :=
  M.minimalRecordMap_intertwines_step N f
    (future_equivalence_preserved_of_step_and_read M N f hstep hread) hstep a

/-- Exact closure packet for O3 and O5: parallel composition has a surjective canonical
minimal completion, and every step/Read-preserving morphism descends and intertwines the
minimal updates without an extra future-signature axiom. -/
theorem parallel_and_operational_morphism_completion
    (M₁ : WordRecordMachine A R D V) (M₂ : WordRecordMachine B S E W)
    (M : WordRecordMachine L R₁ Q X) (N : WordRecordMachine L R₂ Q X)
    (f : R₁ → R₂)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (hread : ∀ q r, N.read q (f r) = M.read q r) :
    Function.Surjective (parallelMinimalRecordMap M₁ M₂) ∧
      (∀ a : L,
        operationalMorphismMinimalRecordMap M N f hstep hread ∘ M.quotientStep a =
          N.quotientStep a ∘
            operationalMorphismMinimalRecordMap M N f hstep hread) :=
  ⟨parallelMinimalRecordMap_surjective M₁ M₂,
    operationalMorphismMinimalRecordMap_intertwines_step M N f hstep hread⟩

end OperationalRecordParallelAndSignature
end NCG
