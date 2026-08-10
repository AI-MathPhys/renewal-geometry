/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordCompletionOp
import NCG.Grand.GeneratedMinimalRecord
import NCG.Grand.CombTomography

/-!
# Functoriality of operational record completion

This module supplies the quotient and word-level clauses of
`thm:operational-record-completion`.  Together with the Kraus, discard, and
composition identities in `RecordCompletionOp`, it proves that the minimal
all-future record is canonical under unread refinements and compatible cutoff
maps, and that separating terminal Reads recover the full generated ledger.
-/

namespace NCG

open Matrix
open scoped Kronecker ComplexOrder

/-- The Choi matrix of every record-completed Kraus branch is positive, the
finite-dimensional certificate of complete positivity. -/
theorem completedKrausChoi_pos {r c : Type*} {ι : Type}
    [Fintype r] [Fintype c] [Fintype ι]
    (W : Matrix r r ℂ) (K : ι → Matrix c c ℂ) :
    (∑ j, Matrix.vecMulVec
      (fun p : (r × c) × (r × c) => (W ⊗ₖ K j) p.2 p.1)
      (star fun p : (r × c) × (r × c) => (W ⊗ₖ K j) p.2 p.1)).PosSemidef :=
  (comb_tomography (m := r × c)).2.1 (fun j => W ⊗ₖ K j)

/-- A normalized family of core instruments and a complete orthogonal writer
partition give a normalized completed instrument. -/
theorem completedInstrument_normalized
    {r c a : Type*} {ι : Type} [Fintype r] [Fintype c] [Fintype a] [Fintype ι]
    [DecidableEq r] [DecidableEq c]
    (W : a → Matrix r r ℂ) (K : a → ι → Matrix c c ℂ)
    (hW : ∑ x, (W x)ᴴ * W x = 1)
    (hK : ∀ x, ∑ j, (K x j)ᴴ * K x j = 1) :
    ∑ x, ∑ j, (W x ⊗ₖ K x j)ᴴ * (W x ⊗ₖ K x j)
      = (1 : Matrix (r × c) (r × c) ℂ) := by
  have hbranch : ∀ x, ∑ j, (W x ⊗ₖ K x j)ᴴ * (W x ⊗ₖ K x j)
      = ((W x)ᴴ * W x) ⊗ₖ (1 : Matrix c c ℂ) := by
    intro x
    calc
      ∑ j, (W x ⊗ₖ K x j)ᴴ * (W x ⊗ₖ K x j)
          = ((W x)ᴴ * W x) ⊗ₖ (∑ j, (K x j)ᴴ * K x j) :=
            (operational_record_completion (r := r) (c := c)).1
              (ι := ι) (W x) (K x)
      _ = ((W x)ᴴ * W x) ⊗ₖ (1 : Matrix c c ℂ) := by rw [hK x]
  rw [Finset.sum_congr rfl fun x _ => hbranch x]
  ext p q
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [← Finset.sum_mul]
  have hWpq := congrFun (congrFun hW p.1) q.1
  simp only [Matrix.sum_apply, Matrix.one_apply] at hWpq
  rw [hWpq]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [Prod.ext_iff, h1, h2]

/-- A map preserving future equivalence descends canonically to minimal
records. -/
def minimalRecordMap {R S SigR SigS : Type*}
    (sigR : R → SigR) (sigS : S → SigS) (f : R → S)
    (h : ∀ {r r'}, sigR r = sigR r' → sigS (f r) = sigS (f r')) :
    MinRec sigR → MinRec sigS :=
  Quotient.lift
    (fun r => Quotient.mk (minRecSetoid sigS) (f r))
    (fun _ _ hrr => Quotient.sound (h hrr))

@[simp] theorem minimalRecordMap_mk {R S SigR SigS : Type*}
    (sigR : R → SigR) (sigS : S → SigS) (f : R → S)
    (h : ∀ {r r'}, sigR r = sigR r' → sigS (f r) = sigS (f r'))
    (r : R) :
    minimalRecordMap sigR sigS f h
        (Quotient.mk (minRecSetoid sigR) r)
      = Quotient.mk (minRecSetoid sigS) (f r) := rfl

/-- Minimal-record descent preserves identity maps. -/
theorem minimalRecordMap_id {R Sig : Type*} (sig : R → Sig) :
    minimalRecordMap sig sig id (fun h => h) = id := by
  funext q
  induction q using Quotient.ind with
  | _ r => rfl

/-- Minimal-record descent preserves composition, so compatible cutoffs form
a strict functor on the future-equivalence quotients. -/
theorem minimalRecordMap_comp {R S T SigR SigS SigT : Type*}
    (sigR : R → SigR) (sigS : S → SigS) (sigT : T → SigT)
    (f : R → S) (g : S → T)
    (hf : ∀ {r r'}, sigR r = sigR r' → sigS (f r) = sigS (f r'))
    (hg : ∀ {s s'}, sigS s = sigS s' → sigT (g s) = sigT (g s')) :
    minimalRecordMap sigR sigT (g ∘ f) (fun h => hg (hf h))
      = minimalRecordMap sigS sigT g hg ∘ minimalRecordMap sigR sigS f hf := by
  funext q
  induction q using Quotient.ind with
  | _ r => rfl

namespace WordRecordMachine

variable {A R S D V : Type*}

/-- Execute a word directly on the canonical minimal record. -/
def quotientRun (M : WordRecordMachine A R D V) :
    List A → MinRec M.futureSig → MinRec M.futureSig
  | [], q => q
  | a :: w, q => M.quotientRun w (M.quotientStep a q)

/-- Word-length induction: descended execution exactly agrees with executing
the original record machine and then taking its minimal class. -/
@[simp] theorem quotientRun_mk (M : WordRecordMachine A R D V)
    (w : List A) (r : R) :
    M.quotientRun w (Quotient.mk (minRecSetoid M.futureSig) r)
      = Quotient.mk (minRecSetoid M.futureSig) (M.run w r) := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [quotientRun, quotientStep_mk, run_cons]
      exact ih (M.step a r)

/-- A label-preserving machine morphism preserves every finite word. -/
theorem run_map_exact (M : WordRecordMachine A R D V)
    (N : WordRecordMachine A S D V) (f : R → S)
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (w : List A) (r : R) :
    f (M.run w r) = N.run w (f r) := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [run_cons]
      rw [← hstep, ih]

/-- A compatible cutoff morphism descends to minimal records and intertwines
every primitive quotient update. -/
theorem minimalRecordMap_intertwines_step
    (M : WordRecordMachine A R D V) (N : WordRecordMachine A S D V)
    (f : R → S)
    (hfuture : ∀ {r r'}, M.futureSig r = M.futureSig r' →
      N.futureSig (f r) = N.futureSig (f r'))
    (hstep : ∀ a r, f (M.step a r) = N.step a (f r))
    (a : A) :
    minimalRecordMap M.futureSig N.futureSig f hfuture ∘ M.quotientStep a
      = N.quotientStep a ∘
          minimalRecordMap M.futureSig N.futureSig f hfuture := by
  funext q
  induction q using Quotient.ind with
  | _ r =>
      simp only [Function.comp_apply, quotientStep_mk, minimalRecordMap_mk]
      rw [hstep]

/-- Unread refinements compatible with updates and Reads have canonically
isomorphic minimal operational completions. -/
theorem unreadRefinement_minimalCompletion
    (M' : WordRecordMachine A S D V) (M : WordRecordMachine A R D V)
    (f : S → R) (hsurj : Function.Surjective f)
    (hstep : ∀ a s, f (M'.step a s) = M.step a (f s))
    (hread : ∀ d s, M'.read d s = M.read d (f s)) :
    Nonempty (MinRec M'.futureSig ≃ MinRec M.futureSig) :=
  (record_refinement_bundle_exact M' M f hsurj hstep hread).1

/-- If the complete future signature separates ledger points (in particular,
if actual point Reads do), the minimal record is the full generated ledger. -/
noncomputable def fullLedgerEquiv (M : WordRecordMachine A R D V)
    (hsep : Function.Injective M.futureSig) :
    MinRec M.futureSig ≃ R := by
  let unpack : MinRec M.futureSig → R :=
    Quotient.lift id (fun _ _ h => hsep h)
  refine Equiv.ofBijective unpack ⟨?_, ?_⟩
  · intro q q' hqq
    induction q using Quotient.ind with
    | _ r =>
      induction q' using Quotient.ind with
      | _ r' =>
        exact Quotient.sound (congrArg M.futureSig hqq)
  · intro r
    exact ⟨Quotient.mk (minRecSetoid M.futureSig) r, rfl⟩

/-- Exact quotient-level completion bundle: word recovery, refinement
canonicity, cutoff functoriality, and full-ledger recovery. -/
theorem operationalRecordCompletionFunctoriality
    (M : WordRecordMachine A R D V) :
    (∀ w r, M.quotientRun w
        (Quotient.mk (minRecSetoid M.futureSig) r)
      = Quotient.mk (minRecSetoid M.futureSig) (M.run w r))
    ∧ M.MinimalRecordExact
    ∧ (Function.Injective M.futureSig →
        Nonempty (MinRec M.futureSig ≃ R)) := by
  refine ⟨M.quotientRun_mk, M.minimal_record_exact, ?_⟩
  intro hsep
  exact ⟨M.fullLedgerEquiv hsep⟩

end WordRecordMachine

end NCG
