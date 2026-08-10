/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GeneratedMinimalRecord

/-!
# Canonical causal efficient-score records

This module specializes the generated minimal-record construction to finite
causal score machines and proves the cutoff-refinement quotient map.  The
complete future score-cylinder signature is a right congruence, so primitive
transitions are strongly lumpable; every score coordinate factors uniquely;
and every other future-sufficient record maps uniquely and surjectively onto
the minimal one.
-/

namespace NCG

namespace WordRecordMachine

/-- The exact causal efficient-score record.  Empty-word future coordinates
are the current scores; nonempty words are the future score cylinders. -/
theorem causalEfficientScoreRecord_exact
    {A R Score V S : Type*} (M : WordRecordMachine A R Score V)
    (c : R → S) (hsurj : Function.Surjective c)
    (hsufficient : ∀ wd : List A × Score, ∃ f : S → V,
      ∀ r, f (c r) = M.read wd.2 (M.run wd.1 r)) :
    (∀ s : Score, ∃! scorebar : MinRec M.futureSig → V,
        ∀ r, scorebar (Quotient.mk (minRecSetoid M.futureSig) r) =
          M.read s r)
    ∧ (∀ a : A, ∃! stepbar : MinRec M.futureSig → MinRec M.futureSig,
        ∀ r, stepbar (Quotient.mk (minRecSetoid M.futureSig) r) =
          Quotient.mk (minRecSetoid M.futureSig) (M.step a r))
    ∧ (∃! q : S → MinRec M.futureSig,
        Function.Surjective q ∧
        ∀ r, q (c r) = Quotient.mk (minRecSetoid M.futureSig) r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    refine ⟨M.quotientRead ([], s), fun r => rfl, ?_⟩
    intro f hf
    exact M.quotient_fun_unique f (M.quotientRead ([], s)) fun r => by
      rw [hf r]
      rfl
  · intro a
    refine ⟨M.quotientStep a, fun r => rfl, ?_⟩
    intro stepbar hstepbar
    exact M.quotient_fun_unique stepbar (M.quotientStep a) fun r => by
      rw [hstepbar r]
      rfl
  · choose f hf using hsufficient
    let g : S → (List A × Score → V) := fun s wd => f wd s
    have hfac : ∀ r, g (c r) = M.futureSig r := by
      intro r
      funext wd
      exact hf wd r
    obtain ⟨q, hq, huniq⟩ := minimal_record_universal
      M.futureSig c g hsurj hfac
    have hqsurj : Function.Surjective q := by
      intro target
      induction target using Quotient.ind with
      | _ r => exact ⟨c r, hq r⟩
    refine ⟨q, ⟨hqsurj, hq⟩, ?_⟩
    intro q' hq'
    exact huniq q' hq'.2

/-- Preservation of every old future signature along a surjective cutoff map
induces the unique surjective map from the fine minimal record onto the old
minimal record.  This is the strict quotient-system clause. -/
theorem minimalScoreRecord_refinementQuotient
    {Rfine Rcoarse SigFine SigCoarse : Type*}
    (fineSig : Rfine → SigFine) (coarseSig : Rcoarse → SigCoarse)
    (π : Rfine → Rcoarse) (hπ : Function.Surjective π)
    (hpreserve : ∀ x y, fineSig x = fineSig y →
      coarseSig (π x) = coarseSig (π y)) :
    ∃! q : MinRec fineSig → MinRec coarseSig,
      Function.Surjective q
      ∧ ∀ r, q (Quotient.mk (minRecSetoid fineSig) r) =
        Quotient.mk (minRecSetoid coarseSig) (π r) := by
  let q : MinRec fineSig → MinRec coarseSig :=
    Quotient.lift
      (fun r => Quotient.mk (minRecSetoid coarseSig) (π r))
      (fun x y h => Quotient.sound (hpreserve x y h))
  have hq : ∀ r, q (Quotient.mk (minRecSetoid fineSig) r) =
      Quotient.mk (minRecSetoid coarseSig) (π r) := fun r => rfl
  have hsurj : Function.Surjective q := by
    intro target
    induction target using Quotient.ind with
    | _ r =>
        obtain ⟨r', hr'⟩ := hπ r
        refine ⟨Quotient.mk (minRecSetoid fineSig) r', ?_⟩
        rw [hq, hr']
  refine ⟨q, ⟨hsurj, hq⟩, ?_⟩
  intro q' hq'
  funext source
  induction source using Quotient.ind with
  | _ r =>
      rw [hq'.2 r, hq r]

/-- Cutoff refinements of causal score machines therefore form a strict
system of surjective maps between their canonical minimal records. -/
theorem causalEfficientScoreRecord_cutoffQuotient
    {A Rfine Rcoarse ScoreFine ScoreCoarse V : Type*}
    (Mfine : WordRecordMachine A Rfine ScoreFine V)
    (Mcoarse : WordRecordMachine A Rcoarse ScoreCoarse V)
    (π : Rfine → Rcoarse) (hπ : Function.Surjective π)
    (hfuture : ∀ x y, Mfine.futureSig x = Mfine.futureSig y →
      Mcoarse.futureSig (π x) = Mcoarse.futureSig (π y)) :
    ∃! q : MinRec Mfine.futureSig → MinRec Mcoarse.futureSig,
      Function.Surjective q
      ∧ ∀ r, q (Quotient.mk (minRecSetoid Mfine.futureSig) r) =
        Quotient.mk (minRecSetoid Mcoarse.futureSig) (π r) :=
  minimalScoreRecord_refinementQuotient
    Mfine.futureSig Mcoarse.futureSig π hπ hfuture

end WordRecordMachine

end NCG
