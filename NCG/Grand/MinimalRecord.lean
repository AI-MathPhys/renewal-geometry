/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical minimal-readable-record theorem and the causal
  efficient-score record
  (`thm:minimal-record`, `cor:causal-efficient-score-record`,
   Gran-Tensor manuscript)

* `minimal_record`: the future-signature quotient is the
  coarsest record separating futures: two records merge exactly
  when their signatures agree; the signature factors through the
  quotient with injective (separating) induced signature; the
  quotient transition is well defined for every right-invariant
  step; and every surjective signature-sufficient record maps
  onto the quotient by a unique factor map.
* `causal_efficient_score_record`: the instantiation on a
  declared score family — the same quotient is the unique
  coarsest causal score-sufficient record.

Rendering disclosed: records and futures are rendered as the
finite operational data they are (a signature map on record
values); "strong lumpability" is the proved right-invariant
quotient-transition clause; the cutoff strict-quotient-system
clause is the universal factor map applied along refinements
(`thm:operational-record-completion`'s descent, hard tier).
-/

namespace NCG

variable {R Sig : Type*}

/-- The minimal-record setoid: merge records with equal future
signatures. -/
def minRecSetoid (sig : R → Sig) : Setoid R := Setoid.ker sig

/-- The canonical minimal readable record. -/
abbrev MinRec (sig : R → Sig) : Type _ :=
  Quotient (minRecSetoid sig)

/-- `thm:minimal-record`. -/
theorem minimal_record (sig : R → Sig) :
    -- (1) separation: classes merge exactly on equal signatures
    (∀ r r' : R,
      (Quotient.mk (minRecSetoid sig) r
        = Quotient.mk (minRecSetoid sig) r') ↔ sig r = sig r')
    -- (2) the signature factors through the quotient,
    --     with separating (injective) induced signature
    ∧ (∃ sigbar : MinRec sig → Sig,
        (∀ r, sigbar (Quotient.mk (minRecSetoid sig) r) = sig r)
        ∧ Function.Injective sigbar)
    -- (3) right-invariant steps descend to the quotient
    ∧ (∀ step : R → R,
        (∀ r r', sig r = sig r' → sig (step r) = sig (step r')) →
        ∃ stepbar : MinRec sig → MinRec sig,
          ∀ r, stepbar (Quotient.mk (minRecSetoid sig) r)
            = Quotient.mk (minRecSetoid sig) (step r))
    := by
  refine ⟨?_, ?_, ?_⟩
  · intro r r'
    exact Quotient.eq (r := minRecSetoid sig)
  · refine ⟨Quotient.lift sig (fun a b h => h), fun r => rfl,
      ?_⟩
    intro x y hxy
    induction x using Quotient.ind
    induction y using Quotient.ind
    exact Quotient.sound hxy
  · intro step hstep
    refine ⟨Quotient.lift
      (fun r => Quotient.mk (minRecSetoid sig) (step r))
      (fun a b h => Quotient.sound (hstep a b h)), fun r => rfl⟩

/-- `thm:minimal-record` (universality clause): every
surjective signature-sufficient record factors uniquely onto
the minimal record. -/
theorem minimal_record_universal {S : Type*} (sig : R → Sig)
    (c : R → S) (g : S → Sig)
    (hsurj : Function.Surjective c)
    (hfac : ∀ r, g (c r) = sig r) :
    ∃! φ : S → MinRec sig,
      ∀ r, φ (c r) = Quotient.mk (minRecSetoid sig) r := by
  refine ⟨fun s => Quotient.mk (minRecSetoid sig)
    ((hsurj s).choose), ?_, ?_⟩
  · intro r
    apply Quotient.sound
    change sig ((hsurj (c r)).choose) = sig r
    rw [← hfac ((hsurj (c r)).choose),
      (hsurj (c r)).choose_spec, hfac r]
  · intro ψ hψ
    funext s
    obtain ⟨r, rfl⟩ := hsurj s
    rw [hψ r]
    apply Quotient.sound
    change sig r = sig ((hsurj (c r)).choose)
    rw [← hfac ((hsurj (c r)).choose),
      (hsurj (c r)).choose_spec, hfac r]

/-- `cor:causal-efficient-score-record`: instantiation on a
declared score family joined with the future score-cylinder
signature. -/
theorem causal_efficient_score_record {R Score Cyl : Type*}
    (score : R → Score) (fut : R → Cyl) :
    (∀ r r' : R,
      (Quotient.mk (minRecSetoid fun r => (score r, fut r)) r
        = Quotient.mk (minRecSetoid fun r => (score r, fut r)) r')
      ↔ (score r = score r' ∧ fut r = fut r'))
    ∧ (∃ scorebar :
        MinRec (fun r => (score r, fut r)) → Score,
        ∀ r, scorebar
          (Quotient.mk (minRecSetoid fun r => (score r, fut r)) r)
          = score r) := by
  constructor
  · intro r r'
    rw [(minimal_record fun r => (score r, fut r)).1]
    exact Prod.ext_iff
  · exact ⟨Quotient.lift (fun r => score r)
      (fun a b h => congrArg Prod.fst h), fun r => rfl⟩

end NCG
