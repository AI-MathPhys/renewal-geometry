/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/

import Mathlib

/-!
# The terminating weighted-locality alternative

This file is the exact finite decision layer of
`thm:GTLOC-terminating-alternative`.  The twelve preliminary outcomes are
tested in manuscript order.  A returned branch stores its typed witness and
proofs that every earlier branch was inapplicable.  If none applies, the
packet's coverage theorem produces the all-selected-rows certificate used by
the thirteenth (reconstruction) branch.

The compiler deliberately has no output field asserting a global decay
exponent or promoting an endpoint response to a local insertion route.  Those
are the two firewall clauses at the end of the manuscript theorem.
-/

namespace NCG.FiniteWeightedLocalityAlternative

/-- A decidable condition and the typed result returned when it applies. -/
structure AuditBranch (Witness : Type*) where
  applicable : Prop
  decision : Decidable applicable
  witness : applicable → Witness

/-- The twelve preliminary rows of the weighted-locality audit, in the exact
order (A1)--(A12) of the manuscript.  `FinalCertificate` is the inherited
critical-form OS reconstruction invoked in branch (A13). -/
structure AuditPacket
    (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*) where
  missingLocalityCarrier : AuditBranch A1
  missingWeightedOccurrence : AuditBranch A2
  boundedInsertionConvolution : AuditBranch A3
  criticalWeightedLocality : AuditBranch A4
  positiveRouteLeakage : AuditBranch A5
  pairOnlyLocalityBirth : AuditBranch A6
  localContactObstruction : AuditBranch A7
  escapingLongRangeBlock : AuditBranch A8
  targetRelativeLocality : AuditBranch A9
  localWordProductInverseObstruction : AuditBranch A10
  localConnectedOS : AuditBranch A11
  independentReconstructionObstruction : AuditBranch A12
  allSelectedRowsPass : Prop
  coverage :
    ¬missingLocalityCarrier.applicable →
    ¬missingWeightedOccurrence.applicable →
    ¬boundedInsertionConvolution.applicable →
    ¬criticalWeightedLocality.applicable →
    ¬positiveRouteLeakage.applicable →
    ¬pairOnlyLocalityBirth.applicable →
    ¬localContactObstruction.applicable →
    ¬escapingLongRangeBlock.applicable →
    ¬targetRelativeLocality.applicable →
    ¬localWordProductInverseObstruction.applicable →
    ¬localConnectedOS.applicable →
    ¬independentReconstructionObstruction.applicable →
    allSelectedRowsPass
  reconstruct : allSelectedRowsPass → FinalCertificate

/-- Every constructor after (A1) records that all earlier branches failed.
Consequently an inhabitant returned by `compile` is not merely some applicable
outcome: it is the first applicable outcome. -/
inductive CompilerOutcome
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*}
    (P : AuditPacket A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
      FinalCertificate) where
  | a1 (w : A1)
  | a2 (h1 : ¬P.missingLocalityCarrier.applicable) (w : A2)
  | a3 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable) (w : A3)
  | a4 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable) (w : A4)
  | a5 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable) (w : A5)
  | a6 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable) (w : A6)
  | a7 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable) (w : A7)
  | a8 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable) (w : A8)
  | a9 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable)
      (h8 : ¬P.escapingLongRangeBlock.applicable) (w : A9)
  | a10 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable)
      (h8 : ¬P.escapingLongRangeBlock.applicable)
      (h9 : ¬P.targetRelativeLocality.applicable) (w : A10)
  | a11 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable)
      (h8 : ¬P.escapingLongRangeBlock.applicable)
      (h9 : ¬P.targetRelativeLocality.applicable)
      (h10 : ¬P.localWordProductInverseObstruction.applicable) (w : A11)
  | a12 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable)
      (h8 : ¬P.escapingLongRangeBlock.applicable)
      (h9 : ¬P.targetRelativeLocality.applicable)
      (h10 : ¬P.localWordProductInverseObstruction.applicable)
      (h11 : ¬P.localConnectedOS.applicable) (w : A12)
  | a13 (h1 : ¬P.missingLocalityCarrier.applicable)
      (h2 : ¬P.missingWeightedOccurrence.applicable)
      (h3 : ¬P.boundedInsertionConvolution.applicable)
      (h4 : ¬P.criticalWeightedLocality.applicable)
      (h5 : ¬P.positiveRouteLeakage.applicable)
      (h6 : ¬P.pairOnlyLocalityBirth.applicable)
      (h7 : ¬P.localContactObstruction.applicable)
      (h8 : ¬P.escapingLongRangeBlock.applicable)
      (h9 : ¬P.targetRelativeLocality.applicable)
      (h10 : ¬P.localWordProductInverseObstruction.applicable)
      (h11 : ¬P.localConnectedOS.applicable)
      (h12 : ¬P.independentReconstructionObstruction.applicable)
      (rows : P.allSelectedRowsPass) (certificate : FinalCertificate)

/-- Executable thirteen-way audit.  The nested decisions are structurally
finite, and the negative hypotheses retained by each constructor prove the
"first applicable branch" clause. -/
def compile
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*}
    (P : AuditPacket A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
      FinalCertificate) : CompilerOutcome P := by
  letI := P.missingLocalityCarrier.decision
  letI := P.missingWeightedOccurrence.decision
  letI := P.boundedInsertionConvolution.decision
  letI := P.criticalWeightedLocality.decision
  letI := P.positiveRouteLeakage.decision
  letI := P.pairOnlyLocalityBirth.decision
  letI := P.localContactObstruction.decision
  letI := P.escapingLongRangeBlock.decision
  letI := P.targetRelativeLocality.decision
  letI := P.localWordProductInverseObstruction.decision
  letI := P.localConnectedOS.decision
  letI := P.independentReconstructionObstruction.decision
  by_cases h1 : P.missingLocalityCarrier.applicable
  · exact .a1 (P.missingLocalityCarrier.witness h1)
  by_cases h2 : P.missingWeightedOccurrence.applicable
  · exact .a2 h1 (P.missingWeightedOccurrence.witness h2)
  by_cases h3 : P.boundedInsertionConvolution.applicable
  · exact .a3 h1 h2 (P.boundedInsertionConvolution.witness h3)
  by_cases h4 : P.criticalWeightedLocality.applicable
  · exact .a4 h1 h2 h3 (P.criticalWeightedLocality.witness h4)
  by_cases h5 : P.positiveRouteLeakage.applicable
  · exact .a5 h1 h2 h3 h4 (P.positiveRouteLeakage.witness h5)
  by_cases h6 : P.pairOnlyLocalityBirth.applicable
  · exact .a6 h1 h2 h3 h4 h5 (P.pairOnlyLocalityBirth.witness h6)
  by_cases h7 : P.localContactObstruction.applicable
  · exact .a7 h1 h2 h3 h4 h5 h6 (P.localContactObstruction.witness h7)
  by_cases h8 : P.escapingLongRangeBlock.applicable
  · exact .a8 h1 h2 h3 h4 h5 h6 h7 (P.escapingLongRangeBlock.witness h8)
  by_cases h9 : P.targetRelativeLocality.applicable
  · exact .a9 h1 h2 h3 h4 h5 h6 h7 h8 (P.targetRelativeLocality.witness h9)
  by_cases h10 : P.localWordProductInverseObstruction.applicable
  · exact .a10 h1 h2 h3 h4 h5 h6 h7 h8 h9
      (P.localWordProductInverseObstruction.witness h10)
  by_cases h11 : P.localConnectedOS.applicable
  · exact .a11 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      (P.localConnectedOS.witness h11)
  by_cases h12 : P.independentReconstructionObstruction.applicable
  · exact .a12 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      (P.independentReconstructionObstruction.witness h12)
  · have rows := P.coverage h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    exact .a13 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 rows
      (P.reconstruct rows)

/-- Recognizer for the all-rows-pass reconstruction outcome. -/
def isReconstruction
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*}
    {P : AuditPacket A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
      FinalCertificate} : CompilerOutcome P → Prop
  | .a13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | _ => False

/-- Branch (A13) occurs exactly when none of branches (A1)--(A12) is
applicable. -/
theorem compile_reconstruction_iff
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*}
    (P : AuditPacket A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
      FinalCertificate) :
    isReconstruction (compile P) ↔
      ¬P.missingLocalityCarrier.applicable ∧
      ¬P.missingWeightedOccurrence.applicable ∧
      ¬P.boundedInsertionConvolution.applicable ∧
      ¬P.criticalWeightedLocality.applicable ∧
      ¬P.positiveRouteLeakage.applicable ∧
      ¬P.pairOnlyLocalityBirth.applicable ∧
      ¬P.localContactObstruction.applicable ∧
      ¬P.escapingLongRangeBlock.applicable ∧
      ¬P.targetRelativeLocality.applicable ∧
      ¬P.localWordProductInverseObstruction.applicable ∧
      ¬P.localConnectedOS.applicable ∧
      ¬P.independentReconstructionObstruction.applicable := by
  constructor
  · intro hfinal
    have h1 : ¬P.missingLocalityCarrier.applicable := by
      intro h
      simp [compile, isReconstruction, h] at hfinal
    have h2 : ¬P.missingWeightedOccurrence.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h] at hfinal
    have h3 : ¬P.boundedInsertionConvolution.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h] at hfinal
    have h4 : ¬P.criticalWeightedLocality.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h] at hfinal
    have h5 : ¬P.positiveRouteLeakage.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h] at hfinal
    have h6 : ¬P.pairOnlyLocalityBirth.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h] at hfinal
    have h7 : ¬P.localContactObstruction.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h] at hfinal
    have h8 : ¬P.escapingLongRangeBlock.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h] at hfinal
    have h9 : ¬P.targetRelativeLocality.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h8, h]
        at hfinal
    have h10 : ¬P.localWordProductInverseObstruction.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h8, h9, h]
        at hfinal
    have h11 : ¬P.localConnectedOS.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h] at hfinal
    have h12 : ¬P.independentReconstructionObstruction.applicable := by
      intro h
      simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, h] at hfinal
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    simp [compile, isReconstruction, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12]

/-- **`thm:GTLOC-terminating-alternative`.**  The ordered audit always
terminates, and its final result is precisely the selected all-rows-pass
critical-form reconstruction branch. -/
theorem finite_weighted_locality_alternative
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 FinalCertificate : Type*}
    (P : AuditPacket A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
      FinalCertificate) :
    Nonempty (CompilerOutcome P) ∧
      (isReconstruction (compile P) ↔
        ¬P.missingLocalityCarrier.applicable ∧
        ¬P.missingWeightedOccurrence.applicable ∧
        ¬P.boundedInsertionConvolution.applicable ∧
        ¬P.criticalWeightedLocality.applicable ∧
        ¬P.positiveRouteLeakage.applicable ∧
        ¬P.pairOnlyLocalityBirth.applicable ∧
        ¬P.localContactObstruction.applicable ∧
        ¬P.escapingLongRangeBlock.applicable ∧
        ¬P.targetRelativeLocality.applicable ∧
        ¬P.localWordProductInverseObstruction.applicable ∧
        ¬P.localConnectedOS.applicable ∧
        ¬P.independentReconstructionObstruction.applicable) :=
  ⟨⟨compile P⟩, compile_reconstruction_iff P⟩

end NCG.FiniteWeightedLocalityAlternative
