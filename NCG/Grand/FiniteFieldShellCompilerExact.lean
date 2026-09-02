/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AnomalyFreeFieldShellGaugeQuotientExact
import NCG.Grand.CommonReversibleFieldReactionSlabExact
import NCG.Grand.DobrushinProjectiveContinuumExact
import NCG.Grand.BoundaryResponseGaussianNormalCollarExact
import NCG.Grand.PalatiniSpectralTailHandoff

/-!
# Terminating finite field-shell compiler

This file proves `thm:SMFS-master` as an executable typed alternative.  Its
ten gates are ordered exactly as in the manuscript.  Every negative branch
contains the witness emitted by the first failed gate, while the positive
branch contains proofs that all representation, spectral, reversible-slab,
BRST, score/operator, projective-map, gauge-line, boundary, and Palatini rows
passed.  Thus no failed row can be hidden inside a nominally positive shell.
-/

namespace NCG.FiniteFieldShellCompiler

/-- A decidable audit gate together with its typed counter-witness producer. -/
structure AuditGate (Witness : Type*) where
  pass : Prop
  decision : Decidable pass
  failureWitness : ¬pass → Witness

/-- The ten ordered rows of the literal finite field-shell audit. -/
structure AuditPacket
    (AnomalyWitness SpectralWitness DynamicsWitness SlabWitness
      BRSTWitness OperatorWitness ProjectiveWitness GaugeLineWitness
      BoundaryWitness PalatiniWitness : Type*) where
  representation : AuditGate AnomalyWitness
  spectralFloors : AuditGate SpectralWitness
  dynamics : AuditGate DynamicsWitness
  reflectedSlab : AuditGate SlabWitness
  brstDescent : AuditGate BRSTWitness
  scoreAndOperatorBirth : AuditGate OperatorWitness
  projectiveLoading : AuditGate ProjectiveWitness
  gaugeAndLineDescent : AuditGate GaugeLineWitness
  assembledBoundary : AuditGate BoundaryWitness
  palatiniTail : AuditGate PalatiniWitness

/-- A literal positive shell certificate: every one of the ten load-bearing
rows has passed in the prescribed order. -/
structure PositiveFieldReactionShell
    {W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*}
    (P : AuditPacket W1 W2 W3 W4 W5 W6 W7 W8 W9 W10) : Prop where
  representation : P.representation.pass
  spectralFloors : P.spectralFloors.pass
  dynamics : P.dynamics.pass
  reflectedSlab : P.reflectedSlab.pass
  brstDescent : P.brstDescent.pass
  scoreAndOperatorBirth : P.scoreAndOperatorBirth.pass
  projectiveLoading : P.projectiveLoading.pass
  gaugeAndLineDescent : P.gaugeAndLineDescent.pass
  assembledBoundary : P.assembledBoundary.pass
  palatiniTail : P.palatiniTail.pass

/-- The first explicit obstruction returned by the compiler. -/
inductive FailureWitness
    (W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*) where
  | anomaly : W1 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | divisorOrChiral : W2 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | influenceOrClock : W3 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | reflectedWriter : W4 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | brst : W5 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | operatorBirth : W6 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | missingProjectiveMap : W7 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | gaugeOrLine : W8 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | boundary : W9 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10
  | palatiniOrCutoff : W10 → FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10

/-- Positive shell or the first typed negative witness. -/
inductive CompilerOutcome
    {W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*}
    (P : AuditPacket W1 W2 W3 W4 W5 W6 W7 W8 W9 W10) where
  | positive : PositiveFieldReactionShell P → CompilerOutcome P
  | negative : FailureWitness W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 →
      CompilerOutcome P

/-- The literal ordered compiler.  Pattern matching on stored `Decidable`
certificates makes termination computational rather than merely existential. -/
def compile
    {W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*}
    (P : AuditPacket W1 W2 W3 W4 W5 W6 W7 W8 W9 W10) :
    CompilerOutcome P :=
  match P.representation.decision with
  | isFalse h => .negative (.anomaly (P.representation.failureWitness h))
  | isTrue h1 =>
    match P.spectralFloors.decision with
    | isFalse h => .negative (.divisorOrChiral (P.spectralFloors.failureWitness h))
    | isTrue h2 =>
      match P.dynamics.decision with
      | isFalse h => .negative (.influenceOrClock (P.dynamics.failureWitness h))
      | isTrue h3 =>
        match P.reflectedSlab.decision with
        | isFalse h => .negative (.reflectedWriter (P.reflectedSlab.failureWitness h))
        | isTrue h4 =>
          match P.brstDescent.decision with
          | isFalse h => .negative (.brst (P.brstDescent.failureWitness h))
          | isTrue h5 =>
            match P.scoreAndOperatorBirth.decision with
            | isFalse h => .negative (.operatorBirth
                (P.scoreAndOperatorBirth.failureWitness h))
            | isTrue h6 =>
              match P.projectiveLoading.decision with
              | isFalse h => .negative (.missingProjectiveMap
                  (P.projectiveLoading.failureWitness h))
              | isTrue h7 =>
                match P.gaugeAndLineDescent.decision with
                | isFalse h => .negative (.gaugeOrLine
                    (P.gaugeAndLineDescent.failureWitness h))
                | isTrue h8 =>
                  match P.assembledBoundary.decision with
                  | isFalse h => .negative (.boundary
                      (P.assembledBoundary.failureWitness h))
                  | isTrue h9 =>
                    match P.palatiniTail.decision with
                    | isFalse h => .negative (.palatiniOrCutoff
                        (P.palatiniTail.failureWitness h))
                    | isTrue h10 => .positive {
                        representation := h1
                        spectralFloors := h2
                        dynamics := h3
                        reflectedSlab := h4
                        brstDescent := h5
                        scoreAndOperatorBirth := h6
                        projectiveLoading := h7
                        gaugeAndLineDescent := h8
                        assembledBoundary := h9
                        palatiniTail := h10 }

theorem compile_positive_iff
    {W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*}
    (P : AuditPacket W1 W2 W3 W4 W5 W6 W7 W8 W9 W10) :
    (∃ shell, compile P = CompilerOutcome.positive shell) ↔
      Nonempty (PositiveFieldReactionShell P) := by
  constructor
  · rintro ⟨shell, -⟩
    exact ⟨shell⟩
  · rintro ⟨shell⟩
    rcases shell with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    let shell : PositiveFieldReactionShell P :=
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨shell, ?_⟩
    have d1 : P.representation.decision = isTrue h1 := Subsingleton.elim _ _
    have d2 : P.spectralFloors.decision = isTrue h2 := Subsingleton.elim _ _
    have d3 : P.dynamics.decision = isTrue h3 := Subsingleton.elim _ _
    have d4 : P.reflectedSlab.decision = isTrue h4 := Subsingleton.elim _ _
    have d5 : P.brstDescent.decision = isTrue h5 := Subsingleton.elim _ _
    have d6 : P.scoreAndOperatorBirth.decision = isTrue h6 := Subsingleton.elim _ _
    have d7 : P.projectiveLoading.decision = isTrue h7 := Subsingleton.elim _ _
    have d8 : P.gaugeAndLineDescent.decision = isTrue h8 := Subsingleton.elim _ _
    have d9 : P.assembledBoundary.decision = isTrue h9 := Subsingleton.elim _ _
    have d10 : P.palatiniTail.decision = isTrue h10 := Subsingleton.elim _ _
    simp only [compile, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10]

/-- **`thm:SMFS-master`.**  The finite field-shell audit terminates in one
literal all-rows-positive shell or in one of the ten explicit obstruction
families, and its positive output is equivalent to simultaneous passage of
all load-bearing rows. -/
theorem finite_field_shell_alternative
    {W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 : Type*}
    (P : AuditPacket W1 W2 W3 W4 W5 W6 W7 W8 W9 W10) :
    Nonempty (CompilerOutcome P) ∧
      ((∃ shell, compile P = CompilerOutcome.positive shell) ↔
        Nonempty (PositiveFieldReactionShell P)) :=
  ⟨⟨compile P⟩, compile_positive_iff P⟩

end NCG.FiniteFieldShellCompiler
