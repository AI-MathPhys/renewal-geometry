/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operational clock–geometry source alternative
  (`thm:clock-geometry-alternative-master`, flagship manuscript)

`clock_geometry_decision_tree`: the finite tests applied in
order return exactly one terminal outcome — with the five test
certificates `A` (amplitude access), `B` (zero-depth residual
zero), `C` (no finite chronology closure needed), `D` (sector
amplitudes/phases trivial), `E` (score certificates pass) as
propositions, exactly one of the six terminal outcomes

(A1) nonidentifiability `¬A`;
(A2) extra action source `A ∧ ¬B ∧ ¬C`;
(A3) chronology filter `A ∧ ¬B ∧ C`;
(A4) sector split `A ∧ B ∧ ¬D`;
(A5) semantic split `A ∧ B ∧ D ∧ ¬E`;
(A6) exact source identity `A ∧ B ∧ D ∧ E`

holds (`∃!` over the six-entry outcome vector).  No nonzero
residual is absorbed: each failing test terminates in its own
labelled branch.

Rendering disclosed: the identification of the test propositions
with the concrete certificates (branch-interference port,
zero-depth Schur residual, cross-Hankel closure degree, sector
amplitude/phase data, persistent-transfer/frequency-mixing/
depth-two scores) is the cited constituent records; outcome (A6)
is the entry gate of the common-action record.
-/

namespace NCG

/-- The six terminal outcomes of the ordered test tree. -/
def cgOutcome (A B C D E : Prop) : Fin 6 → Prop :=
  ![¬A,
    A ∧ ¬B ∧ ¬C,
    A ∧ ¬B ∧ C,
    A ∧ B ∧ ¬D,
    A ∧ B ∧ D ∧ ¬E,
    A ∧ B ∧ D ∧ E]

/-- `thm:clock-geometry-alternative-master`: exactly one
terminal outcome is returned. -/
theorem clock_geometry_decision_tree (A B C D E : Prop) :
    ∃! k : Fin 6, cgOutcome A B C D E k := by
  by_cases hA : A
  · by_cases hB : B
    · by_cases hD : D
      · by_cases hE : E
        · refine ⟨5, ⟨hA, hB, hD, hE⟩, ?_⟩
          intro k hk
          fin_cases k <;> simp_all [cgOutcome]
        · refine ⟨4, ⟨hA, hB, hD, hE⟩, ?_⟩
          intro k hk
          fin_cases k <;> simp_all [cgOutcome]
      · refine ⟨3, ⟨hA, hB, hD⟩, ?_⟩
        intro k hk
        fin_cases k <;> simp_all [cgOutcome]
    · by_cases hC : C
      · refine ⟨2, ⟨hA, hB, hC⟩, ?_⟩
        intro k hk
        fin_cases k <;> simp_all [cgOutcome]
      · refine ⟨1, ⟨hA, hB, hC⟩, ?_⟩
        intro k hk
        fin_cases k <;> simp_all [cgOutcome]
  · refine ⟨0, hA, ?_⟩
    intro k hk
    fin_cases k <;> simp_all [cgOutcome]

end NCG
