/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BrandNewEasy02

/-!
# Finite represented stress/current Ward criterion

This file packages the simultaneous Ward-short machinery as the exact finite
criterion of `thm:SMOS-stress-current-criterion`.  Every column of the stacked
source is tagged by one of the six declared relation kinds; all are shortened
against one common nuisance/improvement/EOM/BRST/boundary source bank.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace FiniteStressCurrentWardCriterion

/-- The six relation rows in the manuscript's stacked stress/Ward source. -/
inductive RelationKind
  | conservation
  | stressSymmetry
  | gradedLocality
  | wardLeibniz
  | contactCocycle
  | directTripleOccurrence
  deriving DecidableEq

/-- A finite represented stress/current packet.  `relationOfColumn` records
which of the six relations each source column tests. -/
structure Packet (h f e : ℕ) where
  nuisance : Matrix (Fin h) (Fin f) ℂ
  stackedSource : Matrix (Fin h) (Fin e) ℂ
  relationOfColumn : Fin e → RelationKind

/-- The positive simultaneous relation Gram after removal of every admitted
trivial direction. -/
noncomputable def relationGram {h f e : ℕ} (P : Packet h f e) :
    Matrix (Fin e) (Fin e) ℂ :=
  wardPhysicalGram P.nuisance P.stackedSource

/-- One common improvement/EOM/BRST/boundary representative exists exactly
when the entire stacked source factors through the single nuisance bank. -/
def HasCommonTrivialRepresentative {h f e : ℕ} (P : Packet h f e) : Prop :=
  ∃ L : Matrix (Fin f) (Fin e) ℂ,
    P.stackedSource = P.nuisance * L

/-- The simultaneous stress/current relation Gram is positive semidefinite. -/
theorem relationGram_posSemidef {h f e : ℕ} (P : Packet h f e) :
    (relationGram P).PosSemidef := by
  exact (wardPhysicalGram_eq_schur P.nuisance P.stackedSource).2

/-- Exact necessary-and-sufficient criterion: all six tagged relation panels
admit one common trivial representative iff the simultaneous Gram vanishes. -/
theorem relationGram_eq_zero_iff {h f e : ℕ} (P : Packet h f e) :
    relationGram P = 0 ↔ HasCommonTrivialRepresentative P := by
  exact (ward_short_zero_iff P.nuisance P.stackedSource).2

/-- The physical residual synthesizes the relation Gram as an actual Gram
matrix. -/
theorem physicalResidual_gram {h f e : ℕ} (P : Packet h f e) :
    (wardPhysicalResidual P.nuisance P.stackedSource)ᴴ *
        wardPhysicalResidual P.nuisance P.stackedSource = relationGram P := by
  unfold wardPhysicalResidual relationGram wardPhysicalGram
  obtain ⟨hPH, hP2, -⟩ :=
    (sourceGramPseudoinverse_projection P.nuisance).2.2.2
  change (sourceRangeProjection P.nuisance)ᴴ =
    sourceRangeProjection P.nuisance at hPH
  change sourceRangeProjection P.nuisance *
    sourceRangeProjection P.nuisance = sourceRangeProjection P.nuisance at hP2
  exact orthComplement_gram_synthesis
    (sourceRangeProjection P.nuisance) hPH hP2 P.stackedSource

/-- Every other synthesis of the same physical relation Gram has exactly the
same rank as the canonical polar-range residual. -/
theorem physicalResidual_sourceMinimal {h f e p : ℕ}
    (P : Packet h f e) (B : Matrix (Fin p) (Fin e) ℂ)
    (hB : Bᴴ * B = relationGram P) :
    B.rank = (wardPhysicalResidual P.nuisance P.stackedSource).rank := by
  apply gram_synthesis_rank_eq
  rw [physicalResidual_gram P]
  exact hB

/-- The number of new physical obstruction directions is the exact rank
increment obtained by appending the full tagged relation source. -/
theorem relation_rank_increment {h f e : ℕ} (P : Packet h f e) :
    (Matrix.fromCols P.nuisance P.stackedSource).rank - P.nuisance.rank =
      (relationGram P).rank := by
  exact ward_short_rank_increment P.nuisance P.stackedSource

/-- **`thm:SMOS-stress-current-criterion`.**  Consolidated positivity,
common-representative equivalence, and source-minimal obstruction clauses. -/
theorem smos_stress_current_criterion {h f e : ℕ} (P : Packet h f e) :
    (relationGram P).PosSemidef ∧
      (relationGram P = 0 ↔ HasCommonTrivialRepresentative P) ∧
      (∀ {p : ℕ} (B : Matrix (Fin p) (Fin e) ℂ),
        Bᴴ * B = relationGram P →
          B.rank =
            (wardPhysicalResidual P.nuisance P.stackedSource).rank) ∧
      (Matrix.fromCols P.nuisance P.stackedSource).rank - P.nuisance.rank =
        (relationGram P).rank := by
  exact ⟨relationGram_posSemidef P, relationGram_eq_zero_iff P,
    physicalResidual_sourceMinimal P, relation_rank_increment P⟩

end FiniteStressCurrentWardCriterion
end NCG
