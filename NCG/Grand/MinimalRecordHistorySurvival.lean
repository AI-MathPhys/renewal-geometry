/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContextualFutureNullIdeal
import NCG.Grand.GeneratedMinimalRecord

/-!
# Survival of minimal records in the contextual history algebra

This file proves the five clauses of `thm:record-survival`.  On the finite
minimal-record carrier, readable classes are diagonal projections and a
deterministic writer from one class to another is the corresponding matrix
unit.  All matrix-entry coordinates are admitted contextual Reads, so the
two-sided future-null ideal is exactly zero.  Consequently distinct record
projections, nonzero branches, their writers, and declared provenance points
all survive the contextual quotient.  The final unread-fibre clause is the
exact generated-future-algebra theorem on `MinRec`.
-/

namespace NCG

open scoped ComplexOrder

section FiniteRecordAlgebra

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The contextual Read which extracts one matrix coordinate. -/
def minimalRecordEntryRead (ij : Q × Q) :
    CStarMatrix Q Q ℂ →ₗ[ℂ] ℂ where
  toFun x := x ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The contextual future-null ideal for the complete finite matrix panel. -/
abbrev minimalRecordFutureNullIdeal : Ideal (CStarMatrix Q Q ℂ) :=
  contextualFutureNullIdeal
    (fun ij : Q × Q => (minimalRecordEntryRead ij).toAddMonoidHom)

/-- The readable-record projection associated with a minimal class. -/
def minimalRecordProjection (q : Q) : CStarMatrix Q Q ℂ :=
  fun i j => if i = q ∧ j = q then 1 else 0

/-- The deterministic writer carrying the source class to the target class. -/
def deterministicRecordWriter (source target : Q) : CStarMatrix Q Q ℂ :=
  fun i j => if i = target ∧ j = source then 1 else 0

@[simp] theorem minimalRecordProjection_diagonal (q : Q) :
    minimalRecordProjection q q q = 1 := by
  simp [minimalRecordProjection]

@[simp] theorem minimalRecordProjection_diagonal_of_ne
    {q r : Q} (hqr : q ≠ r) :
    minimalRecordProjection r q q = 0 := by
  simp [minimalRecordProjection, hqr]

@[simp] theorem deterministicRecordWriter_target_source
    (source target : Q) :
    deterministicRecordWriter source target target source = 1 := by
  simp [deterministicRecordWriter]

/-- The complete contextual matrix-entry panel has no nonzero future-null
direction, even before passing to the quotient. -/
theorem minimalRecord_contextualFutureNull_iff_eq_zero
    (x : CStarMatrix Q Q ℂ) :
    contextualFutureNull
        (fun ij : Q × Q => (minimalRecordEntryRead ij).toAddMonoidHom) x
      ↔ x = 0 := by
  constructor
  · intro hx
    apply CStarMatrix.ext
    intro i j
    have hij := hx.1 (i, j) 1 1
    simp only [one_mul, mul_one] at hij
    change x i j = 0 at hij
    exact hij
  · rintro rfl
    constructor <;> intro ij u v <;> simp [minimalRecordEntryRead]

/-- Therefore the contextual future-null ideal of the complete minimal-record
matrix algebra is the zero ideal. -/
theorem minimalRecordFutureNullIdeal_eq_bot :
    minimalRecordFutureNullIdeal (Q := Q) = ⊥ := by
  ext x
  change contextualFutureNull
      (fun ij : Q × Q => (minimalRecordEntryRead ij).toAddMonoidHom) x ↔ x ∈ (⊥ : Ideal _)
  rw [minimalRecord_contextualFutureNull_iff_eq_zero, Ideal.mem_bot]

theorem minimalRecordProjection_ne_zero (q : Q) :
    minimalRecordProjection q ≠ 0 := by
  intro h
  have hqq := congrFun (congrFun h q) q
  simp [minimalRecordProjection] at hqq

theorem minimalRecordProjection_ne_of_ne {q r : Q} (hqr : q ≠ r) :
    minimalRecordProjection q ≠ minimalRecordProjection r := by
  intro h
  have hqq := congrFun (congrFun h q) q
  simp [minimalRecordProjection, hqr] at hqq

theorem deterministicRecordWriter_ne_zero (source target : Q) :
    deterministicRecordWriter source target ≠ 0 := by
  intro h
  have hts := congrFun (congrFun h target) source
  simp [deterministicRecordWriter] at hts

/-- A nonzero finite matrix survives the contextual history quotient. -/
theorem minimalRecordHistory_mk_ne_zero
    {x : CStarMatrix Q Q ℂ} (hx : x ≠ 0) :
    Ideal.Quotient.mk (minimalRecordFutureNullIdeal (Q := Q)) x ≠ 0 := by
  intro h
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [minimalRecordFutureNullIdeal_eq_bot, Ideal.mem_bot] at hmem
  exact hx hmem

end FiniteRecordAlgebra

section MinimalRecordMachine

variable {A R D : Type*}

/-- `thm:record-survival`, clauses (S1)--(S5), on the actual finite
`MinRec` carrier of a word-record machine. -/
theorem minimalRecordHistory_survival
    (M : WordRecordMachine A R D ℂ)
    [Finite R]
    [Fintype (MinRec M.futureSig)] [DecidableEq (MinRec M.futureSig)]
    (declaredProvenance : Set (MinRec M.futureSig)) :
    let Q := MinRec M.futureSig
    let I := minimalRecordFutureNullIdeal (Q := Q)
    -- (S1) Distinct minimal readable classes remain distinct.
    (∀ q r : Q, q ≠ r →
      Ideal.Quotient.mk I (minimalRecordProjection q) ≠
        Ideal.Quotient.mk I (minimalRecordProjection r))
    -- (S2) Every nonzero minimal record projection survives.
    ∧ (∀ q : Q, Ideal.Quotient.mk I (minimalRecordProjection q) ≠ 0)
    -- (S3) Every deterministic writer on a surviving branch survives.
    ∧ (∀ source target : Q,
      Ideal.Quotient.mk I (minimalRecordProjection source) ≠ 0 →
      Ideal.Quotient.mk I (deterministicRecordWriter source target) ≠ 0)
    -- (S4) Every physically declared provenance point survives.
    ∧ (∀ p : Q, p ∈ declaredProvenance →
      Ideal.Quotient.mk I (minimalRecordProjection p) ≠ 0)
    -- (S5) Only functions constant on unread future fibres enter intrinsically.
    ∧ M.generatedFutureAlgebra = M.fibreConstantAlgebra := by
  dsimp only
  constructor
  · intro q r hqr heq
    apply minimalRecordProjection_ne_of_ne hqr
    have hmem := Ideal.Quotient.eq.mp heq
    rw [minimalRecordFutureNullIdeal_eq_bot, Ideal.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  constructor
  · intro q
    exact minimalRecordHistory_mk_ne_zero (minimalRecordProjection_ne_zero q)
  constructor
  · intro source target _
    exact minimalRecordHistory_mk_ne_zero
      (deterministicRecordWriter_ne_zero source target)
  constructor
  · intro p _
    exact minimalRecordHistory_mk_ne_zero (minimalRecordProjection_ne_zero p)
  · exact M.minimal_read_algebra_exact

end MinimalRecordMachine

end NCG
