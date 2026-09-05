/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ESSCIndependence

/-!
# Current entrance and principle count
  (`cor:master-principle-count`, flagship manuscript)

The revised ledger of the master programme as formal data: five
targets (finite local Lorentzian cell, canonical ADM generator,
local Einstein–matter dynamics, selected orientation, `G` and
`Λ`), each with a finite/analytic entrance and a broad schema
(`none`, `none`, four independent continuum clauses, state/
boundary phase, metrology).

* `ledgerSchema` / `ledgerEntrances`: the ledger rows as data;
* `master_principle_count`: the boxed counting facts — exactly
  the first two targets carry no broad schema, the Einstein
  target is the unique one carrying the four-continuum-clause
  schema, and those four clauses are logically independent (the
  proved `thm:ESSC-independence-master` witness schema);
* `ledger_entrance_finite`: every entrance list is finite and
  nonempty — no target enters through an empty or infinite
  hypothesis set.

Rendering disclosed: the identification of each entrance row
with its cited constituent records is the manuscript's table
prose; the counting, uniqueness, and clause-independence
content is what is proved here.
-/

namespace NCG

/-- The broad-schema column of the revised ledger:
`none` (finite cell), `none` (canonical ADM),
`some 0` = four independent continuum clauses (Einstein–matter),
`some 1` = state/boundary phase (orientation),
`some 2` = metrology (`G` and `Λ`). -/
def ledgerSchema : Fin 5 → Option (Fin 3) :=
  ![none, none, some 0, some 1, some 2]

/-- The finite/analytic entrance counts of the five ledger rows
(predictive RN envelope + analytic germ + loaded odd line +
depth two; metric-volume source + source identity + connection +
anomaly tests; matter + compactness/variation; deck edge law +
phase certificate; TT susceptibility + calibration + volume
score). -/
def ledgerEntrances : Fin 5 → ℕ := ![4, 4, 2, 2, 3]

/-- `cor:master-principle-count`: the boxed ledger counts — two
schema-free targets, the Einstein target uniquely carries the
four-clause schema, and the four continuum clauses are logically
independent. -/
theorem master_principle_count :
    ((Finset.univ.filter
        (fun t : Fin 5 => ledgerSchema t = none)).card = 2
      ∧ Finset.univ.filter
          (fun t : Fin 5 => ledgerSchema t = none)
        = {0, 1})
    ∧ (∀ t : Fin 5, ledgerSchema t = some 0 ↔ t = 2)
    ∧ (∀ i : Fin 4, ¬(∀ m : ClauseModel,
        (∀ j : Fin 4, j ≠ i → clause j m) → clause i m)) := by
  exact ⟨⟨by decide, by decide⟩, by decide,
    essc_clause_independence⟩

/-- Every entrance list is finite and nonempty. -/
theorem ledger_entrance_finite :
    ∀ t : Fin 5, 0 < ledgerEntrances t := by
  intro t
  fin_cases t <;> norm_num [ledgerEntrances]

end NCG
