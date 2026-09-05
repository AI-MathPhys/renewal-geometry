/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LockedIncidenceOrbitPolytope

/-!
# Matched-marginal locked provenance witnesses

The four coordinates of `LockedOrbitMass` are precisely the four diagonal
`S₄` incidence orbits.  Thus a nonnegative table of these masses is a positive
diagonally invariant cylinder.  This file constructs five such cylinders with
the same terminal total `1` and binary-tail total `1/3` in every cell, realizing
all five branches of `cth:SMST-provenance-marginals`.
-/

namespace NCG
namespace LockedProvenanceMarginalWitnesses

noncomputable section

abbrev Cell := Fin 3
abbrev StandardRow := Fin 2 → ℝ

def mass (q0 qt qh qo : ℝ) : LockedOrbitMass := ⟨q0, qt, qh, qo⟩

def addMass (x y : LockedOrbitMass) : LockedOrbitMass :=
  ⟨x.q0 + y.q0, x.qt + y.qt, x.qh + y.qh, x.qo + y.qo⟩

@[simp] theorem total_addMass (x y : LockedOrbitMass) :
    (addMass x y).total = x.total + y.total := by
  simp [addMass, LockedOrbitMass.total]
  ring

@[simp] theorem standardE_addMass (x y : LockedOrbitMass) :
    (addMass x y).standardE = x.standardE + y.standardE := by
  simp [addMass, LockedOrbitMass.standardE]
  ring

@[simp] theorem standardA_addMass (x y : LockedOrbitMass) :
    (addMass x y).standardA = x.standardA + y.standardA := by
  simp [addMass, LockedOrbitMass.standardA]
  ring

/-- A positive orbit cylinder is specified by its tail and complementary
positive orbit masses; the aggregate is their componentwise sum. -/
structure PositiveLockedCylinder where
  tail : Cell → LockedOrbitMass
  rest : Cell → LockedOrbitMass
  tail_nonnegative : ∀ c, (tail c).Nonnegative
  rest_nonnegative : ∀ c, (rest c).Nonnegative

namespace PositiveLockedCylinder

def aggregate (C : PositiveLockedCylinder) (c : Cell) : LockedOrbitMass :=
  addMass (C.tail c) (C.rest c)

def aggregateRow (C : PositiveLockedCylinder) (c : Cell) : StandardRow :=
  ![(C.aggregate c).standardE, (C.aggregate c).standardA]

def tailRow (C : PositiveLockedCylinder) (c : Cell) : StandardRow :=
  ![(C.tail c).standardE, (C.tail c).standardA]

/-- The entry/terminal and binary-tail marginals fixed in all five witnesses. -/
def HasLockedMarginals (C : PositiveLockedCylinder) : Prop :=
  ∀ c, (C.aggregate c).total = 1 ∧ (C.tail c).total = 1 / 3

def cross (u v : StandardRow) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Rank zero, one, and two for the two-column aggregate standard table. -/
def AggregateRankZero (C : PositiveLockedCylinder) : Prop :=
  ∀ c, C.aggregateRow c = 0

def AggregateRankOne (C : PositiveLockedCylinder) : Prop :=
  (∃ c, C.aggregateRow c ≠ 0) ∧
    ∀ c d, cross (C.aggregateRow c) (C.aggregateRow d) = 0

def AggregateRankTwo (C : PositiveLockedCylinder) : Prop :=
  ∃ c d, cross (C.aggregateRow c) (C.aggregateRow d) ≠ 0

/-- A common `2×2` right factor explains all tail rows from aggregate rows. -/
def TailExplainedByAggregate (C : PositiveLockedCylinder) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
    ∀ c, Matrix.vecMul (C.aggregateRow c) P = C.tailRow c

/-- Exact rank-one homogeneous factor with scalar `p`. -/
def RankOneTailFactor (C : PositiveLockedCylinder) (p : ℝ) : Prop :=
  ∀ c, C.tailRow c = p • C.aggregateRow c

end PositiveLockedCylinder

def balanced : LockedOrbitMass := mass (1/6) (1/3) (1/3) (1/6)
def tailBalanced : LockedOrbitMass := mass (1/18) (1/9) (1/9) (1/18)
def restBalanced : LockedOrbitMass := mass (1/9) (2/9) (2/9) (1/9)

def pure0Tail : LockedOrbitMass := mass (1/3) 0 0 0
def pure0Rest : LockedOrbitMass := mass (2/3) 0 0 0
def pureTouchTail : LockedOrbitMass := mass 0 (1/3) 0 0
def pureTouchRest : LockedOrbitMass := mass 0 (2/3) 0 0

private theorem nonnegative_of_explicit
    (q : LockedOrbitMass)
    (h0 : 0 ≤ q.q0) (ht : 0 ≤ q.qt) (hh : 0 ≤ q.qh) (ho : 0 ≤ q.qo) :
    q.Nonnegative := ⟨h0, ht, hh, ho⟩

def rankZeroCylinder : PositiveLockedCylinder where
  tail := ![tailBalanced, tailBalanced, tailBalanced]
  rest := ![restBalanced, restBalanced, restBalanced]
  tail_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, tailBalanced, mass]
  rest_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, restBalanced, mass]

def rankOneCylinder : PositiveLockedCylinder where
  tail := ![pure0Tail, pure0Tail, pure0Tail]
  rest := ![pure0Rest, pure0Rest, pure0Rest]
  tail_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, pure0Tail, mass]
  rest_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, pure0Rest, mass]

def rankTwoCylinder : PositiveLockedCylinder where
  tail := ![pure0Tail, pureTouchTail, tailBalanced]
  rest := ![pure0Rest, pureTouchRest, restBalanced]
  tail_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, pure0Tail, pureTouchTail,
        tailBalanced, mass]
  rest_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, pure0Rest, pureTouchRest,
        restBalanced, mass]

/- Strictly positive aggregate rows in cells 0 and 1, with a tail-only standard
perturbation in cell 2. -/
def residualTail : Cell → LockedOrbitMass :=
  ![mass (1/12) (1/9) (1/9) (1/36),
    mass (1/18) (5/36) (1/9) (1/36),
    mass (1/12) (1/9) (1/9) (1/36)]

def residualRest : Cell → LockedOrbitMass :=
  ![mass (1/6) (2/9) (2/9) (1/18),
    mass (1/9) (5/18) (2/9) (1/18),
    mass (1/12) (2/9) (2/9) (5/36)]

def positiveSchurCylinder : PositiveLockedCylinder where
  tail := residualTail
  rest := residualRest
  tail_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, residualTail, mass]
  rest_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, residualRest, mass]

/- Rank-one aggregate perturbation `ε = 1/12` and tail perturbation `δ = 1/18`.
The resulting exact factor is `p = δ/ε = 2/3 > s = 1/3`. -/
def expansiveTail : Cell → LockedOrbitMass :=
  ![mass (1/9) (1/9) (1/9) 0, tailBalanced, tailBalanced]

def expansiveRest : Cell → LockedOrbitMass :=
  ![mass (5/36) (2/9) (2/9) (1/12), restBalanced, restBalanced]

def noncontractiveCylinder : PositiveLockedCylinder where
  tail := expansiveTail
  rest := expansiveRest
  tail_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, expansiveTail, tailBalanced, mass]
  rest_nonnegative c := by
    fin_cases c <;>
      norm_num [LockedOrbitMass.Nonnegative, expansiveRest, restBalanced, mass]

private theorem explicit_locked_marginals
    (C : PositiveLockedCylinder)
    (hagg : ∀ c, (C.aggregate c).total = 1)
    (htail : ∀ c, (C.tail c).total = 1 / 3) :
    C.HasLockedMarginals := fun c => ⟨hagg c, htail c⟩

theorem rankZero_marginals : rankZeroCylinder.HasLockedMarginals := by
  apply explicit_locked_marginals <;> intro c <;> fin_cases c <;>
    norm_num [PositiveLockedCylinder.aggregate, rankZeroCylinder, tailBalanced,
      restBalanced, balanced, mass, LockedOrbitMass.total, addMass]

theorem rankOne_marginals : rankOneCylinder.HasLockedMarginals := by
  apply explicit_locked_marginals <;> intro c <;> fin_cases c <;>
    norm_num [PositiveLockedCylinder.aggregate, rankOneCylinder, pure0Tail,
      pure0Rest, mass, LockedOrbitMass.total, addMass]

theorem rankTwo_marginals : rankTwoCylinder.HasLockedMarginals := by
  apply explicit_locked_marginals <;> intro c <;> fin_cases c <;>
    norm_num [PositiveLockedCylinder.aggregate, rankTwoCylinder, pure0Tail,
      pure0Rest, pureTouchTail, pureTouchRest, tailBalanced, restBalanced,
      mass, LockedOrbitMass.total, addMass]

theorem positiveSchur_marginals : positiveSchurCylinder.HasLockedMarginals := by
  apply explicit_locked_marginals <;> intro c <;> fin_cases c <;>
    norm_num [PositiveLockedCylinder.aggregate, positiveSchurCylinder,
      residualTail, residualRest, mass, LockedOrbitMass.total, addMass]

theorem noncontractive_marginals :
    noncontractiveCylinder.HasLockedMarginals := by
  apply explicit_locked_marginals <;> intro c <;> fin_cases c <;>
    norm_num [PositiveLockedCylinder.aggregate, noncontractiveCylinder,
      expansiveTail, expansiveRest, tailBalanced, restBalanced, mass,
      LockedOrbitMass.total, addMass]

theorem rankZero_branch : rankZeroCylinder.AggregateRankZero := by
  intro c
  fin_cases c <;> ext i <;> fin_cases i <;>
    norm_num [PositiveLockedCylinder.aggregateRow,
      PositiveLockedCylinder.aggregate, rankZeroCylinder, tailBalanced,
      restBalanced, mass, addMass, LockedOrbitMass.standardE,
      LockedOrbitMass.standardA]

theorem rankOne_branch : rankOneCylinder.AggregateRankOne := by
  constructor
  · refine ⟨0, ?_⟩
    intro h
    have := congrFun h 0
    norm_num [PositiveLockedCylinder.aggregateRow,
      PositiveLockedCylinder.aggregate, rankOneCylinder, pure0Tail,
      pure0Rest, mass, addMass, LockedOrbitMass.standardE,
      LockedOrbitMass.standardA] at this
  · intro c d
    fin_cases c <;> fin_cases d <;>
      norm_num [PositiveLockedCylinder.cross,
        PositiveLockedCylinder.aggregateRow,
        PositiveLockedCylinder.aggregate, rankOneCylinder, pure0Tail,
        pure0Rest, mass, addMass, LockedOrbitMass.standardE,
        LockedOrbitMass.standardA]

theorem rankTwo_branch : rankTwoCylinder.AggregateRankTwo := by
  refine ⟨0, 1, ?_⟩
  norm_num [PositiveLockedCylinder.cross,
    PositiveLockedCylinder.aggregateRow, PositiveLockedCylinder.aggregate,
    rankTwoCylinder, pure0Tail, pure0Rest, pureTouchTail, pureTouchRest,
    mass, addMass, LockedOrbitMass.standardE, LockedOrbitMass.standardA]

/-- The tail-only perturbation in cell 2 cannot be produced from the aggregate
table: that aggregate row is zero while the tail row is nonzero.  This is the
strict Schur-residual branch. -/
theorem positiveSchur_branch :
    ¬ positiveSchurCylinder.TailExplainedByAggregate := by
  rintro ⟨P, hP⟩
  have h := hP 2
  have hz : positiveSchurCylinder.aggregateRow 2 = 0 := by
    ext i
    fin_cases i <;>
      simp [PositiveLockedCylinder.aggregateRow,
        PositiveLockedCylinder.aggregate, positiveSchurCylinder,
        residualTail, residualRest, mass, addMass,
        LockedOrbitMass.standardE, LockedOrbitMass.standardA] <;>
      norm_num
  rw [hz, Matrix.zero_vecMul] at h
  have h0 := congrFun h 0
  simp [PositiveLockedCylinder.tailRow, positiveSchurCylinder,
    residualTail, mass, LockedOrbitMass.standardE,
    LockedOrbitMass.standardA] at h0
  norm_num at h0

theorem noncontractive_rankOne :
    noncontractiveCylinder.AggregateRankOne := by
  constructor
  · refine ⟨0, ?_⟩
    intro h
    have := congrFun h 0
    norm_num [PositiveLockedCylinder.aggregateRow,
      PositiveLockedCylinder.aggregate, noncontractiveCylinder,
      expansiveTail, expansiveRest, tailBalanced, restBalanced, mass,
      addMass, LockedOrbitMass.standardE, LockedOrbitMass.standardA] at this
  · intro c d
    fin_cases c <;> fin_cases d <;>
      norm_num [PositiveLockedCylinder.cross,
        PositiveLockedCylinder.aggregateRow,
        PositiveLockedCylinder.aggregate, noncontractiveCylinder,
        expansiveTail, expansiveRest, tailBalanced, restBalanced, mass,
        addMass, LockedOrbitMass.standardE, LockedOrbitMass.standardA]

theorem noncontractive_factor :
    noncontractiveCylinder.RankOneTailFactor (2/3) := by
  intro c
  fin_cases c <;> ext i <;> fin_cases i <;>
    norm_num [PositiveLockedCylinder.tailRow,
      PositiveLockedCylinder.aggregateRow, PositiveLockedCylinder.aggregate,
      noncontractiveCylinder, expansiveTail, expansiveRest, tailBalanced,
      restBalanced, mass, addMass, LockedOrbitMass.standardE,
      LockedOrbitMass.standardA]

theorem noncontractive_factor_exceeds_tailScale :
    (1/3 : ℝ) ^ 2 < (2/3 : ℝ) ^ 2 := by norm_num

/-- `cth:SMST-provenance-marginals`: five positive diagonal-`S₄` orbit
cylinders have identical locked marginals and realize rank zero, rank one,
rank two, a strict unexplained-tail (positive Schur residual) branch, and a
rank-one propagation factor whose metric square exceeds `s²`. -/
theorem lockedMarginals_do_not_select_provenanceBranch :
    rankZeroCylinder.HasLockedMarginals
    ∧ rankOneCylinder.HasLockedMarginals
    ∧ rankTwoCylinder.HasLockedMarginals
    ∧ positiveSchurCylinder.HasLockedMarginals
    ∧ noncontractiveCylinder.HasLockedMarginals
    ∧ rankZeroCylinder.AggregateRankZero
    ∧ rankOneCylinder.AggregateRankOne
    ∧ rankTwoCylinder.AggregateRankTwo
    ∧ ¬ positiveSchurCylinder.TailExplainedByAggregate
    ∧ noncontractiveCylinder.AggregateRankOne
    ∧ noncontractiveCylinder.RankOneTailFactor (2/3)
    ∧ (1/3 : ℝ) ^ 2 < (2/3 : ℝ) ^ 2 := by
  exact ⟨rankZero_marginals, rankOne_marginals, rankTwo_marginals,
    positiveSchur_marginals, noncontractive_marginals, rankZero_branch,
    rankOne_branch, rankTwo_branch, positiveSchur_branch,
    noncontractive_rankOne, noncontractive_factor,
    noncontractive_factor_exceeds_tailScale⟩

end
end LockedProvenanceMarginalWitnesses
end NCG
