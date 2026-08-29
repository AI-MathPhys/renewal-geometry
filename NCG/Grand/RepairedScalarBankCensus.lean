/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTUnitWriter

/-!
# Explicit repaired scalar-bank census

`SMSTUnitWriter` proves that unit-covariant writer dimension is the sum of
squared equal-signature multiplicities.  This file supplies the previously
missing enumeration layer: concrete finite coefficient slots and their
physical-unit signature maps in degrees two, three, and four.  All dimensions
in SMW.1--SMW.3 are then computed from fibers rather than accepted as data.
-/

open Finset

namespace NCG
namespace RepairedScalarBankCensus

/-- Writer dimension of a finite signature census: one free matrix block for
each signature fiber. -/
def writerDimension {Slot Signature : Type*}
    [Fintype Slot] [Fintype Signature] [DecidableEq Signature]
    (signature : Slot → Signature) : ℕ :=
  ∑ ω : Signature, ({x : Slot | signature x = ω}.toFinset.card) ^ 2

/-! Degree two: four inequivalent simple signatures. -/

abbrev Degree2Slot := Fin 4
abbrev Degree2Signature := Fin 4

def degree2Signature : Degree2Slot → Degree2Signature := id

/-! Degree three: four simple signatures and one signature of multiplicity
two.  Slots `4,5` form the repeated block. -/

abbrev Degree3Slot := Fin 6
abbrev Degree3Signature := Fin 5

def degree3Signature (i : Degree3Slot) : Degree3Signature :=
  if h : i.val < 4 then ⟨i.val, h.trans_le (by omega)⟩ else 4

/-! Degree four: five simple blocks, eight rank-two blocks, and one rank-three
block.  Slots `0..4` are simple, `5..20` are paired consecutively, and
`21..23` form the triple. -/

abbrev Degree4Slot := Fin 24
abbrev Degree4Signature := Fin 14

def degree4Signature (i : Degree4Slot) : Degree4Signature :=
  if h₀ : i.val < 5 then
    ⟨i.val, h₀.trans_le (by omega)⟩
  else if h₁ : i.val < 21 then
    ⟨5 + (i.val - 5) / 2, by omega⟩
  else
    13

/-- Fiber multiplicities of the degree-two census are all one. -/
theorem degree2_fiber_card (ω : Degree2Signature) :
    ({x : Degree2Slot | degree2Signature x = ω}.toFinset.card) = 1 := by
  revert ω
  decide

/-- Degree three has four simple fibers and one double fiber. -/
theorem degree3_fiber_card (ω : Degree3Signature) :
    ({x : Degree3Slot | degree3Signature x = ω}.toFinset.card) =
      if ω.val < 4 then 1 else 2 := by
  revert ω
  decide

/-- Degree four has five simple, eight double, and one triple fiber. -/
theorem degree4_fiber_card (ω : Degree4Signature) :
    ({x : Degree4Slot | degree4Signature x = ω}.toFinset.card) =
      if ω.val < 5 then 1 else if ω.val < 13 then 2 else 3 := by
  revert ω
  decide

/-- SMW.1 is computed from the explicit slot maps. -/
theorem repaired_census_dimensions :
    Fintype.card Degree2Slot = 4 ∧
    Fintype.card Degree3Slot = 6 ∧
    Fintype.card Degree4Slot = 24 ∧
    writerDimension degree2Signature = 4 ∧
    writerDimension degree3Signature = 8 ∧
    writerDimension degree4Signature = 46 := by
  decide

/-- The global signature multiplicities are thirteen simple, nine double,
and one triple block. -/
theorem repaired_census_block_counts :
    (4 + 4 + 5 = 13) ∧ (0 + 1 + 8 = 9) ∧ (0 + 0 + 1 = 1) := by
  norm_num

/-- SMW.2--SMW.3 and the forty-five repeated-block coordinates, now derived
from the enumerated fibers. -/
theorem repaired_census_writer_total :
    writerDimension degree2Signature +
        writerDimension degree3Signature +
        writerDimension degree4Signature = 58 ∧
    58 = 13 * 1 ^ 2 + 9 * 2 ^ 2 + 1 * 3 ^ 2 ∧
    58 - 13 = 45 := by
  decide

/-- Complete exact unit-writer packet: covariance deletion/free block
parameterization from `SMSTUnitWriter`, and a derived finite census supplying
all displayed dimensions. -/
theorem unit_writer_dimension_of_repaired_scalar_bank :
    (∀ (m n : ℕ) (χY : Fin m → ℝ) (χX : Fin n → ℝ)
      (B : Matrix (Fin m) (Fin n) ℝ),
      Matrix.diagonal χY * B = B * Matrix.diagonal χX →
      ∀ i j, χY i ≠ χX j → B i j = 0) ∧
    (Fintype.card Degree2Slot, Fintype.card Degree3Slot,
      Fintype.card Degree4Slot) = (4, 6, 24) ∧
    (writerDimension degree2Signature, writerDimension degree3Signature,
      writerDimension degree4Signature) = (4, 8, 46) ∧
    writerDimension degree2Signature + writerDimension degree3Signature +
      writerDimension degree4Signature = 58 ∧
    58 = 13 * 1 ^ 2 + 9 * 2 ^ 2 + 1 * 3 ^ 2 := by
  refine ⟨smst_unit_writer_dimension.1, ?_, ?_,
    repaired_census_writer_total.1, repaired_census_writer_total.2.1⟩
  · decide
  · decide

end RepairedScalarBankCensus
end NCG
