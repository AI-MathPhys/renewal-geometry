/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# First terminal short and its rank-one germ witness

This file proves `thm:GT-NCG-terminal-short`.  The missing differentiated germ
is represented by one normalized target column.  If that column is outside the
actual source range, its Moore--Penrose orthogonal short is a nonzero positive
`1 × 1` matrix, hence has rank exactly one.  Its polar innovation range is the
source-minimal missing direction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace TerminalGermRankOneShort

/-- The presently populated prefix together with the fixed one-dimensional
differentiated-germ query.  `target_outside` is the precise occurrence claim:
the same-carrier differentiated channel incidence has not yet been supplied. -/
structure Packet (h e : ℕ) where
  source : Matrix (Fin h) (Fin e) ℂ
  prefixShort : Matrix (Fin 0) (Fin 0) ℂ
  prefix_zero : prefixShort = 0
  germTarget : Matrix (Fin h) (Fin 1) ℂ
  target_outside : ¬ SourceRangeIncluded germTarget source

/-- Orthogonal germ innovation `(I-P_S)b_delta`. -/
def germInnovation {h e : ℕ} (P : Packet h e) : Matrix (Fin h) (Fin 1) ℂ :=
  (1 - sourceRangeProjection P.source) * P.germTarget

/-- The terminal scalar short `b_delta^* (I-P_S) b_delta`. -/
def germShort {h e : ℕ} (P : Packet h e) : Matrix (Fin 1) (Fin 1) ℂ :=
  sourceSchurResidual P.source P.germTarget

/-- The exact source-minimal missing direction. -/
def missingDirection {h e : ℕ} (P : Packet h e) : Submodule ℂ (Fin h → ℂ) :=
  LinearMap.range (germInnovation P).mulVecLin

theorem germShort_eq_display {h e : ℕ} (P : Packet h e) :
    germShort P = P.germTargetᴴ *
      (1 - sourceRangeProjection P.source) * P.germTarget :=
  sourceSchurResidual_eq_orthogonalResidual P.source P.germTarget

theorem germShort_posSemidef {h e : ℕ} (P : Packet h e) :
    (germShort P).PosSemidef :=
  sourceSchurResidual_posSemidef P.source P.germTarget

theorem germShort_ne_zero {h e : ℕ} (P : Packet h e) : germShort P ≠ 0 := by
  intro hzero
  exact P.target_outside
    ((sourceSchurResidual_eq_zero_iff_rangeIncluded
      P.source P.germTarget).mp hzero)

/-- The unique scalar entry of the terminal short is strictly positive. -/
theorem germShort_scalar_pos {h e : ℕ} (P : Packet h e) :
    0 < (germShort P 0 0).re := by
  have hpsd := germShort_posSemidef P
  have hnonnegC : (0 : ℂ) ≤ germShort P 0 0 := hpsd.diag_nonneg
  have hnonneg : 0 ≤ (germShort P 0 0).re :=
    (RCLike.nonneg_iff.mp hnonnegC).1
  have him : (germShort P 0 0).im = 0 :=
    (RCLike.nonneg_iff.mp hnonnegC).2
  have hentry : germShort P 0 0 ≠ 0 := by
    intro hz
    apply germShort_ne_zero P
    ext i j
    fin_cases i
    fin_cases j
    exact hz
  exact lt_of_le_of_ne hnonneg fun hre =>
    hentry (Complex.ext hre.symm him)

/-- A nonzero positive scalar short has matrix rank exactly one. -/
theorem germShort_rank_one {h e : ℕ} (P : Packet h e) :
    (germShort P).rank = 1 := by
  have hentry : germShort P 0 0 ≠ 0 := by
    intro hz
    have hp := germShort_scalar_pos P
    rw [hz] at hp
    simp at hp
  have hdet : IsUnit (germShort P).det := by
    apply isUnit_iff_ne_zero.mpr
    simpa using hentry
  have h := Matrix.rank_mul_eq_right_of_isUnit_det
    (germShort P) (1 : Matrix (Fin 1) (Fin 1) ℂ) hdet
  simpa using h

theorem germInnovation_ne_zero {h e : ℕ} (P : Packet h e) :
    germInnovation P ≠ 0 := by
  intro hzero
  apply germShort_ne_zero P
  rw [germShort_eq_display]
  rw [Matrix.mul_assoc]
  change P.germTargetᴴ * germInnovation P = 0
  rw [hzero, Matrix.mul_zero]

/-- The polar innovation range is exactly one-dimensional, so it is the
source-minimal first missing direction rather than merely an upper bound. -/
theorem missingDirection_finrank_one {h e : ℕ} (P : Packet h e) :
    Module.finrank ℂ (missingDirection P) = 1 := by
  change (germInnovation P).rank = 1
  apply le_antisymm
  · exact (germInnovation P).rank_le_width
  · have hpos : 0 < (germInnovation P).rank := by
      rw [Matrix.rank, Module.finrank_pos_iff]
      have hne := germInnovation_ne_zero P
      have hex : ∃ i j, germInnovation P i j ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hne
        ext i j
        exact hall i j
      obtain ⟨i, j, hij⟩ := hex
      let y : Fin h → ℂ := (germInnovation P).mulVec (Pi.single j 1)
      have hyi : y i = germInnovation P i j := by
        simp [y, Matrix.mulVec, dotProduct, Pi.single_apply]
      let yr : LinearMap.range (germInnovation P).mulVecLin :=
        ⟨y, ⟨Pi.single j 1, rfl⟩⟩
      have hyr : yr ≠ 0 := by
        intro hz
        have hz' := congrArg
          (fun z : LinearMap.range (germInnovation P).mulVecLin => (z : Fin h → ℂ) i) hz
        simp only [yr, Submodule.coe_mk, Pi.zero_apply] at hz'
        exact hij (hyi ▸ hz')
      exact ⟨⟨yr, 0, hyr⟩⟩
    omega

/-- **`thm:GT-NCG-terminal-short`.**  The zero populated prefix is followed by
the positive rank-one short of the fixed missing germ query, and its innovation
range is the exact one-dimensional source-minimal missing bank. -/
theorem first_terminal_short_and_source_minimal_germ_witness
    {h e : ℕ} (P : Packet h e) :
    P.prefixShort = 0 ∧
    (germShort P).PosSemidef ∧
    0 < (germShort P 0 0).re ∧
    (germShort P).rank = 1 ∧
    germInnovation P ≠ 0 ∧
    Module.finrank ℂ (missingDirection P) = 1 :=
  ⟨P.prefix_zero, germShort_posSemidef P, germShort_scalar_pos P,
    germShort_rank_one P, germInnovation_ne_zero P,
    missingDirection_finrank_one P⟩

end TerminalGermRankOneShort
end NCG
