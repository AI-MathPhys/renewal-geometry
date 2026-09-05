import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic

/-!
# Finite boxes in the integer Fourier lattice

This file packages the elementary finite-set combinatorics used by Fourier
cutoff arguments.  The box of radius `R` consists of the modes whose every
coordinate has absolute value at most `R`.  Its complement therefore contains
a coordinate strictly larger than `R` in absolute value.
-/

namespace NCG

open Finset

/-- The finite `ℓ∞`-box of radius `R` in the integer lattice `d → ℤ`. -/
def integerFourierBox (d : Type*) [Fintype d] [DecidableEq d] (R : ℕ) :
    Finset (d → ℤ) :=
  Fintype.piFinset fun _ : d ↦ Finset.Icc (-(R : ℤ)) (R : ℤ)

@[simp]
theorem mem_integerFourierBox_iff
    {d : Type*} [Fintype d] [DecidableEq d] (R : ℕ) (k : d → ℤ) :
    k ∈ integerFourierBox d R ↔ ∀ j, |k j| ≤ (R : ℤ) := by
  simp [integerFourierBox, abs_le]

theorem coordinate_abs_le_of_mem_integerFourierBox
    {d : Type*} [Fintype d] [DecidableEq d]
    {R : ℕ} {k : d → ℤ} (hk : k ∈ integerFourierBox d R) (j : d) :
    |k j| ≤ (R : ℤ) :=
  (mem_integerFourierBox_iff R k).1 hk j

/-- A mode outside an integer Fourier box has a high coordinate. -/
theorem exists_coordinate_abs_gt_of_not_mem_integerFourierBox
    {d : Type*} [Fintype d] [DecidableEq d]
    {R : ℕ} {k : d → ℤ} (hk : k ∉ integerFourierBox d R) :
    ∃ j, (R : ℤ) < |k j| := by
  rw [mem_integerFourierBox_iff] at hk
  push_neg at hk
  exact hk

/-- Real-valued form of the high-coordinate conclusion. -/
theorem exists_coordinate_natCast_lt_abs_intCast_of_not_mem_integerFourierBox
    {d : Type*} [Fintype d] [DecidableEq d]
    {R : ℕ} {k : d → ℤ} (hk : k ∉ integerFourierBox d R) :
    ∃ j, (R : ℝ) < |((k j : ℤ) : ℝ)| := by
  obtain ⟨j, hj⟩ := exists_coordinate_abs_gt_of_not_mem_integerFourierBox hk
  refine ⟨j, ?_⟩
  have hcast : (((R : ℤ) : ℝ)) < ((|k j| : ℤ) : ℝ) :=
    Int.cast_lt.mpr hj
  simpa only [Int.cast_natCast, Int.cast_abs] using hcast

/-- The integer Fourier boxes are monotone in their radius. -/
theorem integerFourierBox_mono
    {d : Type*} [Fintype d] [DecidableEq d]
    {R S : ℕ} (hRS : R ≤ S) :
    integerFourierBox d R ⊆ integerFourierBox d S := by
  intro k hk
  rw [mem_integerFourierBox_iff] at hk ⊢
  intro j
  exact hk j |>.trans (by exact_mod_cast hRS)

end NCG
