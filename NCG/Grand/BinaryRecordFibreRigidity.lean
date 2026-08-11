/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Binary record-fibre rigidity

This file gives the exact finite faithful-record argument behind
`thm:SMST-record-grading-rigidity` in the Gran-Tensor manuscript.  A strictly
positive weight is the faithful record state, and conditional expectation onto
the locked binary pointer is its weighted fibre average.
-/

namespace NCG

open scoped BigOperators

/-- The mass assigned by a finite record state to one locked pointer fibre. -/
noncomputable def lockedFibreMass {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (pointer : Ω → Fin 2) (b : Fin 2) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b), weight ω

/-- Conditional expectation of a real record writer on a locked pointer fibre. -/
noncomputable def lockedFibreMean {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2) (b : Fin 2) : ℝ :=
  (∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b),
      weight ω * writer ω) / lockedFibreMass weight pointer b

/-- The faithful conditional-expectation defect.  This is the squared
`L²(weight)` distance from the algebra of locked-pointer functions. -/
noncomputable def lockedFibreDefect {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2) : ℝ :=
  ∑ b, ∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b),
    weight ω * (writer ω - lockedFibreMean weight writer pointer b) ^ 2

/-- Literal constancy of a record writer on every locked-sign fibre. -/
def ConstantOnLockedFibres {Ω : Type*}
    (pointer : Ω → Fin 2) (writer : Ω → ℝ) : Prop :=
  ∀ ⦃ω ν⦄, pointer ω = pointer ν → writer ω = writer ν

theorem lockedFibreMass_pos {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (b : Fin 2) :
    0 < lockedFibreMass weight pointer b := by
  obtain ⟨ω, hω⟩ := hpointer b
  unfold lockedFibreMass
  exact Finset.sum_pos (fun ν _ => hweight ν) ⟨ω, by simp [hω]⟩

theorem lockedFibreMean_eq_of_constant {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (hconstant : ConstantOnLockedFibres pointer writer) (ω : Ω) :
    lockedFibreMean weight writer pointer (pointer ω) = writer ω := by
  have hmass := lockedFibreMass_pos weight pointer hweight hpointer (pointer ω)
  have hnum :
      (∑ ν ∈ Finset.univ.filter (fun ν => pointer ν = pointer ω),
        weight ν * writer ν) =
        lockedFibreMass weight pointer (pointer ω) * writer ω := by
    rw [lockedFibreMass]
    calc
      (∑ ν ∈ Finset.univ.filter (fun ν => pointer ν = pointer ω),
          weight ν * writer ν) =
          ∑ ν ∈ Finset.univ.filter (fun ν => pointer ν = pointer ω),
            weight ν * writer ω := by
              apply Finset.sum_congr rfl
              intro ν hν
              rw [hconstant (Finset.mem_filter.mp hν).2]
      _ = (∑ ν ∈ Finset.univ.filter (fun ν => pointer ν = pointer ω),
          weight ν) * writer ω := by rw [Finset.sum_mul]
  unfold lockedFibreMean
  rw [hnum, mul_div_cancel_left₀ _ hmass.ne']

/-- On a protected binary writer, the conditional variance on one fibre is
exactly `p_b (1 - m_b²)`, as in the manuscript proof. -/
theorem lockedFibreVariance_formula {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1) (b : Fin 2) :
    (∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b),
      weight ω * (writer ω - lockedFibreMean weight writer pointer b) ^ 2) =
      lockedFibreMass weight pointer b *
        (1 - lockedFibreMean weight writer pointer b ^ 2) := by
  let s := Finset.univ.filter (fun ω => pointer ω = b)
  let m := lockedFibreMean weight writer pointer b
  have hmass := lockedFibreMass_pos weight pointer hweight hpointer b
  have hsquare : (∑ ω ∈ s, weight ω * writer ω ^ 2) =
      ∑ ω ∈ s, weight ω := by
    apply Finset.sum_congr rfl
    intro ω _
    rcases hbinary ω with h | h <;> rw [h] <;> norm_num
  have hmean : (∑ ω ∈ s, weight ω * writer ω) =
      lockedFibreMass weight pointer b * m := by
    dsimp [s, m, lockedFibreMean]
    field_simp [hmass.ne']
  have hexpand : ∀ ω,
      weight ω * (writer ω - m) ^ 2 =
        weight ω * writer ω ^ 2 - (2 * m) * (weight ω * writer ω) +
          m ^ 2 * weight ω := by
    intro ω
    ring
  change (∑ ω ∈ s, weight ω * (writer ω - m) ^ 2) =
    lockedFibreMass weight pointer b * (1 - m ^ 2)
  simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsquare, hmean]
  change lockedFibreMass weight pointer b -
      2 * m * (lockedFibreMass weight pointer b * m) +
      m ^ 2 * lockedFibreMass weight pointer b =
    lockedFibreMass weight pointer b * (1 - m ^ 2)
  ring

/-- The full two-fibre defect is the sum of the two faithful binary variance
contributions. -/
theorem lockedFibreDefect_formula {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1) :
    lockedFibreDefect weight writer pointer =
      ∑ b, lockedFibreMass weight pointer b *
        (1 - lockedFibreMean weight writer pointer b ^ 2) := by
  unfold lockedFibreDefect
  apply Finset.sum_congr rfl
  intro b _
  exact lockedFibreVariance_formula weight writer pointer
    hweight hpointer hbinary b

/-- Faithfulness turns zero conditional variance into actual, rather than
almost-everywhere, constancy on each locked pointer fibre. -/
theorem lockedFibreDefect_eq_zero_iff {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer) :
    lockedFibreDefect weight writer pointer = 0 ↔
      ConstantOnLockedFibres pointer writer := by
  have hterm : ∀ b ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ ∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b),
        weight ω * (writer ω - lockedFibreMean weight writer pointer b) ^ 2 := by
    intro b _
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (hweight ω)) (sq_nonneg _)
  constructor
  · intro hzero
    have houter : ∀ b ∈ (Finset.univ : Finset (Fin 2)),
        (∑ ω ∈ Finset.univ.filter (fun ω => pointer ω = b),
          weight ω * (writer ω - lockedFibreMean weight writer pointer b) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero
    have hmean : ∀ ω,
        writer ω = lockedFibreMean weight writer pointer (pointer ω) := by
      intro ω
      have hinner : ∀ ν ∈ Finset.univ.filter (fun ν => pointer ν = pointer ω),
          weight ν *
            (writer ν - lockedFibreMean weight writer pointer (pointer ω)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ =>
          mul_nonneg (le_of_lt (hweight ν)) (sq_nonneg _))).mp
            (houter (pointer ω) (Finset.mem_univ _))
      have hproduct := hinner ω (by simp)
      have hsquare :
          (writer ω - lockedFibreMean weight writer pointer (pointer ω)) ^ 2 = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt (hweight ω))
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    intro ω ν hων
    rw [hmean ω, hmean ν, hων]
  · intro hconstant
    unfold lockedFibreDefect
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro ω hω
    have hptr : pointer ω = b := (Finset.mem_filter.mp hω).2
    rw [← hptr, lockedFibreMean_eq_of_constant weight writer pointer
      hweight hpointer hconstant]
    simp

/-- The locked binary pointer as a protected `±1` writer. -/
def lockedPointerWriter {Ω : Type*} (pointer : Ω → Fin 2) : Ω → ℝ :=
  fun ω => if pointer ω = 0 then 1 else -1

/-- There are exactly four binary writers constant on the two nonempty locked
fibres: the two constants and the two orientations of the locked pointer. -/
theorem constantBinaryWriter_fourChoices {Ω : Type*}
    (pointer : Ω → Fin 2) (writer : Ω → ℝ)
    (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1)
    (hconstant : ConstantOnLockedFibres pointer writer) :
    writer = (fun _ => 1) ∨ writer = (fun _ => -1) ∨
      writer = lockedPointerWriter pointer ∨
      writer = fun ω => -lockedPointerWriter pointer ω := by
  obtain ⟨ω₀, hω₀⟩ := hpointer 0
  obtain ⟨ω₁, hω₁⟩ := hpointer 1
  rcases hbinary ω₀ with h₀ | h₀ <;>
    rcases hbinary ω₁ with h₁ | h₁
  · left
    funext ω
    by_cases h : pointer ω = 0
    · exact (hconstant (h.trans hω₀.symm)).trans h₀
    · have h' : pointer ω = 1 := by omega
      exact (hconstant (h'.trans hω₁.symm)).trans h₁
  · right; right; left
    funext ω
    by_cases h : pointer ω = 0
    · rw [lockedPointerWriter, if_pos h]
      exact (hconstant (h.trans hω₀.symm)).trans h₀
    · have h' : pointer ω = 1 := by omega
      rw [lockedPointerWriter, if_neg h]
      exact (hconstant (h'.trans hω₁.symm)).trans h₁
  · right; right; right
    funext ω
    by_cases h : pointer ω = 0
    · simpa [lockedPointerWriter, h] using
        (hconstant (h.trans hω₀.symm)).trans h₀
    · have h' : pointer ω = 1 := by omega
      simpa [lockedPointerWriter, h] using
        (hconstant (h'.trans hω₁.symm)).trans h₁
  · right; left
    funext ω
    by_cases h : pointer ω = 0
    · exact (hconstant (h.trans hω₀.symm)).trans h₀
    · have h' : pointer ω = 1 := by omega
      exact (hconstant (h'.trans hω₁.symm)).trans h₁

/-- After minimal-record reduction, nonconstancy removes the two scalar
writers and leaves precisely the two orientations of the pointer writer. -/
theorem nonconstantBinaryWriter_eq_pointer_or_neg {Ω : Type*}
    (pointer : Ω → Fin 2) (writer : Ω → ℝ)
    (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1)
    (hconstant : ConstantOnLockedFibres pointer writer)
    (hnonconstant : ¬ ∀ ω ν, writer ω = writer ν) :
    writer = lockedPointerWriter pointer ∨
      writer = fun ω => -lockedPointerWriter pointer ω := by
  rcases constantBinaryWriter_fourChoices pointer writer hpointer hbinary hconstant with
    h | h | h | h
  · exfalso
    apply hnonconstant
    intro ω ν
    rw [h]
  · exfalso
    apply hnonconstant
    intro ω ν
    rw [h]
  · exact Or.inl h
  · exact Or.inr h

/-- Exact four-branch rigidity, now with fibre constancy derived from the
vanishing faithful conditional-expectation defect. -/
theorem zeroDefect_binaryWriter_fourChoices {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1)
    (hzero : lockedFibreDefect weight writer pointer = 0) :
    writer = (fun _ => 1) ∨ writer = (fun _ => -1) ∨
      writer = lockedPointerWriter pointer ∨
      writer = fun ω => -lockedPointerWriter pointer ω :=
  constantBinaryWriter_fourChoices pointer writer hpointer hbinary
    ((lockedFibreDefect_eq_zero_iff weight writer pointer
      hweight hpointer).mp hzero)

/-- The nonconstant minimal-record branch is the pointer grading, up to its
single globally oriented sign. -/
theorem zeroDefect_nonconstantBinaryWriter_eq_pointer_or_neg
    {Ω : Type*} [Fintype Ω]
    (weight writer : Ω → ℝ) (pointer : Ω → Fin 2)
    (hweight : ∀ ω, 0 < weight ω) (hpointer : Function.Surjective pointer)
    (hbinary : ∀ ω, writer ω = 1 ∨ writer ω = -1)
    (hzero : lockedFibreDefect weight writer pointer = 0)
    (hnonconstant : ¬ ∀ ω ν, writer ω = writer ν) :
    writer = lockedPointerWriter pointer ∨
      writer = fun ω => -lockedPointerWriter pointer ω :=
  nonconstantBinaryWriter_eq_pointer_or_neg pointer writer hpointer hbinary
    ((lockedFibreDefect_eq_zero_iff weight writer pointer
      hweight hpointer).mp hzero) hnonconstant

/-- Changing the literal sign of a grading implementer changes neither its
conjugation automorphism nor its odd shorting. -/
theorem gradingSignChange_preserves_automorphism_and_oddShorting
    {n : Type*} [Fintype n] [DecidableEq n]
    (Z X : Matrix n n ℂ) :
    (-Z) * X * (-Z) = Z * X * Z ∧
      (2 : ℂ)⁻¹ • (X - (-Z) * X * (-Z)) =
        (2 : ℂ)⁻¹ • (X - Z * X * Z) := by
  constructor <;> noncomm_ring

/-- One oriented branch distinguishes the two literal signs. -/
theorem orientedBranch_fixes_pointerSign {Ω : Type*}
    (pointer : Ω → Fin 2) (writer : Ω → ℝ)
    (hchoice : writer = lockedPointerWriter pointer ∨
      writer = fun ω => -lockedPointerWriter pointer ω)
    (ω : Ω) (horiented : writer ω = lockedPointerWriter pointer ω) :
    writer = lockedPointerWriter pointer := by
  rcases hchoice with h | h
  · exact h
  · exfalso
    rw [h] at horiented
    have hnonzero : lockedPointerWriter pointer ω ≠ 0 := by
      unfold lockedPointerWriter
      split <;> norm_num
    have : lockedPointerWriter pointer ω = 0 := by linarith
    exact hnonzero this

end NCG
