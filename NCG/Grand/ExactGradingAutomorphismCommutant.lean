/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GradingCommutant

/-!
# Exact grading-automorphism commutant and central sign ambiguity

This module proves the nondegenerate content of
`thm:SMST-grading-commutant`: the action residual is related to the transition
commutator by unitary sandwiching (not by definition), equality of grading
automorphisms propagates from generators to their algebra, and a central
self-adjoint involution is `±1` on every minimal central block.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Difference of the two grading conjugation automorphisms. -/
def gradingActionDefect {n : Type*} [Fintype n]
    (Z₁ Z₀ X : Matrix n n ℂ) : Matrix n n ℂ :=
  Z₁ * X * Z₁ - Z₀ * X * Z₀

/-- Odd shorting associated with a grading implementer. -/
noncomputable def gradingOddShorting {n : Type*} [Fintype n]
    (Z X : Matrix n n ℂ) : Matrix n n ℂ :=
  ((2 : ℂ)⁻¹) • (X - Z * X * Z)

/-- Difference of the two odd shortings. -/
noncomputable def gradingSplitDefect {n : Type*} [Fintype n]
    (Z₁ Z₀ X : Matrix n n ℂ) : Matrix n n ℂ :=
  gradingOddShorting Z₁ X - gradingOddShorting Z₀ X

/-- The genuine bridge between the conjugation residual and the transition
commutator. -/
theorem gradingTransition_commutator_eq_sandwich
    {n : Type*} [Fintype n] [DecidableEq n]
    (Z₁ Z₀ X : Matrix n n ℂ)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1) :
    X * (Z₁ * Z₀) - (Z₁ * Z₀) * X =
      Z₁ * gradingActionDefect Z₁ Z₀ X * Z₀ := by
  symm
  calc
    Z₁ * gradingActionDefect Z₁ Z₀ X * Z₀ =
        (Z₁ * Z₁) * X * (Z₁ * Z₀) -
          (Z₁ * Z₀) * X * (Z₀ * Z₀) := by
      unfold gradingActionDefect
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = X * (Z₁ * Z₀) - (Z₁ * Z₀) * X := by
      rw [hZ₁2, hZ₀2, Matrix.one_mul, Matrix.mul_one]

set_option maxHeartbeats 800000 in
-- Reassociating the generic matrix sandwich is expensive for the elaborator.
/-- Unitary sandwiching preserves the Hilbert--Schmidt square of the genuine
action residual. -/
theorem gradingActionDefect_hilbertSchmidt_eq_commutator
    {n : Type*} [Fintype n] [DecidableEq n]
    (Z₁ Z₀ X : Matrix n n ℂ)
    (hZ₁H : Z₁ᴴ = Z₁) (hZ₀H : Z₀ᴴ = Z₀)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1) :
    (((X * (Z₁ * Z₀) - (Z₁ * Z₀) * X)ᴴ) *
        (X * (Z₁ * Z₀) - (Z₁ * Z₀) * X)).trace =
      ((gradingActionDefect Z₁ Z₀ X)ᴴ *
        gradingActionDefect Z₁ Z₀ X).trace := by
  rw [gradingTransition_commutator_eq_sandwich Z₁ Z₀ X hZ₁2 hZ₀2]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hZ₁H, hZ₀H]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Z₁ Z₁, hZ₁2, Matrix.one_mul]
  rw [← Matrix.mul_assoc
    (gradingActionDefect Z₁ Z₀ X)ᴴ
    (gradingActionDefect Z₁ Z₀ X) Z₀]
  let M := (gradingActionDefect Z₁ Z₀ X)ᴴ *
    gradingActionDefect Z₁ Z₀ X
  change (Z₀ * (M * Z₀)).trace = M.trace
  rw [Matrix.trace_mul_comm Z₀ (M * Z₀)]
  rw [Matrix.mul_assoc, hZ₀2, Matrix.mul_one]

/-- The difference of odd shortings is exactly minus one half of the
conjugation defect. -/
theorem gradingSplitDefect_eq_half_actionDefect
    {n : Type*} [Fintype n]
    (Z₁ Z₀ X : Matrix n n ℂ) :
    gradingSplitDefect Z₁ Z₀ X =
      (-(2 : ℂ)⁻¹) • gradingActionDefect Z₁ Z₀ X := by
  unfold gradingSplitDefect gradingOddShorting gradingActionDefect
  module

/-- The manuscript's genuine factor-four relation, after deriving the split
defect from the two grading shortings. -/
theorem gradingActionDefect_eq_four_splitDefect
    {n : Type*} [Fintype n]
    (Z₁ Z₀ X : Matrix n n ℂ) :
    ((gradingActionDefect Z₁ Z₀ X)ᴴ *
        gradingActionDefect Z₁ Z₀ X).trace =
      4 * ((gradingSplitDefect Z₁ Z₀ X)ᴴ *
        gradingSplitDefect Z₁ Z₀ X).trace := by
  rw [gradingSplitDefect_eq_half_actionDefect]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  norm_num [RCLike.star_def]
  ring

/-- Equality of the two grading automorphisms is equivalent to commutation
with their transition writer. -/
theorem gradingAutomorphisms_eq_iff_commutes_transition
    {n : Type*} [Fintype n] [DecidableEq n]
    (Z₁ Z₀ X : Matrix n n ℂ)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1) :
    gradingActionDefect Z₁ Z₀ X = 0 ↔
      X * (Z₁ * Z₀) = (Z₁ * Z₀) * X := by
  constructor
  · intro hD
    apply sub_eq_zero.mp
    rw [gradingTransition_commutator_eq_sandwich Z₁ Z₀ X hZ₁2 hZ₀2,
      hD, Matrix.mul_zero, Matrix.zero_mul]
  · intro hC
    have hsand : Z₁ * gradingActionDefect Z₁ Z₀ X * Z₀ = 0 := by
      rw [← gradingTransition_commutator_eq_sandwich Z₁ Z₀ X hZ₁2 hZ₀2,
        sub_eq_zero.mpr hC]
    calc
      gradingActionDefect Z₁ Z₀ X =
          (Z₁ * Z₁) * gradingActionDefect Z₁ Z₀ X * (Z₀ * Z₀) := by
            rw [hZ₁2, hZ₀2, Matrix.one_mul, Matrix.mul_one]
      _ = Z₁ * (Z₁ * gradingActionDefect Z₁ Z₀ X * Z₀) * Z₀ := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hsand, Matrix.mul_zero, Matrix.zero_mul]

/-- Commutation with a generating tuple propagates to every word in its
generated action algebra. -/
theorem transition_commutes_generatedActionAlgebra
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (c : ι → Matrix n n ℂ) (U X : Matrix n n ℂ)
    (hU : ∀ j, Commute U (c j))
    (hX : X ∈ Algebra.adjoin ℂ (Set.range c)) :
    Commute U X := by
  exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hX
    (fun x hx => by
      rcases hx with ⟨j, rfl⟩
      exact hU j)

/-- Exact finite assembly of the four equivalent vanishing/commutant/
automorphism/shorting clauses. -/
theorem gradingResidualCommutantEquivalences
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (c : ι → Matrix n n ℂ) (Z₁ Z₀ : Matrix n n ℂ)
    (hZ₁H : Z₁ᴴ = Z₁) (hZ₀H : Z₀ᴴ = Z₀)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1) :
    ((∑ j, ((gradingActionDefect Z₁ Z₀ (c j))ᴴ *
        gradingActionDefect Z₁ Z₀ (c j)).trace = 0)
      ↔ ∀ j, Commute (Z₁ * Z₀) (c j))
    ∧ (∀ X ∈ Algebra.adjoin ℂ (Set.range c),
        Commute (Z₁ * Z₀) X ↔ gradingActionDefect Z₁ Z₀ X = 0)
    ∧ (∀ X, gradingActionDefect Z₁ Z₀ X = 0 ↔
        gradingSplitDefect Z₁ Z₀ X = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hsum j
      have hpsd : ∀ k : ι,
          ((gradingActionDefect Z₁ Z₀ (c k))ᴴ *
            gradingActionDefect Z₁ Z₀ (c k)).PosSemidef :=
        fun k => Matrix.posSemidef_conjTranspose_mul_self _
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => (hpsd k).trace_nonneg)).mp hsum j (Finset.mem_univ j)
      have hD := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
      exact (gradingAutomorphisms_eq_iff_commutes_transition
        Z₁ Z₀ (c j) hZ₁2 hZ₀2).mp hD |>.symm
    · intro hcomm
      refine Finset.sum_eq_zero fun j _ => ?_
      have hD := (gradingAutomorphisms_eq_iff_commutes_transition
        Z₁ Z₀ (c j) hZ₁2 hZ₀2).mpr (hcomm j).symm.eq
      rw [hD]
      simp
  · intro X _
    constructor
    · intro h
      exact (gradingAutomorphisms_eq_iff_commutes_transition
        Z₁ Z₀ X hZ₁2 hZ₀2).mpr h.eq.symm
    · intro h
      exact (gradingAutomorphisms_eq_iff_commutes_transition
        Z₁ Z₀ X hZ₁2 hZ₀2).mp h |>.symm
  · intro X
    rw [gradingSplitDefect_eq_half_actionDefect]
    constructor
    · intro h; rw [h, smul_zero]
    · intro h
      have hc : (-(2 : ℂ)⁻¹) ≠ 0 := by norm_num
      exact (smul_eq_zero.mp h).resolve_left hc

/-- Under finite Howe duality, if both grading signs commute with the
multiplicity algebra, their transition writer is a central self-adjoint
involution in that algebra. -/
theorem howeTransition_isCentralSelfAdjointInvolution
    {n : Type*} [Fintype n] [DecidableEq n]
    (action multiplicity : Subalgebra ℂ (Matrix n n ℂ))
    (Z₁ Z₀ : Matrix n n ℂ)
    (hZ₁H : Z₁ᴴ = Z₁) (hZ₀H : Z₀ᴴ = Z₀)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1)
    (hHowe : ∀ T, T ∈ multiplicity ↔
      ∀ X ∈ action, Commute T X)
    (htransition : ∀ X ∈ action, Commute (Z₁ * Z₀) X)
    (hZ₁mult : ∀ Y ∈ multiplicity, Commute Z₁ Y)
    (hZ₀mult : ∀ Y ∈ multiplicity, Commute Z₀ Y) :
    (Z₁ * Z₀ ∈ multiplicity)
    ∧ (∀ Y ∈ multiplicity, Commute (Z₁ * Z₀) Y)
    ∧ (Z₁ * Z₀)ᴴ = Z₁ * Z₀
    ∧ (Z₁ * Z₀) * (Z₁ * Z₀) = 1 := by
  have hmem : Z₁ * Z₀ ∈ multiplicity :=
    (hHowe (Z₁ * Z₀)).mpr htransition
  have hcentral : ∀ Y ∈ multiplicity, Commute (Z₁ * Z₀) Y := by
    intro Y hY
    show (Z₁ * Z₀) * Y = Y * (Z₁ * Z₀)
    calc
      (Z₁ * Z₀) * Y = Z₁ * (Z₀ * Y) := by
        simp only [Matrix.mul_assoc]
      _ = Z₁ * (Y * Z₀) := by rw [(hZ₀mult Y hY).eq]
      _ = (Z₁ * Y) * Z₀ := by simp only [Matrix.mul_assoc]
      _ = (Y * Z₁) * Z₀ := by rw [(hZ₁mult Y hY).eq]
      _ = Y * (Z₁ * Z₀) := by simp only [Matrix.mul_assoc]
  have hZcommU := hZ₀mult (Z₁ * Z₀) hmem
  have hZcomm : Z₀ * Z₁ = Z₁ * Z₀ := by
    have h := hZcommU.eq
    simp only [Matrix.mul_assoc] at h
    rw [hZ₀2, Matrix.mul_one] at h
    have hright := congrArg (fun M => M * Z₀) h
    simp only [Matrix.mul_assoc] at hright
    rw [hZ₀2, Matrix.mul_one] at hright
    exact hright
  refine ⟨hmem, hcentral, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hZ₁H, hZ₀H, hZcomm]
  · calc
      (Z₁ * Z₀) * (Z₁ * Z₀) = (Z₁ * Z₀) * (Z₀ * Z₁) := by
        rw [hZcomm]
      _ = Z₁ * (Z₀ * Z₀) * Z₁ := by simp only [Matrix.mul_assoc]
      _ = Z₁ * Z₁ := by rw [hZ₀2, Matrix.mul_one]
      _ = 1 := hZ₁2

/-- A finite family of nonzero minimal central projections resolves every
central involution into independent `±1` signs. -/
theorem centralInvolution_signDecomposition
    {n a : Type*} [Fintype n] [DecidableEq n] [Fintype a]
    (U : Matrix n n ℂ) (z : a → Matrix n n ℂ)
    (hU2 : U * U = 1)
    (hzsum : ∑ i, z i = 1)
    (hzidem : ∀ i, z i * z i = z i)
    (hzcomm : ∀ i, Commute U (z i))
    (hznonzero : ∀ i, z i ≠ 0)
    (hminimal : ∀ i, ∃ lam : ℂ, U * z i = lam • z i) :
    ∃ ε : a → ℂ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      U = ∑ i, ε i • z i := by
  choose ε hε using hminimal
  have hsign : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    have hsquare : (ε i * ε i - 1) • z i = 0 := by
      have hblock : (U * z i) * (U * z i) = z i := by
        calc
          (U * z i) * (U * z i) = U * (z i * U) * z i := by
            simp only [Matrix.mul_assoc]
          _ = U * (U * z i) * z i := by rw [(hzcomm i).eq.symm]
          _ = (U * U) * (z i * z i) := by
            simp only [Matrix.mul_assoc]
          _ = z i := by rw [hU2, hzidem, Matrix.one_mul]
      rw [hε, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        hzidem] at hblock
      rw [← sub_eq_zero] at hblock
      simpa [sub_smul] using hblock
    have hscalar : ε i * ε i = 1 := by
      rcases smul_eq_zero.mp hsquare with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h (hznonzero i)
    have hfactor : (ε i - 1) * (ε i + 1) = 0 := by
      rw [mul_add, sub_mul]
      linear_combination hscalar
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  refine ⟨ε, hsign, ?_⟩
  calc
    U = U * 1 := (Matrix.mul_one U).symm
    _ = U * ∑ i, z i := by rw [hzsum]
    _ = ∑ i, U * z i := by rw [Matrix.mul_sum]
    _ = ∑ i, ε i • z i := Finset.sum_congr rfl (fun i _ => hε i)

/-- In a factor there is only one central block, so two implementers of the
same grading differ by one global sign. -/
theorem factorGradingImplementers_differBySign
    {n : Type*} [Fintype n] [DecidableEq n]
    (Z₁ Z₀ U : Matrix n n ℂ)
    (hU : U = Z₁ * Z₀) (hUone : U = 1 ∨ U = -1)
    (hZ₀2 : Z₀ * Z₀ = 1) :
    Z₁ = Z₀ ∨ Z₁ = -Z₀ := by
  have hrecover : Z₁ = U * Z₀ := by
    rw [hU, Matrix.mul_assoc, hZ₀2, Matrix.mul_one]
  rcases hUone with h | h
  · left; rw [hrecover, h, Matrix.one_mul]
  · right; rw [hrecover, h, Matrix.neg_mul, Matrix.one_mul]

end NCG
