/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactGradingAutomorphismCommutant

/-!
# Exact grading automorphism and residual commutant package

This assembles the norm identity, vanishing equivalences, Howe-central
transition, central sign decomposition, and factorial sign ambiguity of
`thm:SMST-grading-commutant` into one theorem.
-/

open Matrix

namespace NCG

/-- The complete finite grading-commutant theorem.  Minimality of the central
projections and the finite Howe identification are explicit hypotheses, as in
the manuscript. -/
theorem grading_automorphism_residual_commutant_exact
    {n ι a : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [Fintype a]
    (c : ι → Matrix n n ℂ)
    (action multiplicity : Subalgebra ℂ (Matrix n n ℂ))
    (Z₁ Z₀ : Matrix n n ℂ) (z : a → Matrix n n ℂ)
    (hZ₁H : Z₁ᴴ = Z₁) (hZ₀H : Z₀ᴴ = Z₀)
    (hZ₁2 : Z₁ * Z₁ = 1) (hZ₀2 : Z₀ * Z₀ = 1)
    (hHowe : ∀ T, T ∈ multiplicity ↔ ∀ X ∈ action, Commute T X)
    (htransition : ∀ X ∈ action, Commute (Z₁ * Z₀) X)
    (hZ₁mult : ∀ Y ∈ multiplicity, Commute Z₁ Y)
    (hZ₀mult : ∀ Y ∈ multiplicity, Commute Z₀ Y)
    (hzsum : ∑ i, z i = 1)
    (hzidem : ∀ i, z i * z i = z i)
    (hznonzero : ∀ i, z i ≠ 0)
    (hzmem : ∀ i, z i ∈ multiplicity)
    (hminimal : ∀ i, ∃ lam : ℂ, (Z₁ * Z₀) * z i = lam • z i) :
    (∑ j, ((gradingActionDefect Z₁ Z₀ (c j))ᴴ *
        gradingActionDefect Z₁ Z₀ (c j)).trace)
      = ∑ j, (((c j * (Z₁ * Z₀) - (Z₁ * Z₀) * c j)ᴴ) *
          (c j * (Z₁ * Z₀) - (Z₁ * Z₀) * c j)).trace
    ∧ (∑ j, ((gradingActionDefect Z₁ Z₀ (c j))ᴴ *
        gradingActionDefect Z₁ Z₀ (c j)).trace)
      = 4 * ∑ j, ((gradingSplitDefect Z₁ Z₀ (c j))ᴴ *
          gradingSplitDefect Z₁ Z₀ (c j)).trace
    ∧ (((∑ j, ((gradingActionDefect Z₁ Z₀ (c j))ᴴ *
          gradingActionDefect Z₁ Z₀ (c j)).trace = 0)
        ↔ ∀ j, Commute (Z₁ * Z₀) (c j))
      ∧ (∀ X ∈ Algebra.adjoin ℂ (Set.range c),
          Commute (Z₁ * Z₀) X ↔ gradingActionDefect Z₁ Z₀ X = 0)
      ∧ (∀ X, gradingActionDefect Z₁ Z₀ X = 0 ↔
          gradingSplitDefect Z₁ Z₀ X = 0))
    ∧ ((Z₁ * Z₀ ∈ multiplicity)
      ∧ (∀ Y ∈ multiplicity, Commute (Z₁ * Z₀) Y)
      ∧ (Z₁ * Z₀)ᴴ = Z₁ * Z₀
      ∧ (Z₁ * Z₀) * (Z₁ * Z₀) = 1)
    ∧ (∃ ε : a → ℂ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        Z₁ * Z₀ = ∑ i, ε i • z i)
    ∧ ((Z₁ * Z₀ = 1 ∨ Z₁ * Z₀ = -1) →
        Z₁ = Z₀ ∨ Z₁ = -Z₀) := by
  have hcentral := howeTransition_isCentralSelfAdjointInvolution
    action multiplicity Z₁ Z₀ hZ₁H hZ₀H hZ₁2 hZ₀2 hHowe
    htransition hZ₁mult hZ₀mult
  have hsign := centralInvolution_signDecomposition (Z₁ * Z₀) z
    hcentral.2.2.2 hzsum hzidem
    (fun i => hcentral.2.1 (z i) (hzmem i)) hznonzero hminimal
  refine ⟨?_, ?_,
    gradingResidualCommutantEquivalences c Z₁ Z₀
      hZ₁H hZ₀H hZ₁2 hZ₀2,
    hcentral, hsign, ?_⟩
  · apply Finset.sum_congr rfl
    intro j _
    exact (gradingActionDefect_hilbertSchmidt_eq_commutator
      Z₁ Z₀ (c j) hZ₁H hZ₀H hZ₁2 hZ₀2).symm
  · simp_rw [gradingActionDefect_eq_four_splitDefect]
    rw [Finset.mul_sum]
  · intro hfactor
    exact factorGradingImplementers_differBySign
      Z₁ Z₀ (Z₁ * Z₀) rfl hfactor hZ₀2

end NCG
