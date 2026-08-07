/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact no-matter obstruction for the displayed six-state
  source (`thm:SM-six-state-no-matter`, Gran-Tensor manuscript)

* `six_state_no_matter`: the support-preserving coefficients
  (both cross blocks zero) contain the unit and are closed
  under sum, product, and adjoint; hence every word in
  support-preserving coefficients is support preserving — so
  every grading-changing Maslov/Walsh coefficient and every
  marked finite-Dirac block extracted from such a network is
  zero (`K_μ = 0`, `Q_μ = 0`, `D_F = 0`).

Rendering disclosed: norm limits, postselection, feedback and
chronological limits are the manuscript's operational reading
of the proved algebraic closure (the closed set is a unital
`*`-subalgebra and the listed operations stay inside it); the
displayed six-state source instantiates the
commuting-refinement hypothesis.
-/

open Matrix

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Support preservation relative to complementary hermitian
projections. -/
def SupportPreserving (PL PR M : Matrix n n ℂ) : Prop :=
  PL * M * PR = 0 ∧ PR * M * PL = 0

/-- `thm:SM-six-state-no-matter`. -/
theorem six_state_no_matter (PL PR : Matrix n n ℂ)
    (hsum : PL + PR = 1) (hLR : PL * PR = 0)
    (hRL : PR * PL = 0) (hLH : PLᴴ = PL) (hRH : PRᴴ = PR) :
    (SupportPreserving PL PR 1)
    ∧ (∀ M N, SupportPreserving PL PR M →
        SupportPreserving PL PR N →
        SupportPreserving PL PR (M + N))
    ∧ (∀ M N, SupportPreserving PL PR M →
        SupportPreserving PL PR N →
        SupportPreserving PL PR (M * N))
    ∧ (∀ M, SupportPreserving PL PR M →
        SupportPreserving PL PR Mᴴ)
    ∧ (∀ l : List (Matrix n n ℂ),
        (∀ M ∈ l, SupportPreserving PL PR M) →
        SupportPreserving PL PR l.prod) := by
  have hone : SupportPreserving PL PR 1 := by
    constructor
    · rw [Matrix.mul_one]
      exact hLR
    · rw [Matrix.mul_one]
      exact hRL
  have hadd : ∀ M N, SupportPreserving PL PR M →
      SupportPreserving PL PR N →
      SupportPreserving PL PR (M + N) := by
    rintro M N ⟨hM1, hM2⟩ ⟨hN1, hN2⟩
    constructor
    · rw [Matrix.mul_add, Matrix.add_mul, hM1, hN1, add_zero]
    · rw [Matrix.mul_add, Matrix.add_mul, hM2, hN2, add_zero]
  have hmul : ∀ M N, SupportPreserving PL PR M →
      SupportPreserving PL PR N →
      SupportPreserving PL PR (M * N) := by
    rintro M N ⟨hM1, hM2⟩ ⟨hN1, hN2⟩
    constructor
    · calc PL * (M * N) * PR
          = PL * M * (1 * (N * PR)) := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = PL * M * ((PL + PR) * (N * PR)) := by rw [hsum]
        _ = (PL * M) * (PL * N * PR)
            + (PL * M * PR) * (N * PR) := by
            rw [Matrix.add_mul, Matrix.mul_add]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hN1, hM1, Matrix.mul_zero, Matrix.zero_mul,
              add_zero]
    · calc PR * (M * N) * PL
          = PR * M * (1 * (N * PL)) := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = PR * M * ((PL + PR) * (N * PL)) := by rw [hsum]
        _ = (PR * M * PL) * (N * PL)
            + (PR * M) * (PR * N * PL) := by
            rw [Matrix.add_mul, Matrix.mul_add]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hN2, hM2, Matrix.mul_zero, Matrix.zero_mul,
              zero_add]
  have hstar : ∀ M, SupportPreserving PL PR M →
      SupportPreserving PL PR Mᴴ := by
    rintro M ⟨hM1, hM2⟩
    constructor
    · rw [show PL * Mᴴ * PR = (PR * M * PL)ᴴ from by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hLH, hRH]
        simp only [Matrix.mul_assoc]]
      rw [hM2, Matrix.conjTranspose_zero]
    · rw [show PR * Mᴴ * PL = (PL * M * PR)ᴴ from by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hLH, hRH]
        simp only [Matrix.mul_assoc]]
      rw [hM1, Matrix.conjTranspose_zero]
  refine ⟨hone, hadd, hmul, hstar, ?_⟩
  intro l
  induction l with
  | nil =>
      intro _
      simpa using hone
  | cons M l ih =>
      intro hmem
      rw [List.prod_cons]
      exact hmul M l.prod
        (hmem M List.mem_cons_self)
        (ih fun N hN => hmem N (List.mem_cons_of_mem M hN))

end NCG
