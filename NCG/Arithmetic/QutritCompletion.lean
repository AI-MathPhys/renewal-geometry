/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Nondegenerate qutrit completion
  (`thm:qutrit`, arithmetic manuscript)

The nine revision operators `R_{(a,b)} = UᵃVᵇ` of the
nondegenerate `𝔽₃²` projective datum are realized by the clock
and shift pair `U = diag(1, ω, ω²)`, `V = cyclic shift` for a
primitive cube root of unity (`ω³ = 1`, `1 + ω + ω² = 0` — the
nondegeneracy of the commutator bicharacter, disclosed):

* the Weyl commutation `UV = ω·VU` (`qutrit_weyl`);
* tracelessness of the nontrivial revision operators
  (`qutrit_traceless`, the manuscript's conjugation argument in
  concrete form);
* the boxed completion `C*(R_a) ≅ M₃(ℂ)`: the generated complex
  unital algebra is all of `M₃(ℂ)` (`qutrit_algebra_top`), whose
  minimal faithful irreducible carrier is the three-dimensional
  column space (prose; the C*-closure adds nothing in finite
  dimension, disclosed).
-/

open Matrix Finset

namespace NCG

noncomputable section

/-- The clock operator `U = diag(1, ω, ω²)`. -/
def qutritU (ω : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

/-- The cyclic shift operator `V`. -/
def qutritV : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- Weyl commutation `UV = ω·VU`. -/
theorem qutrit_weyl (ω : ℂ) (hω3 : ω ^ 3 = 1) :
    qutritU ω * qutritV = ω • (qutritV * qutritU ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritU, qutritV, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination -hω3
  · ring

/-- The nontrivial revision operators are traceless. -/
theorem qutrit_traceless (ω : ℂ) (hsum : 1 + ω + ω ^ 2 = 0) :
    (qutritU ω).trace = 0 ∧ qutritV.trace = 0 := by
  constructor
  · simp [qutritU, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    linear_combination hsum
  · simp [qutritV, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

set_option linter.unusedSimpArgs false in
/-- The zero diagonal unit as a clock combination. -/
lemma qutrit_E0 (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (hsum : 1 + ω + ω ^ 2 = 0) :
    (3⁻¹ : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ)
        + qutritU ω + qutritU ω * qutritU ω)
      = Matrix.single 0 0 1 := by
  have h4 : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul,
      pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritU, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply]
  · norm_num
  · linear_combination hsum
  · linear_combination hsum + ω * hω3

/-- Every matrix unit is a word in the clock combination and the
shift. -/
lemma qutrit_single (ω : ℂ) (_hω3 : ω ^ 3 = 1)
    (_hsum : 1 + ω + ω ^ 2 = 0) (j k : Fin 3) :
    Matrix.single j k (1 : ℂ)
      = qutritV ^ (j : ℕ) * Matrix.single 0 0 1
          * qutritV ^ ((3 - (k : ℕ)) % 3) := by
  fin_cases j <;> fin_cases k <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [qutritV, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_three, pow_succ,
          Matrix.single_apply]

/-- `thm:qutrit`, boxed completion: the revision operators
generate all of `M₃(ℂ)`. -/
theorem qutrit_algebra_top (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (hsum : 1 + ω + ω ^ 2 = 0) :
    Algebra.adjoin ℂ
      ({qutritU ω, qutritV} :
        Set (Matrix (Fin 3) (Fin 3) ℂ)) = ⊤ := by
  set S := Algebra.adjoin ℂ
    ({qutritU ω, qutritV} : Set (Matrix (Fin 3) (Fin 3) ℂ))
    with hS
  have hU : qutritU ω ∈ S := Algebra.subset_adjoin (by simp)
  have hV : qutritV ∈ S := Algebra.subset_adjoin (by simp)
  have hE0 : Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) ∈ S := by
    rw [← qutrit_E0 ω hω3 hsum]
    exact S.smul_mem
      (add_mem (add_mem (one_mem S) hU) (mul_mem hU hU)) _
  have hunit : ∀ j k : Fin 3,
      Matrix.single j k (1 : ℂ) ∈ S := by
    intro j k
    rw [qutrit_single ω hω3 hsum j k]
    exact mul_mem (mul_mem (pow_mem hV _) hE0) (pow_mem hV _)
  rw [eq_top_iff]
  intro M _
  have hM : M = ∑ j : Fin 3, ∑ k : Fin 3,
      M j k • Matrix.single j k (1 : ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Fin.sum_univ_three]
  rw [hM]
  exact sum_mem fun j _ => sum_mem fun k _ =>
    S.smul_mem (hunit j k) _

end

end NCG
