/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The forced timelike generator and its Clifford completion

**Proposition `prop:forced-timelike-generator`**: for a normalized
hyperbolic pair — Hermitian involutions `J` and `R` with `JR = −RJ` —
the composite `γ⁰ := J·R` is anti-Hermitian, Krein-odd, and squares to
`−1` (`NCG.forced_timelike_generator`): the Lorentzian temporal square
is forced by the pair and survives every compatible rephasing.

**Lemma `lem:temporal-clifford-completion`**: in the `2×2` normal form
`J = diag(1,−1)`, `R = offdiag(1,1)` the temporal generator is the
standard symplectic block `γ⁰ = [[0,1],[−1,0]]` with `(γ⁰)² = −1`
(`NCG.hyperbolic_pair_normal_form`); tensoring the `J`-block with the
Hermitian generators of the irreducible spatial Clifford module
completes it to the full `Cl_{1+d}(ℂ)` representation.  The choice of
the irreducible `Cl_d(ℂ)`-module and the Schur uniqueness of the
completion are the noted steps.
-/

namespace NCG

/-- **Proposition `prop:forced-timelike-generator`**: for a normalized
hyperbolic pair — `J`, `R` Hermitian involutions with `JR = −RJ` —
the temporal generator `γ⁰ = J·R` is anti-Hermitian
(`(γ⁰)* = −γ⁰`), Krein-odd (`Jγ⁰J = −γ⁰`), and has the forced
Lorentzian square `(γ⁰)² = −1`. -/
theorem forced_timelike_generator {A : Type*} [Ring A] [StarRing A]
    (J R : A) (hJstar : star J = J) (hJsq : J * J = 1)
    (hRstar : star R = R) (hRsq : R * R = 1)
    (hanti : J * R = -(R * J)) :
    star (J * R) = -(J * R)
      ∧ J * (J * R) * J = -(J * R)
      ∧ (J * R) * (J * R) = -1 := by
  have hRJ : R * J = -(J * R) := by
    rw [hanti, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [star_mul, hRstar, hJstar, hRJ]
  · have h1 : J * (J * R) * J = ((J * J) * R) * J := by
      rw [← mul_assoc]
    rw [h1, hJsq, one_mul, hRJ]
  · have h1 : (J * R) * (J * R) = (J * (R * J)) * R := by
      rw [← mul_assoc, mul_assoc J R J]
    have h2 : J * (J * R) * R = (J * J) * (R * R) := by
      rw [← mul_assoc J J R, mul_assoc (J * J) R R]
    rw [h1, hRJ, mul_neg, neg_mul, h2, hJsq, hRsq, one_mul]

/-- **Lemma `lem:temporal-clifford-completion` (normal-form core)**:
in the hyperbolic normal form `J = diag(1,−1)`, `R = offdiag(1,1)`,
the temporal generator is the symplectic block
`γ⁰ = J·R = [[0,1],[−1,0]]`, it squares to `−1`, and the pair
anticommutes. -/
theorem hyperbolic_pair_normal_form :
    ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]
        = !![0, 1; -1, 0])
      ∧ ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          * !![0, 1; -1, 0] = -1)
      ∧ ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]
          = -(!![0, 1; 1, 0] * !![1, 0; 0, -1])) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]

end NCG
