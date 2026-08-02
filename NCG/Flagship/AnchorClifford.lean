/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# One-anchor depth-two external Clifford construction
  (`thm:anchor-external-clifford-master`, flagship manuscript)

Two locally addressable clock copies `A, B` carry the boxed
generators `γ⁰ = -iX_A⊗I`, `γ¹ = Z_A⊗Z_B`, `γ² = Z_A⊗Y_B`,
`γ³ = Y_A⊗I` on `ℂ²⊗ℂ² ≅ ℂ⁴`:

* `(γ⁰)² = -I`, `(γⁱ)² = I`, and all six mixed anticommutators
  vanish — each mixed pair contains exactly one local Pauli
  anticommutation (`anchor_external_clifford`);
* the boxed generation claim: the four generators generate all of
  `M₄(ℂ)` as a complex unital algebra (`clifford_algebra_top`;
  this is the matrix realization `Cl₁,₃(ℂ) ≅ M₄(ℂ)`, with the
  Clifford presentation certified by the displayed relations —
  disclosed);
* the parity-effect identity
  `P^A_+⊗P^D_+ + P^A_-⊗P^D_- = ½(I + A⊗D)` for the local-parity
  implementation of `γ¹, γ²` effects (`parity_effect`);
* the boxed direction second-moment identity: choosing the three
  axis procedures with probability `⅓` gives
  `Σ_{i,s} p_{i,s}(ρ)(se_i)(se_i)ᵀ = ⅓I₃` for every unit-trace
  state (`gamma_direction_moment`).

Completion-equivalence of the parity branches after the external
replacement/twirl is prose.
-/

open Matrix Kronecker

namespace NCG

noncomputable section

/-- `γ⁰ = -iX_A ⊗ I_B`. -/
def gamma0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (-Complex.I) • (clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- `γ¹ = Z_A ⊗ Z_B`. -/
def gamma1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  clockZ ⊗ₖ clockZ

/-- `γ² = Z_A ⊗ Y_B`. -/
def gamma2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  clockZ ⊗ₖ clockY

/-- `γ³ = Y_A ⊗ I_B`. -/
def gamma3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- `(γ⁰)² = -I`. -/
lemma gamma0_sq : gamma0 * gamma0 = -1 := by
  obtain ⟨_, ⟨hXX, _, _⟩, _⟩ := pauli_relations
  have h : (clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      * (clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hXX, one_mul,
      Matrix.one_kronecker_one]
  rw [gamma0, smul_mul_assoc, mul_smul_comm, smul_smul, h,
    show (-Complex.I) * (-Complex.I) = (-1 : ℂ) by
      simp [Complex.I_mul_I]]
  simp

/-- `(γ¹)² = I`. -/
lemma gamma1_sq : gamma1 * gamma1 = 1 := by
  obtain ⟨_, ⟨_, _, hZZ⟩, _⟩ := pauli_relations
  rw [gamma1, ← Matrix.mul_kronecker_mul, hZZ,
    Matrix.one_kronecker_one]

/-- `(γ²)² = I`. -/
lemma gamma2_sq : gamma2 * gamma2 = 1 := by
  obtain ⟨_, ⟨_, hYY, hZZ⟩, _⟩ := pauli_relations
  rw [gamma2, ← Matrix.mul_kronecker_mul, hZZ, hYY,
    Matrix.one_kronecker_one]

/-- `(γ³)² = I`. -/
lemma gamma3_sq : gamma3 * gamma3 = 1 := by
  obtain ⟨_, ⟨_, hYY, _⟩, _⟩ := pauli_relations
  rw [gamma3, ← Matrix.mul_kronecker_mul, hYY, one_mul,
    Matrix.one_kronecker_one]

/-- `γ⁰γ¹ + γ¹γ⁰ = 0`. -/
lemma gamma_anti_01 : gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  obtain ⟨_, _, _, _, hZX⟩ := pauli_relations
  rw [gamma0, gamma1, smul_mul_assoc, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, ← smul_add, ← Matrix.add_kronecker,
    show clockX * clockZ + clockZ * clockX = 0 by
      rw [add_comm]; exact hZX,
    Matrix.zero_kronecker, smul_zero]

/-- `γ⁰γ² + γ²γ⁰ = 0`. -/
lemma gamma_anti_02 : gamma0 * gamma2 + gamma2 * gamma0 = 0 := by
  obtain ⟨_, _, _, _, hZX⟩ := pauli_relations
  rw [gamma0, gamma2, smul_mul_assoc, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, ← smul_add, ← Matrix.add_kronecker,
    show clockX * clockZ + clockZ * clockX = 0 by
      rw [add_comm]; exact hZX,
    Matrix.zero_kronecker, smul_zero]

/-- `γ⁰γ³ + γ³γ⁰ = 0`. -/
lemma gamma_anti_03 : gamma0 * gamma3 + gamma3 * gamma0 = 0 := by
  obtain ⟨_, _, hXY, _, _⟩ := pauli_relations
  rw [gamma0, gamma3, smul_mul_assoc, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, ← smul_add, ← Matrix.add_kronecker, hXY,
    Matrix.zero_kronecker, smul_zero]

/-- `γ¹γ² + γ²γ¹ = 0`. -/
lemma gamma_anti_12 : gamma1 * gamma2 + gamma2 * gamma1 = 0 := by
  obtain ⟨_, _, _, hYZ, _⟩ := pauli_relations
  rw [gamma1, gamma2, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.kronecker_add,
    show clockZ * clockY + clockY * clockZ = 0 by
      rw [add_comm]; exact hYZ,
    Matrix.kronecker_zero]

/-- `γ¹γ³ + γ³γ¹ = 0`. -/
lemma gamma_anti_13 : gamma1 * gamma3 + gamma3 * gamma1 = 0 := by
  obtain ⟨_, _, _, hYZ, _⟩ := pauli_relations
  rw [gamma1, gamma3, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    ← Matrix.add_kronecker,
    show clockZ * clockY + clockY * clockZ = 0 by
      rw [add_comm]; exact hYZ,
    Matrix.zero_kronecker]

/-- `γ²γ³ + γ³γ² = 0`. -/
lemma gamma_anti_23 : gamma2 * gamma3 + gamma3 * gamma2 = 0 := by
  obtain ⟨_, _, _, hYZ, _⟩ := pauli_relations
  rw [gamma2, gamma3, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    ← Matrix.add_kronecker,
    show clockZ * clockY + clockY * clockZ = 0 by
      rw [add_comm]; exact hYZ,
    Matrix.zero_kronecker]

/-- `XY = iZ` on a single clock copy. -/
lemma clockX_mul_Y : clockX * clockY = Complex.I • clockZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- `YZ = iX` on a single clock copy. -/
lemma clockY_mul_Z : clockY * clockZ = Complex.I • clockX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- `P₀ = (I + Z)/2`. -/
lemma clockP0_eq : clockP0 = (2⁻¹ : ℂ) • (1 + clockZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [clockP0, clockZ]

/-- Kronecker product of matrix units is a matrix unit. -/
lemma single_kron (a b c d : Fin 2) :
    (Matrix.single a b (1 : ℂ)) ⊗ₖ (Matrix.single c d (1 : ℂ))
      = Matrix.single (a, c) (b, d) (1 : ℂ) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.single_apply,
    Prod.mk.injEq]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;>
    by_cases h3 : c = k <;> by_cases h4 : d = l <;>
    simp [h1, h2, h3, h4]

/-- Boxed generation claim: the four `γ`-generators generate all
of `M₄(ℂ)` as a complex unital algebra. -/
theorem clifford_algebra_top :
    Algebra.adjoin ℂ ({gamma0, gamma1, gamma2, gamma3} :
      Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤ := by
  obtain ⟨_, ⟨hXX, hYY, hZZ⟩, hXY, hYZ, hZX⟩ := pauli_relations
  set S := Algebra.adjoin ℂ ({gamma0, gamma1, gamma2, gamma3} :
    Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) with hS
  rw [eq_top_iff]
  intro M _
  have hg0 : gamma0 ∈ S := Algebra.subset_adjoin (by simp)
  have hg1 : gamma1 ∈ S := Algebra.subset_adjoin (by simp)
  have hg2 : gamma2 ∈ S := Algebra.subset_adjoin (by simp)
  have hg3 : gamma3 ∈ S := Algebra.subset_adjoin (by simp)
  have hX1 : clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
    have h : clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = Complex.I • gamma0 := by
      rw [gamma0, smul_smul, show Complex.I * -Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h]
    exact S.smul_mem hg0 _
  have hY1 : clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := hg3
  have hZ1 : clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
    have h1 : (clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * (clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = Complex.I • (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, clockX_mul_Y, one_mul,
        Matrix.smul_kronecker]
    have h2 : clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = (-Complex.I) • ((clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
          * (clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
      rw [h1, smul_smul, show -Complex.I * Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h2]
    exact S.smul_mem (mul_mem hX1 hY1) _
  have h1Z : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ ∈ S := by
    have h : (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * gamma1
        = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ := by
      rw [gamma1, ← Matrix.mul_kronecker_mul, hZZ, one_mul]
    rw [← h]
    exact mul_mem hZ1 hg1
  have h1Y : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY ∈ S := by
    have h : (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * gamma2
        = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY := by
      rw [gamma2, ← Matrix.mul_kronecker_mul, hZZ, one_mul]
    rw [← h]
    exact mul_mem hZ1 hg2
  have h1X : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX ∈ S := by
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY)
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ)
        = Complex.I • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX) := by
      rw [← Matrix.mul_kronecker_mul, clockY_mul_Z, one_mul,
        Matrix.kronecker_smul]
    have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX
        = (-Complex.I) • (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY)
          * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ)) := by
      rw [h1, smul_smul, show -Complex.I * Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h2]
    exact S.smul_mem (mul_mem h1Y h1Z) _
  have hP0A : clockP0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
    rw [clockP0_eq, Matrix.smul_kronecker, Matrix.add_kronecker,
      Matrix.one_kronecker_one]
    exact S.smul_mem (add_mem (one_mem S) hZ1) _
  have hP0B : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockP0 ∈ S := by
    rw [clockP0_eq, Matrix.kronecker_smul, Matrix.kronecker_add,
      Matrix.one_kronecker_one]
    exact S.smul_mem (add_mem (one_mem S) h1Z) _
  have h00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = clockP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [clockP0]
  have h01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = clockP0 * clockX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = clockX * clockP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = clockX * clockP0 * clockX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockP0, clockX, Matrix.mul_apply, Fin.sum_univ_two]
  have hsingleA : ∀ a b : Fin 2,
      (Matrix.single a b (1 : ℂ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ∈ S := by
    have hsplit : ∀ P Q : Matrix (Fin 2) (Fin 2) ℂ,
        (P * Q) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
          = (P ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
            * (Q ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      intro P Q
      rw [← Matrix.mul_kronecker_mul, one_mul]
    have m00 : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ))
        ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [h00]; exact hP0A
    have m01 : (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))
        ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [h01, hsplit]; exact mul_mem hP0A hX1
    have m10 : (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ))
        ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [h10, hsplit]; exact mul_mem hX1 hP0A
    have m11 : (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ))
        ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [h11, hsplit, hsplit]
      exact mul_mem (mul_mem hX1 hP0A) hX1
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
        | exact m00
        | exact m01
        | exact m10
        | exact m11
  have hsingleB : ∀ c d : Fin 2,
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Matrix.single c d (1 : ℂ))
        ∈ S := by
    have hsplit : ∀ P Q : Matrix (Fin 2) (Fin 2) ℂ,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (P * Q)
          = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P)
            * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q) := by
      intro P Q
      rw [← Matrix.mul_kronecker_mul, one_mul]
    have m00 : (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ⊗ₖ (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) ∈ S := by
      rw [h00]; exact hP0B
    have m01 : (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ⊗ₖ (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) ∈ S := by
      rw [h01, hsplit]; exact mul_mem hP0B h1X
    have m10 : (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ⊗ₖ (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)) ∈ S := by
      rw [h10, hsplit]; exact mul_mem h1X hP0B
    have m11 : (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ⊗ₖ (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) ∈ S := by
      rw [h11, hsplit, hsplit]
      exact mul_mem (mul_mem h1X hP0B) h1X
    intro c d
    fin_cases c <;> fin_cases d <;>
      first
        | exact m00
        | exact m01
        | exact m10
        | exact m11
  have hunit : ∀ p q : Fin 2 × Fin 2,
      Matrix.single p q (1 : ℂ) ∈ S := by
    rintro ⟨a, c⟩ ⟨b, d⟩
    have hprod : ((Matrix.single a b (1 : ℂ))
          ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ)
          ⊗ₖ (Matrix.single c d (1 : ℂ)))
        = (Matrix.single a b (1 : ℂ)) ⊗ₖ (Matrix.single c d (1 : ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    rw [← single_kron, ← hprod]
    exact mul_mem (hsingleA a b) (hsingleB c d)
  have hM : M = ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
      M p q • Matrix.single p q (1 : ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [hM]
  exact sum_mem fun p _ => sum_mem fun q _ =>
    S.smul_mem (hunit p q) _

/-- `thm:anchor-external-clifford-master`, boxed Clifford
relations bundle. -/
theorem anchor_external_clifford :
    (gamma0 * gamma0 = -1 ∧ gamma1 * gamma1 = 1
      ∧ gamma2 * gamma2 = 1 ∧ gamma3 * gamma3 = 1)
    ∧ (gamma0 * gamma1 + gamma1 * gamma0 = 0
      ∧ gamma0 * gamma2 + gamma2 * gamma0 = 0
      ∧ gamma0 * gamma3 + gamma3 * gamma0 = 0
      ∧ gamma1 * gamma2 + gamma2 * gamma1 = 0
      ∧ gamma1 * gamma3 + gamma3 * gamma1 = 0
      ∧ gamma2 * gamma3 + gamma3 * gamma2 = 0)
    ∧ Algebra.adjoin ℂ ({gamma0, gamma1, gamma2, gamma3} :
        Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤ :=
  ⟨⟨gamma0_sq, gamma1_sq, gamma2_sq, gamma3_sq⟩,
    ⟨gamma_anti_01, gamma_anti_02, gamma_anti_03,
      gamma_anti_12, gamma_anti_13, gamma_anti_23⟩,
    clifford_algebra_top⟩

/-- Parity-effect identity for the local implementation of the
tensor effects: `P^A_+⊗P^D_+ + P^A_-⊗P^D_- = ½(I + A⊗D)`
(the minus effects written as `(I + (-1)·A)/2`). -/
lemma parity_effect (A D : Matrix (Fin 2) (Fin 2) ℂ) :
    ((2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + A))
        ⊗ₖ ((2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + D))
      + ((2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (-1 : ℂ) • A))
        ⊗ₖ ((2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (-1 : ℂ) • D))
      = (2⁻¹ : ℂ) • ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
          + A ⊗ₖ D) := by
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.add_kronecker, Matrix.kronecker_add,
    Matrix.one_kronecker_one, smul_smul]
  module

/-! ### The boxed direction second-moment identity -/

set_option linter.unusedSimpArgs false in
/-- The three diagonal dyads `e_ie_iᵀ` sum to `I₃`. -/
lemma sum_single_diag_three :
    ∑ i : Fin 3, Matrix.single i i (1 : ℂ)
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

/-- The three direction generators. -/
def gammaDir : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![gamma1, gamma2, gamma3]

/-- The sign effect of axis `i`. -/
def gammaEffect (i : Fin 3) (s : ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + s • gammaDir i)

/-- The two sign effects of one axis sum to the identity. -/
lemma gammaEffect_complete (i : Fin 3) :
    gammaEffect i 1 + gammaEffect i (-1) = 1 := by
  rw [gammaEffect, gammaEffect]
  module

/-- `thm:anchor-external-clifford-master`, boxed direction
moment: choosing the three axis procedures with probability `⅓`
gives `Σ_{i,s} p_{i,s}(ρ)(se_i)(se_i)ᵀ = ⅓I₃` on every unit-trace
state. -/
theorem gamma_direction_moment
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.trace = 1) :
    ∑ i : Fin 3,
      ((3⁻¹ : ℂ) * (ρ * gammaEffect i 1).trace
        + (3⁻¹ : ℂ) * (ρ * gammaEffect i (-1)).trace)
        • Matrix.single i i (1 : ℂ)
      = (3⁻¹ : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hcoef : ∀ i : Fin 3,
      (3⁻¹ : ℂ) * (ρ * gammaEffect i 1).trace
        + (3⁻¹ : ℂ) * (ρ * gammaEffect i (-1)).trace = 3⁻¹ := by
    intro i
    rw [← mul_add, ← Matrix.trace_add, ← Matrix.mul_add,
      gammaEffect_complete, Matrix.mul_one, hρ, mul_one]
  rw [Finset.sum_congr rfl fun i _ => by rw [hcoef i],
    ← Finset.smul_sum, sum_single_diag_three]

end

end NCG
