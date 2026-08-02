/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.AnchorClifford

/-!
# Finite Lorentzian Clifford theorem
  (`thm:clifford`, arithmetic manuscript)

For self-adjoint involutions `J, S` on the binary order plane with
`JS = -SJ`, the matrices `γ⁰ = J⊗I`, `γⁱ = (JS)⊗σᵢ` satisfy the
boxed relations `γᵘγᵛ + γᵛγᵘ = 2ηᵘᵛI₄`, `η = diag(1,-1,-1,-1)`
(`lorentz_clifford`, stated as the explicit signature list:
`(γ⁰)² = I`, `(γⁱ)² = -I`, all mixed anticommutators zero — the
entries of `2η`).  In the canonical binary-plane realization
`J = Z`, `S = X` the four generators generate all of `M₄(ℂ)`
(`lorentz_clifford_algebra_top`, by reduction to the flagship
generation theorem): this is the matrix realization
`Cl₁,₃(ℂ) ≅ M₄(ℂ)`, the Clifford presentation being certified by
the displayed relations (disclosed).
-/

open Matrix Kronecker

namespace NCG

noncomputable section

variable (J S : Matrix (Fin 2) (Fin 2) ℂ)

/-- `thm:clifford`, boxed relations `γᵘγᵛ + γᵛγᵘ = 2ηᵘᵛ` in
explicit signature form. -/
theorem lorentz_clifford (hJ2 : J * J = 1) (hS2 : S * S = 1)
    (hJS : J * S = -(S * J)) :
    ((J ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * (J ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
      ∧ ((J * S) ⊗ₖ clockX) * ((J * S) ⊗ₖ clockX) = -1
      ∧ ((J * S) ⊗ₖ clockY) * ((J * S) ⊗ₖ clockY) = -1
      ∧ ((J * S) ⊗ₖ clockZ) * ((J * S) ⊗ₖ clockZ) = -1)
    ∧ ((∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
        (J ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((J * S) ⊗ₖ σ)
          + ((J * S) ⊗ₖ σ) * (J ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
          = 0)
      ∧ ((J * S) ⊗ₖ clockX) * ((J * S) ⊗ₖ clockY)
          + ((J * S) ⊗ₖ clockY) * ((J * S) ⊗ₖ clockX) = 0
      ∧ ((J * S) ⊗ₖ clockY) * ((J * S) ⊗ₖ clockZ)
          + ((J * S) ⊗ₖ clockZ) * ((J * S) ⊗ₖ clockY) = 0
      ∧ ((J * S) ⊗ₖ clockZ) * ((J * S) ⊗ₖ clockX)
          + ((J * S) ⊗ₖ clockX) * ((J * S) ⊗ₖ clockZ) = 0) := by
  obtain ⟨_, ⟨hXX, hYY, hZZ⟩, hXY, hYZ, hZX⟩ := pauli_relations
  have hSJ : S * J = -(J * S) := by
    rw [hJS, neg_neg]
  have hJSJS : (J * S) * (J * S) = -1 := by
    rw [show (J * S) * (J * S) = J * (S * J) * S from by
        simp only [Matrix.mul_assoc], hSJ, Matrix.mul_neg,
      Matrix.neg_mul,
      show J * (J * S) * S = (J * J) * (S * S) from by
        simp only [Matrix.mul_assoc], hJ2, hS2, Matrix.one_mul]
  have hneg1 : ((-1 : Matrix (Fin 2) (Fin 2) ℂ))
      ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ)
        = ((-1 : ℂ)) • 1 from by simp, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
    simp
  have hsq : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ, σ * σ = 1 →
      ((J * S) ⊗ₖ σ) * ((J * S) ⊗ₖ σ) = -1 := by
    intro σ hσ
    rw [← Matrix.mul_kronecker_mul, hJSJS, hσ, hneg1]
  have hmixJ : J * (J * S) + (J * S) * J = 0 := by
    have h1 : J * (J * S) = S := by
      rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
    have h2 : (J * S) * J = -S := by
      rw [Matrix.mul_assoc, hSJ, Matrix.mul_neg, h1]
    rw [h1, h2, add_neg_cancel]
  have hpair : ∀ σ τ : Matrix (Fin 2) (Fin 2) ℂ,
      σ * τ + τ * σ = 0 →
      ((J * S) ⊗ₖ σ) * ((J * S) ⊗ₖ τ)
        + ((J * S) ⊗ₖ τ) * ((J * S) ⊗ₖ σ) = 0 := by
    intro σ τ hστ
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hJSJS, ← Matrix.kronecker_add, hστ, Matrix.kronecker_zero]
  refine ⟨⟨?_, hsq clockX hXX, hsq clockY hYY, hsq clockZ hZZ⟩,
    ?_, hpair clockX clockY hXY, hpair clockY clockZ hYZ,
    hpair clockZ clockX hZX⟩
  · rw [← Matrix.mul_kronecker_mul, hJ2, Matrix.one_mul,
      Matrix.one_kronecker_one]
  · intro σ
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, ← Matrix.add_kronecker,
      hmixJ, Matrix.zero_kronecker]

/-- `ZX = iY` on the binary order plane. -/
lemma clockZ_mul_X : clockZ * clockX = Complex.I • clockY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- `thm:clifford`, generation claim in the canonical realization
`J = Z`, `S = X`: the four Lorentzian generators generate all of
`M₄(ℂ)`. -/
theorem lorentz_clifford_algebra_top :
    Algebra.adjoin ℂ
      ({clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ),
        (clockZ * clockX) ⊗ₖ clockX,
        (clockZ * clockX) ⊗ₖ clockY,
        (clockZ * clockX) ⊗ₖ clockZ} :
        Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤ := by
  obtain ⟨_, ⟨hXX, hYY, hZZ⟩, hXY, hYZ, hZX⟩ := pauli_relations
  set N := Algebra.adjoin ℂ
    ({clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ),
      (clockZ * clockX) ⊗ₖ clockX,
      (clockZ * clockX) ⊗ₖ clockY,
      (clockZ * clockX) ⊗ₖ clockZ} :
      Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) with hN
  have hg0 : clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ N :=
    Algebra.subset_adjoin (by simp)
  have hg1 : (clockZ * clockX) ⊗ₖ clockX ∈ N :=
    Algebra.subset_adjoin (by simp)
  have hg2 : (clockZ * clockX) ⊗ₖ clockY ∈ N :=
    Algebra.subset_adjoin (by simp)
  have hg3 : (clockZ * clockX) ⊗ₖ clockZ ∈ N :=
    Algebra.subset_adjoin (by simp)
  have hZXZX : (clockZ * clockX) * (clockZ * clockX) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clockX, clockZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hneg : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ),
      ((-1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ (c • A)
        = (-c) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) := by
    intro A c
    rw [Matrix.kronecker_smul,
      show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = ((-1 : ℂ)) • 1 from
        by simp,
      Matrix.smul_kronecker, smul_smul,
      show c * (-1 : ℂ) = -c by ring]
  have h1Z : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ ∈ N := by
    have h12 : ((clockZ * clockX) ⊗ₖ clockX)
        * ((clockZ * clockX) ⊗ₖ clockY)
        = (-Complex.I)
          • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ) := by
      rw [← Matrix.mul_kronecker_mul, hZXZX, clockX_mul_Y, hneg]
    have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ
        = Complex.I • (((clockZ * clockX) ⊗ₖ clockX)
          * ((clockZ * clockX) ⊗ₖ clockY)) := by
      rw [h12, smul_smul, show Complex.I * -Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h]
    exact N.smul_mem (mul_mem hg1 hg2) _
  have h1X : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX ∈ N := by
    have h23 : ((clockZ * clockX) ⊗ₖ clockY)
        * ((clockZ * clockX) ⊗ₖ clockZ)
        = (-Complex.I)
          • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX) := by
      rw [← Matrix.mul_kronecker_mul, hZXZX, clockY_mul_Z, hneg]
    have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX
        = Complex.I • (((clockZ * clockX) ⊗ₖ clockY)
          * ((clockZ * clockX) ⊗ₖ clockZ)) := by
      rw [h23, smul_smul, show Complex.I * -Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h]
    exact N.smul_mem (mul_mem hg2 hg3) _
  have h1Y : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY ∈ N := by
    have h31 : ((clockZ * clockX) ⊗ₖ clockZ)
        * ((clockZ * clockX) ⊗ₖ clockX)
        = (-Complex.I)
          • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY) := by
      rw [← Matrix.mul_kronecker_mul, hZXZX, clockZ_mul_X, hneg]
    have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY
        = Complex.I • (((clockZ * clockX) ⊗ₖ clockZ)
          * ((clockZ * clockX) ⊗ₖ clockX)) := by
      rw [h31, smul_smul, show Complex.I * -Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h]
    exact N.smul_mem (mul_mem hg3 hg1) _
  have hZX1 : (clockZ * clockX)
      ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ N := by
    have h : ((clockZ * clockX) ⊗ₖ clockX)
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockX)
        = (clockZ * clockX)
          ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, hXX]
    rw [← h]
    exact mul_mem hg1 h1X
  have hX1 : clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ N := by
    have h : (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * ((clockZ * clockX) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = clockX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
        ← Matrix.mul_assoc, hZZ, Matrix.one_mul]
    rw [← h]
    exact mul_mem hg0 hZX1
  have hY1 : clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ N := by
    have h : (clockZ * clockX)
        ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = Complex.I
          • (clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [clockZ_mul_X, Matrix.smul_kronecker]
    have h2 : clockY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = (-Complex.I) • ((clockZ * clockX)
          ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h, smul_smul, show -Complex.I * Complex.I = 1 by
        simp [Complex.I_mul_I], one_smul]
    rw [h2]
    exact N.smul_mem hZX1 _
  rw [eq_top_iff, ← clifford_algebra_top]
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [gamma0]
    exact N.smul_mem hX1 _
  · rw [gamma1, show clockZ ⊗ₖ clockZ
        = (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
          * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockZ) from by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul]]
    exact mul_mem hg0 h1Z
  · rw [gamma2, show clockZ ⊗ₖ clockY
        = (clockZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
          * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ clockY) from by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul]]
    exact mul_mem hg0 h1Y
  · rw [gamma3]
    exact hY1

end

end NCG
