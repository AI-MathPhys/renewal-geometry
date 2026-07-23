/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Concrete Hermitian Clifford generators on `ℂ² ⊗ ℂ²`

Concrete content for `thm:common-origin-clifford`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): the internal space `S = ℂ⁴` (realized as
`ℂ² ⊗ ℂ²`) **does** carry Hermitian Clifford generators
`Γ₀, Γ₁, Γ₂, Γ₃` with `Γ_μ Γ_ν + Γ_ν Γ_μ = 2δ_{μν} 1`, via
Pauli–Kronecker products

`Γ₀ = σ₁⊗1, Γ₁ = σ₂⊗1, Γ₂ = σ₃⊗σ₁, Γ₃ = σ₃⊗σ₂`.

We prove:

* the Pauli algebra on `ℂ²` (squares, anticommutation, Hermiticity,
  `σ₁σ₂ = iσ₃`, and the trivial commutant `pauli_commutant`);
* `gamma_sq`, `gamma_anticomm`, `gamma_clifford` — the Clifford
  relations;
* `gamma_herm`, `gamma_unitary` — each `Γ_μ` is a Hermitian unitary
  (the hypotheses of the common-origin internal maps `Ad(Γ_a)`),
  and `gammaJR_skew` — the sheet-rotated implementers `Γ₀Γ_a` are
  skew-Hermitian (the other branch of `adMap_hs_selfadjoint`);
* `gamma_commutant` — **irreducibility**: a matrix commuting with
  all four generators is scalar (first-factor slices are Pauli
  commutants, then the residual second factor is again a Pauli
  commutant).

The remaining abstract identification `ℂ_σ[F₂⁴] ≅ Cl₄(ℂ) ≅ M₄(ℂ)`
(finite Stone–von Neumann uniqueness) stays unformalized; these
lemmas realize its concrete existence half and the irreducibility of
the realization.
-/

namespace NCG.CommonOrigin

open Matrix Kronecker

/-- The first Pauli matrix. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The second Pauli matrix. -/
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- The third Pauli matrix. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli1_sq : pauli1 * pauli1 = 1 := by
  rw [pauli1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli2_sq : pauli2 * pauli2 = 1 := by
  rw [pauli2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

theorem pauli3_sq : pauli3 * pauli3 = 1 := by
  rw [pauli3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli12_anticomm : pauli1 * pauli2 = -(pauli2 * pauli1) := by
  rw [pauli1, pauli2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem pauli13_anticomm : pauli1 * pauli3 = -(pauli3 * pauli1) := by
  rw [pauli1, pauli3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem pauli23_anticomm : pauli2 * pauli3 = -(pauli3 * pauli2) := by
  rw [pauli2, pauli3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem pauli21_anticomm : pauli2 * pauli1 = -(pauli1 * pauli2) := by
  rw [pauli12_anticomm, neg_neg]

theorem pauli31_anticomm : pauli3 * pauli1 = -(pauli1 * pauli3) := by
  rw [pauli13_anticomm, neg_neg]

theorem pauli32_anticomm : pauli3 * pauli2 = -(pauli2 * pauli3) := by
  rw [pauli23_anticomm, neg_neg]

theorem pauli1_herm : pauli1ᴴ = pauli1 := by
  rw [pauli1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

theorem pauli2_herm : pauli2ᴴ = pauli2 := by
  rw [pauli2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

theorem pauli3_herm : pauli3ᴴ = pauli3 := by
  rw [pauli3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

theorem pauli12_eq_I_pauli3 :
    pauli1 * pauli2 = Complex.I • pauli3 := by
  rw [pauli1, pauli2, pauli3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- The Pauli commutant is trivial: a `2 × 2` matrix commuting with
`σ₁` and `σ₂` is scalar. -/
theorem pauli_commutant (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (h1 : Y * pauli1 = pauli1 * Y) (h2 : Y * pauli2 = pauli2 * Y) :
    Y = Y 0 0 • 1 := by
  -- Y commutes with σ₃ = -i σ₁σ₂
  have h3 : Y * pauli3 = pauli3 * Y := by
    have h4 : Y * (pauli1 * pauli2) = (pauli1 * pauli2) * Y := by
      rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2,
        ← Matrix.mul_assoc]
    rw [pauli12_eq_I_pauli3, Matrix.mul_smul, Matrix.smul_mul]
      at h4
    exact smul_right_injective
      (Matrix (Fin 2) (Fin 2) ℂ) Complex.I_ne_zero h4
  -- σ₃ diagonal with distinct eigenvalues: off-diagonals vanish
  have e01 : Y 0 1 = 0 := by
    have h5 := congrFun (congrFun h3 0) 1
    simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two] at h5
    linear_combination (-1 / 2 : ℂ) * h5
  have e10 : Y 1 0 = 0 := by
    have h5 := congrFun (congrFun h3 1) 0
    simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two] at h5
    linear_combination (1 / 2 : ℂ) * h5
  -- σ₁ swaps the diagonal entries
  have e11 : Y 1 1 = Y 0 0 := by
    have h5 := congrFun (congrFun h1 0) 1
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two] at h5
    linear_combination -h5
  ext i j
  fin_cases i <;> fin_cases j
  · change Y 0 0 = (Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
  · change Y 0 1 = (Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 1
    rw [Matrix.smul_apply,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      smul_eq_mul, mul_zero]
    exact e01
  · change Y 1 0 = (Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
    rw [Matrix.smul_apply,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      smul_eq_mul, mul_zero]
    exact e10
  · change Y 1 1 = (Y 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 1
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    exact e11

/-- The concrete Clifford generators
`Γ₀ = σ₁⊗1, Γ₁ = σ₂⊗1, Γ₂ = σ₃⊗σ₁, Γ₃ = σ₃⊗σ₂`. -/
def gamma : Fin 4 →
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![pauli1 ⊗ₖ 1, pauli2 ⊗ₖ 1, pauli3 ⊗ₖ pauli1, pauli3 ⊗ₖ pauli2]

theorem neg_kron (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.kroneckerMap_apply, Matrix.neg_apply,
    Matrix.neg_apply, Matrix.kroneckerMap_apply, neg_mul]

theorem kron_neg (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.kroneckerMap_apply, Matrix.neg_apply,
    Matrix.neg_apply, Matrix.kroneckerMap_apply, mul_neg]

/-- **The Clifford squares**: `Γ_μ² = 1`. -/
theorem gamma_sq (μ : Fin 4) : gamma μ * gamma μ = 1 := by
  fin_cases μ
  · change pauli1 ⊗ₖ 1 * (pauli1 ⊗ₖ 1) = 1
    rw [← Matrix.mul_kronecker_mul, pauli1_sq, Matrix.one_mul,
      Matrix.one_kronecker_one]
  · change pauli2 ⊗ₖ 1 * (pauli2 ⊗ₖ 1) = 1
    rw [← Matrix.mul_kronecker_mul, pauli2_sq, Matrix.one_mul,
      Matrix.one_kronecker_one]
  · change pauli3 ⊗ₖ pauli1 * (pauli3 ⊗ₖ pauli1) = 1
    rw [← Matrix.mul_kronecker_mul, pauli3_sq, pauli1_sq,
      Matrix.one_kronecker_one]
  · change pauli3 ⊗ₖ pauli2 * (pauli3 ⊗ₖ pauli2) = 1
    rw [← Matrix.mul_kronecker_mul, pauli3_sq, pauli2_sq,
      Matrix.one_kronecker_one]

/-- **The Clifford anticommutation** for distinct indices. -/
theorem gamma_anticomm (μ ν : Fin 4) (h : μ ≠ ν) :
    gamma μ * gamma ν = -(gamma ν * gamma μ) := by
  fin_cases μ <;> fin_cases ν
  · exact absurd rfl h
  · change pauli1 ⊗ₖ 1 * (pauli2 ⊗ₖ 1)
      = -(pauli2 ⊗ₖ 1 * (pauli1 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli12_anticomm, neg_kron]
  · change pauli1 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli1)
      = -(pauli3 ⊗ₖ pauli1 * (pauli1 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli13_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli1 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli2)
      = -(pauli3 ⊗ₖ pauli2 * (pauli1 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli13_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli2 ⊗ₖ 1 * (pauli1 ⊗ₖ 1)
      = -(pauli1 ⊗ₖ 1 * (pauli2 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli21_anticomm, neg_kron]
  · exact absurd rfl h
  · change pauli2 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli1)
      = -(pauli3 ⊗ₖ pauli1 * (pauli2 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli23_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli2 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli2)
      = -(pauli3 ⊗ₖ pauli2 * (pauli2 ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli23_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli3 ⊗ₖ pauli1 * (pauli1 ⊗ₖ 1)
      = -(pauli1 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli31_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli3 ⊗ₖ pauli1 * (pauli2 ⊗ₖ 1)
      = -(pauli2 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli32_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · exact absurd rfl h
  · change pauli3 ⊗ₖ pauli1 * (pauli3 ⊗ₖ pauli2)
      = -(pauli3 ⊗ₖ pauli2 * (pauli3 ⊗ₖ pauli1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli12_anticomm, kron_neg]
  · change pauli3 ⊗ₖ pauli2 * (pauli1 ⊗ₖ 1)
      = -(pauli1 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli2))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli31_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli3 ⊗ₖ pauli2 * (pauli2 ⊗ₖ 1)
      = -(pauli2 ⊗ₖ 1 * (pauli3 ⊗ₖ pauli2))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli32_anticomm, Matrix.one_mul, Matrix.mul_one,
      neg_kron]
  · change pauli3 ⊗ₖ pauli2 * (pauli3 ⊗ₖ pauli1)
      = -(pauli3 ⊗ₖ pauli1 * (pauli3 ⊗ₖ pauli2))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      pauli21_anticomm, kron_neg]
  · exact absurd rfl h

/-- **The Clifford relations**
`Γ_μ Γ_ν + Γ_ν Γ_μ = 2δ_{μν} 1` (`thm:common-origin-clifford`,
existence of the Hermitian Clifford generators). -/
theorem gamma_clifford (μ ν : Fin 4) :
    gamma μ * gamma ν + gamma ν * gamma μ
      = (if μ = ν then (2 : ℂ) else 0) • 1 := by
  by_cases h : μ = ν
  · rw [h, if_pos rfl, gamma_sq]
    ext p q
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [if_neg h, gamma_anticomm μ ν h, zero_smul]
    exact neg_add_cancel _

/-- Conjugate transpose distributes over the Kronecker product. -/
theorem kron_conjTranspose (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_apply]
  exact star_mul' _ _

/-- Each generator is Hermitian. -/
theorem gamma_herm (μ : Fin 4) : (gamma μ)ᴴ = gamma μ := by
  fin_cases μ
  · change (pauli1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
      = pauli1 ⊗ₖ 1
    rw [kron_conjTranspose, pauli1_herm, Matrix.conjTranspose_one]
  · change (pauli2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
      = pauli2 ⊗ₖ 1
    rw [kron_conjTranspose, pauli2_herm, Matrix.conjTranspose_one]
  · change (pauli3 ⊗ₖ pauli1)ᴴ = pauli3 ⊗ₖ pauli1
    rw [kron_conjTranspose, pauli3_herm, pauli1_herm]
  · change (pauli3 ⊗ₖ pauli2)ᴴ = pauli3 ⊗ₖ pauli2
    rw [kron_conjTranspose, pauli3_herm, pauli2_herm]

/-- Each generator is a Hermitian unitary. -/
theorem gamma_unitary (μ : Fin 4) :
    gamma μ * (gamma μ)ᴴ = 1 := by
  rw [gamma_herm, gamma_sq]

/-- The sheet-rotated implementers `Γ₀Γ_a` are skew-Hermitian
(the other hypothesis branch of `adMap_hs_selfadjoint`). -/
theorem gammaJR_skew (a : Fin 4) (ha : a ≠ 0) :
    (gamma 0 * gamma a)ᴴ = -(gamma 0 * gamma a) := by
  rw [Matrix.conjTranspose_mul, gamma_herm, gamma_herm,
    show gamma a * gamma 0 = -(gamma 0 * gamma a) from by
      rw [gamma_anticomm a 0 ha]]

/-- **Irreducibility** (`thm:common-origin-clifford`, primitivity of
the projective revision factor): a matrix commuting with all four
Clifford generators is scalar. -/
theorem gamma_commutant
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : ∀ μ, X * gamma μ = gamma μ * X) :
    ∃ c : ℂ, X = c • 1 := by
  classical
  -- slices in the first factor commute with any `a` from `a ⊗ₖ 1`
  have hslice : ∀ a : Matrix (Fin 2) (Fin 2) ℂ,
      X * (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = (a ⊗ₖ 1) * X →
      ∀ k l : Fin 2,
        (Matrix.of fun m j => X (m, k) (j, l)) * a
          = a * Matrix.of fun m j => X (m, k) (j, l) := by
    intro a hcomm k l
    ext m j
    have h1 := congrFun (congrFun hcomm (m, k)) (j, l)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite,
      ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Matrix.of_apply] at h1 ⊢
    linear_combination h1
  have h0 : X * (pauli1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (pauli1 ⊗ₖ 1) * X := hX 0
  have h1 : X * (pauli2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (pauli2 ⊗ₖ 1) * X := hX 1
  -- every slice is scalar
  have hW : ∀ k l : Fin 2,
      (Matrix.of fun m j => X (m, k) (j, l))
        = X ((0 : Fin 2), k) ((0 : Fin 2), l) • 1 := by
    intro k l
    have h2 := pauli_commutant _ (hslice pauli1 h0 k l)
      (hslice pauli2 h1 k l)
    exact h2
  -- hence `X = 1 ⊗ Y` with `Y k l = X (0,k) (0,l)`
  set Y : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun k l => X (0, k) (0, l) with hYdef
  have hXform : X = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Y := by
    ext ⟨m, k⟩ ⟨j, l⟩
    rw [Matrix.kroneckerMap_apply]
    have h5 := congrFun (congrFun (hW k l) m) j
    rw [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at h5
    rw [h5, hYdef, Matrix.of_apply]
    ring
  -- the second factor commutes with σ₁ and σ₂ via `Γ₂, Γ₃`
  have hY1 : Y * pauli1 = pauli1 * Y := by
    have h6 := hX 2
    rw [show gamma 2 = pauli3 ⊗ₖ pauli1 from rfl, hXform,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one] at h6
    ext k l
    have h7 := congrFun (congrFun h6 (0, k)) (0, l)
    rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
      show pauli3 0 0 = 1 from rfl, one_mul, one_mul] at h7
    exact h7
  have hY2 : Y * pauli2 = pauli2 * Y := by
    have h6 := hX 3
    rw [show gamma 3 = pauli3 ⊗ₖ pauli2 from rfl, hXform,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one] at h6
    ext k l
    have h7 := congrFun (congrFun h6 (0, k)) (0, l)
    rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
      show pauli3 0 0 = 1 from rfl, one_mul, one_mul] at h7
    exact h7
  have h8 := pauli_commutant Y hY1 hY2
  refine ⟨Y 0 0, ?_⟩
  have h9 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Y
      = Y 0 0 • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      := by
    conv_lhs => rw [h8]
    rw [Matrix.kronecker_smul, Matrix.one_kronecker_one]
  rw [hXform, h9]

end NCG.CommonOrigin
