/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Anticommuting Store-block decomposition
  (`thm:store-block-decomposition`, Gran-Tensor manuscript)

* `store_block_decomposition`:
  (1) grading normal form — a hermitian `L` anticommuting with
      the grading `Z = diag(I, −I)` is exactly an off-diagonal
      corner `L = [[0, Aᴴ],[A, 0]]`;
  (2) grading commutant — an operator commuting with `Z` is
      block diagonal;
  (3) the Pauli-block core — on one singular block
      (`σ_z, μσ_x`), the joint commutant is scalar: any `R`
      commuting with both `σ_z` and `σ_x` is `α·I`.

Rendering disclosed: the singular-value decomposition of the
corner `A` (assembling the `⊕_j ℂ²⊗M_j` Pauli normal form and
the commutant `⊕_j I₂⊗B(M_j)`) is the manuscript's SVD
assembly over the proved per-block normal form; multiplicity
spaces enter through the proved scalar-block core tensored
with the declared multiplicity.
-/

open Matrix

namespace NCG

private lemma half_cancel {m m' : Type*} (A : Matrix m m' ℂ)
    (hA : A = -A) : A = 0 := by
  have h2 : A + A = 0 := by
    nth_rewrite 2 [hA]
    exact add_neg_cancel A
  have h2' : (2 : ℂ) • A = 0 := by
    rw [two_smul]
    exact h2
  rcases smul_eq_zero.mp h2' with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- `thm:store-block-decomposition`. -/
theorem store_block_decomposition {p q : Type*} [Fintype p]
    [Fintype q] [DecidableEq p] [DecidableEq q] :
    -- (1) graded normal form for anticommuting hermitian L
    (∀ L : Matrix (p ⊕ q) (p ⊕ q) ℂ, Lᴴ = L →
      Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0
          (-(1 : Matrix q q ℂ)) * L
        = -(L * Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0
          (-(1 : Matrix q q ℂ))) →
      L = Matrix.fromBlocks 0 (L.toBlocks₂₁)ᴴ
          (L.toBlocks₂₁) 0)
    -- (2) grading commutant is block diagonal
    ∧ (∀ R : Matrix (p ⊕ q) (p ⊕ q) ℂ,
        R * Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0
            (-(1 : Matrix q q ℂ))
          = Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0
            (-(1 : Matrix q q ℂ)) * R →
        R = Matrix.fromBlocks (R.toBlocks₁₁) 0 0
            (R.toBlocks₂₂))
    -- (3) the Pauli-block core: scalar joint commutant
    ∧ (∀ R : Matrix (Fin 2) (Fin 2) ℂ,
        R * !![(1 : ℂ), 0; 0, -1] = !![(1 : ℂ), 0; 0, -1] * R →
        R * !![(0 : ℂ), 1; 1, 0] = !![(0 : ℂ), 1; 1, 0] * R →
        ∃ α : ℂ, R = α • 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L hLH hanti
    rw [← Matrix.fromBlocks_toBlocks L] at hanti
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      at hanti
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_neg,
      add_zero, zero_add, Matrix.fromBlocks_neg, neg_neg]
      at hanti
    have h11 := congrArg Matrix.toBlocks₁₁ hanti
    have h22 := congrArg Matrix.toBlocks₂₂ hanti
    rw [Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₁] at h11
    rw [Matrix.toBlocks_fromBlocks₂₂,
      Matrix.toBlocks_fromBlocks₂₂] at h22
    have hz11 : L.toBlocks₁₁ = 0 := half_cancel _ h11
    have hz22 : L.toBlocks₂₂ = 0 := by
      have := half_cancel (-(L.toBlocks₂₂)) (by rw [neg_neg]; exact h22)
      simpa using this
    have hherm : L.toBlocks₁₂ = (L.toBlocks₂₁)ᴴ := by
      have h := congrArg Matrix.toBlocks₁₂
        (congrArg Matrix.conjTranspose
          (Matrix.fromBlocks_toBlocks L).symm)
      rw [hLH] at h
      rw [Matrix.fromBlocks_conjTranspose,
        Matrix.toBlocks_fromBlocks₁₂] at h
      exact h
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks L]
    rw [hz11, hz22, hherm]
  · intro R hcomm
    rw [← Matrix.fromBlocks_toBlocks R] at hcomm
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      at hcomm
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_neg,
      add_zero, zero_add] at hcomm
    have h12 := congrArg Matrix.toBlocks₁₂ hcomm
    have h21 := congrArg Matrix.toBlocks₂₁ hcomm
    rw [Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₁₂] at h12
    rw [Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₁] at h21
    have hz12 : R.toBlocks₁₂ = 0 := half_cancel _ h12.symm
    have hz21 : R.toBlocks₂₁ = 0 := by
      have := half_cancel (-(R.toBlocks₂₁)) (by rw [neg_neg]; exact h21.symm)
      simpa using this
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks R]
    rw [hz12, hz21]
  · intro R hz hx
    have hcz : Commute !![(1 : ℂ), 0; 0, -1] R := hz.symm
    have hcx : Commute !![(0 : ℂ), 1; 1, 0] R := hx.symm
    have hczx : Commute
        (!![(1 : ℂ), 0; 0, -1] * !![(0 : ℂ), 1; 1, 0]) R :=
      hcz.mul_left hcx
    have hsingle : ∀ i j : Fin 2,
        Commute (Matrix.single i j (1 : ℂ)) R := by
      intro i j
      fin_cases i <;> fin_cases j
      · change Commute
          (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) R
        rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
            = (2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
              + !![(1 : ℂ), 0; 0, -1]) from by
          ext a b
          fin_cases a <;> fin_cases b <;>
            (simp; try norm_num)]
        exact ((Commute.one_left R).add_left hcz).smul_left _
      · change Commute
          (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) R
        rw [show Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
            = (2 : ℂ)⁻¹ • (!![(0 : ℂ), 1; 1, 0]
              + !![(1 : ℂ), 0; 0, -1]
                * !![(0 : ℂ), 1; 1, 0]) from by
          ext a b
          fin_cases a <;> fin_cases b <;>
            (simp; try norm_num)]
        exact (hcx.add_left hczx).smul_left _
      · change Commute
          (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)) R
        rw [show Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
            = (2 : ℂ)⁻¹ • (!![(0 : ℂ), 1; 1, 0]
              - !![(1 : ℂ), 0; 0, -1]
                * !![(0 : ℂ), 1; 1, 0]) from by
          ext a b
          fin_cases a <;> fin_cases b <;>
            (simp; try norm_num)]
        exact (hcx.sub_left hczx).smul_left _
      · change Commute
          (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) R
        rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
            = (2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ)
              - !![(1 : ℂ), 0; 0, -1]) from by
          ext a b
          fin_cases a <;> fin_cases b <;>
            (simp; try norm_num)]
        exact ((Commute.one_left R).sub_left hcz).smul_left _
    obtain ⟨α, hα⟩ :=
      Matrix.mem_range_scalar_iff_commute_single'.mpr
        (fun i j => hsingle i j)
    refine ⟨α, ?_⟩
    rw [← hα]
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

end NCG
