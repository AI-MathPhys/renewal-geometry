/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Automorphism reconstruction of the global gauge group
  (`thm:SM-group`, Gran-Tensor manuscript)

* `sm_group`: the boxed quotient presentation
  `S(U(3)×U(2)) ≅ (SU(3)×SU(2)×U(1))/Z₆` through the explicit
  map `Φ(g₃,g₂,z) = (z⁻²g₃, z³g₂)`:
  (1) determinant-constraint preservation: `Φ` lands in the
      determinant-one-product locus
      (`det(z⁻²g₃)·det(z³g₂) = det g₃ · det g₂`);
  (2) phases of modulus one preserve unitarity
      (`(z·g)ᴴ(z·g) = gᴴg` when `z̄z = 1`);
  (3) surjectivity: every pair with `det A · det B = 1` is
      `Φ(g₃,g₂,z)` for special-unitary-determinant `g₃, g₂`
      and a sixth root `z⁶ = det B`;
  (4) kernel: `Φ(g₃,g₂,z) = (1,1)` with `det g₃ = 1` forces
      `g₃ = z²·1`, `g₂ = z⁻³·1`, and `z⁶ = 1` — the boxed
      order-six central subgroup.

Rendering disclosed: the identification of the τ-preserving
unitary tensor automorphisms with the `det·det = 1` locus is
the one-line determinant-line action (`τ ↦ det(A)det(B)τ`),
declared as the seed's defining property; the group-isomorphism
packaging of clauses (1)–(4) is the standard first-isomorphism
bookkeeping.
-/

open Matrix

namespace NCG

/-- `thm:SM-group`. -/
theorem sm_group :
    -- (1) Φ preserves the determinant constraint
    (∀ (g₃ : Matrix (Fin 3) (Fin 3) ℂ)
       (g₂ : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ), z ≠ 0 →
      ((z⁻¹) ^ 2 • g₃).det * ((z ^ 3) • g₂).det
        = g₃.det * g₂.det)
    -- (2) unit phases preserve unitarity
    ∧ (∀ {n : Type} [Fintype n] [DecidableEq n]
        (z : ℂ) (g : Matrix n n ℂ), star z * z = 1 →
        (z • g)ᴴ * (z • g) = gᴴ * g)
    -- (3) surjectivity onto the constraint locus
    ∧ (∀ (A : Matrix (Fin 3) (Fin 3) ℂ)
        (B : Matrix (Fin 2) (Fin 2) ℂ),
        A.det * B.det = 1 →
        ∃ (z : ℂ) (g₃ : Matrix (Fin 3) (Fin 3) ℂ)
          (g₂ : Matrix (Fin 2) (Fin 2) ℂ),
          z ≠ 0 ∧ z ^ 6 = B.det ∧ g₃.det = 1 ∧ g₂.det = 1
          ∧ (z⁻¹) ^ 2 • g₃ = A ∧ (z ^ 3) • g₂ = B)
    -- (4) the boxed ℤ₆ kernel
    ∧ (∀ (g₃ : Matrix (Fin 3) (Fin 3) ℂ)
        (g₂ : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ), z ≠ 0 →
        g₃.det = 1 →
        (z⁻¹) ^ 2 • g₃ = 1 → (z ^ 3) • g₂ = 1 →
        g₃ = z ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)
        ∧ g₂ = (z⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ∧ z ^ 6 = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₃ g₂ z hz
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin,
      Fintype.card_fin]
    field_simp
  · intro n _ _ z g hzu
    rw [Matrix.conjTranspose_smul, smul_mul_smul_comm, hzu,
      one_smul]
  · intro A B hAB
    have hBdet : B.det ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hAB
      exact zero_ne_one hAB
    obtain ⟨z, hz6⟩ : ∃ z : ℂ, z ^ 6 = B.det :=
      IsAlgClosed.exists_pow_nat_eq B.det (by norm_num)
    have hz : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hz6
      exact hBdet hz6.symm
    refine ⟨z, z ^ 2 • A, (z⁻¹) ^ 3 • B, hz, hz6, ?_, ?_,
      ?_, ?_⟩
    · rw [Matrix.det_smul, Fintype.card_fin]
      have : (z ^ 2) ^ 3 * A.det = z ^ 6 * A.det := by ring
      rw [this, hz6, mul_comm]
      exact hAB
    · rw [Matrix.det_smul, Fintype.card_fin]
      have h1 : ((z⁻¹) ^ 3) ^ 2 = (z ^ 6)⁻¹ := by
        field_simp
      rw [h1, hz6, inv_mul_cancel₀ hBdet]
    · rw [smul_smul]
      have : (z⁻¹) ^ 2 * z ^ 2 = 1 := by
        field_simp
      rw [this, one_smul]
    · rw [smul_smul]
      have : z ^ 3 * (z⁻¹) ^ 3 = 1 := by
        field_simp
      rw [this, one_smul]
  · intro g₃ g₂ z hz hdet h3 h2
    have hg₃ : g₃ = z ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
      have h := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) ℂ => z ^ 2 • M) h3
      rw [smul_smul,
        show z ^ 2 * (z⁻¹) ^ 2 = 1 from by field_simp,
        one_smul] at h
      exact h
    have hg₂ : g₂
        = (z⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℂ => (z⁻¹) ^ 3 • M) h2
      rw [smul_smul,
        show (z⁻¹) ^ 3 * z ^ 3 = 1 from by field_simp,
        one_smul] at h
      exact h
    have hz6 : z ^ 6 = 1 := by
      have h := hdet
      rw [hg₃, Matrix.det_smul, Fintype.card_fin,
        Matrix.det_one, mul_one] at h
      calc z ^ 6 = (z ^ 2) ^ 3 := by ring
        _ = 1 := h
    exact ⟨hg₃, hg₂, hz6⟩

end NCG
