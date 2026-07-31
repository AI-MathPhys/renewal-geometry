/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The projective revision theorem
  (`thm:projective-revision`, SM_emergence)

An additive family of invertible implementers on an irreducible
matrix factor whose adjoint actions compose additively carries a
scalar two-cocycle:

* `projective_revision` — if `Ad_{R_a}∘Ad_{R_b} = Ad_{R_{a+b}}`
  then `R_aR_b = τ(a,b)·R_{a+b}` for a nowhere-zero scalar
  `τ` satisfying the cocycle identity, and the scalar commutator
  `R_aR_b = (τ(a,b)/τ(b,a))·R_bR_a` is the section-independent
  alternating bicharacter datum.

The proof is the Schur argument: `R_{a+b}⁻¹R_aR_b` commutes with
every matrix, hence is scalar
(`Matrix.mem_range_scalar_iff_commute_single'`).
-/

namespace NCG

open Matrix

private lemma scalar_smul_one {n : Type*} [Fintype n]
    [DecidableEq n] (c : ℂ) :
    Matrix.scalar n c = c • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.one_apply_ne h,
      Matrix.diagonal_apply_ne _ h]

/-- `thm:projective-revision`: the automatic scalar two-cocycle of
an additive adjoint action. -/
theorem projective_revision {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {H : Type*} [AddCommGroup H]
    (R : H → Matrix n n ℂ) (hR : ∀ a, IsUnit (R a))
    (hAd : ∀ a b (M : Matrix n n ℂ),
      R a * (R b * M * (R b)⁻¹) * (R a)⁻¹
        = R (a + b) * M * (R (a + b))⁻¹) :
    ∃ τ : H → H → ℂ,
      (∀ a b, τ a b ≠ 0)
      ∧ (∀ a b, R a * R b = τ a b • R (a + b))
      ∧ (∀ a b c, τ a b * τ (a + b) c = τ b c * τ a (b + c))
      ∧ (∀ a b, R a * R b = (τ a b / τ b a) • (R b * R a)) := by
  have hdet : ∀ a, IsUnit (R a).det := fun a =>
    (Matrix.isUnit_iff_isUnit_det (R a)).mp (hR a)
  have hRne : ∀ a, R a ≠ 0 := by
    intro a h0
    exact not_isUnit_zero (h0 ▸ hR a)
  -- Step 1: the ratio `R_{a+b}⁻¹ R_a R_b` is a nonzero scalar.
  have key : ∀ a b, ∃ c : ℂ, c ≠ 0 ∧ R a * R b = c • R (a + b) := by
    intro a b
    have hcomm : ∀ M : Matrix n n ℂ,
        ((R (a + b))⁻¹ * (R a * R b)) * M
          = M * ((R (a + b))⁻¹ * (R a * R b)) := by
      intro M
      have h := hAd a b M
      have h1 : R a * R b * M * ((R b)⁻¹ * (R a)⁻¹ * (R a * R b))
          = R (a + b) * M * ((R (a + b))⁻¹ * (R a * R b)) := by
        calc R a * R b * M * ((R b)⁻¹ * (R a)⁻¹ * (R a * R b))
            = (R a * (R b * M * (R b)⁻¹) * (R a)⁻¹)
                * (R a * R b) := by noncomm_ring
          _ = (R (a + b) * M * (R (a + b))⁻¹) * (R a * R b) := by
              rw [h]
          _ = R (a + b) * M * ((R (a + b))⁻¹ * (R a * R b)) := by
              noncomm_ring
      have hb1 : (R b)⁻¹ * (R a)⁻¹ * (R a * R b) = 1 := by
        rw [mul_assoc, ← mul_assoc ((R a)⁻¹),
          Matrix.nonsing_inv_mul _ (hdet a), one_mul,
          Matrix.nonsing_inv_mul _ (hdet b)]
      rw [hb1, mul_one] at h1
      have h2 : (R (a + b))⁻¹ * (R a * R b * M)
          = (R (a + b))⁻¹ * (R (a + b) * M
              * ((R (a + b))⁻¹ * (R a * R b))) := by rw [h1]
      rw [show (R (a + b))⁻¹ * (R (a + b) * M
            * ((R (a + b))⁻¹ * (R a * R b)))
          = ((R (a + b))⁻¹ * R (a + b)) * M
            * ((R (a + b))⁻¹ * (R a * R b)) by noncomm_ring,
        Matrix.nonsing_inv_mul _ (hdet (a + b)), one_mul] at h2
      calc ((R (a + b))⁻¹ * (R a * R b)) * M
          = (R (a + b))⁻¹ * (R a * R b * M) := by noncomm_ring
        _ = M * ((R (a + b))⁻¹ * (R a * R b)) := h2
    have hscalar : (R (a + b))⁻¹ * (R a * R b)
        ∈ Set.range (Matrix.scalar n) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      exact (hcomm (Matrix.single i j 1)).symm
    obtain ⟨c, hc⟩ := hscalar
    have hmain : R a * R b = c • R (a + b) := by
      have h3 : R (a + b) * ((R (a + b))⁻¹ * (R a * R b))
          = R (a + b) * Matrix.scalar n c := by rw [hc]
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hdet (a + b)),
        one_mul, scalar_smul_one, Matrix.mul_smul, mul_one] at h3
      exact h3
    refine ⟨c, ?_, hmain⟩
    intro hc0
    rw [hc0, zero_smul] at hmain
    exact not_isUnit_zero (hmain ▸ ((hR a).mul (hR b)))
  choose τ hτne hτ using key
  -- scalar cancellation against a nonzero matrix
  have hcancel : ∀ (c₁ c₂ : ℂ) (a : H),
      c₁ • R a = c₂ • R a → c₁ = c₂ := by
    intro c₁ c₂ a h
    have h0 : (c₁ - c₂) • R a = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 (hRne a)
  refine ⟨τ, hτne, hτ, ?_, ?_⟩
  · -- cocycle identity from associativity
    intro a b c
    have hL : R a * R b * R c
        = (τ a b * τ (a + b) c) • R (a + b + c) := by
      rw [hτ a b, Matrix.smul_mul, hτ (a + b) c, smul_smul]
    have hR' : R a * (R b * R c)
        = (τ b c * τ a (b + c)) • R (a + (b + c)) := by
      rw [hτ b c, Matrix.mul_smul, hτ a (b + c), smul_smul]
    rw [mul_assoc] at hL
    rw [show a + (b + c) = a + b + c by rw [add_assoc]] at hR'
    exact hcancel _ _ _ (hL.symm.trans hR')
  · -- scalar commutator
    intro a b
    have h1 : R b * R a = τ b a • R (a + b) := by
      rw [hτ b a, add_comm b a]
    have h2 : R (a + b) = (τ b a)⁻¹ • (R b * R a) := by
      rw [h1, smul_smul, inv_mul_cancel₀ (hτne b a), one_smul]
    rw [hτ a b, h2, smul_smul, div_eq_mul_inv]

end NCG
