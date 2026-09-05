/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptanceLikelihood
import NCG.Grand.SemanticStripping
import NCG.Grand.GeneratedMinimalRecord

/-!
# likelihood gauge and semantic stripping
-/

namespace NCG

/-! ## Acceptance likelihood -/

/-- Once the rejected score and the common accepted score are
distinct, the unique affine normalization sends rejection to
zero and every accepted outcome to one. -/
theorem acceptance_affine_normalization {J : Type*} [Nonempty J]
    (sEmpty : ℝ) (s : J → ℝ) (c : ℝ)
    (hs : ∀ j, s j = c) (hne : c ≠ sEmpty) :
    let normalizedEmpty := (sEmpty - sEmpty) / (c - sEmpty)
    let normalized := fun j => (s j - sEmpty) / (c - sEmpty)
    normalizedEmpty = 0
      ∧ (∀ j, normalized j = 1)
      ∧ (∀ A B : ℝ,
          A * sEmpty + B = 0 →
          (∀ j, A * s j + B = 1) →
          A = (c - sEmpty)⁻¹ ∧ B = -sEmpty * (c - sEmpty)⁻¹) := by
  dsimp
  have hden : c - sEmpty ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨by field_simp; ring, ?_, ?_⟩
  · intro j
    rw [hs j]
    exact div_self hden
  · intro A B h0 h1
    let j₀ : J := Classical.choice (inferInstance : Nonempty J)
    have hacc := h1 j₀
    rw [hs j₀] at hacc
    have hA : A * (c - sEmpty) = 1 := by linarith
    have hA' : A = (c - sEmpty)⁻¹ :=
      (mul_eq_one_iff_eq_inv₀ hden).mp hA
    refine ⟨hA', ?_⟩
    rw [hA'] at h0
    calc
      B = -((c - sEmpty)⁻¹ * sEmpty) := by linarith
      _ = -sEmpty * (c - sEmpty)⁻¹ := by ring

/-- `cor:acceptance-likelihood`: equality of accepted scores
from the scalar partition operator, plus the unique affine gauge
normalization asserted in the manuscript. -/
theorem acceptance_likelihood_exact {J : Type*} [Fintype J] [Nonempty J]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : J → V) (hlin : LinearIndependent ℝ E)
    (s : J → ℝ) (sEmpty a b : ℝ) (hab : a < b) (w : ℝ → ℝ)
    (hscalar : ∀ q ∈ Set.Ioo a b,
      ∑ j, Real.exp (q * s j) • E j = w q • ∑ j, E j)
    (hne : s (Classical.choice (inferInstance : Nonempty J)) ≠ sEmpty) :
    (∀ j k, s j = s k)
    ∧ let c := s (Classical.choice (inferInstance : Nonempty J))
       let normalizedEmpty := (sEmpty - sEmpty) / (c - sEmpty)
       let normalized := fun j => (s j - sEmpty) / (c - sEmpty)
       normalizedEmpty = 0 ∧ ∀ j, normalized j = 1 := by
  have heq := acceptance_likelihood E hlin s a b hab w hscalar
  refine ⟨heq, ?_⟩
  dsimp
  have hnorm := acceptance_affine_normalization sEmpty s
    (s (Classical.choice (inferInstance : Nonempty J)))
    (fun j => heq j (Classical.choice (inferInstance : Nonempty J))) hne
  exact ⟨hnorm.1, hnorm.2.1⟩

/-! ## Semantic stripping -/

/-- Equality of a restricted operational table canonically
preserves both its minimal record quotient and its Hankel
response space. -/
theorem restricted_table_reconstruction_invariant
    {R Sig P F : Type*} (sig sig' : R → Sig)
    (tbl tbl' : F → P → ℂ) (hsig : sig' = sig) (htbl : tbl' = tbl) :
    Nonempty (MinRec sig' ≃ MinRec sig)
      ∧ Nonempty (HankelResponseSpace tbl' ≃ₗ[ℂ]
        HankelResponseSpace tbl) := by
  subst sig'
  subst tbl'
  exact ⟨⟨Equiv.refl _⟩, ⟨LinearEquiv.refl ℂ _⟩⟩

/-- The reconstruction-level clause of
`thm:renewal-semantic-stripping`: restricting an enlarged table
back to the identical renewal-native table leaves its two
canonical minimal quotients unchanged. -/
theorem renewal_semantic_stripping_reconstruction
    {R Sig P F : Type*} (sig : R → Sig) (tbl : F → P → ℂ) :
    Nonempty (MinRec sig ≃ MinRec sig)
      ∧ Nonempty (HankelResponseSpace tbl ≃ₗ[ℂ]
        HankelResponseSpace tbl) :=
  restricted_table_reconstruction_invariant sig sig tbl tbl rfl rfl

end NCG
