/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SupportPrototype

/-!
# Covariance of support-resolved Grams

This module derives the boxed covariance in
`thm:S4-support-prototype` from covariance of the differentiated synthesis and
of the support projections.  It then combines that identity with the explicit
transitivity of `S₄` on the two- and three-element subsets of four cells.
-/

open Matrix

namespace NCG

/-- A covariant synthesis and a covariant projection family produce covariant
support-resolved Grams. -/
theorem supportGram_covariant {G a k I : Type*}
    [Fintype a] [DecidableEq a] [Fintype k] [DecidableEq k]
    (U : G → Matrix a a ℂ) (ρ : G → Matrix k k ℂ)
    (F : Matrix a k ℂ) (P : I → Matrix a a ℂ) (act : G → I → I)
    (hU : ∀ g, U g * (U g)ᴴ = 1 ∧ (U g)ᴴ * U g = 1)
    (hρ : ∀ g, ρ g * (ρ g)ᴴ = 1 ∧ (ρ g)ᴴ * ρ g = 1)
    (hF : ∀ g, U g * F = F * ρ g)
    (hP : ∀ g A, U g * P A * (U g)ᴴ = P (act g A)) :
    ∀ g A,
      (ρ g)ᴴ * (Fᴴ * P (act g A) * F) * ρ g = Fᴴ * P A * F := by
  intro g A
  have hUstarF : (U g)ᴴ * F = F * (ρ g)ᴴ := by
    calc
      (U g)ᴴ * F = (U g)ᴴ * F * (ρ g * (ρ g)ᴴ) := by
        rw [(hρ g).1, Matrix.mul_one]
      _ = (U g)ᴴ * (F * ρ g) * (ρ g)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = (U g)ᴴ * (U g * F) * (ρ g)ᴴ := by rw [hF g]
      _ = F * (ρ g)ᴴ := by
        simp only [← Matrix.mul_assoc, (hU g).2, Matrix.one_mul]
  have hFstarU : Fᴴ * U g = ρ g * Fᴴ := by
    have h := congrArg Matrix.conjTranspose hUstarF
    simpa [Matrix.conjTranspose_mul] using h
  calc
    (ρ g)ᴴ * (Fᴴ * P (act g A) * F) * ρ g
        = (ρ g)ᴴ * Fᴴ * (U g * P A * (U g)ᴴ) * F * ρ g := by
            rw [hP g A]
            simp only [Matrix.mul_assoc]
    _ = (ρ g)ᴴ * (ρ g * Fᴴ) * P A * ((U g)ᴴ * F) * ρ g := by
          rw [← hFstarU]
          simp only [Matrix.mul_assoc]
    _ = ((ρ g)ᴴ * ρ g) * Fᴴ * P A * ((U g)ᴴ * F) * ρ g := by
          simp only [Matrix.mul_assoc]
    _ = Fᴴ * P A * (F * (ρ g)ᴴ) * ρ g := by
          rw [(hρ g).2, Matrix.one_mul, hUstarF]
    _ = Fᴴ * P A * F * ((ρ g)ᴴ * ρ g) := by
          simp only [Matrix.mul_assoc]
    _ = Fᴴ * P A * F := by rw [(hρ g).2, Matrix.mul_one]

/-- Exact four-cell `S₄` support audit derived from synthesis covariance rather
than assumed Gram covariance. -/
theorem s4_support_gram_prototype_exact {a k : Type*}
    [Fintype a] [DecidableEq a] [Fintype k] [DecidableEq k]
    (U : Equiv.Perm (Fin 4) → Matrix a a ℂ)
    (ρ : Equiv.Perm (Fin 4) → Matrix k k ℂ)
    (F : Matrix a k ℂ) (P : Finset (Fin 4) → Matrix a a ℂ)
    (hU : ∀ σ, U σ * (U σ)ᴴ = 1 ∧ (U σ)ᴴ * U σ = 1)
    (hρ : ∀ σ, ρ σ * (ρ σ)ᴴ = 1 ∧ (ρ σ)ᴴ * ρ σ = 1)
    (hF : ∀ σ, U σ * F = F * ρ σ)
    (hP : ∀ σ A, U σ * P A * (U σ)ᴴ = P (A.image σ)) :
    let C := fun A => Fᴴ * P A * F
    -- Boxed covariance.
    (∀ σ A, (ρ σ)ᴴ * C (A.image σ) * ρ σ = C A)
    -- One pair and one triple are orbit prototypes.
    ∧ (∀ A B : Finset (Fin 4), A.card = 2 → B.card = 2 →
        ∃ σ : Equiv.Perm (Fin 4), A.image σ = B)
    ∧ (∀ A B : Finset (Fin 4), A.card = 3 → B.card = 3 →
        ∃ σ : Equiv.Perm (Fin 4), A.image σ = B)
    -- The pairwise branch is decided by one triple and the four-body panel.
    ∧ (((∀ A : Finset (Fin 4), A.card = 3 → C A = 0)
          ∧ C Finset.univ = 0) ↔
        (C {0, 1, 2} = 0 ∧ C Finset.univ = 0))
    -- A pair prototype decides all six pair panels in either direction.
    ∧ (C {0, 1} ≠ 0 →
        ∀ A : Finset (Fin 4), A.card = 2 → C A ≠ 0)
    ∧ (C {0, 1} = 0 →
        ∀ A : Finset (Fin 4), A.card = 2 → C A = 0) := by
  dsimp only
  have hboxed : ∀ σ A,
      (ρ σ)ᴴ * (Fᴴ * P (A.image σ) * F) * ρ σ = Fᴴ * P A * F :=
    supportGram_covariant U ρ F P (fun σ A => A.image σ) hU hρ hF hP
  have hzero : ∀ (σ : Equiv.Perm (Fin 4)) (A : Finset (Fin 4)),
      (Fᴴ * P (A.image σ) * F = 0 ↔ Fᴴ * P A * F = 0) := by
    intro σ A
    constructor
    · intro hz
      have hca : (0 : Matrix k k ℂ) = Fᴴ * P A * F := by
        simpa [hz] using hboxed σ A
      exact hca.symm
    · intro hz
      have hc := hboxed σ A
      rw [hz] at hc
      have hconj : (ρ σ)ᴴ * (Fᴴ * P (A.image σ) * F) * ρ σ = 0 := by
        simpa using hc
      have h := congrArg (fun X => ρ σ * X * (ρ σ)ᴴ) hconj
      calc
        Fᴴ * P (A.image σ) * F
            = (ρ σ * (ρ σ)ᴴ) * (Fᴴ * P (A.image σ) * F)
                * (ρ σ * (ρ σ)ᴴ) := by
                  rw [(hρ σ).1, Matrix.one_mul, Matrix.mul_one]
        _ = ρ σ * ((ρ σ)ᴴ * (Fᴴ * P (A.image σ) * F) * ρ σ)
                * (ρ σ)ᴴ := by simp only [Matrix.mul_assoc]
        _ = 0 := by simpa using h
  have haudit := four_cell_support_orbit_audit
    (fun A => Fᴴ * P A * F) hzero
  rcases haudit with ⟨hpair, htriple, hpairNonzero, htripleZero⟩
  refine ⟨hboxed, hpair, htriple, ?_, hpairNonzero, ?_⟩
  · constructor
    · intro h
      exact ⟨h.1 {0, 1, 2} (by decide), h.2⟩
    · intro h
      exact ⟨htripleZero h.1, h.2⟩
  · intro hproto A hA
    obtain ⟨σ, hσ⟩ := hpair {0, 1} A (by decide) hA
    rw [← hσ]
    exact (hzero σ {0, 1}).mpr hproto

end NCG
