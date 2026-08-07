/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.MarkedFactor

/-!
# Factor-commutant obstruction
  (`thm:SMST-factor-obstruction`, Gran-Tensor manuscript)

* `smst_factor_obstruction`: on the split carrier
  `ℂ^I ⊗ ℂ^J`, (i) the commutant of the external factor
  `{g ⊗ 1}` is exactly the right factor `1 ⊗ M_J` (the marked
  Kronecker commutant); (ii) the commutant is itself a factor —
  any element commuting with both the external factor and its
  commutant is scalar; (iii) hence no candidate internal algebra
  containing a nonscalar central element can equal the full
  commutant of the external factor — the reducible/nontrivial-
  centre obstruction.

Rendering disclosed: the abstract `H ≅ ℂ^n ⊗ K` splitting for a
unital `M_n(ℂ)` copy on an abstract carrier is the
Skolem–Noether normal form (`NCG.skolem_noether`); here the
split carrier is taken as the frame and the boxed commutant
identifications and the obstruction clause are proved exactly.
-/

open Matrix Kronecker

namespace NCG

/-- A matrix commuting with every matrix is scalar. -/
lemma central_scalar {J : Type*} [Fintype J]
    [DecidableEq J] [Nonempty J] (b : Matrix J J ℂ)
    (h : ∀ c : Matrix J J ℂ, c * b = b * c) :
    ∃ c : ℂ, b = c • 1 := by
  classical
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  refine ⟨b j₀ j₀, ?_⟩
  ext j l
  by_cases hjl : j = l
  · subst hjl
    have h1 := congrFun (congrFun (h (Matrix.single j j₀ 1)) j) j₀
    simp only [Matrix.mul_apply, Matrix.single_apply, true_and,
      and_true, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    exact h1.symm
  · have h2 := congrFun (congrFun (h (Matrix.single j j 1)) j) l
    simp only [Matrix.mul_apply, Matrix.single_apply, true_and,
      hjl, and_false, if_false, ite_mul, one_mul, zero_mul,
      mul_zero, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [Matrix.smul_apply, Matrix.one_apply_ne hjl, smul_eq_mul,
      mul_zero]
    exact h2

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- `thm:SMST-factor-obstruction`: the marked commutant
identification, factoriality of the commutant, and the
nontrivial-centre obstruction. -/
theorem smst_factor_obstruction [Nonempty I] [Nonempty J] :
    ({B : Matrix (I × J) (I × J) ℂ | ∀ g : Matrix I I ℂ,
        (g ⊗ₖ (1 : Matrix J J ℂ)) * B = B * (g ⊗ₖ 1)}
      = Set.range fun b : Matrix J J ℂ =>
          (1 : Matrix I I ℂ) ⊗ₖ b)
    ∧ (∀ B : Matrix (I × J) (I × J) ℂ,
        (∀ g : Matrix I I ℂ,
          (g ⊗ₖ (1 : Matrix J J ℂ)) * B = B * (g ⊗ₖ 1)) →
        (∀ b : Matrix J J ℂ,
          ((1 : Matrix I I ℂ) ⊗ₖ b) * B
            = B * ((1 : Matrix I I ℂ) ⊗ₖ b)) →
        ∃ c : ℂ, B = c • 1)
    ∧ (∀ (S : Set (Matrix (I × J) (I × J) ℂ))
        (Z : Matrix (I × J) (I × J) ℂ), Z ∈ S →
        (∀ Y ∈ S, Z * Y = Y * Z) → (∀ c : ℂ, Z ≠ c • 1) →
        S ≠ {B | ∀ g : Matrix I I ℂ,
          (g ⊗ₖ (1 : Matrix J J ℂ)) * B = B * (g ⊗ₖ 1)}) := by
  have hscal : ∀ B : Matrix (I × J) (I × J) ℂ,
      (∀ g : Matrix I I ℂ,
        (g ⊗ₖ (1 : Matrix J J ℂ)) * B = B * (g ⊗ₖ 1)) →
      (∀ b : Matrix J J ℂ,
        ((1 : Matrix I I ℂ) ⊗ₖ b) * B
          = B * ((1 : Matrix I I ℂ) ⊗ₖ b)) →
      ∃ c : ℂ, B = c • 1 := by
    intro B hBleft hBright
    obtain ⟨b₀, rfl⟩ := CommonOrigin.left_factor_commutant B hBleft
    have hmul : ∀ b : Matrix J J ℂ, b * b₀ = b₀ * b := by
      intro b
      have h := hBright b
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul] at h
      ext j l
      obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
      have he := congrFun (congrFun h (i₀, j)) (i₀, l)
      simpa [Matrix.kroneckerMap_apply, Matrix.one_apply]
        using he
    obtain ⟨c, rfl⟩ := central_scalar b₀ hmul
    refine ⟨c, ?_⟩
    rw [Matrix.kronecker_smul, Matrix.one_kronecker_one]
  refine ⟨?_, hscal, ?_⟩
  · ext B
    constructor
    · intro hB
      obtain ⟨b, hb⟩ := CommonOrigin.left_factor_commutant B hB
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩ g
      exact CommonOrigin.kron_right_commutes g b
  · intro S Z hZS hZcomm hZns heq
    subst heq
    obtain ⟨c, hc⟩ := hscal Z hZS
      (fun b => (hZcomm _ (fun g => CommonOrigin.kron_right_commutes g b)).symm)
    exact hZns c hc

end NCG
