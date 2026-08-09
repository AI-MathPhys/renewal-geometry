import NCG.Grand.ExactEasy43
import NCG.Grand.LoadedSubhierarchy
import NCG.Grand.GrandOtherLoadings

/-!
# Exact EASY 70: emergence and compression of the other loadings

This file closes the bookkeeping clauses left out of `other_loadings`.  A
loaded hierarchy is represented by its finite synthesis matrices.  Its exact
certificate records positivity at every depth, finite flatness of the nested
word spans, source-minimality among all Gram factorizations, and the unique
source-fixing isometry between any two realizations of the same Gram.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Exact finite certificate attached to a loaded word-Gram hierarchy. -/
def IsCanonicalLoadedHierarchy
    {h e : Type} [Fintype h] [Fintype e]
    (W : ℕ → Matrix h e ℂ) : Prop :=
  (∀ r, ((W r)ᴴ * W r).PosSemidef)
  ∧ (∃ r, LinearMap.range (W (r + 1)).mulVecLin
      = LinearMap.range (W r).mulVecLin)
  ∧ (∀ r {k : Type} [Fintype k] (Z : Matrix k e ℂ),
      Zᴴ * Z = (W r)ᴴ * W r →
        ((W r)ᴴ * W r).rank ≤ Fintype.card k)
  ∧ (∀ r {k : Type} [Fintype k] (Z : Matrix k e ℂ),
      (W r)ᴴ * W r = Zᴴ * Z →
      ∃! U : LinearMap.range (W r).mulVecLin ≃ₗ[ℂ]
          LinearMap.range Z.mulVecLin,
        (∀ u : e → ℂ,
          U ((W r).mulVecLin.rangeRestrict u)
            = Z.mulVecLin.rangeRestrict u)
        ∧ (∀ x y : LinearMap.range (W r).mulVecLin,
          star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
            = star (U x : k → ℂ) ⬝ᵥ (U y : k → ℂ)))

/-- Every nested finite synthesis hierarchy has the exact canonical, positive,
finite-flat, source-minimal certificate. -/
theorem canonical_loaded_hierarchy
    {h e : Type} [Fintype h] [Fintype e]
    (W : ℕ → Matrix h e ℂ)
    (hNested : ∀ r, LinearMap.range (W r).mulVecLin ≤
      LinearMap.range (W (r + 1)).mulVecLin) :
    IsCanonicalLoadedHierarchy W := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact loaded_subhierarchy.1 (W r)
  · exact loaded_subhierarchy.2.2
      (fun r => LinearMap.range (W r).mulVecLin) hNested
  · intro r k _ Z hGram
    rw [← hGram, Matrix.rank_conjTranspose_mul_self]
    exact Matrix.rank_le_card_height Z
  · intro r k _ Z hGram
    exact joint_source_unique_range_unitary (W r) Z hGram

/-- `thm:other-loadings`, exact assembly.  Components and the joint loading
carry the full canonical hierarchy certificate; restriction of the joint
synthesis gives the displayed typed Gram compression; and the explicit
positive two-by-two pair proves that separate component Grams do not determine
mixed cross kernels. -/
theorem other_loadings_exact
    {δ h e j : Type} [Fintype δ] [Fintype h] [Fintype e]
    [Fintype j]
    (W : δ → ℕ → Matrix h e ℂ) (WJ : ℕ → Matrix h j ℂ)
    (Icl : δ → ℕ → Matrix j e ℂ)
    (hNested : ∀ d r, LinearMap.range (W d r).mulVecLin ≤
      LinearMap.range (W d (r + 1)).mulVecLin)
    (hNestedJ : ∀ r, LinearMap.range (WJ r).mulVecLin ≤
      LinearMap.range (WJ (r + 1)).mulVecLin)
    (hRestrict : ∀ d r, W d r = WJ r * Icl d r) :
    (∀ d, IsCanonicalLoadedHierarchy (W d))
    ∧ IsCanonicalLoadedHierarchy WJ
    ∧ (∀ d r, (W d r)ᴴ * W d r
        = (Icl d r)ᴴ * ((WJ r)ᴴ * WJ r) * Icl d r)
    ∧ (∃ K₁ K₂ : Matrix (Fin 2) (Fin 2) ℂ,
      K₁.PosSemidef ∧ K₂.PosSemidef
      ∧ K₁ 0 0 = K₂ 0 0 ∧ K₁ 1 1 = K₂ 1 1
      ∧ K₁ ≠ K₂) := by
  refine ⟨fun d => canonical_loaded_hierarchy (W d) (hNested d),
    canonical_loaded_hierarchy WJ hNestedJ, ?_, ?_⟩
  · intro d r
    rw [hRestrict d r, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · exact (other_loadings (0 : Matrix (Fin 1) (Fin 1) ℂ)
      Matrix.PosSemidef.zero (0 : Matrix (Fin 1) (Fin 1) ℂ)).2

end NCG
