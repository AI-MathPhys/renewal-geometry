/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactEasy66
import NCG.Grand.InnovationDecomposition

/-!
# Exact EASY 67: the stacked provenance-innovation rank formula

The Moore--Penrose row projector `P_A = A^dagger A` is used only through
three intrinsic facts: it is idempotent, it fixes `A` on the right, and it
has the same rank as `A`.  These facts identify its range with the row space
of `A`.  Splitting every finer row into its projected and complementary
parts then gives the manuscript's stacked-rank identity.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Dimension increment after adjoining a family of vectors, split by an
idempotent whose range is the old family's range. -/
theorem finrank_coprod_sub_of_projection
    {U W V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (a : U →ₗ[ℂ] V) (s : W →ₗ[ℂ] V) (p : V →ₗ[ℂ] V)
    (hp : IsIdempotentElem p) (ha : LinearMap.range a = LinearMap.range p) :
    Module.finrank ℂ (LinearMap.range (a.coprod s))
        - Module.finrank ℂ (LinearMap.range a)
      = Module.finrank ℂ (LinearMap.range ((LinearMap.id - p).comp s)) := by
  let q : V →ₗ[ℂ] V := LinearMap.id - p
  have hsup : LinearMap.range a ⊔ LinearMap.range s
      = LinearMap.range p ⊔ LinearMap.range (q.comp s) := by
    rw [ha]
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rintro y ⟨x, rfl⟩
      have hp_mem : p (s x) ∈ LinearMap.range p := ⟨s x, rfl⟩
      have hq_mem : q (s x) ∈ LinearMap.range (q.comp s) := ⟨x, rfl⟩
      have hsum : p (s x) + q (s x) ∈
          LinearMap.range p ⊔ LinearMap.range (q.comp s) :=
        add_mem
          ((show LinearMap.range p ≤
              LinearMap.range p ⊔ LinearMap.range (q.comp s) from le_sup_left) hp_mem)
          ((show LinearMap.range (q.comp s) ≤
              LinearMap.range p ⊔ LinearMap.range (q.comp s) from le_sup_right) hq_mem)
      simpa [q] using hsum
    · refine sup_le le_sup_left ?_
      rintro y ⟨x, rfl⟩
      have hs_mem : s x ∈ LinearMap.range s := ⟨x, rfl⟩
      have hp_mem : p (s x) ∈ LinearMap.range p := ⟨s x, rfl⟩
      have hsub : s x - p (s x) ∈
          LinearMap.range p ⊔ LinearMap.range s :=
        sub_mem
          ((show LinearMap.range s ≤
              LinearMap.range p ⊔ LinearMap.range s from le_sup_right) hs_mem)
          ((show LinearMap.range p ≤
              LinearMap.range p ⊔ LinearMap.range s from le_sup_left) hp_mem)
      simpa [q] using hsub
  have hdisj : Disjoint (LinearMap.range p) (LinearMap.range (q.comp s)) := by
    rw [disjoint_iff_inf_le]
    rintro y ⟨⟨x, rfl⟩, ⟨w, hw⟩⟩
    have hpy : p (p x) = p x := by
      have h := DFunLike.congr_fun hp x
      simpa only [Module.End.mul_apply] using h
    have hpq : p (q (s w)) = 0 := by
      have h := DFunLike.congr_fun hp (s w)
      simp only [Module.End.mul_apply] at h
      simp [q, h]
    change q (s w) = p x at hw
    rw [hw, hpy] at hpq
    change p x = 0
    exact hpq
  have hdim : Module.finrank ℂ
        ↥(LinearMap.range p ⊔ LinearMap.range (q.comp s))
      = Module.finrank ℂ ↥(LinearMap.range p)
        + Module.finrank ℂ ↥(LinearMap.range (q.comp s)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range p) (LinearMap.range (q.comp s))
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h
  rw [LinearMap.range_coprod, hsup, hdim, ha]
  exact Nat.add_sub_cancel_left _ _

/-- The rows of a vertical stack span the supremum of the two row spaces. -/
lemma rank_fromRows_eq_finrank_coprod {a s n : Type*}
    [Fintype a] [Fintype s] [Fintype n]
    (A : Matrix a n ℂ) (S : Matrix s n ℂ) :
    (Matrix.fromRows A S).rank = Module.finrank ℂ
      (LinearMap.range
        ((Matrix.mulVecLin A.transpose).coprod
          (Matrix.mulVecLin S.transpose))) := by
  rw [Matrix.rank_eq_finrank_span_row]
  have hrange : Set.range (Matrix.fromRows A S).row
      = Set.range A.row ∪ Set.range S.row := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [hrange, Submodule.span_union]
  have hA : Submodule.span ℂ (Set.range A.row)
      = LinearMap.range (Matrix.mulVecLin A.transpose) := by
    simpa only [Matrix.col_transpose] using
      (Matrix.range_mulVecLin A.transpose).symm
  have hS : Submodule.span ℂ (Set.range S.row)
      = LinearMap.range (Matrix.mulVecLin S.transpose) := by
    simpa only [Matrix.col_transpose] using
      (Matrix.range_mulVecLin S.transpose).symm
  rw [hA, hS, LinearMap.range_coprod]

/-- Exact stacked-rank formula for an algebraically characterized row-space
projector.  These hypotheses are satisfied by `P_A = A^dagger A`. -/
theorem stacked_rank_innovation {a s n : Type*}
    [Fintype a] [Fintype s] [Fintype n] [DecidableEq n]
    (A : Matrix a n ℂ) (S : Matrix s n ℂ) (PA : Matrix n n ℂ)
    (hA2 : PA * PA = PA) (hfix : A * PA = A)
    (hrank : PA.rank = A.rank) :
    (Matrix.fromRows A S).rank - A.rank = (S * (1 - PA)).rank := by
  let aLin : (a → ℂ) →ₗ[ℂ] (n → ℂ) := Matrix.mulVecLin A.transpose
  let sLin : (s → ℂ) →ₗ[ℂ] (n → ℂ) := Matrix.mulVecLin S.transpose
  let p : (n → ℂ) →ₗ[ℂ] (n → ℂ) := Matrix.mulVecLin PA.transpose
  have hp : IsIdempotentElem p := by
    rw [isIdempotentElem_iff]
    apply LinearMap.ext
    intro x
    change PA.transpose *ᵥ (PA.transpose *ᵥ x) = PA.transpose *ᵥ x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hA2]
  have hcomp : p.comp aLin = aLin := by
    apply LinearMap.ext
    intro x
    change PA.transpose *ᵥ (A.transpose *ᵥ x) = A.transpose *ᵥ x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hfix]
  have hle : LinearMap.range aLin ≤ LinearMap.range p := by
    rintro y ⟨x, rfl⟩
    exact ⟨aLin x, by
      have h := DFunLike.congr_fun hcomp x
      change p (aLin x) = aLin x at h
      exact h⟩
  have harange : LinearMap.range aLin = LinearMap.range p := by
    apply Submodule.eq_of_le_of_finrank_le hle
    change PA.transpose.rank ≤ A.transpose.rank
    simpa using le_of_eq hrank
  have hmain := finrank_coprod_sub_of_projection aLin sLin p hp harange
  have hstack := rank_fromRows_eq_finrank_coprod A S
  change (Matrix.fromRows A S).rank - A.rank = _
  have hArank : Module.finrank ℂ (LinearMap.range aLin) = A.rank := by
    change A.transpose.rank = A.rank
    exact Matrix.rank_transpose A
  rw [← hstack, hArank] at hmain
  have hres : LinearMap.range ((LinearMap.id - p).comp sLin)
      = LinearMap.range (Matrix.mulVecLin (S * (1 - PA)).transpose) := by
    apply congrArg LinearMap.range
    apply LinearMap.ext
    intro x
    change S.transpose *ᵥ x - PA.transpose *ᵥ (S.transpose *ᵥ x) =
      (S * (1 - PA)).transpose *ᵥ x
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
    rw [Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec]
  rw [hres] at hmain
  change (Matrix.fromRows A S).rank - A.rank
      = (S * (1 - PA)).transpose.rank at hmain
  exact hmain.trans (Matrix.rank_transpose (S * (1 - PA)))

/-- `thm:provenance-innovation-decomposition`, including the manuscript's
boxed stacked-rank identity. -/
theorem provenance_innovation_decomposition_exact {a n s : Type*}
    [Fintype a] [Fintype n] [Fintype s] [DecidableEq n]
    (A : Matrix a n ℂ) (S : Matrix s n ℂ)
    (PA PL : Matrix n n ℂ)
    (hAH : PAᴴ = PA) (hLH : PLᴴ = PL)
    (hA2 : PA * PA = PA) (hL2 : PL * PL = PL)
    (href : PL * PA = PA) (hfix : A * PA = A)
    (hrank : PA.rank = A.rank) :
    S * (1 - PA) * Sᴴ
        = S * (PL - PA) * Sᴴ + S * (1 - PL) * Sᴴ
    ∧ (S * (PL - PA) * Sᴴ).PosSemidef
    ∧ (S * (1 - PL) * Sᴴ).PosSemidef
    ∧ (Matrix.fromRows A S).rank - A.rank
        = (S * (1 - PA) * Sᴴ).rank := by
  obtain ⟨hpyth, hposL, hposNew, hgram⟩ :=
    provenance_innovation_decomposition S PA PL hAH hLH hA2 hL2 href
  refine ⟨hpyth, hposL, hposNew, ?_⟩
  rw [hgram, ← stacked_rank_innovation A S PA hA2 hfix hrank]

end NCG
