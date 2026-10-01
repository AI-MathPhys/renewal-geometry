/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# All-rank range test and sharp affine obstruction
  (`thm:supp-finite-range-test`, `eq:supp-finite-range-test`,
  `eq:supp-finite-range-floor`, `eq:supp-finite-range-distance`;
  emergent-spacetime manuscript)

Coordinates are orthonormal for the fixed positive coefficient inner product, so the inner
product is the dot product and the norm is `eNorm v = √(v ⬝ᵥ v)`.  The matrix
`C = C_* = 𝒞_g` (rows `m`, in the paper `m = Fin 3`; columns `k`, in the paper `k = Fin 2`)
and `q = q_* = q_{0,can}`.

**Pseudoinverse.**  Mathlib has no Moore–Penrose inverse of a rectangular matrix.  The
theorem only uses that `C C^†` is the orthogonal projection onto `Ran C`, which follows from
the two Penrose identities `C C^† C = C` and `(C C^†)ᵀ = C C^†`; we therefore state every
result for an arbitrary `D` satisfying these two identities (`IsRangeProjector C D`), which
the Moore–Penrose inverse `C^†` does.  `isRangeProjector_of_isUnit` gives the explicit
full-column-rank instance `D = (Cᵀ C)⁻¹ Cᵀ`.  The residual is `e_* = (I - C D) q`
(`residual`).

Results:
* `range_test`: `q ∈ Ran C ↔ rank (C | q) = rank C ↔ e_* = 0` (`eq:supp-finite-range-test`),
  the augmented matrix being `fromCols C (replicateCol Unit q)`;
* `residual_isLeast`: `‖e_*‖` is the distance from `0` to the affine space `q - Ran C`
  (attained at `D q`);
* `slope_floor`: if `𝒬_can(c) = q - C A ℛ(c)` for every `c` (the rank-two factorization
  `eq:supp-exact-rank-two-factorization` with `A = 𝒜_g⁻¹`, hypothesis `hfact`), then
  `‖𝒬_can(c)‖ ≥ ‖e_*‖` (`eq:supp-finite-range-floor`);
* `residual_norm_rank_two`: for `C = (c₁ c₂)` of rank two and `n = c₁ × c₂`,
  `‖e_*‖ = |nᵀ q| / ‖n‖ = |det(c₁, c₂, q)| / ‖c₁ × c₂‖` (`eq:supp-finite-range-distance`);
* `mem_range_iff_cross_eq_zero_of_rank_one`: rank one with a nonzero column `u`:
  `q ∈ Ran C ↔ u × q = 0`; `mem_range_iff_eq_zero_of_rank_zero`: rank zero: `q ∈ Ran C ↔ q = 0`.
-/

namespace RenewalGeometry
namespace FiniteRangeTest

open Matrix Module

section General

variable {m k : Type*} [Fintype m] [Fintype k]

theorem dot_self_nonneg (v : m → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- The Euclidean norm in orthonormal coordinates, `‖v‖ = √(vᵀ v)`. -/
noncomputable def eNorm (v : m → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The two Penrose identities `C D C = C`, `(C D)ᵀ = C D` (satisfied by the Moore–Penrose
inverse `D = C^†`), which make `C D` the orthogonal projection onto `Ran C`. -/
structure IsRangeProjector (C : Matrix m k ℝ) (D : Matrix k m ℝ) : Prop where
  mul_mul : C * D * C = C
  symm : (C * D)ᵀ = C * D

/-- Full column rank instance: `D = (Cᵀ C)⁻¹ Cᵀ`. -/
theorem isRangeProjector_of_isUnit [DecidableEq k] (C : Matrix m k ℝ) (h : IsUnit (Cᵀ * C).det) :
    IsRangeProjector C ((Cᵀ * C)⁻¹ * Cᵀ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]
  · rw [transpose_mul, transpose_mul, transpose_transpose, transpose_nonsing_inv,
      transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- The residual `e_* = (I - C D) q`. -/
def residual (C : Matrix m k ℝ) (D : Matrix k m ℝ) (q : m → ℝ) : m → ℝ := q - (C * D) *ᵥ q

variable {C : Matrix m k ℝ} {D : Matrix k m ℝ}

theorem projector_mulVec_range (hP : IsRangeProjector C D) (x : k → ℝ) :
    (C * D) *ᵥ (C *ᵥ x) = C *ᵥ x := by
  rw [mulVec_mulVec, hP.mul_mul]

/-- `(C D q)ᵀ w = qᵀ (C D w)`. -/
theorem projector_dot (hP : IsRangeProjector C D) (q w : m → ℝ) :
    ((C * D) *ᵥ q) ⬝ᵥ w = q ⬝ᵥ ((C * D) *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hP.symm, dotProduct_comm]

/-- The residual is orthogonal to `Ran C`. -/
theorem residual_dot_range (hP : IsRangeProjector C D) (q : m → ℝ) (x : k → ℝ) :
    residual C D q ⬝ᵥ (C *ᵥ x) = 0 := by
  rw [residual, sub_dotProduct, projector_dot hP, projector_mulVec_range hP, sub_self]

/-- `q - C (D q) = e_*`. -/
theorem sub_mulVec_eq_residual (q : m → ℝ) : q - C *ᵥ (D *ᵥ q) = residual C D q := by
  rw [residual, mulVec_mulVec]

/-- `q ∈ Ran C ↔ e_* = 0`. -/
theorem mem_range_iff_residual_eq_zero (hP : IsRangeProjector C D) (q : m → ℝ) :
    q ∈ LinearMap.range C.mulVecLin ↔ residual C D q = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [residual, mulVecLin_apply, projector_mulVec_range hP, sub_self]
  · intro h
    refine ⟨D *ᵥ q, ?_⟩
    have h' := sub_mulVec_eq_residual (C := C) (D := D) q
    rw [h, sub_eq_zero] at h'
    rw [mulVecLin_apply]
    exact h'.symm

omit [Fintype m] in
/-- The column space of the augmented matrix `(C | q)` is `Ran C ⊔ span {q}`. -/
theorem range_augmented (q : m → ℝ) :
    LinearMap.range (fromCols C (replicateCol Unit q)).mulVecLin
      = LinearMap.range C.mulVecLin ⊔ Submodule.span ℝ {q} := by
  have hcol : ∀ u : Unit → ℝ, replicateCol Unit q *ᵥ u = u () • q := by
    intro u; ext i; simp [mulVec, dotProduct, replicateCol, mul_comm]
  ext w
  simp only [LinearMap.mem_range, mulVecLin_apply, fromCols_mulVec, hcol, Submodule.mem_sup,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨v ∘ Sum.inl, rfl⟩, _, ⟨v (Sum.inr ()), rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
    exact ⟨Sum.elim x fun _ => a, by simp [Function.comp_def]⟩

omit [Fintype m] in
/-- `rank (C | q) = rank C ↔ q ∈ Ran C`. -/
theorem rank_augmented_eq_iff (q : m → ℝ) :
    (fromCols C (replicateCol Unit q)).rank = C.rank ↔ q ∈ LinearMap.range C.mulVecLin := by
  rw [Matrix.rank, Matrix.rank, range_augmented]
  constructor
  · intro h
    have heq := Submodule.eq_of_le_of_finrank_eq (le_sup_left :
      LinearMap.range C.mulVecLin ≤ LinearMap.range C.mulVecLin ⊔ Submodule.span ℝ {q}) h.symm
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self q)
  · intro h
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h)]

/-- **`thm:supp-finite-range-test`, `eq:supp-finite-range-test`.**
`q ∈ Ran C ↔ rank (C | q) = rank C ↔ e_* = 0`. -/
theorem range_test (hP : IsRangeProjector C D) (q : m → ℝ) :
    (q ∈ LinearMap.range C.mulVecLin ↔ (fromCols C (replicateCol Unit q)).rank = C.rank) ∧
      ((fromCols C (replicateCol Unit q)).rank = C.rank ↔ residual C D q = 0) := by
  rw [rank_augmented_eq_iff, mem_range_iff_residual_eq_zero hP]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Pythagoras: `‖q - C y‖² = ‖e_*‖² + ‖C (D q - y)‖²`, hence `‖e_*‖² ≤ ‖q - C y‖²`. -/
theorem residual_dot_le (hP : IsRangeProjector C D) (q : m → ℝ) (y : k → ℝ) :
    residual C D q ⬝ᵥ residual C D q ≤ (q - C *ᵥ y) ⬝ᵥ (q - C *ᵥ y) := by
  set e := residual C D q
  set w := C *ᵥ (D *ᵥ q - y)
  have hsplit : q - C *ᵥ y = e + w := by
    simp only [e, w, ← sub_mulVec_eq_residual, mulVec_sub]; abel
  have hew : e ⬝ᵥ w = 0 := residual_dot_range hP q _
  have hwe : w ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hew
  rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, hew, hwe]
  have := dot_self_nonneg w
  linarith

/-- **Distance clause.** `‖e_*‖` is the exact distance from `0` to the affine space
`q - Ran C`: it bounds `‖q - C y‖` for every `y` and is attained at `y = D q`. -/
theorem residual_isLeast (hP : IsRangeProjector C D) (q : m → ℝ) :
    IsLeast (Set.range fun y : k → ℝ => eNorm (q - C *ᵥ y)) (eNorm (residual C D q)) := by
  refine ⟨⟨D *ᵥ q, by simp only [sub_mulVec_eq_residual]⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact Real.sqrt_le_sqrt (residual_dot_le hP q y)

/-- **`eq:supp-finite-range-floor`.** Given the rank-two factorization
`𝒬_can(c) = q_* - C_* A ℛ(c)` (`A = 𝒜_g⁻¹`; hypothesis `hfact`, the conclusion of
`thm:supp-exact-rank-two-factorization`), every harmonic slope satisfies
`‖𝒬_can(c)‖ ≥ ‖e_*‖`. -/
theorem slope_floor {κ : Type*} (hP : IsRangeProjector C D) (A : Matrix k k ℝ) (q : m → ℝ)
    (Qcan : κ → m → ℝ) (R : κ → k → ℝ) (hfact : ∀ c, Qcan c = q - (C * A) *ᵥ R c) (c : κ) :
    eNorm (residual C D q) ≤ eNorm (Qcan c) := by
  rw [hfact c, ← mulVec_mulVec]
  exact (residual_isLeast hP q).2 ⟨A *ᵥ R c, rfl⟩

end General

/-! ## The three-dimensional rank tests -/

section Three

open scoped Matrix

theorem cross_eq_zero_iff_mem_span {u q : Fin 3 → ℝ} (hu : u ≠ 0) :
    u ⨯₃ q = 0 ↔ q ∈ Submodule.span ℝ {u} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hli : LinearIndependent ℝ ![u, q] := (LinearIndependent.pair_iff' hu).mpr hne
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h
  · rintro ⟨a, rfl⟩
    rw [map_smul, cross_self, smul_zero]

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **Rank one.** If `rank C = 1` and the column `u = C_{·j}` is nonzero, then
`q ∈ Ran C ↔ u × q = 0`. -/
theorem mem_range_iff_cross_eq_zero_of_rank_one {C : Matrix (Fin 3) k ℝ} (hC : C.rank = 1)
    (j : k) (hu : Cᵀ j ≠ 0) (q : Fin 3 → ℝ) :
    q ∈ LinearMap.range C.mulVecLin ↔ Cᵀ j ⨯₃ q = 0 := by
  have hle : Submodule.span ℝ {Cᵀ j} ≤ LinearMap.range C.mulVecLin := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]; rfl⟩
  have heq : Submodule.span ℝ {Cᵀ j} = LinearMap.range C.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hu]; exact hC.symm)
  rw [← heq, cross_eq_zero_iff_mem_span hu]

omit [DecidableEq k] in
/-- **Rank zero.** If `rank C = 0`, then `q ∈ Ran C ↔ q = 0`. -/
theorem mem_range_iff_eq_zero_of_rank_zero {m : Type*} [Fintype m] {C : Matrix m k ℝ}
    (hC : C.rank = 0) (q : m → ℝ) :
    q ∈ LinearMap.range C.mulVecLin ↔ q = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero] at hC
  rw [hC, Submodule.mem_bot]

variable {C : Matrix (Fin 3) (Fin 2) ℝ} {D : Matrix (Fin 2) (Fin 3) ℝ}

/-- The normal `n = c₁ × c₂` is orthogonal to `Ran C`. -/
theorem normal_dot_range (x : Fin 2 → ℝ) : (Cᵀ 0 ⨯₃ Cᵀ 1) ⬝ᵥ (C *ᵥ x) = 0 := by
  rw [dotProduct_mulVec, ← mulVec_transpose]
  have h0 : (Cᵀ *ᵥ (Cᵀ 0 ⨯₃ Cᵀ 1)) = 0 := by
    ext j
    fin_cases j
    · exact dot_self_cross _ _
    · exact dot_cross_self _ _
  rw [h0, zero_dotProduct]

/-- `nᵀ q = det(c₁, c₂, q)`. -/
theorem normal_dot_eq_det (q : Fin 3 → ℝ) :
    (Cᵀ 0 ⨯₃ Cᵀ 1) ⬝ᵥ q = Matrix.det ![Cᵀ 0, Cᵀ 1, q] := by
  rw [dotProduct_comm, ← triple_product_eq_det, triple_product_permutation,
    triple_product_permutation]

/-- Rank two forces `n = c₁ × c₂ ≠ 0`. -/
theorem normal_ne_zero_of_rank_two (hC : C.rank = 2) : Cᵀ 0 ⨯₃ Cᵀ 1 ≠ 0 := by
  rw [crossProduct_ne_zero_iff_linearIndependent]
  have hcol : C.col = ![Cᵀ 0, Cᵀ 1] := by
    ext j i; fin_cases j <;> rfl
  rw [← hcol, linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    ← rank_eq_finrank_span_cols, hC, Fintype.card_fin]

/-- `‖e_*‖² ‖n‖² = (nᵀ q)²` (Lagrange identity with `e_* × n = 0`). -/
theorem residual_dot_mul_normal_dot (hP : IsRangeProjector C D) (q : Fin 3 → ℝ) :
    (residual C D q ⬝ᵥ residual C D q) * ((Cᵀ 0 ⨯₃ Cᵀ 1) ⬝ᵥ (Cᵀ 0 ⨯₃ Cᵀ 1))
      = ((Cᵀ 0 ⨯₃ Cᵀ 1) ⬝ᵥ q) ^ 2 := by
  set e := residual C D q
  set n := Cᵀ 0 ⨯₃ Cᵀ 1
  have he : ∀ j : Fin 2, e ⬝ᵥ Cᵀ j = 0 := by
    intro j
    have := residual_dot_range hP q (Pi.single j 1)
    rwa [mulVec_single_one] at this
  have hcross : e ⨯₃ n = 0 := by
    rw [cross_cross_eq_smul_sub_smul', he 1, dotProduct_comm, he 0, zero_smul, zero_smul,
      sub_zero]
  have hL := cross_dot_cross e n e n
  rw [hcross, zero_dotProduct] at hL
  have hnq : n ⬝ᵥ q = n ⬝ᵥ e := by
    have : q = e + C *ᵥ (D *ᵥ q) := by
      have h' : q - C *ᵥ (D *ᵥ q) = e := sub_mulVec_eq_residual q
      rw [← h']; abel
    conv_lhs => rw [this]
    rw [dotProduct_add, normal_dot_range, add_zero]
  rw [hnq, dotProduct_comm n e, sq]
  rw [dotProduct_comm n e] at hL
  linarith

/-- **`eq:supp-finite-range-distance`.** For `C = (c₁ c₂)` of rank two and `n = c₁ × c₂`,
`‖e_*‖ = |nᵀ q| / ‖n‖ = |det(c₁, c₂, q)| / ‖c₁ × c₂‖`. -/
theorem residual_norm_rank_two (hP : IsRangeProjector C D) (hC : C.rank = 2) (q : Fin 3 → ℝ) :
    eNorm (residual C D q) = |(Cᵀ 0 ⨯₃ Cᵀ 1) ⬝ᵥ q| / eNorm (Cᵀ 0 ⨯₃ Cᵀ 1) ∧
      eNorm (residual C D q) = |Matrix.det ![Cᵀ 0, Cᵀ 1, q]| / eNorm (Cᵀ 0 ⨯₃ Cᵀ 1) := by
  have hn := normal_ne_zero_of_rank_two hC
  set n := Cᵀ 0 ⨯₃ Cᵀ 1
  have hnn : 0 < n ⬝ᵥ n := lt_of_le_of_ne (dot_self_nonneg n)
    (Ne.symm (by rwa [Ne, dotProduct_self_eq_zero]))
  have hkey := residual_dot_mul_normal_dot hP q
  have he : residual C D q ⬝ᵥ residual C D q = (n ⬝ᵥ q) ^ 2 / (n ⬝ᵥ n) := by
    field_simp; linarith
  have h1 : eNorm (residual C D q) = |n ⬝ᵥ q| / eNorm n := by
    rw [eNorm, he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, eNorm]
  exact ⟨h1, by rw [h1, normal_dot_eq_det]⟩

end Three

end FiniteRangeTest
end RenewalGeometry
